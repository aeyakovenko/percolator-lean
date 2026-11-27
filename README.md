# `percolator-lean` — Formally Verified Realizable Cross-Margin Perpetuals DEX on Solana

> **⚠️ Educational & Research Purposes Only — Not Audited for Production Use**
>
> This repository, on-chain programs, and formal proofs are provided **strictly for educational and research purposes**. This code has **not** undergone an independent third-party security audit and is **not** intended for production deployment or handling real user funds. Formal proofs apply only to the explicitly modeled specifications and invariants and do not guarantee the absence of bugs across unverified handlers, external integrations, or the compiler/runtime boundary. Use at your own risk — provided **"AS IS"** without warranty of any kind under the [Apache License 2.0](LICENSE).

`percolator-lean` is a minimal, composable, formally verified Solana perpetuals DEX written in **Lean 4** and compiled directly to zero-heap **sBPF v3** (`e_flags = 3`) bytecode via [`lean-svm`](https://github.com/aeyakovenko/lean-svm).

It achieves **full cross-margin capital efficiency on healthy markets** (hedged spreads net 1:1 with zero warmup drag and optional `I_m`-contained cross-PnL fronting) while maintaining **machine-checked per-market risk isolation**: permissionlessly created or adversarial markets cannot drain other markets, untouched users, or other markets' insurance pools.

The repository ships a minimal core clearinghouse ([`percolator.so`](Percolator/Program.lean)) plus **5 formally verified composable external programs** that integrate via CPI without bloating or modifying the core ABI:
- **[`Percolator.Matcher`](Percolator/Matcher.lean)** (`6,200 B`) — zero-signer-delegation CPI-Out PropAMM supporting single- and multi-market batch fills (`k ∈ [1..8]`) with market allowlist pinning, spread + inventory-impact quoting, and 0 custody.
- **[`Percolator.LimitMatcher`](Percolator/LimitMatcher.lean)** (`13,488 B`) — **zero-ABI-change Hyperliquid-parity personal orderbook** (`864 B` `LimitBookCtx`, 8 independent order slots across any markets) bound via `SetPortfolioMatcher` + `TradeWithMatcher` with `Sysvar1nstructions` caller auth (`LErr.wrongCaller = 302`). Supports all 13 HL modes: multi-order ladders, GTC, GTD expiry, ALO Post-Only, FOK, Reduce-Only, Price Improvement, Stop-Loss Market/Limit, Take-Profit Market/Limit, Trailing Stop (+ permissionless `Op 5 CrankTrailing`), TWAP Slicer, atomic linked OCO (`ocoLink ∈ 0..7`), Multi-Market Batch Fills (`k ∈ [1..8]`), and 1-tx crossing-order flash-arb clearing (`15,070 CU`, 0 maker sigs).
- **[`Percolator.OracleAdapter`](Percolator/OracleAdapter.lean)** (`18,936 B`) — permissionless on-chain oracle bridge natively parsing **Pyth Pull (`PriceUpdateV2`)**, **Chainlink OCR2 (`Transmissions`)**, **Switchboard On-Demand (`PullFeedAccountData`, 128-bit `PRECISION=18`)**, custom feeds, **2-leg composite ratios** (`base / quote`, e.g. `STOXX/SOL`), and **EWMA smoothing + Hybrid After-Hours mode**, with pinned feed owners/IDs, confidence & staleness checks, smooth multi-slot auto-clamped convergence, and on-chain premium funding.
- **[`Percolator.HlpVault`](Percolator/HlpVault.lean)** (`17,384 B`) — permissionless LP share vault owning a PDA `Portfolio` for zero-ADL liquidation takeovers (`Liquidate mode=1`) and allowlist-pinned PropAMM market-making with anti-ERC-4626-inflation first-deposit locking and NAV non-dilution proofs.
- **[`Percolator.RewardModule`](Percolator/RewardModule.lean)** (`20,456 B`) — permissionless per-market Gavel $xy=k$ uniform-price batch buy-and-burn module supporting SPL Token, Token-2022, and wSOL with strict 5th-bucket (`F_tot`) isolation.

| Program | ELF `.so` Size (sBPF v3) | sBPF Insns | Stack | Heap | Formal Lean 4 Proofs (`0 sorry`, `0` custom axioms) |
|---|---:|---:|---:|---:|---|
| **[`Percolator.Program`](Percolator/Program.lean)** (Core DEX) | **92,592 B** | 11,532 | 784 B | 0 B | **234+ public theorems** across `Spec`/`Proofs`/`TraceProofs`/`ThreatModel`/`Refinement`/`AbiProofs`/`HandlerProofs`/`LivenessProofs`/`ExternalProofs` |
| **[`Percolator.Matcher`](Percolator/Matcher.lean)** (CPI-Out PropAMM) | **6,200 B** | 733 | 64 B | 0 B | **7 theorems** (layout, ask/bid bounds, `maxMove` clamp, LP-favorable spread) |
| **[`Percolator.LimitMatcher`](Percolator/LimitMatcher.lean)** (HL Orderbook) | **13,488 B** | 1,644 | 280 B | 0 B | **7 theorems** (`limit_book_layout_valid`, `limit_fill_conserves_remaining`, `oco_sync_cancels_partner`, `twap_slice_bounded`, `alo_post_only_passive`, `stop_and_tp_trigger_sound`, `trailing_watermark_monotone`) |
| **[`Percolator.OracleAdapter`](Percolator/OracleAdapter.lean)** (Oracle Bridge) | **18,936 B** | 2,325 | 552 B | 0 B | **8 theorems** (clamp + funding bounds, OCR2 ring-buffer, E6 scaling, 2-leg ratio, EWMA bounds/fixed-point/refinement) |
| **[`Percolator.HlpVault`](Percolator/HlpVault.lean)** (HLP Takeover Vault) | **17,384 B** | 2,131 | 864 B | 0 B | **7 theorems** (layout, anti-inflation lock, NAV non-dilution, withdrawal solvency, allowlist subset anti-rug) |
| **[`Percolator.RewardModule`](Percolator/RewardModule.lean)** (Buy & Burn) | **20,456 B** | 2,515 | 704 B | 0 B | **10 theorems** (layout, $xy=k$ invariant, batch solvency, quiet-epoch cap, spam monotonicity, exact fee-split conservation) |
| *Total* | *6 production ELFs* | — | — | **0 B** | **273 public theorems** (322 incl. private lemmas), `0 sorry`, `0` custom axioms |

---

## 1. Architecture & Composability

```
┌──────────────────────────────────┐  ┌──────────────────────────────────┐
│ Percolator.Matcher (6,200 B)     │  │ Percolator.LimitMatcher (13.5KB) │
│ • CPI-Out PropAMM (k=1..8 batch) │  │ • 8-Slot HL Personal Orderbook   │
│ • Zero Signer Delegation         │  │ • All 13 HL Modes + OCO + TWAP   │
│ • Allowlist-Pinned Markets       │  │ • Sysvar1nstructions Caller Auth │
└────────────────┬─────────────────┘  └────────────────┬─────────────────┘
                 └──────────┐  CPI-Out (`MRET`) ┌──────┘
                            ▼  TradeWithMatcher ▼
┌────────────────────────────────────────────────────────────────────────┐
│           percolator-lean Core (92,592 B · 24 ops · sBPF v3 · 0 heap)  │
│ • Realizable 8-Leg Cross-Margin     • Per-Leg `lockedMm` Firewall      │
│ • 5-Bucket Exact C+I+R+S+F = V      • I_m-Contained Cross-PnL Fronting │
│ • Mode-4 Atomic Netting / Flip      • K+1=5 Compounded Oracle Envelope │
│ • Post-ADL Monotone Recovery        • Zero-Heap sol_log_64_ Events     │
└──────────────────▲──────────────────────────▲──────────────────────────┘
                   │ CPI                      │ CPI
┌──────────────────┴───────────────┐  ┌───────┴──────────────────────────┐
│ Percolator.OracleAdapter (18.9KB)│  │ Percolator.HlpVault (17.4KB) &   │
│ • Pyth V2 / Chainlink / SB 128b  │  │ Percolator.RewardModule (20.5KB) │
│ • 2-Leg Ratios + EWMA / AfterHrs │  │ • PDA Takeover + xy=k Buy&Burn   │
└──────────────────────────────────┘  └──────────────────────────────────┘
```

Keeping matching, limit orderbooks, AMM quoting, external oracle parsing, HLP vaults, and fee buy-and-burn in external composable programs keeps the core clearinghouse minimal, auditable, and ABI-stable:
- Any user EOA (or PDA vault) can bind an external matcher context (`Matcher` or `LimitMatcher`) to their `Portfolio` via `SetPortfolioMatcher` with **zero signer delegation** and **zero custody**: the matcher only writes `(execPrice_i, fillQty_i)` quotes into its `MRET` context during `TradeWithMatcher` CPI-Out, while `Percolator.Program` enforces margin, `maxMoveBps` clamp, and settlement.
- Any external oracle bridge (Pyth, Switchboard, Chainlink, composite ratio, EWMA) can hold `Market.oracleAuth` via its PDA and crank `UpdateOracle`.

---

## 2. Core Protocol Design

### 2.1 Realizable Shared Cross-Margin & Exact 5-Bucket Stock Equality

1. **One shared quote custody vault (`DexVault` PDA `["dvlt", dex]`)**, created and initialized directly on-chain by `InitDex` via `SystemProgram::Transfer + Allocate + Assign + SPL Token InitializeAccount3` (immune to 1-lamport pre-funding griefing).
2. **Exact five-class accounting partition:**
   $$C_{\text{tot}} + I_{\text{tot}} + R_{\text{tot}} + S_{\text{tot}} + F_{\text{tot}} = V$$
   where $C_{\text{tot}} = \sum_p (\text{capital}_p + \text{totalLockedMm}_p)$ (shared free collateral + per-leg isolated maintenance margin), $I_{\text{tot}} = \sum_m I_m$ (per-market isolated insurance), $R_{\text{tot}} = \sum_m R_m$ (per-market isolated realized loser pools), $S_{\text{tot}} = \sum_m S_m$ (rounding sinks + orphan dust), $F_{\text{tot}} = \sum_m \text{rewardAccrued}_m$ (per-market reward module accruals), and $V$ is the exact SPL Token balance of `DexVault`.
3. **Instant backed profit realization & `I_m`-contained fronting:** Positive PnL on market $m$ (`posPnl`) is a claim strictly against market $m$'s own `realizedPool` $R_m$ (plus optional `maxFrontBps`-capped senior fronting from $I_m$ when `adl == ADL_ONE`, repaid first by incoming loser settlement). On healthy markets, `RefreshLeg` immediately credits `posPnl` **1:1 into shared `pfl.capital`** with zero warmup drag.
4. **Insolvent haircut conservation:** When $R_m < P^+_m$ (and fronting does not cover), positive PnL payout is strictly bounded by floor division $\lfloor p \cdot \min(R_m, P^+_m) / P^+_m \rfloor \le \min(p, R_m)$, proven monotone non-decreasing for remaining claimants (`haircutPayout_monotone_ratio` — no first-mover drain).

### 2.2 Per-Leg `lockedMm` Firewall & Cross-Market Non-Contagion

Each `Portfolio` splits collateral into shared free `capital` and per-leg isolated `leg.lockedMm` (`totalLockedMm = ∑ active_leg.lockedMm`), with exact accounting invariant $C_{\text{tot}} = \sum_p (\text{capital}_p + \text{totalLockedMm}_p)$. When leg $j$ incurs a loss or liquidation fee, debits are strictly capped at:

$$\text{availCap}(j) = \text{capital} + \text{leg}_j.\text{lockedMm}$$

Other legs' `lockedMm` (`otherLocked = totalLockedMm - leg_j.lockedMm`) are **never** touched or raided by market $j$:
- **Strict Permissionless Non-Contagion:** Even a god-mode attacker who creates a malicious market `M_atk`, pumps it +25%–+1000%, and drains shared `freeCapital -> 0` and `M_atk.lockedMm -> 0` leaves `BTC.lockedMm` **bit-for-bit intact** (`svm_to_firewall_multi_market_isolation`, `threat_multi_market_permissionless_firewall_non_contagion`), guaranteeing `shortfall = 0` and `0` draw on `I_BTC`.
- **Full HL-UX Capital Efficiency:** Free excess capital above `totalLockedMm` (plus instant realized profits) flows 1:1 across all 8 legs, letting hedged cross-margin portfolios survive deep parallel moves (`Suite 16E` -20% survival & 3rd-leg cross reuse) without liquidation.
- **Overflow-Immune Settlement & `MAX_MKT_NOTIONAL` Cap:** Both `CreateMarket` and `UpdateOracle` enforce `max(oiL, oiS) * markPrice / POS_SCALE <= MAX_MKT_NOTIONAL` (`10^17` = `$100B` at E6), and `settleAndRefreshLeg` uses saturating 128-bit arithmetic (`mulDiv64Sat`, `mulDiv64CeilSat`, `creditSatGain`) so adversarial self-made markets can never trigger `ArithmeticOverflow` DoS (`#110`).

### 2.3 Bankrupt Settlement Containment, All-Leg Freshness & Post-Fee Partial-Liq Solvency

- **No silent bad-debt write-offs outside `Liquidate` (`#109` / PR #8):** `settleAndRefreshLeg` enforces `allowBankrupt = false` on every non-liquidation path (`RefreshLeg`, `Trade` `mode=0..4`, `TradeWithMatcher`, and `Liquidate` takeover liquidator), rejecting any `shortfall > 0` with `PErr.insufficientMargin` (`Custom(107)`) so `Mkt.insFronted` can never be silently written off without running the liquidation waterfall.
- **Anti-selective-liquidation without 2-bankrupt-leg deadlock (`#109` / `#110`):** `Liquidate` enforces `checkAllLegsFreshLoop` (`leg.lastRefreshSlot == curSlot` across all active legs) whenever the target leg is solvent (`shortfall == 0 && (freeCap > 0 || legLock > 0)`), protecting net-healthy hedged spreads from selective single-leg liquidation while allowing any genuinely bankrupt leg to liquidate immediately without another bankrupt/stale leg holding a veto.
- **Post-`liqFee` partial-liquidation solvency (`#107`):** Any partial liquidation (`remRaw > 0`) enforces `remEff > 0 && postAvail > 0 && postEq >= remMm && remMm >= minMm` (`PErr.invalidParams` / `Custom(103)`), where `postAvail = availCap - liqFee` and `postEq = postAvail + posPnl` — eliminating zero-capital post-fee zombie legs and dust-notional unit mismatches.
- **Exact `K+1=5` compounded oracle envelope:** `CreateMarket` enforces exact 5-step compounding `k5MoveBps + liqAtP5 <= mmBps` (`threat_k5_compounded_bound_exact`, `threat_k5_liqFee_at_p5_zero_bad_debt`), preventing multi-slot leader-censorship bad debt across `K = 4` censored slots.

### 2.4 Fair Liquidations, Atomic Flip (`mode=4`), Post-ADL Recovery & Bounded Lifecycle

- **Zero trusted liquidation oracle:** Partial/full closes (`mode=0` fallback, `mode=1` zero-ADL counterparty/HLP takeover) derive strictly from on-chain mark prices and exact `oiSide / rawBasisSide` ratios, with gradual deficit-scaled liquidation fees.
- **Atomic netting & position flip (`Trade` / `TradeWithMatcher` `mode=4`):** Closes existing opposite exposure and opens net new exposure in a single instruction (`tradeNettedSplit_sound`, `legCloseCapU64_refines_spec`), including multi-market batch flips (`k ∈ [1..8]`).
- **Post-ADL monotone recovery & same-side hand-offs (`mode=2/3`):** Partially-ADL'd markets remain open for new bilateral trades (`postAdlOpen_preserves_adl_monotone`) and zero-ADL takeovers (`liquidateTakeoverPostAdl_sound`). Same-side L→L / S→S hand-offs preserve OI & ADL bit-for-bit while charging `tradeFeeBps` on the incoming buyer.
- **Bounded permissionless exit liveness:** `maxStaleness ≤ 9,000` (~1h), `exitWindow ≤ 216,000` (~24h), `Active → WindDown → ForceClosePair → ResolveMarket → ClaimResolved → TombstoneMarket → CloseAccount` (100% rent reclaim with permanent `MAGIC_CLOSED` same-tx revival immunity).

---

## 3. Account Layouts

| Account | Magic | Size | Key Fields |
|---|---|---:|---|
| **`Dex`** | `PDEX` | 208 B | `admin`, `quoteMint`, `vaultPda`, `vaultBump`, `decimals`, `allowFreeze`, `feeVault`, `nextMarketId`, `nextPortfolioId`, `createFee`, `vaultBalance (V)`, `totalCapital (C)`, `totalInsurance (I)`, `totalResidual (R)`, `totalSurplus (S)`, `totalRewards (F)` |
| **`Market`** | `MKTP` | 400 B | `status`, `maxFrontBps`, `marketId`, `dex`, `oracleAuth`, `marketAdmin`, `markPrice`, `lastOracleSlot`, `windDownSlot`, immutable risk params (`imBps`, `mmBps`, `liqFeeBps`, `tradeFeeBps`, `maxMoveBps`, `maxInsDrawBps`, `maxOi`, `exitWindow`, `maxStaleness`, `minMm`, `rewardBps`, `rewardRecipient`), `realizedPool`, `insurance`, `insFronted`, `totalPosPnl`, `totalInsShares`, `oiLong/Short`, `rawBasisLong/Short`, `adlLong/Short`, `kLong/Short`, `resolvedNum/Den`, `activeLegs`, `rewardAccrued` |
| **`Portfolio`** | `PFLO` | 976 B | 144 B header (`legCount`, `portfolioId`, `totalLockedMm`, `dex`, `owner`, `capital`, `totalMm`, `totalIm`, `matcherCtx`) + **8 × 104 B `Leg` slots** (incl. per-leg `lockedMm`) |
| **`InsReceipt`** | `INSR` | 88 B | `marketId`, `owner`, `market`, `shares` |
| **`LimitBookCtx`** | `MRET` | 864 B | 144 B standard `MatcherReturn` (16 B header + 8 × 16 B quotes) + `owner` + `percolatorProg` + `paused` + **8 × 80 B `OrderSlot`** |

---

## 4. Core Instruction Set (24 Minimal Instructions)

| Op | Instruction | Purpose |
|---:|---|---|
| 0 | `InitDex` | Initialize `Dex` (208 B) and create/initialize `DexVault` PDA on-chain (`Transfer + Allocate + Assign + InitializeAccount3`) |
| 1 | `UpdateCreateFee` | Update future `createFee` (`<= MAX_CREATE_FEE`) and optionally rotate `dex.admin` |
| 2 | `CreateMarket` | Permissionlessly create isolated `Market` (400 B) enforcing `K+1=5` solvency envelope, `MAX_MKT_NOTIONAL`, optional `minMm` & `rewardBps` |
| 3 | `UpdateMarketAuth` | Transfer or permanently burn `marketAdmin` (`role=0`), or rotate `oracleAuth` (`role=1`) |
| 4 | `UpdateOracle` | Rate-limited (`curSlot > lastOracleSlot`), clamped mark price + funding step + `MAX_MKT_NOTIONAL` guard |
| 5 | `InitPortfolio` | Initialize 8-leg shared cross-margin `Portfolio` (976 B, EOA or PDA owner) |
| 6 | `DepositCollateral` | Permissionlessly deposit quote SPL tokens into any portfolio's shared `capital` |
| 7 | `WithdrawCollateral` | Owner-signed withdrawal enforcing same-slot leg freshness + `freeCap' + totalLockedMm >= totalIm` |
| 8 | `DepositInsurance` | Mint isolated LP shares for `I_m` (`MIN_FIRST_INS_DEPOSIT`), or permanently donate (`donate=1`) |
| 9 | `WithdrawInsurance` | Burn LP shares for pro-rata `I_m` (requires `OI == 0 ∧ rawBasis == 0`; allows worthless share burn post-tombstone) |
| 10 | `RefreshLeg` | Permissionless $O(1)$ settle (`allowBankrupt = false`), backed/fronted `posPnl` realization, firewall sync & slot stamp |
| 11 | `Trade` | Bilateral open (`mode=0`), proportional reduce (`mode=1`), same-side hand-off (`mode=2/3`), or atomic netting/flip (`mode=4`) with optional clamped `execPrice` spread |
| 12 | `Liquidate` | Permissionless partial/full liquidation (`mode=0` fallback or `mode=1` zero-ADL takeover) with post-`liqFee` solvency, all-leg freshness on solvent legs, bankrupt deadlock bypass, and capped `I_m` + derived ADL |
| 13 | `ClearDeadLeg` | Permissionlessly clear zero-OI post-ADL leg & reset `adlSide → ADL_ONE` |
| 14 | `StartWindDown` | Admin or permissionless stale-oracle transition to `WindDown` |
| 15 | `ForceClosePair` | Permissionless post-`exitWindow` forced bilateral close |
| 16 | `ResolveMarket` | Snapshot immutable pro-rata payout ratio once `oi = rawBasis = activeLegs = 0` |
| 17 | `ClaimResolved` | Order-independent pro-rata claim from `R_m` into shared `pfl.capital` |
| 18 | `TombstoneMarket` | Permanently seal drained market (`I_m = 0 ∧ P^+_m = 0 ∧ rewardAccrued = 0`) |
| 19 | `CloseAccount` | Unified rent reclaim with permanent `MAGIC_CLOSED` (`DEAD`) stamp for empty `Portfolio`, `InsReceipt`, or `Tombstoned` `Market` |
| 20 | `SweepSurplus` | Admin sweep strictly bounded to `Dex.totalSurplus` (`S_tot`); never touches `C`, `I`, `R`, or `F` |
| 21 | `ClaimReward` | Permissionless-market `rewardRecipient`-signed claim of accrued `Market.rewardAccrued` (`F_m`) |
| 22 | `SetPortfolioMatcher` | Portfolio owner binds/unbinds an external `Matcher` or `LimitMatcher` context (`PflOff.matcherCtx`) with 0 signer delegation |
| 23 | `TradeWithMatcher` | Single- or multi-market batch (`k ∈ [1..8]`) taker fill via CPI-Out to maker's bound matcher (`Matcher` or `LimitMatcher`) |

---

## 5. Structured Zero-Heap Event Logs (`sol_log_64_`)

| Tag | Event | Payload `(arg0, arg1, arg2, arg3, arg4)` |
|---:|---|---|
| `1` | `Oracle` | `(1, marketId, newPrice, fundSign, fundE6)` |
| `2` | `Trade` | `(2, (marketId << 8) \| mode, qty, execPrice, markPrice)` |
| `3` | `Liquidate` | `(3, (marketId << 8) \| mode, rawClose, liqFee, shortfall)` |
| `4` | `Deposit` | `(4, portfolioId, amount, newCapital, 0)` |
| `5` | `Withdraw` | `(5, portfolioId, amount, newCapital, 0)` |
| `6` | `ForceClose` | `(6, marketId, closedQty, remainingOi, slot)` |
| `7` | `Resolve` | `(7, marketId, resolvedNum, resolvedDen, 0)` |
| `8` | `SweepSurplus` | `(8, sweepAmt, remainingSurplus, 0, 0)` |
| `9` | `ClaimReward` | `(9, marketId, claimAmt, remainingReward, 0)` |

---

## 6. Verification & Benchmarks (LiteSVM `0.18.2` / Agave `4.3.2`, sBPF v3)

See [`INVARIANTS.md`](INVARIANTS.md) for the full catalog of **273 public Lean 4 theorems** (`0 sorry`, `0` custom axioms). All **17 end-to-end LiteSVM suites** in [`svm-runner/src/main.rs`](svm-runner/src/main.rs) + **22 standalone tests** in [`svm-runner/src/boring_tests.rs`](svm-runner/src/boring_tests.rs) pass 100% on strict sBPF v3 ELFs (`e_flags = 3`, 0 relocations, 0 heap):

### Worst-Case 8-Leg / 16-Leg CU & Legacy Wire-MTU Benchmarks (Suite 11)

| Role & Worst-Case Transaction | Compute Units | % of 200k Default CU | Legacy Wire Size | % of 1,232 B MTU |
|---|---:|---:|---:|---:|
| **User — 8-Leg Atomic Withdraw** `[8× RefreshLeg + WithdrawCollateral]` | **12,372 CU** | 6.2% | **793 B** | 64.4% |
| **User — Double-8-Leg Trade** `[16× RefreshLeg + Trade]` (16 legs) | **20,920 CU** | 10.5% | **865 B** | 70.2% |
| **User — Position Hand-Off** `[7× RefreshLeg + Trade(mode=2 / mode=3)]` | **11,175 / 12,016 CU** | 5.6% / 6.0% | **793 B** | 64.4% |
| **User — Post-ADL Open** `[15× RefreshLeg + Trade(mode=0)]` | **21,380 CU** | 10.7% | **857 B** | 69.6% |
| **Liquidation Keeper — 8-Leg Fallback** `[7× RefreshLeg + Liquidate(mode=0)]` | **12,350 CU** | 6.2% | **690 B** | 56.0% |
| **Liquidation Keeper — Double-8-Leg Post-ADL Takeover** `[14× RefreshLeg + Liquidate(mode=1)]` | **19,718 CU** | 9.9% | **876 B** | 71.1% |
| **Crank — 8-Market Oracle Batch** `[8× UpdateOracle]` (1 tx) | **5,384 CU** | 2.7% | **702 B** | 57.0% |
| **Crank — Native Oracle Parsers (CPI)** (Pyth V2 / CL OCR2 / SB 128b / Ratio / EWMA live / AH / Push) | **2,439 / 2,393 / 3,338 / 2,705 / 2,722 / 2,592 / 372 CU** | 0.2%–1.7% | — | — |
| **Hyperliquid LimitMatcher — 1-Tx Crossing Flash-Arb** `[2× TradeWithMatcher]` (0 maker sigs) | **15,070 CU** | 7.5% | — | — |
| **PropAMM Batch CPI-Out** (`k=1` open/close, `k=2`, `k=5` open/close) | **5,013 / 4,633 / 7,815 / 16,815 / 15,193 CU** | 2.3%–8.4% | — | — |
| **Atomic Position Flip (`mode=4`)** (direct / `k=3` PropAMM batch flip) | **5,090 / 22,304 CU** | 2.5% / 11.2% | — | — |

### Full 17-Suite Verification Summary

1. **Suite 1 — On-Chain `InitDex` PDA Vault Creation (`5,542 CU`)**: Real SPL `DexVault` PDA creation despite 1-lamport pre-funding griefing; rejects fake token/system programs & bad bumps.
2. **Suite 2 — Multi-Market Creation (`3,462 CU`)**: Enforces `K+1=5` solvency envelope & isolated `I_m`.
3. **Suite 3 — Cross-Margin Capital Efficiency (`trade 2,761 CU`, `refresh 1,231 CU`, `atomic-wdr 4,228 CU`)**: Hedged BTC/ETH spread survives parallel drop with 0 liquidation and atomic withdrawal.
4. **Suite 4 — Permissionless 8-Leg Cross-Margin Firewall + God-Mode `RUG` Immunity (`liq 3,258 CU`)**: Zero shielding, zero cross-insurance leak, stale-leg non-blocking, Bug 1B/1C checks.
5. **Suite 5 — Runtime Security Regressions**: Rejects same-slot oracle spam, unclamped jumps, executable `noop.so` as `tokenProgram`, wrong mint/vault, aliased trades, live-OI insurance withdrawals.
6. **Suite 6 — Post-ADL Recovery, Wind-Down, Tombstone & Rent Reclaim (`clearDeadLeg 1,175 CU`, `closeAccount 1,115 CU`)**.
7. **Suite 7 — Bounded `execPrice` Spreads, Authority Rotation, `minMm` Floor, Donated-Insurance Tombstone & `sol_log_64_` Events**.
8. **Suite 8 — 1,000-Step Stateful Fuzzer**: 483 valid randomized cross-margin txs checking exact 5-bucket global & per-market invariants — 0 violations.
9. **Suite 9 — External CPI (`OracleAdapter` Pyth/CL/SB/Ratio/EWMA + `Matcher` + Atomic Crank+LP Bundle + `K=4` Censored Liquidation)**.
10. **Suite 10 — Core Hardening & Partial Permissionless Takeover (`4,856 CU`, gradual fee `< max`, 0 ADL)**.
11. **Suite 11 — Worst-Case 8-Leg & 16-Leg CU/MTU Exhaustion + Anti-Selective-Liquidation + Post-ADL Recovery + Position Hand-Off**.
12. **Suite 12 — 22 Functional, Security & HL-Parity Limit-Order Tests ([`svm-runner/src/boring_tests.rs`](svm-runner/src/boring_tests.rs))**:
    - `t01`–`t14`: Deposit/withdraw/reclaim, Long/Short PnL + fees, scale-in & partial closes, position flips, bid/ask spreads, bidirectional funding, 3 exit-order permutations, partial/full liqs, HLP takeovers, cross-margin BTC+ETH offset, margin/freshness guards, AMM fills, Insurance LP yield & redemption, full wind-down lifecycle.
    - `t15`–`t18`: Same-tx account revival / dirty-buffer init / oversized-account / share-coherence, owner-gated `forceHaircut`, freeze-authority flag, `I_m`-fronting & LP NAV sweep, `mode=4` atomic netting/flip edge cases.
    - **`t19` (`test_19_flash_arb_crossing_limit_order_matchers`)**: Full **13-mode Hyperliquid `LimitMatcher`** suite (GTC, GTD, ALO Post-Only, FOK, Reduce-Only, Price-Improve, SL Market/Limit, TP Market/Limit, Trailing Stop + `CrankTrailing`, TWAP Slicer, linked OCO, Multi-Market Batch Fills, `Sysvar1nstructions` grief-rejection, and 1-tx crossing flash-arb in `15,070 CU`).
    - **`t20` (`test_20_pr8_bankrupt_settlement_blocked_regression`)**: Repro of `#109` / PR #8 — proves slot-1 liquidation succeeds with `0` `I_m` draw, rejects bankrupt `TradeWithMatcher(mode=1)`, `Trade(mode=1)`, and `RefreshLeg` with `Custom(107)`, and proves `handleLiquidate` cleanly repays `insFronted`.
    - **`t21` (`test_21_issue107_partial_liq_post_fee_solvency`)**: Repro of `#107` — rejects partial liquidations leaving `postAvail == 0` or `postEq < remMm` (`Custom(103)`), while full liquidation closes cleanly with `0` `I_m` draw.
    - **`t22` (`test_22_issue110_self_made_market_overflow_dos_blocked`)**: Repro of `#110` + `#109` 2-bankrupt-leg deadlock — self-made market + bankrupt BTC both liquidate cleanly without overflow or deadlock.
13. **Suite 13 — Gavel $xy=k$ Uniform-Price Batch Reward Modules**: 8-leg user × 8 unique modules (6× SPL + Token-2022 + wSOL), R1–R6 verified (`settle max 3,375 CU`, `claim max 2,272 CU`).
14. **Suite 14 — Unified Single/Multi-Market CPI-Out PropAMM**: 0 signer delegation, 1-CPI `k=2` & `k=5` mixed Long/Short hedged discount, 12 attacks blocked (`evil_matcher.so`).
15. **Suite 15 — Atomic Position Flip (`mode=4`) + External `HlpVault`**: Direct flip `5,090 CU`, `k=3` batch flip `22,304 CU`, HLP vault takeovers with 0 ADL and 0 rug.
16. **Suite 16 — Full Red-Team + HL-UX Capital Efficiency Regressions**: `16A` `M_atk -> I_BTC` contagion defeated, `16B` PropAMM allowlist, `16C` HLP strategist rugs blocked, `16D` `mode=2/3` handoff fee, `16E` -20% hedged survival & 3rd-leg cross reuse.
17. **Suite 17 — Strict ABI Dup-Stub Regressions (`17A`) + 5,000-Step Multi-Program Adversarial Fuzzer (`17B`)**: 4,760 valid txs across all binaries + 516 adversarial probes blocked, 0 invariant violations.

---

## 7. Build & Reproduce

```bash
# Run full Lean 4 kernel proof verification (273 public theorems, 0 sorry, 0 custom axioms),
# compile all 7 sBPF v3 .so binaries, and execute all 17 LiteSVM suites:
./scripts/build-and-test.sh

# Run all 22 boring exchange, security & HL limit-order LiteSVM tests individually:
cargo test --manifest-path svm-runner/Cargo.toml --release
```

---

## 8. License & Disclaimer

Licensed under the [Apache License, Version 2.0](LICENSE).

This repository is experimental and provided **for educational and research purposes only**. Do not deploy these programs to mainnet with real funds without thorough independent auditing and end-to-end verification.
