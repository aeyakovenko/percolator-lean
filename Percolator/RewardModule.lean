/-
  Percolator.RewardModule
  Formally verified, permissionless Gavel-style `xy = k` Virtual-Reserve X-Minute
  Uniform-Price Batch Buy-and-Burn Reward Module (`percolator-lean` CPI).

  Design (zero admin rug, zero oracle, unlimited AMM-style bids, O(1) settlement,
  supports ANY external SPL Token, Token-2022, or wSOL):
  1. At `CreateMarket`, a permissionless market creator immutably configures `rewardBps`
     (0..10000 bps of that market's trade fees) and `rewardRecipient = PDA(["rewm", cfg.key])`.
  2. `InitReward` (Op 0): One-shot immutable setup by `mkt.marketAdmin`. Binds `RewardCfg` to
     `(percProg, dex, mkt, quoteVault, targetMint, targetEscrow, targetTokProg, burnMode,
     burnSinkTok, epochSlots, minBatchQuote, initReserveRateE6)`.
     - `burnMode = 0`: real SPL Token / Token-2022 `Burn` (`op = 8`) reducing `targetMint.supply`.
     - `burnMode = 1`: permanent dead-sink transfer into `burnSinkTok` owned by `rewAuthPda`
       (ZERO withdraw instruction — required for `wSOL`, since SPL Token forbids `Burn` on NativeMint).
  3. `StartEpoch` (Op 1, permissionless): Once `m.rewardAccrued + rolloverQuote >= minBatchQuote`,
     pulls `m.rewardAccrued` via PDA-signed `percolator::ClaimReward` into `quoteVault`, locks
     the epoch pot `Q_e`, computes virtual reserve `B_virt = ceil(Q_e * reserveRateE6 / 10^6) >= 1`,
     and opens a fixed `epochSlots` window (`>= MIN_EPOCH_SLOTS = 32 >> K = 4` leader window).
  4. `SubmitBid` (Op 2, permissionless, UNLIMITED bids like an AMM, O(1)):
     During `[startSlot, endSlot)`, anyone commits irrevocable `targetMint` into `targetEscrow`
     (measuring exact balance delta — immune to Token-2022 TransferFee inflation!).
     Bids accumulate in per-bidder `BidReceipt` + `epoch.totalBids` (`B_e`). ZERO cancel/spoof!
  5. `SettleEpoch` (Op 3, permissionless, O(1) — NEVER loops over bidders!):
     At `curSlot >= endSlot`, burns ALL `B_e` in ONE single CPI and clears EVERY bidder at the
     exact same uniform `xy = k` clearing price:
       `quotePaid = floor(Q_e * B_e / (B_e + B_virt))`
       `rollover  = Q_e - quotePaid`
     Self-calibrates `reserveRateE6` once per epoch (never per-bid -> zero 1-atom reset griefing!):
       - Healthy epoch (`B_e >= B_virt`): `reserveRateE6 := clamp(clearedRateE6 / 4, 1, MAX_RATE_E6)`
       - Under-filled / quiet epoch (e.g. 1000x pump): `reserveRateE6 := max(1, reserveRateE6 / 2)`
  6. `ClaimQuote` (Op 4, O(1)): Any bidder from any settled epoch independently claims
     `payout_i = floor(Q_e * b_i / (B_e + B_virt))` from `quoteVault` (overlapping epochs supported!).
-/
import LeanSVM
import Percolator.Layout

namespace Percolator.RewardModule

open LeanSVM
open LeanSVM.Input
open LeanSVM.Math
open LeanSVM.CPI
open Percolator

def MAGIC_REWARD    : UInt32 := 0x4D574552 -- "REWM"
def MAGIC_EPOCH     : UInt32 := 0x48435045 -- "EPCH"
def MAGIC_BID       : UInt32 := 0x52444942 -- "BIDR"
def TAG_REW_AUTH    : UInt32 := 0x6D776572 -- "rewm"
def MIN_RATE_E6     : UInt64 := 1_000             -- min 0.001 target-atoms per 1 quote-atom (blocks floor-1 collapse!)
def MAX_RATE_E6     : UInt64 := 1_000_000_000_000 -- 10^6 target-atoms per 1 quote-atom (at E6 scale)
def MAX_VIRT_BIDS   : UInt64 := 0x3FFFFFFFFFFFFFFF -- 2^62 - 1 (caps virtBids so virtBids + totalBids never bricks StartEpoch!)
def MIN_EPOCH_SLOTS : UInt64 := 32                -- >= 8x Solana K=4 leader window
def MAX_EPOCH_SLOTS : UInt64 := 216_000           -- ~24h at 400ms/slot
def EVT_EPOCH_START  : UInt64 := 41
def EVT_SUBMIT_BID   : UInt64 := 42
def EVT_SETTLE_EPOCH : UInt64 := 43
def EVT_CLAIM_QUOTE  : UInt64 := 44

namespace RErr
  def progMismatch   : UInt64 := 400
  def dexMismatch    : UInt64 := 401
  def mktMismatch    : UInt64 := 402
  def mintMismatch   : UInt64 := 403
  def sinkMismatch   : UInt64 := 404
  def epochActive    : UInt64 := 405
  def badBurnMode    : UInt64 := 406
  def recipientBad   : UInt64 := 407
  def belowMinBatch  : UInt64 := 408
  def epochClosed    : UInt64 := 409
  def epochNotEnded  : UInt64 := 410
  def epochMismatch  : UInt64 := 411
  def vaultMismatch  : UInt64 := 413
end RErr

/-! ### Exact Byte Offsets: `RewardCfg` (400B), `EpochState` (104B), `BidReceipt` (120B) -/

namespace RewOff
  def size              : UInt64 := 400
  def magic             : UInt64 := 0   -- u32 ("REWM")
  def pdaBump           : UInt64 := 4   -- u8
  def burnMode          : UInt64 := 5   -- u8 (0 = SPL/Token-2022 Burn, 1 = Permanent wSOL Dead-Sink)
  def quoteDecimals     : UInt64 := 6   -- u8
  def targetDecimals    : UInt64 := 7   -- u8
  def percProg          : UInt64 := 8   -- Pubkey (32)
  def dex               : UInt64 := 40  -- Pubkey (32)
  def market            : UInt64 := 72  -- Pubkey (32)
  def quoteMint         : UInt64 := 104 -- Pubkey (32)
  def quoteVault        : UInt64 := 136 -- Pubkey (32)
  def targetMint        : UInt64 := 168 -- Pubkey (32)
  def targetEscrow      : UInt64 := 200 -- Pubkey (32)
  def targetTokProg     : UInt64 := 232 -- Pubkey (32)
  def burnSinkTok       : UInt64 := 264 -- Pubkey (32)
  def activeEpochAcc    : UInt64 := 296 -- Pubkey (32)
  def epochSlots        : UInt64 := 328 -- u64
  def minBatchQuote     : UInt64 := 336 -- u64
  def reserveRateE6     : UInt64 := 344 -- u64
  def activeEpochId     : UInt64 := 352 -- u64
  def activeQuote       : UInt64 := 360 -- u64
  def rolloverQuote     : UInt64 := 368 -- u64
  def pendingClaims     : UInt64 := 376 -- u64
  def totalQuoteSpent   : UInt64 := 384 -- u64
  def totalTargetBurned : UInt64 := 392 -- u64
end RewOff

namespace EpochOff
  def size         : UInt64 := 104
  def magic        : UInt64 := 0  -- u32 ("EPCH")
  def settled      : UInt64 := 4  -- u8 (0 = open, 1 = settled)
  def cfg          : UInt64 := 8  -- Pubkey (32)
  def epochId      : UInt64 := 40 -- u64
  def quotePot     : UInt64 := 48 -- u64 (Q_e)
  def virtBids     : UInt64 := 56 -- u64 (B_virt)
  def totalBids    : UInt64 := 64 -- u64 (B_e)
  def quotePaid    : UInt64 := 72 -- u64 (floor(Q_e * B_e / (B_e + B_virt)))
  def startSlot    : UInt64 := 80 -- u64
  def endSlot      : UInt64 := 88 -- u64
  def claimedQuote : UInt64 := 96 -- u64
end EpochOff

namespace BidOff
  def size     : UInt64 := 120
  def magic    : UInt64 := 0   -- u32 ("BIDR"; permanently stamped "DEAD" on auto-closing ClaimQuote!)
  def cfg      : UInt64 := 8   -- Pubkey (32)
  def epochAcc : UInt64 := 40  -- Pubkey (32)
  def bidder   : UInt64 := 72  -- Pubkey (32)
  def epochId  : UInt64 := 104 -- u64
  def amount   : UInt64 := 112 -- u64 (b_i)
end BidOff

theorem reward_layout_sizes_valid :
    RewOff.totalTargetBurned + 8 ≤ RewOff.size ∧ RewOff.size % 8 == 0 ∧
    EpochOff.claimedQuote + 8 ≤ EpochOff.size ∧ EpochOff.size % 8 == 0 ∧
    BidOff.amount + 8 ≤ BidOff.size ∧ BidOff.size % 8 == 0 := by
  decide

/-! ### Pure Gavel-Style `xy = k` Batch Clearing Formal Proofs (0 `sorry`, 0 custom axioms) -/

/-- Exact `xy = k` virtual-reserve quote payout for a bidder committing `b` target atoms in an
    epoch with quote pot `Q`, total committed bids `B`, and virtual reserve `B_virt`. -/
def batchPayoutNat (Q b B Bvirt : Nat) : Nat :=
  if B + Bvirt = 0 then 0 else (Q * b) / (B + Bvirt)

/-- Total quote paid out by the epoch (`quotePaid = floor(Q * B / (B + B_virt))`). -/
def epochQuotePaidNat (Q B Bvirt : Nat) : Nat :=
  batchPayoutNat Q B B Bvirt

/-- Unspent quote rolled over to the next epoch (`Q - quotePaid`). -/
def epochRolloverNat (Q B Bvirt : Nat) : Nat :=
  Q - epochQuotePaidNat Q B Bvirt

/-- Once-per-epoch self-calibrating virtual-reserve rate update (`reserveRateE6`):
    - Healthy epoch (`B ≥ B_virt ∧ B > 0 ∧ Q > 0`): `clamp(clearedRate, MIN_RATE_E6, MAX_RATE_E6)`
      (NEVER divides by 4 -> strictly non-decreasing on healthy epochs, blocking `#111` collapse!).
    - Under-filled dust-bid epoch (`0 < B < B_virt`): keeps `prevRate` unchanged (`clamp(prevRate, MIN_RATE_E6, MAX_RATE_E6)`),
      blocking dust-bid rate halving attacks!
    - Truly empty epoch (`B == 0`, e.g. 1000x token pump with 0 quote paid out):
      `max MIN_RATE_E6 (prevRate / 2)`. -/
def nextReserveRateNat (prevRate Q B Bvirt : Nat) : Nat :=
  if B ≥ Bvirt ∧ B > 0 ∧ Q > 0 then
    let clearedRate := (B * 1_000_000) / Q
    min 1_000_000_000_000 (max 1_000 clearedRate)
  else if B > 0 then
    min 1_000_000_000_000 (max 1_000 prevRate)
  else
    max 1_000 (prevRate / 2)

/-- **THEOREM 1 (`epochQuotePaid_le_pot` & Exact Rollover Conservation)**:
    Across EVERY `Q, B, B_virt`: `quotePaid ≤ Q` and `quotePaid + rollover = Q` (zero quote lost!). -/
theorem epochQuotePaid_le_pot (Q B Bvirt : Nat) :
    epochQuotePaidNat Q B Bvirt ≤ Q ∧
    epochQuotePaidNat Q B Bvirt + epochRolloverNat Q B Bvirt = Q := by
  unfold epochRolloverNat epochQuotePaidNat batchPayoutNat
  by_cases hz : B + Bvirt = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    have hpos : 0 < B + Bvirt := by omega
    have hle : Q * B ≤ Q * (B + Bvirt) := Nat.mul_le_mul_left Q (by omega)
    have hdiv : (Q * B) / (B + Bvirt) ≤ Q := by
      have := Nat.div_le_div_right (c := B + Bvirt) hle
      rwa [Nat.mul_div_cancel _ hpos] at this
    exact ⟨hdiv, by omega⟩

/-- **THEOREM 2 (`xy_k_invariant_preserved`)**:
    Exact `xy = k` virtual-reserve conservation: for every settled epoch (`B + B_virt > 0`),
    `(B_virt + B) * (Q - quotePaid) ≥ B_virt * Q` (rounding strictly favors protocol solvency!). -/
theorem xy_k_invariant_preserved (Q B Bvirt : Nat) (hpos : B + Bvirt > 0) :
    (Bvirt + B) * epochRolloverNat Q B Bvirt ≥ Bvirt * Q := by
  have hle := (epochQuotePaid_le_pot Q B Bvirt).1
  unfold epochRolloverNat epochQuotePaidNat batchPayoutNat at hle ⊢
  have hne : B + Bvirt ≠ 0 := by omega
  simp only [hne, ↓reduceIte] at hle ⊢
  have hdm : ((Q * B) / (B + Bvirt)) * (B + Bvirt) ≤ Q * B := Nat.div_mul_le_self (Q * B) (B + Bvirt)
  have h1 : (Bvirt + B) * (Q - (Q * B) / (B + Bvirt)) + (Bvirt + B) * ((Q * B) / (B + Bvirt)) =
      (Bvirt + B) * Q := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hle]
  have h2 : (Bvirt + B) * Q = Bvirt * Q + Q * B := by
    rw [Nat.add_mul, Nat.mul_comm B Q]
  have h3 : (Bvirt + B) * ((Q * B) / (B + Bvirt)) = ((Q * B) / (B + Bvirt)) * (B + Bvirt) := by
    rw [Nat.mul_comm (Bvirt + B), Nat.add_comm Bvirt B]
  omega

/-- Helper: floor division is super-additive (`∑ floor(Q * b_i / D) ≤ floor(Q * ∑ b_i / D)`). -/
private theorem sum_floor_mul_div_le (Q D : Nat) (bids : List Nat) :
    (bids.map (fun b => (Q * b) / D)).sum ≤ (Q * bids.sum) / D := by
  induction bids with
  | nil => simp
  | cons b tl ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases hD : D = 0
    · subst hD; simp at ih ⊢; exact ih
    · have hpos : 0 < D := by omega
      have h1 : (Q * b) / D * D ≤ Q * b := Nat.div_mul_le_self _ _
      have h2 : (Q * tl.sum) / D * D ≤ Q * tl.sum := Nat.div_mul_le_self _ _
      have h3 : ((Q * b) / D + (Q * tl.sum) / D) * D ≤ Q * (b + tl.sum) := by
        rw [Nat.add_mul, Nat.mul_add]; omega
      have h4 : (Q * b) / D + (Q * tl.sum) / D ≤ (Q * (b + tl.sum)) / D :=
        (Nat.le_div_iff_mul_le hpos).mpr h3
      omega

/-- **THEOREM 3 (`batch_solvency_all_bidders_claimable` — UNLIMITED Bidders Solvency!)**:
    For ANY finite list of unlimited bids `bids` with `bids.sum = B`, the exact sum of every
    bidder's individual `ClaimQuote` payout is `≤ epochQuotePaidNat Q B Bvirt ≤ Q`!
    Zero rounding insolvency, zero shortfall, 100% of bidders can ALWAYS claim! -/
theorem batch_solvency_all_bidders_claimable (Q Bvirt : Nat) (bids : List Nat) :
    let B := bids.sum
    (bids.map (fun b => batchPayoutNat Q b B Bvirt)).sum ≤ epochQuotePaidNat Q B Bvirt ∧
    epochQuotePaidNat Q B Bvirt ≤ Q := by
  dsimp only
  refine ⟨?_, (epochQuotePaid_le_pot Q bids.sum Bvirt).1⟩
  unfold epochQuotePaidNat batchPayoutNat
  by_cases hz : bids.sum + Bvirt = 0
  · simp only [hz, ↓reduceIte]
    have h0 : ∀ xs : List Nat, (xs.map (fun _ => 0)).sum = 0 := by
      intro xs; induction xs with
      | nil => rfl
      | cons _ tl ih => simp [ih]
    rw [h0]; exact Nat.le_refl 0
  · simp only [hz, ↓reduceIte]
    exact sum_floor_mul_div_le Q (bids.sum + Bvirt) bids

/-- **THEOREM 4 (`quiet_epoch_price_cap` — Closes Gap R5: 1-Atom Bidder Cannot Steal Pot!)**:
    Even if an attacker is the ONLY bidder in a quiet/censored epoch, their quote payout per
    target atom is strictly capped by `B_virt`: `payout * B_virt ≤ Q * b`! -/
theorem quiet_epoch_price_cap (Q b B Bvirt : Nat) (hvirt : Bvirt > 0) :
    batchPayoutNat Q b B Bvirt * Bvirt ≤ Q * b := by
  unfold batchPayoutNat
  have hne : B + Bvirt ≠ 0 := by omega
  simp only [hne, ↓reduceIte]
  have h1 : (Q * b) / (B + Bvirt) * Bvirt ≤ (Q * b) / (B + Bvirt) * (B + Bvirt) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (Q * b) / (B + Bvirt) * (B + Bvirt) ≤ Q * b := Nat.div_mul_le_self _ _
  omega

/-- **THEOREM 5 (`spam_bid_monotone_of_pos` — Closes Gap R1 & R4!)**:
    For any valid epoch with `B + B_virt > 0`, adding ANY spam bid `Δb > 0` strictly increases
    total burned tokens AND weakly decreases quote-per-target payout for every bidder
    (zero spam griefing advantage!). -/
theorem spam_bid_monotone_of_pos (Q b B Bvirt Δb : Nat) (hpos : B + Bvirt > 0) :
    batchPayoutNat Q b (B + Δb) Bvirt ≤ batchPayoutNat Q b B Bvirt := by
  unfold batchPayoutNat
  have h1 : B + Bvirt ≠ 0 := by omega
  have h2 : B + Δb + Bvirt ≠ 0 := by omega
  simp only [h1, h2, ↓reduceIte]
  exact Nat.div_le_div_left (by omega) hpos

/-- **THEOREM 6 (`reserveRate_halves_on_empty_epoch` — Closes Gap R3 & `#111`)**:
    On a truly empty epoch (`B = 0`, 0 quote spent), `nextReserveRateNat` halves `prevRate` down toward
    `MIN_RATE_E6 = 1_000` (so a 1000x token pump never permanently freezes rewards, yet rate never hits `1`!). -/
theorem reserveRate_halves_on_empty_epoch (prevRate Q Bvirt : Nat) :
    nextReserveRateNat prevRate Q 0 Bvirt = max 1_000 (prevRate / 2) ∧
    1_000 ≤ nextReserveRateNat prevRate Q 0 Bvirt := by
  unfold nextReserveRateNat
  have h1 : ¬ (0 ≥ Bvirt ∧ 0 > 0 ∧ Q > 0) := by omega
  have h2 : ¬ (0 > 0) := by omega
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
  exact ⟨rfl, Nat.le_max_left 1_000 _⟩

/-- **THEOREM 6b (`reserveRate_unchanged_on_dust_bid` — Closes `#111` Dust-Bid Rate Collapse)**:
    A nonzero underfilled dust bid (`0 < B < B_virt`) can NEVER halve or lower `reserveRateE6`! -/
theorem reserveRate_unchanged_on_dust_bid (prevRate Q B Bvirt : Nat)
    (hpos : 0 < B) (hunder : B < Bvirt) (hlo : 1_000 ≤ prevRate) (hhi : prevRate ≤ 1_000_000_000_000) :
    nextReserveRateNat prevRate Q B Bvirt = prevRate := by
  unfold nextReserveRateNat
  have hnot : ¬ (B ≥ Bvirt ∧ B > 0 ∧ Q > 0) := by omega
  rw [ite_eq_right_of_eq_false _ _ (eq_false hnot), ite_eq_left_of_eq_true _ _ (eq_true hpos)]
  omega

/-- **THEOREM 6c (`reserveRate_non_decreasing_on_healthy_epoch` — Closes `#111` Healthy-Epoch Collapse)**:
    Whenever `B ≥ ceil(Q * prevRate / 10^6)` (`B ≥ B_virt`) with `Q > 0` and `prevRate ≤ MAX_RATE_E6`,
    `nextReserveRateNat` NEVER drops below `prevRate`! -/
theorem reserveRate_non_decreasing_on_healthy_epoch (prevRate Q B Bvirt : Nat)
    (hQ : 0 < Q) (hB : 0 < B) (hge : B ≥ Bvirt)
    (hbv : Bvirt * 1_000_000 ≥ Q * prevRate) (hhi : prevRate ≤ 1_000_000_000_000) :
    prevRate ≤ nextReserveRateNat prevRate Q B Bvirt := by
  unfold nextReserveRateNat
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hge, hB, hQ⟩)]
  have hmul : Q * prevRate ≤ B * 1_000_000 :=
    Nat.le_trans hbv (Nat.mul_le_mul_right 1_000_000 hge)
  have hdiv : prevRate ≤ (B * 1_000_000) / Q :=
    (Nat.le_div_iff_mul_le hQ).mpr (by rw [Nat.mul_comm]; exact hmul)
  exact Nat.le_min.mpr ⟨hhi, Nat.le_trans hdiv (Nat.le_max_right 1_000 _)⟩

/-- **THEOREM 7 (`feeSplit_exact_conservation`)**:
    Core trade-fee split (`rewFee = floor(fee2 * rewBps / 10000)`, `insFee = fee2 - rewFee`)
    conserves `fee2` atom-for-atom whenever `rewBps ≤ 10000`! -/
theorem feeSplit_exact_conservation (fee2 rewBps : Nat) (hbps : rewBps ≤ 10_000) :
    let rewFee := (fee2 * rewBps) / 10_000
    let insFee := fee2 - rewFee
    rewFee ≤ fee2 ∧ insFee + rewFee = fee2 := by
  have hm : fee2 * rewBps ≤ fee2 * 10_000 := Nat.mul_le_mul_left fee2 hbps
  have hd : (fee2 * rewBps) / 10_000 ≤ fee2 := by
    have := Nat.div_le_div_right (c := 10_000) hm
    rwa [Nat.mul_div_cancel _ (by decide)] at this
  exact ⟨hd, by omega⟩

/-- Pure capped virtual-reserve computation: `min MAX_VIRT_BIDS (ceil(Q * r / 10^6))`. -/
def virtBidsCappedNat (Q r : Nat) : Nat :=
  min MAX_VIRT_BIDS.toNat ((Q * r + 1_000_000 - 1) / 1_000_000)

/-- **THEOREM 8 (`virtBidsCapped_in_bounds` — Closes Fix #6: Zero `StartEpoch` Overflow Brick)**:
    For EVERY `Q ≥ 1` and `r ≥ 1`, `1 ≤ virtBidsCappedNat Q r ≤ MAX_VIRT_BIDS`, so `B_virt` is
    ALWAYS strictly positive (blocking 1-atom quiet-epoch drain) AND strictly bounded below `2^62`
    (so `StartEpoch` can NEVER overflow `u64::MAX` even on a 10^6x cheap memecoin!). -/
theorem virtBidsCapped_in_bounds (Q r : Nat) (hQ : 1 ≤ Q) (hr : 1 ≤ r) :
    1 ≤ virtBidsCappedNat Q r ∧ virtBidsCappedNat Q r ≤ MAX_VIRT_BIDS.toNat := by
  unfold virtBidsCappedNat
  have h1 : 1 ≤ Q * r := Nat.mul_le_mul hQ hr
  have hceil : 1 ≤ (Q * r + 1_000_000 - 1) / 1_000_000 :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 1_000_000)).mpr (by omega)
  have hmax : 1 ≤ MAX_VIRT_BIDS.toNat := by decide
  exact ⟨Nat.le_min.mpr ⟨hmax, hceil⟩, Nat.min_le_left _ _⟩

/-! ### Runtime Helpers & Outlined CPIs -/

/-- Overflow-free `min MAX_VIRT_BIDS (ceil(totalPot * resRate / POS_SCALE))`: NEVER overflows `UInt64`
    even if `resRate == MAX_RATE_E6 (10^12)` and `totalPot >= 18.4M` quote units! -/
def computeVirtBidsU64 (totalPot resRate : UInt64) : SolanaM UInt64 := do
  if resRate <= POS_SCALE then
    if totalPot >= MAX_VIRT_BIDS then return MAX_VIRT_BIDS
    let v ← mulDiv64Ceil totalPot resRate POS_SCALE
    return if v > MAX_VIRT_BIDS then MAX_VIRT_BIDS else v
  else
    let q := totalPot / POS_SCALE
    if q >= MAX_VIRT_BIDS / resRate then return MAX_VIRT_BIDS
    let v ← mulDiv64Ceil totalPot resRate POS_SCALE
    return if v > MAX_VIRT_BIDS then MAX_VIRT_BIDS else v

def requireNonDup (acc : AccountView) : SolanaM Unit := do
  SolanaM.require ((← rawLoadU8 acc) == ABI.nonDupMarker) PErr.aliasedAccounts

def zeroRewardWords (base off nWords : UInt64) : SolanaM Unit := do
  if h : nWords == 0 then return ()
  else
    storeU64 base off 0
    zeroRewardWords base (off + 8) (nWords - 1)
termination_by nWords.toNat
decreasing_by
  have hne : nWords.toNat ≠ 0 := by
    intro hz
    have h0 : nWords = 0 := UInt64.toNat_inj.mp (by rw [hz]; rfl)
    exact h (by rw [h0]; rfl)
  have h1 : (1 : UInt64).toNat = 1 := rfl
  change (nWords - 1).toNat < nWords.toNat
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), h1]
  omega

def writeRewPdaSeeds (sbuf : Ptr) (cfgKeyPtr : Ptr) (bump : UInt8) : SolanaM Ptr := do
  let seedsArr   := sbuf + 8
  let signersArr := sbuf + 56
  storeU32 sbuf 0 TAG_REW_AUTH
  storeU8  sbuf 4 bump
  storeU64 seedsArr 0  sbuf;       storeU64 seedsArr 8  4
  storeU64 seedsArr 16 cfgKeyPtr;  storeU64 seedsArr 24 32
  storeU64 seedsArr 32 (sbuf + 4); storeU64 seedsArr 40 1
  storeU64 signersArr 0 seedsArr
  storeU64 signersArr 8 3
  return signersArr

def getSlot : SolanaM UInt64 := do
  let buf ← stackAlloc 40
  let rc ← sysGetClock buf
  SolanaM.require (rc == 0) Err.invalidAccountData
  loadU64 buf 0

def checkRewardCfg (cfg : AccountView) (progId : Ptr) : SolanaM Unit := do
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr cfg) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen cfg) == RewOff.size) Err.invalidAccountData
  SolanaM.require ((← loadU32 (AccountView.dataPtr cfg) RewOff.magic) == MAGIC_REWARD) PErr.invalidMagic

def checkEpochAcc (ep : AccountView) (cfg : AccountView) (progId : Ptr) : SolanaM Unit := do
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr ep) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen ep) == EpochOff.size) Err.invalidAccountData
  SolanaM.require ((← loadU32 (AccountView.dataPtr ep) EpochOff.magic) == MAGIC_EPOCH) PErr.invalidMagic
  SolanaM.require (← pubkeyEq (AccountView.dataPtr ep + EpochOff.cfg) (AccountView.keyPtr cfg)) RErr.epochMismatch

def checkInitializedTokAcc (tokAcc tokProg mint ownerKeyPtr : AccountView) : SolanaM Unit := do
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr tokAcc) (AccountView.keyPtr tokProg)) RErr.vaultMismatch
  SolanaM.require ((← AccountView.dataLen tokAcc) >= 165) RErr.vaultMismatch
  let tData := AccountView.dataPtr tokAcc
  SolanaM.require (← pubkeyEq tData (AccountView.keyPtr mint)) RErr.mintMismatch
  SolanaM.require (← pubkeyEq (tData + 32) (AccountView.keyPtr ownerKeyPtr)) RErr.vaultMismatch
  SolanaM.require ((← loadU8 tData 108) == 1) RErr.vaultMismatch -- AccountState::Initialized

/-- Outlined PDA-signed SPL Token / Token-2022 `Burn` (`op = 8`, 344B stack, 0 heap). -/
@[noinline] def tokenBurnSigned (tokenProg account mint authority : AccountView)
    (amount : UInt64) (cfgKeyPtr : Ptr) (bump : UInt8) : SolanaM Unit := do
  let buf ← stackAlloc 344
  let metas := buf + 40
  let infos := buf + 88
  let data  := buf + 256
  let sbuf  := buf + 272
  storeU8  data 0 8
  storeU64 data 1 amount
  writeMeta metas        account   1 0
  writeMeta (metas + 16) mint      1 0
  writeMeta (metas + 32) authority 0 1
  writeAccountInfo infos         account
  writeAccountInfo (infos + 56)  mint
  writeAccountInfo (infos + 112) authority
  writeInstruction buf (AccountView.keyPtr tokenProg) metas 3 data 9
  let signersArr ← writeRewPdaSeeds sbuf cfgKeyPtr bump
  let rc ← sysInvokeSignedC buf infos 3 signersArr 1
  SolanaM.require (rc == 0) rc

/-- Outlined 7-account PDA-signed CPI into `percolator::ClaimReward(dex, mkt, rewAuthPda, mint, vaultPda, destTok, tokProg)`. -/
@[noinline] def cpiClaimReward (percProg : AccountView) (accs7Ptr : Ptr)
    (claimAmt : UInt64) (cfgKeyPtr : Ptr) (bump : UInt8) : SolanaM Unit := do
  let dex      ← loadU64 accs7Ptr 0
  let mkt      ← loadU64 accs7Ptr 8
  let rewAuth  ← loadU64 accs7Ptr 16
  let qMint    ← loadU64 accs7Ptr 24
  let vaultPda ← loadU64 accs7Ptr 32
  let destTok  ← loadU64 accs7Ptr 40
  let qTokProg ← loadU64 accs7Ptr 48
  let buf ← stackAlloc 632
  let metas := buf + 40
  let infos := buf + 152
  let data  := buf + 544
  let sbuf  := buf + 560
  storeU8  data 0 IxOp.claimReward
  storeU64 data 1 claimAmt
  writeMeta metas        dex      1 0
  writeMeta (metas + 16) mkt      1 0
  writeMeta (metas + 32) rewAuth  0 1
  writeMeta (metas + 48) qMint    0 0
  writeMeta (metas + 64) vaultPda 1 0
  writeMeta (metas + 80) destTok  1 0
  writeMeta (metas + 96) qTokProg 0 0
  writeAccountInfo infos         dex
  writeAccountInfo (infos + 56)  mkt
  writeAccountInfo (infos + 112) rewAuth
  writeAccountInfo (infos + 168) qMint
  writeAccountInfo (infos + 224) vaultPda
  writeAccountInfo (infos + 280) destTok
  writeAccountInfo (infos + 336) qTokProg
  writeInstruction buf (AccountView.keyPtr percProg) metas 7 data 9
  let signersArr ← writeRewPdaSeeds sbuf cfgKeyPtr bump
  let rc ← sysInvokeSignedC buf infos 7 signersArr 1
  SolanaM.require (rc == 0) rc

/-- Pure overflow-free runtime self-calibration matching `nextReserveRateNat`!
    - Healthy (`B >= B_virt ∧ B > 0 ∧ Q > 0`): clamps `clearedRate = floor(B * 10^6 / Q)` into `[MIN_RATE_E6, MAX_RATE_E6]`
      (NO `/ 4` slash -> strictly non-decreasing on healthy epochs!).
    - Nonzero dust/underfilled (`0 < B < B_virt`): leaves `prevRate` unchanged (clamped to `[MIN_RATE_E6, MAX_RATE_E6]`).
    - Truly empty (`B == 0`): halves `prevRate` down to `max(MIN_RATE_E6, prevRate / 2)`. -/
def nextReserveRateU64 (prevRate Q B Bvirt : UInt64) : SolanaM UInt64 := do
  if B >= Bvirt && B > 0 && Q > 0 then
    if B / Q >= 1_000_000 then
      return MAX_RATE_E6
    let clearedRate ← mulDiv64 B POS_SCALE Q
    if clearedRate < MIN_RATE_E6 then return MIN_RATE_E6
    else if clearedRate > MAX_RATE_E6 then return MAX_RATE_E6
    else return clearedRate
  else if B > 0 then
    if prevRate < MIN_RATE_E6 then return MIN_RATE_E6
    else if prevRate > MAX_RATE_E6 then return MAX_RATE_E6
    else return prevRate
  else
    let half := prevRate >>> 1
    return if half < MIN_RATE_E6 then MIN_RATE_E6 else half

/-! ### 5 Minimal O(1) Zero-Admin-Rug Instructions -/

/-- Op 0 (`InitReward`): One-shot immutable binding of a per-market Gavel-style `xy = k` Batch
    Buy-and-Burn module.
    Accounts (12, or 13 when `burnMode == 1`):
      0. `cfg` (W) — fresh `RewardCfg` (400B, owned by this program, `magic == 0`)
      1. `mktAdmin` (S) — MUST match `mkt.marketAdmin` (prevents third-party hijack!)
      2. `percProg` — pinned `percolator` program
      3. `dex` — pinned `Dex`
      4. `mkt` — pinned `Market` (MUST have `mkt.rewardRecipient == rewAuthPda`!)
      5. `rewAuthPda` — PDA `["rewm", cfg.key, bump]`
      6. `quoteMint` — MUST match `dex.quoteMint`
      7. `quoteVault` — initialized SPL Token account (`mint == quoteMint`, `owner == rewAuthPda`, `amount == 0`)
      8. `quoteTokProg` — canonical SPL Token program
      9. `targetMint` — ANY external SPL Token, Token-2022, or wSOL mint!
     10. `targetEscrow` — initialized SPL/Token-2022 account (`mint == targetMint`, `owner == rewAuthPda`, `amount == 0`)
     11. `targetTokProg` — canonical SPL Token OR Token-2022 program!
     12. *(required when `burnMode == 1`)* `burnSinkTok` — permanent dead-sink token account
         (`mint == targetMint`, `owner == rewAuthPda`, initialized, distinct from `targetEscrow`/`quoteVault`)!
    Ix data (28 bytes): `[0, bump:u8, burnMode:u8, pad:u8, epochSlots:u64, minBatchQuote:u64, initReserveRateE6:u64]`. -/
def handleInitReward (input : Ptr) : SolanaM Unit := do
  let (n, cfg, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 12 && ix.len >= 28) Err.invalidInstructionData
  let mktAdmin      ← AccountView.nextCursor cfg
  let percProg      ← AccountView.nextCursor mktAdmin
  let dex           ← AccountView.nextCursor percProg
  let mkt           ← AccountView.nextCursor dex
  let rewAuthPda    ← AccountView.nextCursor mkt
  let quoteMint     ← AccountView.nextCursor rewAuthPda
  let quoteVault    ← AccountView.nextCursor quoteMint
  let quoteTokProg  ← AccountView.nextCursor quoteVault
  let targetMint    ← AccountView.nextCursor quoteTokProg
  let targetEscrow  ← AccountView.nextCursor targetMint
  let targetTokProg ← AccountView.nextCursor targetEscrow

  requireNonDup cfg; requireNonDup mktAdmin; requireNonDup percProg; requireNonDup dex
  requireNonDup mkt; requireNonDup rewAuthPda; requireNonDup quoteVault
  requireNonDup targetEscrow
  SolanaM.require (← AccountView.isSigner mktAdmin) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable cfg) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr cfg) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen cfg) == RewOff.size) Err.invalidAccountData
  SolanaM.require ((← loadU32 (AccountView.dataPtr cfg) 0) == 0) Err.accountAlreadyInitialized

  -- Resolve possible Solana ABI duplicate accounts when `targetTokProg == quoteTokProg` (idx 8)
  -- or `targetMint == quoteMint` (idx 6) — Solana deduplicates identical pubkeys to 8-byte markers!
  let tMintDup ← rawLoadU8 targetMint
  let effTargetMint := if tMintDup == ABI.nonDupMarker then targetMint else quoteMint
  if tMintDup != ABI.nonDupMarker then
    SolanaM.require (tMintDup == 6) PErr.aliasedAccounts
  let tProgDup ← rawLoadU8 targetTokProg
  let effTargetTokProg := if tProgDup == ABI.nonDupMarker then targetTokProg else quoteTokProg
  if tProgDup != ABI.nonDupMarker then
    SolanaM.require (tProgDup == 8) PErr.aliasedAccounts

  -- Pin canonical SPL Token for quoteMint & SPL/Token-2022 for targetMint (blocks fake/noop programs!)
  SolanaM.require ((← rawLoadU8 quoteTokProg) == ABI.nonDupMarker) PErr.aliasedAccounts
  SolanaM.require ((← rawLoadU8 quoteMint)    == ABI.nonDupMarker) PErr.aliasedAccounts
  checkTokenProg quoteTokProg
  if tProgDup == ABI.nonDupMarker then
    checkTokenOr2022Prog effTargetTokProg
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr quoteMint) (AccountView.keyPtr quoteTokProg)) RErr.mintMismatch
  SolanaM.require ((← AccountView.dataLen quoteMint) >= 82) Err.invalidAccountData
  let quoteDec ← loadU8 (AccountView.dataPtr quoteMint) 44
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr effTargetMint) (AccountView.keyPtr effTargetTokProg)) RErr.mintMismatch
  SolanaM.require ((← AccountView.dataLen effTargetMint) >= 82) Err.invalidAccountData
  let targetDec ← loadU8 (AccountView.dataPtr effTargetMint) 44

  -- Validate genuine `percolator` Dex & Market owned by `percProg`, signed by `mkt.marketAdmin`,
  -- and pinned `mkt.rewardRecipient == rewAuthPda`!
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr dex) (AccountView.keyPtr percProg)) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen dex) == DexOff.size) Err.invalidAccountData
  SolanaM.require ((← loadU32 (AccountView.dataPtr dex) DexOff.magic) == MAGIC_DEX) PErr.invalidMagic
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr mkt) (AccountView.keyPtr percProg)) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen mkt) == MktOff.size) Err.invalidAccountData
  SolanaM.require ((← loadU32 (AccountView.dataPtr mkt) MktOff.magic) == MAGIC_MARKET) PErr.invalidMagic
  let dData := AccountView.dataPtr dex
  let mData := AccountView.dataPtr mkt
  SolanaM.require (← pubkeyEq (AccountView.keyPtr dex) (mData + MktOff.dex)) RErr.dexMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr quoteMint) (dData + DexOff.quoteMint)) RErr.mintMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr mktAdmin) (mData + MktOff.marketAdmin)) PErr.unauthorized
  SolanaM.require (← pubkeyEq (AccountView.keyPtr rewAuthPda) (mData + MktOff.rewardRecipient)) RErr.recipientBad

  -- Verify dedicated empty PDA-owned quoteVault & targetEscrow (and disallow aliasing!)
  checkInitializedTokAcc quoteVault quoteTokProg quoteMint rewAuthPda
  checkInitializedTokAcc targetEscrow effTargetTokProg effTargetMint rewAuthPda
  SolanaM.require ((← loadU64 (AccountView.dataPtr quoteVault) 64) == 0) RErr.vaultMismatch
  SolanaM.require ((← loadU64 (AccountView.dataPtr targetEscrow) 64) == 0) RErr.vaultMismatch
  SolanaM.require (!(← pubkeyEq (AccountView.keyPtr quoteVault) (AccountView.keyPtr targetEscrow))) PErr.aliasedAccounts

  let bump              ← loadU8  ix.ptr 1
  let burnMode          ← loadU8  ix.ptr 2
  let epochSlots        ← loadU64 ix.ptr 4
  let minBatchQuote     ← loadU64 ix.ptr 12
  let initReserveRateE6 ← loadU64 ix.ptr 20
  SolanaM.require (burnMode <= 1) RErr.badBurnMode
  SolanaM.require (epochSlots >= MIN_EPOCH_SLOTS && epochSlots <= MAX_EPOCH_SLOTS) PErr.invalidParams
  SolanaM.require (minBatchQuote >= 1) PErr.invalidParams
  SolanaM.require (initReserveRateE6 >= MIN_RATE_E6 && initReserveRateE6 <= MAX_RATE_E6) PErr.invalidParams

  let cData := AccountView.dataPtr cfg
  zeroRewardWords cData 0 (RewOff.size >>> 3)
  storeU32 cData RewOff.magic MAGIC_REWARD
  storeU8  cData RewOff.pdaBump bump
  storeU8  cData RewOff.burnMode burnMode
  storeU8  cData RewOff.quoteDecimals quoteDec
  storeU8  cData RewOff.targetDecimals targetDec
  pubkeyCopy (cData + RewOff.percProg)      (AccountView.keyPtr percProg)
  pubkeyCopy (cData + RewOff.dex)           (AccountView.keyPtr dex)
  pubkeyCopy (cData + RewOff.market)        (AccountView.keyPtr mkt)
  pubkeyCopy (cData + RewOff.quoteMint)     (AccountView.keyPtr quoteMint)
  pubkeyCopy (cData + RewOff.quoteVault)    (AccountView.keyPtr quoteVault)
  pubkeyCopy (cData + RewOff.targetMint)    (AccountView.keyPtr effTargetMint)
  pubkeyCopy (cData + RewOff.targetEscrow)  (AccountView.keyPtr targetEscrow)
  pubkeyCopy (cData + RewOff.targetTokProg) (AccountView.keyPtr effTargetTokProg)

  if burnMode == 1 then
    SolanaM.require (n >= 13) Err.notEnoughAccountKeys
    let burnSinkTok ← AccountView.nextCursor targetTokProg
    requireNonDup burnSinkTok
    checkInitializedTokAcc burnSinkTok effTargetTokProg effTargetMint rewAuthPda
    SolanaM.require (!(← pubkeyEq (AccountView.keyPtr burnSinkTok) (AccountView.keyPtr targetEscrow))) PErr.aliasedAccounts
    SolanaM.require (!(← pubkeyEq (AccountView.keyPtr burnSinkTok) (AccountView.keyPtr quoteVault))) PErr.aliasedAccounts
    pubkeyCopy (cData + RewOff.burnSinkTok) (AccountView.keyPtr burnSinkTok)

  storeU64 cData RewOff.epochSlots epochSlots
  storeU64 cData RewOff.minBatchQuote minBatchQuote
  storeU64 cData RewOff.reserveRateE6 initReserveRateE6

/-- Op 1 (`StartEpoch`): Permissionlessly pull accumulated market rewards into `quoteVault` and
    open a new `epochSlots` uniform-price batch epoch once `rollover + pulled >= minBatchQuote`.
    Accounts (10):
      0. `cfg` (W)
      1. `epochAcc` (W) — fresh `EpochState` (104B, owned by this program, `magic == 0`)
      2. `dex` (W)
      3. `mkt` (W)
      4. `rewAuthPda`
      5. `quoteMint`
      6. `dexVault` (W)
      7. `quoteVault` (W)
      8. `quoteTokProg`
      9. `percProg`
    Ix data (1 byte): `[1]`. -/
def handleStartEpoch (input : Ptr) : SolanaM Unit := do
  let (n, cfg, _, progId) ← parseIxOnly input
  SolanaM.require (n >= 10) Err.notEnoughAccountKeys
  let epochAcc     ← AccountView.nextCursor cfg
  let dex          ← AccountView.nextCursor epochAcc
  let mkt          ← AccountView.nextCursor dex
  let rewAuthPda   ← AccountView.nextCursor mkt
  let quoteMint    ← AccountView.nextCursor rewAuthPda
  let dexVault     ← AccountView.nextCursor quoteMint
  let quoteVault   ← AccountView.nextCursor dexVault
  let quoteTokProg ← AccountView.nextCursor quoteVault
  let percProg     ← AccountView.nextCursor quoteTokProg

  requireNonDup cfg; requireNonDup epochAcc; requireNonDup dex; requireNonDup mkt; requireNonDup rewAuthPda
  requireNonDup quoteMint; requireNonDup dexVault; requireNonDup quoteVault
  requireNonDup quoteTokProg; requireNonDup percProg
  SolanaM.require (← AccountView.isWritable cfg) Err.invalidAccountData
  SolanaM.require (← AccountView.isWritable epochAcc) Err.invalidAccountData
  checkRewardCfg cfg progId
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr epochAcc) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen epochAcc) == EpochOff.size) Err.invalidAccountData
  SolanaM.require ((← loadU32 (AccountView.dataPtr epochAcc) 0) == 0) Err.accountAlreadyInitialized

  let cData := AccountView.dataPtr cfg
  SolanaM.require ((← loadU64 cData RewOff.activeQuote) == 0) RErr.epochActive
  SolanaM.require (← pubkeyEq (AccountView.keyPtr percProg)   (cData + RewOff.percProg))   RErr.progMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr dex)        (cData + RewOff.dex))        RErr.dexMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr mkt)        (cData + RewOff.market))     RErr.mktMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr quoteMint)  (cData + RewOff.quoteMint))  RErr.mintMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr quoteVault) (cData + RewOff.quoteVault)) RErr.vaultMismatch
  checkTokenProg quoteTokProg

  -- Pull all newly accrued rewards from `percolator` into `quoteVault` (measuring exact balance delta!)
  let availMkt ← loadU64 (AccountView.dataPtr mkt) MktOff.rewardAccrued
  let mut pulled : UInt64 := 0
  if availMkt > 0 then
    let preQ ← loadU64 (AccountView.dataPtr quoteVault) 64
    let accs7 ← stackAlloc 56
    storeU64 accs7 0  dex
    storeU64 accs7 8  mkt
    storeU64 accs7 16 rewAuthPda
    storeU64 accs7 24 quoteMint
    storeU64 accs7 32 dexVault
    storeU64 accs7 40 quoteVault
    storeU64 accs7 48 quoteTokProg
    let bump ← loadU8 cData RewOff.pdaBump
    cpiClaimReward percProg accs7 availMkt (AccountView.keyPtr cfg) bump
    let postQ ← loadU64 (AccountView.dataPtr quoteVault) 64
    pulled ← checkedSub64 postQ preQ Err.arithmeticOverflow

  let roll ← loadU64 cData RewOff.rolloverQuote
  let totalPot ← checkedAdd64 roll pulled
  let minBatch ← loadU64 cData RewOff.minBatchQuote
  SolanaM.require (totalPot >= minBatch) RErr.belowMinBatch

  let resRate ← loadU64 cData RewOff.reserveRateE6
  let virtBids ← computeVirtBidsU64 totalPot resRate
  let epSlots ← loadU64 cData RewOff.epochSlots
  let curSlot ← getSlot
  let endSlot ← checkedAdd64 curSlot epSlots
  let newId ← checkedAdd64 (← loadU64 cData RewOff.activeEpochId) 1

  -- Initialize `EpochState` cleanly (zero-init first!)
  let eData := AccountView.dataPtr epochAcc
  zeroRewardWords eData 0 (EpochOff.size >>> 3)
  storeU32 eData EpochOff.magic MAGIC_EPOCH
  storeU8  eData EpochOff.settled 0
  pubkeyCopy (eData + EpochOff.cfg) (AccountView.keyPtr cfg)
  storeU64 eData EpochOff.epochId newId
  storeU64 eData EpochOff.quotePot totalPot
  storeU64 eData EpochOff.virtBids virtBids
  storeU64 eData EpochOff.startSlot curSlot
  storeU64 eData EpochOff.endSlot endSlot

  -- Update `RewardCfg` active epoch pointer & conservation buckets
  pubkeyCopy (cData + RewOff.activeEpochAcc) (AccountView.keyPtr epochAcc)
  storeU64 cData RewOff.activeEpochId newId
  storeU64 cData RewOff.activeQuote totalPot
  storeU64 cData RewOff.rolloverQuote 0
  log64 EVT_EPOCH_START newId totalPot virtBids endSlot

/-- Op 2 (`SubmitBid`): Permissionless, IRREVOCABLE, UNLIMITED AMM-style bid into the active epoch!
    O(1) per bid. Measures exact `targetEscrow` balance delta (immune to Token-2022 TransferFee!).
    Accounts (8):
      0. `cfg`
      1. `epochAcc` (W) — MUST equal `cfg.activeEpochAcc`
      2. `bidReceipt` (W) — fresh (120B, `magic == 0`) OR bidder's existing receipt for this epoch
      3. `bidder` (S)
      4. `bidderTargetTok` (W)
      5. `targetEscrow` (W)
      6. `targetMint`
      7. `targetTokProg`
    Ix data (9 bytes): `[2, amount:u64]`. -/
def handleSubmitBid (input : Ptr) : SolanaM Unit := do
  let (n, cfg, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 8 && ix.len >= 9) Err.invalidInstructionData
  let epochAcc        ← AccountView.nextCursor cfg
  let bidReceipt      ← AccountView.nextCursor epochAcc
  let bidder          ← AccountView.nextCursor bidReceipt
  let bidderTargetTok ← AccountView.nextCursor bidder
  let targetEscrow    ← AccountView.nextCursor bidderTargetTok
  let targetMint      ← AccountView.nextCursor targetEscrow
  let targetTokProg   ← AccountView.nextCursor targetMint

  requireNonDup cfg; requireNonDup epochAcc; requireNonDup bidReceipt; requireNonDup bidder
  requireNonDup bidderTargetTok; requireNonDup targetEscrow
  requireNonDup targetMint; requireNonDup targetTokProg
  SolanaM.require (← AccountView.isSigner bidder) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable epochAcc) Err.invalidAccountData
  SolanaM.require (← AccountView.isWritable bidReceipt) Err.invalidAccountData
  checkRewardCfg cfg progId
  checkEpochAcc epochAcc cfg progId

  let cData := AccountView.dataPtr cfg
  let eData := AccountView.dataPtr epochAcc
  SolanaM.require ((← loadU64 cData RewOff.activeQuote) > 0) RErr.epochClosed
  SolanaM.require (← pubkeyEq (AccountView.keyPtr epochAcc) (cData + RewOff.activeEpochAcc)) RErr.epochMismatch
  SolanaM.require ((← loadU8 eData EpochOff.settled) == 0) RErr.epochClosed
  let curSlot ← getSlot
  let endSlot ← loadU64 eData EpochOff.endSlot
  SolanaM.require (curSlot < endSlot) RErr.epochClosed

  SolanaM.require (← pubkeyEq (AccountView.keyPtr targetEscrow) (cData + RewOff.targetEscrow)) RErr.vaultMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr targetMint) (cData + RewOff.targetMint)) RErr.mintMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr targetTokProg) (cData + RewOff.targetTokProg)) Err.incorrectProgramId
  SolanaM.require (!(← pubkeyEq (AccountView.keyPtr bidderTargetTok) (AccountView.keyPtr targetEscrow))) PErr.aliasedAccounts

  let amount ← loadU64 ix.ptr 1
  SolanaM.require (amount > 0) PErr.invalidParams

  -- Validate or fresh-initialize `BidReceipt` (zero-init on first use!)
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr bidReceipt) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen bidReceipt) == BidOff.size) Err.invalidAccountData
  let rData := AccountView.dataPtr bidReceipt
  let epId ← loadU64 eData EpochOff.epochId
  let rMagic ← loadU32 rData BidOff.magic
  if rMagic == 0 then
    zeroRewardWords rData 0 (BidOff.size >>> 3)
    storeU32 rData BidOff.magic MAGIC_BID
    pubkeyCopy (rData + BidOff.cfg) (AccountView.keyPtr cfg)
    pubkeyCopy (rData + BidOff.epochAcc) (AccountView.keyPtr epochAcc)
    pubkeyCopy (rData + BidOff.bidder) (AccountView.keyPtr bidder)
    storeU64 rData BidOff.epochId epId
  else
    SolanaM.require (rMagic == MAGIC_BID) PErr.invalidMagic
    SolanaM.require (← pubkeyEq (rData + BidOff.cfg) (AccountView.keyPtr cfg)) RErr.epochMismatch
    SolanaM.require (← pubkeyEq (rData + BidOff.epochAcc) (AccountView.keyPtr epochAcc)) RErr.epochMismatch
    SolanaM.require (← pubkeyEq (rData + BidOff.bidder) (AccountView.keyPtr bidder)) PErr.unauthorized
    SolanaM.require ((← loadU64 rData BidOff.epochId) == epId) RErr.epochMismatch

  -- Transfer irrevocable target tokens into `targetEscrow` and credit EXACT received delta (Gap R6!)
  let preBal ← loadU64 (AccountView.dataPtr targetEscrow) 64
  let tDec ← loadU8 cData RewOff.targetDecimals
  tokenTransferChecked targetTokProg bidderTargetTok targetMint targetEscrow bidder amount tDec
  let postBal ← loadU64 (AccountView.dataPtr targetEscrow) 64
  let received ← checkedSub64 postBal preBal Err.arithmeticOverflow
  SolanaM.require (received > 0) PErr.invalidParams

  -- Check `totalBids + received + virtBids` never overflows `UInt64`!
  let newTotBids ← checkedAdd64 (← loadU64 eData EpochOff.totalBids) received
  let virtBids ← loadU64 eData EpochOff.virtBids
  let _ ← checkedAdd64 newTotBids virtBids
  let newRecAmt ← checkedAdd64 (← loadU64 rData BidOff.amount) received

  storeU64 eData EpochOff.totalBids newTotBids
  storeU64 rData BidOff.amount newRecAmt
  log64 EVT_SUBMIT_BID epId received newRecAmt newTotBids

/-- Op 3 (`SettleEpoch`): 100% permissionless, strictly O(1) settlement at `curSlot >= endSlot`!
    Burns ALL committed `B_e` in ONE single CPI (real SPL/Token-2022 `Burn` OR permanent wSOL
    dead-sink transfer), locks the uniform `xy = k` clearing price, rolls unspent quote into
    `cfg.rolloverQuote`, and self-calibrates `reserveRateE6` once per epoch!
    Accounts (6, or 7 when `burnMode == 1`):
      0. `cfg` (W)
      1. `epochAcc` (W) — MUST equal `cfg.activeEpochAcc`
      2. `rewAuthPda`
      3. `targetEscrow` (W)
      4. `targetMint` (W)
      5. `targetTokProg`
      6. *(when `burnMode == 1`)* `burnSinkTok` (W)
    Ix data (1 byte): `[3]`. -/
def handleSettleEpoch (input : Ptr) : SolanaM Unit := do
  let (n, cfg, _, progId) ← parseIxOnly input
  SolanaM.require (n >= 6) Err.notEnoughAccountKeys
  let epochAcc      ← AccountView.nextCursor cfg
  let rewAuthPda    ← AccountView.nextCursor epochAcc
  let targetEscrow  ← AccountView.nextCursor rewAuthPda
  let targetMint    ← AccountView.nextCursor targetEscrow
  let targetTokProg ← AccountView.nextCursor targetMint

  requireNonDup cfg; requireNonDup epochAcc; requireNonDup rewAuthPda; requireNonDup targetEscrow
  requireNonDup targetMint; requireNonDup targetTokProg
  SolanaM.require (← AccountView.isWritable cfg) Err.invalidAccountData
  SolanaM.require (← AccountView.isWritable epochAcc) Err.invalidAccountData
  checkRewardCfg cfg progId
  checkEpochAcc epochAcc cfg progId

  let cData := AccountView.dataPtr cfg
  let eData := AccountView.dataPtr epochAcc
  SolanaM.require ((← loadU64 cData RewOff.activeQuote) > 0) RErr.epochClosed
  SolanaM.require (← pubkeyEq (AccountView.keyPtr epochAcc) (cData + RewOff.activeEpochAcc)) RErr.epochMismatch
  SolanaM.require ((← loadU8 eData EpochOff.settled) == 0) RErr.epochClosed
  let curSlot ← getSlot
  let endSlot ← loadU64 eData EpochOff.endSlot
  SolanaM.require (curSlot >= endSlot) RErr.epochNotEnded

  SolanaM.require (← pubkeyEq (AccountView.keyPtr targetEscrow) (cData + RewOff.targetEscrow)) RErr.vaultMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr targetMint) (cData + RewOff.targetMint)) RErr.mintMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr targetTokProg) (cData + RewOff.targetTokProg)) Err.incorrectProgramId

  let qPot     ← loadU64 eData EpochOff.quotePot
  let virtBids ← loadU64 eData EpochOff.virtBids
  let totBids  ← loadU64 eData EpochOff.totalBids
  let epId     ← loadU64 eData EpochOff.epochId
  let bump     ← loadU8  cData RewOff.pdaBump
  let burnMode ← loadU8  cData RewOff.burnMode

  -- Compute exact `xy = k` uniform batch clearing (`quotePaid + rollover == qPot`)
  let mut quotePaid : UInt64 := 0
  if totBids > 0 then
    let denom ← checkedAdd64 totBids virtBids
    quotePaid ← mulDiv64 qPot totBids denom
    -- Burn ALL `totBids` in ONE single O(1) CPI!
    if burnMode == 0 then
      tokenBurnSigned targetTokProg targetEscrow targetMint rewAuthPda totBids (AccountView.keyPtr cfg) bump
    else
      SolanaM.require (n >= 7) Err.notEnoughAccountKeys
      let burnSinkTok ← AccountView.nextCursor targetTokProg
      requireNonDup burnSinkTok
      SolanaM.require (← pubkeyEq (AccountView.keyPtr burnSinkTok) (cData + RewOff.burnSinkTok)) RErr.sinkMismatch
      SolanaM.require (!(← pubkeyEq (AccountView.keyPtr targetEscrow) (AccountView.keyPtr burnSinkTok))) PErr.aliasedAccounts
      let tDec ← loadU8 cData RewOff.targetDecimals
      tokenTransferCheckedSigned targetTokProg targetEscrow targetMint burnSinkTok rewAuthPda totBids tDec
        TAG_REW_AUTH (AccountView.keyPtr cfg) bump

  let rollover ← checkedSub64 qPot quotePaid Err.arithmeticOverflow
  let prevRate ← loadU64 cData RewOff.reserveRateE6
  let nextRate ← nextReserveRateU64 prevRate qPot totBids virtBids

  -- Commit settled epoch + global 3-bucket escrow conservation + monotonic totals
  storeU8  eData EpochOff.settled 1
  storeU64 eData EpochOff.quotePaid quotePaid
  storeU64 cData RewOff.activeQuote 0
  let newRoll ← checkedAdd64 (← loadU64 cData RewOff.rolloverQuote) rollover
  let newPend ← checkedAdd64 (← loadU64 cData RewOff.pendingClaims) quotePaid
  let newTotQ ← checkedAdd64 (← loadU64 cData RewOff.totalQuoteSpent) quotePaid
  let newTotB ← checkedAdd64 (← loadU64 cData RewOff.totalTargetBurned) totBids
  storeU64 cData RewOff.rolloverQuote newRoll
  storeU64 cData RewOff.pendingClaims newPend
  storeU64 cData RewOff.totalQuoteSpent newTotQ
  storeU64 cData RewOff.totalTargetBurned newTotB
  storeU64 cData RewOff.reserveRateE6 nextRate
  log64 EVT_SETTLE_EPOCH epId quotePaid totBids nextRate

/-- Op 4 (`ClaimQuote`): O(1) claim of exact uniform-price quote payout from ANY settled epoch,
    automatically closing `bidReceipt` (`zeroRewardWords` + `MAGIC_CLOSED`) and refunding 100%
    of its rent lamports back to `bidder` (zero rent leak, zero same-tx revival!).
    Accounts (9):
      0. `cfg` (W)
      1. `epochAcc` (W) — any settled `EpochState` belonging to `cfg`
      2. `bidReceipt` (W) — bidder's `BidReceipt` for `epochAcc` (closed & rent refunded!)
      3. `bidder` (W, S) — MUST match `bidReceipt.bidder` (receives reclaimed rent lamports)
      4. `rewAuthPda`
      5. `quoteVault` (W)
      6. `bidderQuoteTok` (W)
      7. `quoteMint`
      8. `quoteTokProg`
    Ix data (1 byte): `[4]`. -/
def handleClaimQuote (input : Ptr) : SolanaM Unit := do
  let (n, cfg, _, progId) ← parseIxOnly input
  SolanaM.require (n >= 9) Err.notEnoughAccountKeys
  let epochAcc       ← AccountView.nextCursor cfg
  let bidReceipt     ← AccountView.nextCursor epochAcc
  let bidder         ← AccountView.nextCursor bidReceipt
  let rewAuthPda     ← AccountView.nextCursor bidder
  let quoteVault     ← AccountView.nextCursor rewAuthPda
  let bidderQuoteTok ← AccountView.nextCursor quoteVault
  let quoteMint      ← AccountView.nextCursor bidderQuoteTok
  let quoteTokProg   ← AccountView.nextCursor quoteMint

  requireNonDup cfg; requireNonDup epochAcc; requireNonDup bidReceipt; requireNonDup bidder
  requireNonDup rewAuthPda; requireNonDup quoteVault; requireNonDup bidderQuoteTok
  requireNonDup quoteMint; requireNonDup quoteTokProg
  SolanaM.require (← AccountView.isSigner bidder) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable cfg) Err.invalidAccountData
  SolanaM.require (← AccountView.isWritable epochAcc) Err.invalidAccountData
  SolanaM.require (← AccountView.isWritable bidReceipt) Err.invalidAccountData
  SolanaM.require (← AccountView.isWritable bidder) Err.invalidAccountData
  SolanaM.require (!(← pubkeyEq (AccountView.keyPtr bidReceipt) (AccountView.keyPtr bidder))) PErr.aliasedAccounts
  checkRewardCfg cfg progId
  checkEpochAcc epochAcc cfg progId

  let cData := AccountView.dataPtr cfg
  let eData := AccountView.dataPtr epochAcc
  let rData := AccountView.dataPtr bidReceipt
  SolanaM.require ((← loadU8 eData EpochOff.settled) == 1) RErr.epochNotEnded

  SolanaM.require (← pubkeyEq (AccountView.ownerPtr bidReceipt) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen bidReceipt) == BidOff.size) Err.invalidAccountData
  SolanaM.require ((← loadU32 rData BidOff.magic) == MAGIC_BID) PErr.invalidMagic
  SolanaM.require (← pubkeyEq (rData + BidOff.cfg) (AccountView.keyPtr cfg)) RErr.epochMismatch
  SolanaM.require (← pubkeyEq (rData + BidOff.epochAcc) (AccountView.keyPtr epochAcc)) RErr.epochMismatch
  SolanaM.require (← pubkeyEq (rData + BidOff.bidder) (AccountView.keyPtr bidder)) PErr.unauthorized
  let epId ← loadU64 eData EpochOff.epochId
  SolanaM.require ((← loadU64 rData BidOff.epochId) == epId) RErr.epochMismatch

  SolanaM.require (← pubkeyEq (AccountView.keyPtr quoteVault) (cData + RewOff.quoteVault)) RErr.vaultMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr quoteMint) (cData + RewOff.quoteMint)) RErr.mintMismatch
  SolanaM.require (!(← pubkeyEq (AccountView.keyPtr quoteVault) (AccountView.keyPtr bidderQuoteTok))) PErr.aliasedAccounts
  checkTokenProg quoteTokProg

  let qPot     ← loadU64 eData EpochOff.quotePot
  let virtBids ← loadU64 eData EpochOff.virtBids
  let totBids  ← loadU64 eData EpochOff.totalBids
  let bidAmt   ← loadU64 rData BidOff.amount

  -- Compute exact uniform `xy = k` payout: `floor(Q_e * b_i / (B_e + B_virt))`
  let mut payout : UInt64 := 0
  if bidAmt > 0 && totBids > 0 then
    let denom ← checkedAdd64 totBids virtBids
    payout ← mulDiv64 qPot bidAmt denom

  -- Checks-Effects-Interactions: permanently close `bidReceipt` (`zeroRewardWords` + `MAGIC_CLOSED`),
  -- refund 100% of rent lamports to `bidder`, and debit `pendingClaims` BEFORE SPL CPI!
  zeroRewardWords rData 0 (BidOff.size >>> 3)
  storeU32 rData BidOff.magic MAGIC_CLOSED
  let recLam ← AccountView.lamports bidReceipt
  let bidLam ← AccountView.lamports bidder
  AccountView.setLamports bidder (← checkedAdd64 bidLam recLam)
  AccountView.setLamports bidReceipt 0
  if payout > 0 then
    let newClaimed ← checkedAdd64 (← loadU64 eData EpochOff.claimedQuote) payout
    let quotePaid  ← loadU64 eData EpochOff.quotePaid
    SolanaM.require (newClaimed <= quotePaid) Err.arithmeticOverflow
    storeU64 eData EpochOff.claimedQuote newClaimed
    let newPend ← checkedSub64 (← loadU64 cData RewOff.pendingClaims) payout Err.arithmeticOverflow
    storeU64 cData RewOff.pendingClaims newPend
    let qDec ← loadU8 cData RewOff.quoteDecimals
    let bump ← loadU8 cData RewOff.pdaBump
    tokenTransferCheckedSigned quoteTokProg quoteVault quoteMint bidderQuoteTok rewAuthPda payout qDec
      TAG_REW_AUTH (AccountView.keyPtr cfg) bump

  log64 EVT_CLAIM_QUOTE epId bidAmt payout (← loadU64 eData EpochOff.claimedQuote)

def dispatch (input : Ptr) : SolanaM Unit := do
  let (_, _, ix, _) ← parseIxOnly input
  SolanaM.require (ix.len >= 1) Err.invalidInstructionData
  let op ← loadU8 ix.ptr 0
  if op == 0 then handleInitReward input
  else if op == 1 then handleStartEpoch input
  else if op == 2 then handleSubmitBid input
  else if op == 3 then handleSettleEpoch input
  else if op == 4 then handleClaimQuote input
  else SolanaM.fail PErr.invalidInstruction

def entrypoint (input : Ptr) (s : SvmState) : UInt64 × SvmState :=
  SolanaM.runEntry (dispatch input) s

end Percolator.RewardModule
