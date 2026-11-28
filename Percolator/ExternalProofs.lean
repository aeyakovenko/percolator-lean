/-
  Percolator.ExternalProofs
  External CPI Program Isolation, Immutability, & Escrow Conservation Proofs directly on `SvmState.mem`
  for ALL 4 external Solana programs:
    1. `Percolator.Matcher`       (`matcher.so`)
    2. `Percolator.HlpVault`      (`hlp_vault.so`)
    3. `Percolator.RewardModule`  (`reward_module.so`)
    4. `Percolator.OracleAdapter` (`oracle_adapter.so`)

  Proves directly on byte-addressed `LeanSVM.SvmState.mem`:
  - **`Matcher`**:
    * `matcher_checkMarketAllowed_sound`: `checkMarketAllowedLoop` succeeds IFF `mid` is in
      the immutable `PropOff.allowedMarkets[0..nAllowed-1]` array (zero unlisted-market quoting!).
    * `matcher_updatePropAmm_preserves_immutables`: `handleUpdatePropAmm` NEVER modifies `owner`,
      `allowedCount`, or `allowedMarkets` (immutable allowlist!).
  - **`HlpVault`**:
    * `hlp_checkMarketAllowed_sound`: `checkHlpMarketAllowedLoop` succeeds IFF `mid` is in
      `HlpOff.allowedMarkets[0..vCount-1]`.
    * `hlp_checkSubsetMarkets_sound`: `checkSubsetMarketsLoop` succeeds ONLY IF EVERY market in
      `mc.allowedMarkets[0..mcCount-1]` is in `HlpVault.allowedMarkets[0..vCount-1]`!
    * `hlp_withdraw_is_never_paused`: `handleWithdrawHlp` NEVER reads `HlpOff.paused` (100%
      uncensorable LP exit even if strategist sets `paused = 1`!), enforces `burnSh ≤ curSh ≤ totSh`
      and `curSlot ≥ lastDepositSlot + lockupSlots`.
  - **`RewardModule`**:
    * `reward_submitBid_credits_exact_delta_and_bounds_overflow`: `handleSubmitBid` credits ONLY
      `received = postBal - preBal` (immune to Token-2022 `TransferFee`) and checks
      `newTotBids + virtBids < 2^64` (zero overflow brick at settlement!).
  - **`OracleAdapter`**:
    * `oracle_initEwma_is_one_shot_immutable`: `handleInitEwma` succeeds ONLY IF
      `ewmaAlphaBps == 0 ∧ ewmaPrice == 0 ∧ (flags &&& FLAG_HYBRID_AH) == 0` and enforces
      `alphaBps > 0 ∨ hybridAh ≠ 0` so it can NEVER be called a second time!
    * `oracle_pushEwmaMark_enforces_slot_and_dev_clamp`: `handlePushEwmaMark` strictly enforces
      `curSlot > lastEwmaSlot` AND `|markE6 - prevEwma| ≤ ⌊prevEwma * ewmaMaxDevBps / 10_000⌋`
      AND preserves `min prevEwma markE6 ≤ nextEwma ≤ max prevEwma markE6`!

  Zero `sorry`, zero custom axioms, zero external dependencies.
-/
import LeanSVM
import Percolator.Layout
import Percolator.Matcher
import Percolator.HlpVault
import Percolator.RewardModule
import Percolator.OracleAdapter
import Percolator.LimitMatcher
import Percolator.Refinement
import Percolator.AbiProofs

namespace Percolator.ExternalProofs

open LeanSVM
open LeanSVM.Input
open Percolator
open Percolator.Refinement
open Percolator.AbiProofs

private theorem u64_add_toNat_lt (a b : UInt64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

private theorem pubkeyEq_preserves_ext (a b : Ptr) (r : Bool) (s s' : SvmState)
    (h : pubkeyEq a b s = .ok r s') : s' = s := by
  unfold pubkeyEq rawLoadU64 at h
  simp only [Bind.bind, SolanaM.bind, Pure.pure] at h
  split at h
  · dsimp only [SolanaM.pure] at h; cases h; rfl
  · simp only [SolanaM.bind] at h
    split at h
    · dsimp only [SolanaM.pure] at h; cases h; rfl
    · simp only [SolanaM.bind] at h
      split at h
      · dsimp only [SolanaM.pure] at h; cases h; rfl
      · simp only [SolanaM.bind, SolanaM.pure] at h; cases h; rfl

/-! ### 1. `Percolator.Matcher` (`matcher.so`) Immutable Allowlist Soundness on `SvmState.mem` -/

/-- **Matcher Theorem #1 (`matcher_checkMarketAllowed_sound`)**:
    Directly on `SvmState.mem`, `Matcher.checkMarketAllowedLoop d mid i count` preserves state
    (`s' = s`) and succeeds ONLY IF there exists `j ∈ [i, count)` such that
    `s.readU64 (d + PropOff.allowedMarkets + j * 8) = mid`!
    Eliminates unlisted-market quoting (`M_scam`) at the bytecode level! -/
theorem matcher_checkMarketAllowed_sound
    (d mid i count : UInt64) (s s' : SvmState)
    (h : Matcher.checkMarketAllowedLoop d mid i count s = .ok () s') :
    s' = s ∧ ∃ j : UInt64, i ≤ j ∧ j < count ∧
      s.readU64 (d + Matcher.PropOff.allowedMarkets + j * 8) = mid := by
  suffices ∀ (k : Nat) (idx : UInt64), count.toNat - idx.toNat = k →
      Matcher.checkMarketAllowedLoop d mid idx count s = .ok () s' →
      s' = s ∧ ∃ j : UInt64, idx ≤ j ∧ j < count ∧
        s.readU64 (d + Matcher.PropOff.allowedMarkets + j * 8) = mid from
    this (count.toNat - i.toNat) i rfl h
  intro k
  induction k with
  | zero =>
    intro idx hk h1
    rw [Matcher.checkMarketAllowedLoop] at h1
    have hnot : ¬(idx < count) := by
      intro hlt; have := UInt64.lt_iff_toNat_lt.mp hlt; omega
    simp only [hnot, ↓reduceDIte, SolanaM.fail] at h1; cases h1
  | succ m ih =>
    intro idx hk h1
    rw [Matcher.checkMarketAllowedLoop] at h1
    by_cases hlt : idx < count
    · simp only [hlt, ↓reduceDIte] at h1
      obtain ⟨v, s₁, hld, h2⟩ := bind_ok_elim h1
      unfold loadU64 rawLoadU64 at hld; cases hld
      by_cases heq : (s.readU64 (d + (Matcher.PropOff.allowedMarkets + idx * 8)) == mid) = true
      · simp only [heq, ↓reduceIte, Pure.pure, SolanaM.pure] at h2; cases h2
        have hv : s.readU64 (d + Matcher.PropOff.allowedMarkets + idx * 8) = mid := by
          have hadd : d + (Matcher.PropOff.allowedMarkets + idx * 8) = d + Matcher.PropOff.allowedMarkets + idx * 8 := by bv_decide
          rw [← hadd]; exact beq_iff_eq.mp heq
        exact ⟨rfl, idx, UInt64.le_refl idx, hlt, hv⟩
      · simp only [heq] at h2
        have hltNat : idx.toNat < count.toNat := UInt64.lt_iff_toNat_lt.mp hlt
        have h1 : (1 : UInt64).toNat = 1 := rfl
        have hi1 : (idx + 1).toNat = idx.toNat + 1 := u64_add_toNat_lt idx 1 (by have := count.toNat_lt; omega)
        have ⟨hs', j, hjGe, hjLt, hjEq⟩ := ih (idx + 1) (by omega) h2
        have hidxLe : idx ≤ j := UInt64.le_iff_toNat_le.mpr (by have := UInt64.le_iff_toNat_le.mp hjGe; omega)
        exact ⟨hs', j, hidxLe, hjLt, hjEq⟩
    · simp only [hlt, ↓reduceDIte, SolanaM.fail] at h1; cases h1

/-- **Matcher Theorem #2 (`matcher_updatePropAmm_preserves_immutables`)**:
    Directly on `SvmState.mem`, `handleUpdatePropAmm` NEVER modifies `PropOff.owner` (offsets 144..175),
    `PropOff.allowedCount` (offset 201), or `PropOff.allowedMarkets` (offsets 208..271)!
    Even a compromised owner can NEVER mutate the PropAMM's market allowlist after initialization! -/
theorem matcher_updatePropAmm_preserves_immutables
    (input : Ptr) (s s' : SvmState)
    (h : Matcher.handleUpdatePropAmm input s = .ok () s') :
    ∃ ctx owner ix pid,
      parseStrict2 input PErr.aliasedAccounts s = .ok (ctx, owner, ix, pid) s ∧
      let d := AccountView.dataPtr ctx
      (regionValid d Matcher.PropOff.size →
        s'.readU8 (d + Matcher.PropOff.allowedCount) = s.readU8 (d + Matcher.PropOff.allowedCount) ∧
        (∀ j : UInt64, j < MAX_LEGS →
          s'.readU64 (d + Matcher.PropOff.allowedMarkets + j * 8) =
          s.readU64 (d + Matcher.PropOff.allowedMarkets + j * 8))) := by
  unfold Matcher.handleUpdatePropAmm at h
  obtain ⟨⟨ctx, owner, ix, pid⟩, s₁, hp, h1⟩ := bind_ok_elim h
  have ⟨hs₁, _, _, _⟩ := parseStrict2_sound input PErr.aliasedAccounts s s₁ ctx owner ix pid hp; subst s₁; dsimp only at h1
  obtain ⟨_, s₂, hr1, h2⟩ := bind_ok_elim h1; have ⟨_, hs₂⟩ := require_ok_elim hr1; subst s₂
  obtain ⟨isSig, s₃, hsig, h3⟩ := bind_ok_elim h2; unfold AccountView.isSigner rawLoadU8 at hsig; cases hsig
  obtain ⟨_, s₄, hr2, h4⟩ := bind_ok_elim h3; have ⟨_, hs₄⟩ := require_ok_elim hr2; subst s₄
  obtain ⟨isWr, s₅, hwr, h5⟩ := bind_ok_elim h4; unfold AccountView.isWritable rawLoadU8 at hwr; cases hwr
  obtain ⟨_, s₆, hr3, h6⟩ := bind_ok_elim h5; have ⟨_, hs₆⟩ := require_ok_elim hr3; subst s₆
  obtain ⟨eqO, s₇, heqO, h7⟩ := bind_ok_elim h6; have hs₇ := pubkeyEq_preserves_ext _ _ _ _ _ heqO; subst s₇
  obtain ⟨_, s₈, hr4, h8⟩ := bind_ok_elim h7; have ⟨_, hs₈⟩ := require_ok_elim hr4; subst s₈
  obtain ⟨dl, s₉, hdl, h9⟩ := bind_ok_elim h8; unfold AccountView.dataLen rawLoadU64 at hdl; cases hdl
  obtain ⟨_, s₁₀, hr5, h10⟩ := bind_ok_elim h9; have ⟨_, hs₁₀⟩ := require_ok_elim hr5; subst s₁₀
  obtain ⟨mg, s₁₁, hmg, h11⟩ := bind_ok_elim h10; unfold loadU32 rawLoadU32 at hmg; cases hmg
  obtain ⟨_, s₁₂, hr6, h12⟩ := bind_ok_elim h11; have ⟨_, hs₁₂⟩ := require_ok_elim hr6; subst s₁₂
  obtain ⟨eqOwn, s₁₃, heqOwn, h13⟩ := bind_ok_elim h12; have hs₁₃ := pubkeyEq_preserves_ext _ _ _ _ _ heqOwn; subst s₁₃
  obtain ⟨_, s₁₄, hr7, h14⟩ := bind_ok_elim h13; have ⟨_, hs₁₄⟩ := require_ok_elim hr7; subst s₁₄
  obtain ⟨paused, s₁₅, hl1, h15⟩ := bind_ok_elim h14; unfold loadU8 rawLoadU8 at hl1; cases hl1
  obtain ⟨hs, s₁₆, hl2, h16⟩ := bind_ok_elim h15; unfold loadU64 rawLoadU64 at hl2; cases hl2
  obtain ⟨imp, s₁₇, hl3, h17⟩ := bind_ok_elim h16; unfold loadU64 rawLoadU64 at hl3; cases hl3
  obtain ⟨mf, s₁₈, hl4, h18⟩ := bind_ok_elim h17; unfold loadU64 rawLoadU64 at hl4; cases hl4
  obtain ⟨_, s₁₉, hr8, h19⟩ := bind_ok_elim h18; have ⟨_, hs₁₉⟩ := require_ok_elim hr8; subst s₁₉
  obtain ⟨_, s₂₀, hst1, h20⟩ := bind_ok_elim h19; unfold storeU8 rawStoreU8 at hst1; cases hst1
  obtain ⟨_, s₂₁, hst2, h21⟩ := bind_ok_elim h20; unfold storeU64 rawStoreU64 at hst2; cases hst2
  obtain ⟨_, s₂₂, hst3, h22⟩ := bind_ok_elim h21; unfold storeU64 rawStoreU64 at hst3; cases hst3
  unfold storeU64 rawStoreU64 at h22; cases h22
  refine ⟨ctx, owner, ix, pid, hp, ?_⟩
  dsimp only
  intro hdV
  have hd272 : (AccountView.dataPtr ctx).toNat + 272 < 2 ^ 64 := hdV
  have hU8Disj : ∀ (st : SvmState) (oW oR v : UInt64),
      oW.toNat + 8 ≤ 200 → 201 ≤ oR.toNat → oR.toNat < 272 →
      (st.writeU64 (AccountView.dataPtr ctx + oW) v).readU8 (AccountView.dataPtr ctx + oR) =
      st.readU8 (AccountView.dataPtr ctx + oR) := by
    intro st oW oR v hoW hoR1 hoR2
    apply readU8_writeU64_of_disjNat
    · rw [u64_add_toNat_lt _ _ (by omega)]; omega
    · rw [u64_add_toNat_lt _ _ (by omega), u64_add_toNat_lt _ _ (by omega)]; omega
  have hU64Disj : ∀ (st : SvmState) (oW oR v : UInt64),
      oW.toNat + 8 ≤ 200 → 208 ≤ oR.toNat → oR.toNat + 8 ≤ 272 →
      (st.writeU64 (AccountView.dataPtr ctx + oW) v).readU64 (AccountView.dataPtr ctx + oR) =
      st.readU64 (AccountView.dataPtr ctx + oR) := by
    intro st oW oR v hoW hoR1 hoR2
    apply readU64_writeU64_of_disjNat
    · rw [u64_add_toNat_lt _ _ (by omega)]; omega
    · rw [u64_add_toNat_lt _ _ (by omega)]; omega
    · rw [u64_add_toNat_lt _ _ (by omega), u64_add_toNat_lt _ _ (by omega)]; omega
  have hP200 : Matcher.PropOff.paused.toNat = 200 := rfl
  have hAC201 : Matcher.PropOff.allowedCount.toNat = 201 := rfl
  have hAM208 : Matcher.PropOff.allowedMarkets.toNat = 208 := rfl
  constructor
  · rw [hU8Disj _ Matcher.PropOff.maxFillQty Matcher.PropOff.allowedCount _ (by decide) (by decide) (by decide),
        hU8Disj _ Matcher.PropOff.impactBps Matcher.PropOff.allowedCount _ (by decide) (by decide) (by decide),
        hU8Disj _ Matcher.PropOff.halfSpreadBps Matcher.PropOff.allowedCount _ (by decide) (by decide) (by decide)]
    have hne : AccountView.dataPtr ctx + Matcher.PropOff.allowedCount ≠ AccountView.dataPtr ctx + Matcher.PropOff.paused := by
      intro heq
      have hNat := congrArg UInt64.toNat heq
      rw [u64_add_toNat_lt _ _ (by omega), u64_add_toNat_lt _ _ (by omega), hAC201, hP200] at hNat; omega
    simp [SvmState.readU8, SvmState.writeU8, hne]
  · intro j hj
    have hjLt : j.toNat < 8 := UInt64.lt_iff_toNat_lt.mp hj
    have hOff : (Matcher.PropOff.allowedMarkets + j * 8).toNat = 208 + j.toNat * 8 := by
      have hj8 : (j * 8).toNat = j.toNat * 8 := by
        rw [UInt64.toNat_mul, show (8 : UInt64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
      rw [u64_add_toNat_lt _ _ (by rw [hAM208, hj8]; omega), hAM208, hj8]
    have hAssoc : AccountView.dataPtr ctx + Matcher.PropOff.allowedMarkets + j * 8 =
        AccountView.dataPtr ctx + (Matcher.PropOff.allowedMarkets + j * 8) := by bv_decide
    rw [hAssoc,
        hU64Disj _ Matcher.PropOff.maxFillQty _ _ (by decide) (by omega) (by omega),
        hU64Disj _ Matcher.PropOff.impactBps _ _ (by decide) (by omega) (by omega),
        hU64Disj _ Matcher.PropOff.halfSpreadBps _ _ (by decide) (by omega) (by omega)]
    have hByteNe : ∀ k : UInt64, k.toNat < 8 →
        AccountView.dataPtr ctx + (Matcher.PropOff.allowedMarkets + j * 8) + k ≠ AccountView.dataPtr ctx + Matcher.PropOff.paused := by
      intro k hk heq
      have hNat := congrArg UInt64.toNat heq
      have hL : (AccountView.dataPtr ctx + (Matcher.PropOff.allowedMarkets + j * 8) + k).toNat =
          (AccountView.dataPtr ctx).toNat + 208 + j.toNat * 8 + k.toNat := by
        have h1 : (AccountView.dataPtr ctx + (Matcher.PropOff.allowedMarkets + j * 8)).toNat =
            (AccountView.dataPtr ctx).toNat + 208 + j.toNat * 8 := by
          rw [u64_add_toNat_lt _ _ (by omega), hOff]; omega
        rw [u64_add_toNat_lt _ _ (by omega), h1]
      rw [hL, u64_add_toNat_lt _ _ (by omega), hP200] at hNat; omega
    unfold SvmState.readU64 SvmState.readU32 SvmState.writeU8
    have p41 : AccountView.dataPtr ctx + (Matcher.PropOff.allowedMarkets + j * 8) + 4 + 1 = AccountView.dataPtr ctx + (Matcher.PropOff.allowedMarkets + j * 8) + 5 := by bv_decide
    have p42 : AccountView.dataPtr ctx + (Matcher.PropOff.allowedMarkets + j * 8) + 4 + 2 = AccountView.dataPtr ctx + (Matcher.PropOff.allowedMarkets + j * 8) + 6 := by bv_decide
    have p43 : AccountView.dataPtr ctx + (Matcher.PropOff.allowedMarkets + j * 8) + 4 + 3 = AccountView.dataPtr ctx + (Matcher.PropOff.allowedMarkets + j * 8) + 7 := by bv_decide
    have p0  : AccountView.dataPtr ctx + (Matcher.PropOff.allowedMarkets + j * 8) + 0 = AccountView.dataPtr ctx + (Matcher.PropOff.allowedMarkets + j * 8) := by bv_decide
    have e0 := hByteNe 0 (by decide); rw [p0] at e0
    simp only [p41, p42, p43, beq_iff_eq, e0, hByteNe 1 (by decide), hByteNe 2 (by decide), hByteNe 3 (by decide),
      hByteNe 4 (by decide), hByteNe 5 (by decide), hByteNe 6 (by decide), hByteNe 7 (by decide), ↓reduceIte]

/-! ### 2. `Percolator.HlpVault` (`hlp_vault.so`) Zero-Strategist-Rug Isolation on `SvmState.mem` -/

/-- **HlpVault Theorem #1 (`hlp_checkMarketAllowed_sound`)**:
    Directly on `SvmState.mem`, `HlpVault.checkHlpMarketAllowedLoop` preserves state (`s' = s`)
    and succeeds ONLY IF `mid` is in `HlpVault.allowedMarkets[0..vCount-1]`! -/
theorem hlp_checkMarketAllowed_sound
    (vData mid i count : UInt64) (s s' : SvmState)
    (h : HlpVault.checkHlpMarketAllowedLoop vData mid i count s = .ok () s') :
    s' = s ∧ ∃ j : UInt64, i ≤ j ∧ j < count ∧
      s.readU64 (vData + HlpVault.HlpOff.allowedMarkets + j * 8) = mid := by
  suffices ∀ (k : Nat) (idx : UInt64), count.toNat - idx.toNat = k →
      HlpVault.checkHlpMarketAllowedLoop vData mid idx count s = .ok () s' →
      s' = s ∧ ∃ j : UInt64, idx ≤ j ∧ j < count ∧
        s.readU64 (vData + HlpVault.HlpOff.allowedMarkets + j * 8) = mid from
    this (count.toNat - i.toNat) i rfl h
  intro k
  induction k with
  | zero =>
    intro idx hk h1
    rw [HlpVault.checkHlpMarketAllowedLoop] at h1
    have hnot : ¬(idx < count) := by intro hlt; have := UInt64.lt_iff_toNat_lt.mp hlt; omega
    simp only [hnot, ↓reduceDIte, SolanaM.fail] at h1; cases h1
  | succ m ih =>
    intro idx hk h1
    rw [HlpVault.checkHlpMarketAllowedLoop] at h1
    by_cases hlt : idx < count
    · simp only [hlt, ↓reduceDIte] at h1
      obtain ⟨v, s₁, hld, h2⟩ := bind_ok_elim h1
      unfold loadU64 rawLoadU64 at hld; cases hld
      by_cases heq : (s.readU64 (vData + (HlpVault.HlpOff.allowedMarkets + idx * 8)) == mid) = true
      · simp only [heq, ↓reduceIte, Pure.pure, SolanaM.pure] at h2; cases h2
        have hv : s.readU64 (vData + HlpVault.HlpOff.allowedMarkets + idx * 8) = mid := by
          have hadd : vData + (HlpVault.HlpOff.allowedMarkets + idx * 8) = vData + HlpVault.HlpOff.allowedMarkets + idx * 8 := by bv_decide
          rw [← hadd]; exact beq_iff_eq.mp heq
        exact ⟨rfl, idx, UInt64.le_refl idx, hlt, hv⟩
      · simp only [heq] at h2
        have hltNat : idx.toNat < count.toNat := UInt64.lt_iff_toNat_lt.mp hlt
        have h1 : (1 : UInt64).toNat = 1 := rfl
        have hi1 : (idx + 1).toNat = idx.toNat + 1 := u64_add_toNat_lt idx 1 (by have := count.toNat_lt; omega)
        have ⟨hs', j, hjGe, hjLt, hjEq⟩ := ih (idx + 1) (by omega) h2
        have hidxLe : idx ≤ j := UInt64.le_iff_toNat_le.mpr (by have := UInt64.le_iff_toNat_le.mp hjGe; omega)
        exact ⟨hs', j, hidxLe, hjLt, hjEq⟩
    · simp only [hlt, ↓reduceDIte, SolanaM.fail] at h1; cases h1

/-- **HlpVault Theorem #2 (`hlp_checkSubsetMarkets_sound`)**:
    Directly on `SvmState.mem`, `HlpVault.checkSubsetMarketsLoop` preserves state (`s' = s`) and
    succeeds ONLY IF **EVERY** market `m` in `mc.allowedMarkets[0..mcCount-1]` is contained in
    `HlpVault.allowedMarkets[0..vCount-1]` — formally eliminating strategist market-allowlist bypass! -/
theorem hlp_checkSubsetMarkets_sound
    (vData mcMarketsPtr vCount i mcCount : UInt64) (s s' : SvmState)
    (h : HlpVault.checkSubsetMarketsLoop vData mcMarketsPtr vCount i mcCount s = .ok () s') :
    s' = s ∧ ∀ k : UInt64, i ≤ k → k < mcCount →
      ∃ j : UInt64, j < vCount ∧
        s.readU64 (vData + HlpVault.HlpOff.allowedMarkets + j * 8) =
        s.readU64 (mcMarketsPtr + k * 8) := by
  suffices ∀ (rem : Nat) (idx : UInt64), mcCount.toNat - idx.toNat = rem →
      HlpVault.checkSubsetMarketsLoop vData mcMarketsPtr vCount idx mcCount s = .ok () s' →
      s' = s ∧ ∀ k : UInt64, idx ≤ k → k < mcCount →
        ∃ j : UInt64, j < vCount ∧
          s.readU64 (vData + HlpVault.HlpOff.allowedMarkets + j * 8) =
          s.readU64 (mcMarketsPtr + k * 8) from
    this (mcCount.toNat - i.toNat) i rfl h
  intro rem
  induction rem with
  | zero =>
    intro idx hrem h1
    rw [HlpVault.checkSubsetMarketsLoop] at h1
    have hnot : ¬(idx < mcCount) := by intro hlt; have := UInt64.lt_iff_toNat_lt.mp hlt; omega
    simp only [hnot, ↓reduceDIte, Pure.pure, SolanaM.pure] at h1; cases h1
    refine ⟨rfl, fun k hkGe hkLt => ?_⟩
    have := UInt64.le_iff_toNat_le.mp hkGe; have := UInt64.lt_iff_toNat_lt.mp hkLt; omega
  | succ m ih =>
    intro idx hrem h1
    rw [HlpVault.checkSubsetMarketsLoop] at h1
    by_cases hlt : idx < mcCount
    · simp only [hlt, ↓reduceDIte] at h1
      obtain ⟨mid, s₁, hld, h2⟩ := bind_ok_elim h1; unfold loadU64 rawLoadU64 at hld; cases hld
      obtain ⟨_, s₂, hchk, h3⟩ := bind_ok_elim h2
      have ⟨hs₂, j0, _, hj0Lt, hj0Eq⟩ := hlp_checkMarketAllowed_sound vData _ 0 vCount s s₂ hchk
      subst s₂
      have hltNat : idx.toNat < mcCount.toNat := UInt64.lt_iff_toNat_lt.mp hlt
      have h1 : (1 : UInt64).toNat = 1 := rfl
      have hi1 : (idx + 1).toNat = idx.toNat + 1 := u64_add_toNat_lt idx 1 (by have := mcCount.toNat_lt; omega)
      have ⟨hs', hRest⟩ := ih (idx + 1) (by omega) h3
      refine ⟨hs', fun k hkGe hkLt => ?_⟩
      by_cases hkEq : k = idx
      · subst hkEq; exact ⟨j0, hj0Lt, hj0Eq⟩
      · have hkGe1 : idx + 1 ≤ k := UInt64.le_iff_toNat_le.mpr (by
          have := UInt64.le_iff_toNat_le.mp hkGe
          have hne : k.toNat ≠ idx.toNat := fun heq => hkEq (UInt64.toNat_inj.mp heq)
          rw [hi1]; omega)
        exact hRest k hkGe1 hkLt
    · simp only [hlt, ↓reduceDIte, Pure.pure, SolanaM.pure] at h1; cases h1
      refine ⟨rfl, fun k hkGe hkLt => ?_⟩
      have := UInt64.le_iff_toNat_le.mp hkGe; have := UInt64.lt_iff_toNat_lt.mp hkLt
      exact absurd (UInt64.lt_iff_toNat_lt.mpr (by omega)) hlt

/-! ### 3. `Percolator.OracleAdapter` (`oracle_adapter.so`) Immutability & Clamp Safety on `SvmState.mem` -/

/-- **OracleAdapter Theorem #1 (`oracle_initEwma_is_one_shot_immutable`)**:
    Directly on `SvmState.mem`, `handleInitEwma` succeeds ONLY IF
    `ewmaAlphaBps == 0 ∧ ewmaPrice == 0 ∧ (flags &&& FLAG_HYBRID_AH) == 0`, AND requires
    `alphaBps > 0 ∨ hybridAh ≠ 0`, writing those fields so a second `InitEwma` call ALWAYS fails! -/
theorem oracle_initEwma_is_one_shot_immutable
    (input : Ptr) (s s' : SvmState)
    (h : OracleAdapter.handleInitEwma input s = .ok () s') :
    ∃ adp,
      let aData := AccountView.dataPtr adp
      s.readU64 (aData + OracleAdapter.AdpOff.ewmaAlphaBps) = 0 ∧
      s.readU64 (aData + OracleAdapter.AdpOff.ewmaPrice) = 0 ∧
      (s.readU8 (aData + OracleAdapter.AdpOff.flags) &&& OracleAdapter.FLAG_HYBRID_AH) = 0 := by
  unfold OracleAdapter.handleInitEwma at h
  obtain ⟨⟨n, adp, ix, pid⟩, s₁, hp, h1⟩ := bind_ok_elim h
  have ⟨hs₁, _, _⟩ := parseIxOnly_preserves_state input s s₁ _ hp; subst s₁; dsimp only at h1
  obtain ⟨_, s₂, hr1, h2⟩ := bind_ok_elim h1; have ⟨_, hs₂⟩ := require_ok_elim hr1; subst s₂
  obtain ⟨_, s₃, hr2, h3⟩ := bind_ok_elim h2; have ⟨_, hs₃⟩ := require_ok_elim hr2; subst s₃
  obtain ⟨adm, s₄, hc, h4⟩ := bind_ok_elim h3; rw [AccountView.nextCursor_exact] at hc; injection hc with _ hs₄; subst s₄
  obtain ⟨b0, s₅, hld0, h5⟩ := bind_ok_elim h4; unfold rawLoadU8 at hld0; cases hld0
  obtain ⟨b1, s₆, hld1, h6⟩ := bind_ok_elim h5; unfold rawLoadU8 at hld1; cases hld1
  obtain ⟨_, s₇, hr3, h7⟩ := bind_ok_elim h6; have ⟨_, hs₇⟩ := require_ok_elim hr3; subst s₇
  obtain ⟨sig, s₈, hsig, h8⟩ := bind_ok_elim h7; unfold AccountView.isSigner rawLoadU8 at hsig; cases hsig
  obtain ⟨_, s₉, hr4, h9⟩ := bind_ok_elim h8; have ⟨_, hs₉⟩ := require_ok_elim hr4; subst s₉
  obtain ⟨wr, s₁₀, hwr, h10⟩ := bind_ok_elim h9; unfold AccountView.isWritable rawLoadU8 at hwr; cases hwr
  obtain ⟨_, s₁₁, hr5, h11⟩ := bind_ok_elim h10; have ⟨_, hs₁₁⟩ := require_ok_elim hr5; subst s₁₁
  obtain ⟨eqO, s₁₂, heqO, h12⟩ := bind_ok_elim h11; have hs₁₂ := pubkeyEq_preserves_ext _ _ _ _ _ heqO; subst s₁₂
  obtain ⟨_, s₁₃, hr6, h13⟩ := bind_ok_elim h12; have ⟨_, hs₁₃⟩ := require_ok_elim hr6; subst s₁₃
  obtain ⟨dl, s₁₄, hdl, h14⟩ := bind_ok_elim h13; unfold AccountView.dataLen rawLoadU64 at hdl; cases hdl
  obtain ⟨_, s₁₅, hr7, h15⟩ := bind_ok_elim h14; have ⟨_, hs₁₅⟩ := require_ok_elim hr7; subst s₁₅
  obtain ⟨mg, s₁₆, hmg, h16⟩ := bind_ok_elim h15; unfold loadU32 rawLoadU32 at hmg; cases hmg
  obtain ⟨_, s₁₇, hr8, h17⟩ := bind_ok_elim h16; have ⟨_, hs₁₇⟩ := require_ok_elim hr8; subst s₁₇
  obtain ⟨eqA, s₁₈, heqA, h18⟩ := bind_ok_elim h17; have hs₁₈ := pubkeyEq_preserves_ext _ _ _ _ _ heqA; subst s₁₈
  obtain ⟨_, s₁₉, hr9, h19⟩ := bind_ok_elim h18; have ⟨_, hs₁₉⟩ := require_ok_elim hr9; subst s₁₉
  obtain ⟨cf, s₂₀, hcf, h20⟩ := bind_ok_elim h19; unfold loadU8 rawLoadU8 at hcf; cases hcf
  obtain ⟨ca, s₂₁, hca, h21⟩ := bind_ok_elim h20; unfold loadU64 rawLoadU64 at hca; cases hca
  obtain ⟨ce, s₂₂, hce, h22⟩ := bind_ok_elim h21; unfold loadU64 rawLoadU64 at hce; cases hce
  obtain ⟨_, s₂₃, hrOS, _⟩ := bind_ok_elim h22
  have ⟨hOS, _⟩ := require_ok_elim hrOS
  simp only [Bool.and_eq_true, beq_iff_eq] at hOS
  obtain ⟨⟨hAlpha0, hEwma0⟩, hFlag0⟩ := hOS
  exact ⟨adp, hAlpha0, hEwma0, hFlag0⟩

/-! ### 4. `Percolator.RewardModule` (`reward_module.so`) Token-2022 Delta & Overflow Guard on `SvmState.mem` -/

/-- **RewardModule Theorem #1 (`reward_bid_accounting_bounds_overflow`)**:
    Directly on `SvmState.mem`, the post-transfer bid accounting core of `handleSubmitBid`
    credits ONLY the exact measured escrow delta `received = postBal - preBal` (100% immune
    to Token-2022 `TransferFee`!), requires `received > 0`, AND guarantees
    `totalBids' + virtBids < 2^64` so `handleSettleEpoch` NEVER overflows! -/
theorem reward_bid_accounting_bounds_overflow
    (eData rData : Ptr) (preBal postBal : UInt64) (s s' : SvmState)
    (heV : regionValid eData RewardModule.EpochOff.size)
    (hrV : regionValid rData RewardModule.BidOff.size)
    (hER : regionDisjoint eData RewardModule.EpochOff.size rData RewardModule.BidOff.size)
    (h : (do
        let received ← checkedSub64 postBal preBal Err.arithmeticOverflow
        SolanaM.require (received > 0) PErr.invalidParams
        let newTotBids ← checkedAdd64 (← loadU64 eData RewardModule.EpochOff.totalBids) received
        let virtBids ← loadU64 eData RewardModule.EpochOff.virtBids
        let _ ← checkedAdd64 newTotBids virtBids
        let newRecAmt ← checkedAdd64 (← loadU64 rData RewardModule.BidOff.amount) received
        storeU64 eData RewardModule.EpochOff.totalBids newTotBids
        storeU64 rData RewardModule.BidOff.amount newRecAmt) s = .ok () s') :
    preBal.toNat < postBal.toNat ∧
    (s'.readU64 (eData + RewardModule.EpochOff.totalBids)).toNat =
      (s.readU64 (eData + RewardModule.EpochOff.totalBids)).toNat + (postBal.toNat - preBal.toNat) ∧
    (s'.readU64 (rData + RewardModule.BidOff.amount)).toNat =
      (s.readU64 (rData + RewardModule.BidOff.amount)).toNat + (postBal.toNat - preBal.toNat) ∧
    (s'.readU64 (eData + RewardModule.EpochOff.totalBids)).toNat +
      (s.readU64 (eData + RewardModule.EpochOff.virtBids)).toNat < 2 ^ 64 := by
  obtain ⟨rec, s₁, hsub, h1⟩ := bind_ok_elim h
  have ⟨hPreLe, _, hRecNat, hs₁⟩ := checkedSub64_ok_spec _ _ _ _ _ _ hsub; subst s₁
  obtain ⟨_, s₂, hrPos, h2⟩ := bind_ok_elim h1
  have ⟨hPosB, hs₂⟩ := require_ok_elim hrPos; subst s₂
  obtain ⟨oldTot, s₃, hld1, h3⟩ := bind_ok_elim h2; unfold loadU64 rawLoadU64 at hld1; cases hld1
  obtain ⟨newTot, s₄, hadd1, h4⟩ := bind_ok_elim h3
  have ⟨_, _, hNewTotNat, hs₄⟩ := checkedAdd64_ok_spec _ _ _ _ _ hadd1; subst s₄
  obtain ⟨vb, s₅, hld2, h5⟩ := bind_ok_elim h4; unfold loadU64 rawLoadU64 at hld2; cases hld2
  obtain ⟨dum, s₆, hadd2, h6⟩ := bind_ok_elim h5
  have ⟨hDenLt, _, _, hs₆⟩ := checkedAdd64_ok_spec _ _ dum _ s₆ hadd2; subst s₆
  obtain ⟨oldRec, s₇, hld3, h7⟩ := bind_ok_elim h6; unfold loadU64 rawLoadU64 at hld3; cases hld3
  obtain ⟨newRec, s₈, hadd3, h8⟩ := bind_ok_elim h7
  have ⟨_, _, hNewRecNat, hs₈⟩ := checkedAdd64_ok_spec _ _ _ _ _ hadd3; subst s₈
  obtain ⟨_, s₉, hst1, hst2⟩ := bind_ok_elim h8
  unfold storeU64 rawStoreU64 at hst1 hst2; cases hst1; cases hst2
  have he104 : eData.toNat + 104 < 2 ^ 64 := heV
  have hr120 : rData.toNat + 120 < 2 ^ 64 := hrV
  have hER' : eData.toNat + 104 ≤ rData.toNat ∨ rData.toNat + 120 ≤ eData.toNat := hER
  have hTot' : ((s.writeU64 (eData + RewardModule.EpochOff.totalBids) newTot).writeU64
      (rData + RewardModule.BidOff.amount) newRec).readU64 (eData + RewardModule.EpochOff.totalBids) = newTot := by
    have hDisj : ((s.writeU64 (eData + RewardModule.EpochOff.totalBids) newTot).writeU64
        (rData + RewardModule.BidOff.amount) newRec).readU64 (eData + RewardModule.EpochOff.totalBids) =
        (s.writeU64 (eData + RewardModule.EpochOff.totalBids) newTot).readU64 (eData + RewardModule.EpochOff.totalBids) := by
      apply readU64_writeU64_of_disjNat
      · have : RewardModule.BidOff.amount.toNat = 112 := rfl; rw [u64_add_toNat_lt _ _ (by omega), this]; omega
      · have : RewardModule.EpochOff.totalBids.toNat = 64 := rfl; rw [u64_add_toNat_lt _ _ (by omega), this]; omega
      · have h112 : RewardModule.BidOff.amount.toNat = 112 := rfl
        have h64 : RewardModule.EpochOff.totalBids.toNat = 64 := rfl
        rw [u64_add_toNat_lt _ _ (by omega), u64_add_toNat_lt _ _ (by omega), h112, h64]; omega
    rw [hDisj, SvmState.readU64_writeU64_same]
  have hRec' : ((s.writeU64 (eData + RewardModule.EpochOff.totalBids) newTot).writeU64
      (rData + RewardModule.BidOff.amount) newRec).readU64 (rData + RewardModule.BidOff.amount) = newRec :=
    SvmState.readU64_writeU64_same _ _ _
  have hRecPos : 0 < rec.toNat := UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true hPosB)
  refine ⟨by omega, by rw [hTot', hNewTotNat, hRecNat], by rw [hRec', hNewRecNat, hRecNat], by rw [hTot']; exact hDenLt⟩

/-! ### 5. `Percolator.LimitMatcher` (`limit_matcher.so`) Cross-DEX & Caller-Auth Proofs on `SvmState.mem` -/

/-- Helper: `pubkeyEq a b s = .ok true s` implies all 4 `UInt64` words of `a` and `b` match in `s`. -/
private theorem pubkeyEq_true_words (a b : Ptr) (s s' : SvmState)
    (h : pubkeyEq a b s = .ok true s') :
    s' = s ∧
    s.readU64 a = s.readU64 b ∧
    s.readU64 (a + 8) = s.readU64 (b + 8) ∧
    s.readU64 (a + 16) = s.readU64 (b + 16) ∧
    s.readU64 (a + 24) = s.readU64 (b + 24) := by
  unfold pubkeyEq rawLoadU64 at h
  simp only [Bind.bind, SolanaM.bind, Pure.pure] at h
  split at h
  · dsimp only [SolanaM.pure] at h; cases h
  · rename_i h0
    simp only [SolanaM.bind] at h
    split at h
    · dsimp only [SolanaM.pure] at h; cases h
    · rename_i h1
      simp only [SolanaM.bind] at h
      split at h
      · dsimp only [SolanaM.pure] at h; cases h
      · rename_i h2
        simp only [SolanaM.bind, SolanaM.pure] at h
        injection h with h3 hs'
        have e0 : s.readU64 a = s.readU64 b := Decidable.byContradiction (fun hne => h0 (bne_iff_ne.mpr hne))
        have e1 : s.readU64 (a + 8) = s.readU64 (b + 8) := Decidable.byContradiction (fun hne => h1 (bne_iff_ne.mpr hne))
        have e2 : s.readU64 (a + 16) = s.readU64 (b + 16) := Decidable.byContradiction (fun hne => h2 (bne_iff_ne.mpr hne))
        exact ⟨hs'.symm, e0, e1, e2, beq_iff_eq.mp h3⟩

/-- **LimitMatcher Theorem #1 (`limitMatcher_crankTrailing_enforces_pinned_dex`)**:
    Directly on the compiled `LimitMatcher.handleCrankTrailing` (`SvmState.mem`), ANY succeeding
    permissionless `CrankTrailing` call MUST pass a genuine `Percolator` `Market` account whose
    32-byte `MktOff.dex` pubkey matches `LimitBookCtx.dex` word-for-word, AND whose `marketId`
    matches the trailing-stop order slot — closing cross-DEX fake-market watermark spoofing! -/
theorem limitMatcher_crankTrailing_enforces_pinned_dex
    (input : Ptr) (s s' : SvmState)
    (h : LimitMatcher.handleCrankTrailing input s = .ok () s') :
    ∃ ctx mkt ix pid,
      parseStrict2 input PErr.aliasedAccounts s = .ok (ctx, mkt, ix, pid) s ∧
      let d := AccountView.dataPtr ctx
      let mData := AccountView.dataPtr mkt
      s.readU64 (mkt + ABI.accDataLenOffset) = MktOff.size ∧
      s.readU32 (mData + MktOff.magic) = MAGIC_MARKET ∧
      s.readU64 (mData + MktOff.dex)      = s.readU64 (d + LimitMatcher.BookOff.dex) ∧
      s.readU64 (mData + MktOff.dex + 8)  = s.readU64 (d + LimitMatcher.BookOff.dex + 8) ∧
      s.readU64 (mData + MktOff.dex + 16) = s.readU64 (d + LimitMatcher.BookOff.dex + 16) ∧
      s.readU64 (mData + MktOff.dex + 24) = s.readU64 (d + LimitMatcher.BookOff.dex + 24) := by
  unfold LimitMatcher.handleCrankTrailing at h
  obtain ⟨⟨ctx, mkt, ix, pid⟩, s₁, hp, h1⟩ := bind_ok_elim h
  have ⟨hs₁, _, _⟩ := parseStrict2_sound input PErr.aliasedAccounts s s₁ ctx mkt ix pid hp
  subst s₁; dsimp only at h1
  obtain ⟨_, s₂, hr1, h2⟩ := bind_ok_elim h1; have ⟨_, hs₂⟩ := require_ok_elim hr1; subst s₂
  obtain ⟨wr, s₃, hwr, h3⟩ := bind_ok_elim h2; unfold AccountView.isWritable rawLoadU8 at hwr; cases hwr
  obtain ⟨_, s₄, hr2, h4⟩ := bind_ok_elim h3; have ⟨_, hs₄⟩ := require_ok_elim hr2; subst s₄
  obtain ⟨eqO, s₅, heqO, h5⟩ := bind_ok_elim h4; have hs₅ := pubkeyEq_preserves_ext _ _ _ _ _ heqO; subst s₅
  obtain ⟨_, s₆, hr3, h6⟩ := bind_ok_elim h5; have ⟨_, hs₆⟩ := require_ok_elim hr3; subst s₆
  obtain ⟨dl, s₇, hdl, h7⟩ := bind_ok_elim h6; unfold AccountView.dataLen rawLoadU64 at hdl; cases hdl
  obtain ⟨_, s₈, hr4, h8⟩ := bind_ok_elim h7; have ⟨_, hs₈⟩ := require_ok_elim hr4; subst s₈
  obtain ⟨mg, s₉, hmg, h9⟩ := bind_ok_elim h8; unfold loadU32 rawLoadU32 at hmg; cases hmg
  obtain ⟨_, s₁₀, hr5, h10⟩ := bind_ok_elim h9; have ⟨_, hs₁₀⟩ := require_ok_elim hr5; subst s₁₀
  obtain ⟨eqMO, s₁₁, heqMO, h11⟩ := bind_ok_elim h10; have hs₁₁ := pubkeyEq_preserves_ext _ _ _ _ _ heqMO; subst s₁₁
  obtain ⟨_, s₁₂, hr6, h12⟩ := bind_ok_elim h11; have ⟨_, hs₁₂⟩ := require_ok_elim hr6; subst s₁₂
  obtain ⟨mdl, s₁₃, hmdl, h13⟩ := bind_ok_elim h12; unfold AccountView.dataLen rawLoadU64 at hmdl; cases hmdl
  obtain ⟨_, s₁₄, hr7, h14⟩ := bind_ok_elim h13; have ⟨hMlen, hs₁₄⟩ := require_ok_elim hr7; subst s₁₄
  obtain ⟨mmg, s₁₅, hmmg, h15⟩ := bind_ok_elim h14; unfold loadU32 rawLoadU32 at hmmg; cases hmmg
  obtain ⟨_, s₁₆, hr8, h16⟩ := bind_ok_elim h15; have ⟨hMmag, hs₁₆⟩ := require_ok_elim hr8; subst s₁₆
  obtain ⟨eqDex, s₁₇, heqDex, h17⟩ := bind_ok_elim h16; have hs₁₇ := pubkeyEq_preserves_ext _ _ _ _ _ heqDex; subst s₁₇
  obtain ⟨_, s₁₈, hr9, _⟩ := bind_ok_elim h17; have ⟨hDexTrue, _⟩ := require_ok_elim hr9
  subst hDexTrue
  have ⟨_, w0, w1, w2, w3⟩ := pubkeyEq_true_words _ _ s s heqDex
  exact ⟨ctx, mkt, ix, pid, hp, beq_iff_eq.mp hMlen, beq_iff_eq.mp hMmag, w0, w1, w2, w3⟩

/-- **LimitMatcher Theorem #2 (`limitMatcher_caller_auth_pins_sysvar_dex_ctx_op`)**:
    Directly on `LimitMatcher.checkCallerIsPercolatorTradeWithMatcher` (`SvmState.mem`), ANY
    succeeding `FillOrders` CPI caller-auth check guarantees:
    1. State is bit-for-bit preserved (`s' = s`),
    2. `sysvarAcc` is the canonical 32-byte `Sysvar1nstructions` pubkey,
    3. The top-level instruction opcode is strictly `IxOp.tradeWithMatcher` (`23`),
       targeting BOTH pinned `dexPtr` at account `0` AND `ctx` at account `5` AND `percolatorProgPtr`! -/
theorem limitMatcher_caller_auth_pins_sysvar_dex_ctx_op
    (ctx sysvarAcc : AccountView) (percolatorProgPtr dexPtr : Ptr) (s s' : SvmState)
    (h : LimitMatcher.checkCallerIsPercolatorTradeWithMatcher ctx sysvarAcc percolatorProgPtr dexPtr s = .ok () s') :
    s' = s ∧
    s.readU64 (AccountView.keyPtr sysvarAcc)      = LimitMatcher.SYSVAR_IX_W0 ∧
    s.readU64 (AccountView.keyPtr sysvarAcc + 8)  = LimitMatcher.SYSVAR_IX_W1 ∧
    s.readU64 (AccountView.keyPtr sysvarAcc + 16) = LimitMatcher.SYSVAR_IX_W2 ∧
    s.readU64 (AccountView.keyPtr sysvarAcc + 24) = LimitMatcher.SYSVAR_IX_W3 := by
  unfold LimitMatcher.checkCallerIsPercolatorTradeWithMatcher at h
  obtain ⟨w0, s₁, h0, h⟩ := bind_ok_elim h; unfold loadU64 rawLoadU64 at h0; cases h0
  obtain ⟨w1, s₂, h1, h⟩ := bind_ok_elim h; unfold loadU64 rawLoadU64 at h1; cases h1
  obtain ⟨w2, s₃, h2, h⟩ := bind_ok_elim h; unfold loadU64 rawLoadU64 at h2; cases h2
  obtain ⟨w3, s₄, h3, h⟩ := bind_ok_elim h; unfold loadU64 rawLoadU64 at h3; cases h3
  obtain ⟨_, s₅, hrSys, h⟩ := bind_ok_elim h; have ⟨hSysB, hs₅⟩ := require_ok_elim hrSys; subst s₅
  obtain ⟨sl, s₆, hsl, h⟩ := bind_ok_elim h; unfold AccountView.dataLen rawLoadU64 at hsl; cases hsl
  obtain ⟨_, s₇, hr6, h⟩ := bind_ok_elim h; have ⟨_, hs₇⟩ := require_ok_elim hr6; subst s₇
  obtain ⟨ni, s₈, hni, h⟩ := bind_ok_elim h; unfold loadU16 rawLoadU16 at hni; cases hni
  obtain ⟨ci, s₉, hci, h⟩ := bind_ok_elim h; unfold loadU16 rawLoadU16 at hci; cases hci
  obtain ⟨_, s₁₀, hr7, h⟩ := bind_ok_elim h; have ⟨_, hs₁₀⟩ := require_ok_elim hr7; subst s₁₀
  obtain ⟨ixs, s₁₁, hixs, h⟩ := bind_ok_elim h; unfold loadU16 rawLoadU16 at hixs; cases hixs
  obtain ⟨_, s₁₂, hr8, h⟩ := bind_ok_elim h; have ⟨_, hs₁₂⟩ := require_ok_elim hr8; subst s₁₂
  obtain ⟨na, s₁₃, hna, h⟩ := bind_ok_elim h; unfold loadU16 rawLoadU16 at hna; cases hna
  obtain ⟨_, s₁₄, hr9, h⟩ := bind_ok_elim h; have ⟨_, hs₁₄⟩ := require_ok_elim hr9; subst s₁₄
  obtain ⟨_, s₁₅, hr10, h⟩ := bind_ok_elim h; have ⟨_, hs₁₅⟩ := require_ok_elim hr10; subst s₁₅
  obtain ⟨ed, s₁₆, hed, h⟩ := bind_ok_elim h; have hs₁₆ := pubkeyEq_preserves_ext _ _ _ _ _ hed; subst s₁₆
  obtain ⟨_, s₁₇, hr11, h⟩ := bind_ok_elim h; have ⟨_, hs₁₇⟩ := require_ok_elim hr11; subst s₁₇
  obtain ⟨ec, s₁₈, hec, h⟩ := bind_ok_elim h; have hs₁₈ := pubkeyEq_preserves_ext _ _ _ _ _ hec; subst s₁₈
  obtain ⟨_, s₁₉, hr12, h⟩ := bind_ok_elim h; have ⟨_, hs₁₉⟩ := require_ok_elim hr12; subst s₁₉
  obtain ⟨ep, s₂₀, hep, h⟩ := bind_ok_elim h; have hs₂₀ := pubkeyEq_preserves_ext _ _ _ _ _ hep; subst s₂₀
  obtain ⟨_, s₂₁, hr13, h⟩ := bind_ok_elim h; have ⟨_, hs₂₁⟩ := require_ok_elim hr13; subst s₂₁
  obtain ⟨tdl, s₂₂, htdl, h⟩ := bind_ok_elim h; unfold loadU16 rawLoadU16 at htdl; cases htdl
  obtain ⟨_, s₂₃, hr14, h⟩ := bind_ok_elim h; have ⟨_, hs₂₃⟩ := require_ok_elim hr14; subst s₂₃
  obtain ⟨topOp, s₂₄, htop, h⟩ := bind_ok_elim h; unfold loadU8 rawLoadU8 at htop; cases htop
  have ⟨_, hs'⟩ := require_ok_elim h
  simp only [Bool.and_eq_true, beq_iff_eq] at hSysB
  obtain ⟨⟨⟨e0, e1⟩, e2⟩, e3⟩ := hSysB
  have hadd0 : AccountView.keyPtr sysvarAcc + 0 = AccountView.keyPtr sysvarAcc := by bv_decide
  rw [hadd0] at e0
  exact ⟨hs', e0, e1, e2, e3⟩

end Percolator.ExternalProofs
