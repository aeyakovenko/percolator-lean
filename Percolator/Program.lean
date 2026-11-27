/-
  Percolator.Program
  Unified, zero-separation Lean 4 → Solana sBPF perpetual DEX program (v2).
  Realizable Shared Cross-Margin (full cross-margin capital efficiency on healthy markets)
  + Provable Per-Market Risk Isolation (`cross_margin_isolation_envelope`)
  + Exact Global Stock Equality (`C_tot + I_tot + R_tot + S_tot = V`).

  Written in clean, idiomatic Lean 4 with ZERO manual `@[noinline]` annotations or
  hand-rolled optimizations: `lean-svm` automatically handles smart outlining, constant
  rematerialization, binary-search switch dispatch, loop-weighted register allocation,
  and basic-block value-tracking peephole folding.
-/
import LeanSVM
import Percolator.Layout

namespace Percolator.Program

open LeanSVM
open LeanSVM.Input
open LeanSVM.Math
open LeanSVM.CPI
open Percolator

/-! ### Core Account, PDA, Token-Program & Checked-Mutation Helpers -/

def requireNonDup (acc : AccountView) : SolanaM Unit := do
  SolanaM.require ((← rawLoadU8 acc) == ABI.nonDupMarker) PErr.aliasedAccounts

def requireSigner (acc : AccountView) : SolanaM Unit := do
  SolanaM.require (← AccountView.isSigner acc) Err.missingRequiredSignature

def requireWritable (acc : AccountView) : SolanaM Unit := do
  SolanaM.require (← AccountView.isWritable acc) Err.invalidAccountData

def requireKeyEq (a b : Ptr) (err : UInt64) : SolanaM Unit := do
  SolanaM.require (← pubkeyEq a b) err

def requireKeyNe (a b : Ptr) (err : UInt64) : SolanaM Unit := do
  SolanaM.require (!(← pubkeyEq a b)) err

def pubkeyIsZero (p : Ptr) : SolanaM Bool := do
  let w0 ← loadU64 p 0
  let w1 ← loadU64 p 8
  let w2 ← loadU64 p 16
  let w3 ← loadU64 p 24
  return (w0 ||| w1 ||| w2 ||| w3) == 0

/-- Pin every SPL Token CPI strictly to canonical `TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA`. -/
def checkTokenProg (tokProg : AccountView) : SolanaM Unit := do
  let k := AccountView.keyPtr tokProg
  SolanaM.require ((← loadU64 k 0)  == SPL_TOK_W0) PErr.invalidTokenProg
  SolanaM.require ((← loadU64 k 8)  == SPL_TOK_W1) PErr.invalidTokenProg
  SolanaM.require ((← loadU64 k 16) == SPL_TOK_W2) PErr.invalidTokenProg
  SolanaM.require ((← loadU64 k 24) == SPL_TOK_W3) PErr.invalidTokenProg

/-- Pin SystemProgram CPIs strictly to canonical `11111111111111111111111111111111` (all zeros). -/
def checkSysProg (sysProg : AccountView) : SolanaM Unit := do
  SolanaM.require (← pubkeyIsZero (AccountView.keyPtr sysProg)) PErr.invalidSysProg

def getClockSlot : SolanaM UInt64 := do
  let buf ← stackAlloc 40
  let rc ← sysGetClock buf
  SolanaM.require (rc == 0) Err.invalidAccountData
  loadU64 buf 0

/-- Zero `nWords` consecutive 8-byte words starting at `base + off`.
    Used by every `Init*` handler, `freeLegIfEmpty`, and `handleCloseAccount` so NO account
    can ever retain dirty or cross-type residual bytes across reuse or same-tx revival attempts. -/
def zeroWordsLoop (base off nWords : UInt64) : SolanaM Unit := do
  if h : nWords == 0 then
    return ()
  else
    storeU64 base off 0
    zeroWordsLoop base (off + 8) (nWords - 1)
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

def checkOwnedMagic (acc : AccountView) (progId : Ptr) (exactLen : UInt64) (magic : UInt32) : SolanaM Unit := do
  requireKeyEq (AccountView.ownerPtr acc) progId Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen acc) == exactLen) Err.invalidAccountData
  SolanaM.require ((← loadU32 (AccountView.dataPtr acc) 0) == magic) PErr.invalidMagic

def checkFreshAccount (acc : AccountView) (progId : Ptr) (exactLen : UInt64) : SolanaM Unit := do
  requireWritable acc
  requireKeyEq (AccountView.ownerPtr acc) progId Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen acc) == exactLen) Err.invalidAccountData
  SolanaM.require ((← loadU32 (AccountView.dataPtr acc) 0) == 0) Err.accountAlreadyInitialized

def addU64At (base off delta : UInt64) : SolanaM Unit := do
  storeU64 base off (← checkedAdd64 (← loadU64 base off) delta)

def subU64At (base off delta : UInt64) : SolanaM Unit := do
  storeU64 base off (← checkedSub64 (← loadU64 base off) delta)

def loadOptU8 (ixPtr ixLen off : UInt64) : SolanaM UInt8 := do
  if ixLen > off then loadU8 ixPtr off else return 0

def loadOptU64 (ixPtr ixLen off : UInt64) : SolanaM UInt64 := do
  if ixLen >= off + 8 then loadU64 ixPtr off else return 0

def checkOracleFresh (mData : Ptr) (curSlot : UInt64) : SolanaM Unit := do
  let lastSlot ← loadU64 mData MktOff.lastOracleSlot
  let maxStale ← loadU64 mData MktOff.maxStaleness
  let age := if curSlot >= lastSlot then curSlot - lastSlot else 0
  SolanaM.require (age <= maxStale) PErr.oracleStale

def checkDexVaultAndMint (dexData : Ptr) (mint vaultPda tokProg : AccountView) : SolanaM Unit := do
  SolanaM.require ((← rawLoadU8 tokProg)  == ABI.nonDupMarker) PErr.aliasedAccounts
  SolanaM.require ((← rawLoadU8 mint)     == ABI.nonDupMarker) PErr.aliasedAccounts
  SolanaM.require ((← rawLoadU8 vaultPda) == ABI.nonDupMarker) PErr.aliasedAccounts
  checkTokenProg tokProg
  requireKeyEq (AccountView.keyPtr mint)     (dexData + DexOff.quoteMint) PErr.mintMismatch
  requireKeyEq (AccountView.keyPtr vaultPda) (dexData + DexOff.vaultPda)  PErr.vaultMismatch

/-- Sweep any floor-division dust from `m.realizedPool` once `m.totalPosPnl == 0`:
    credits `m.insurance` when LP shares exist, else `dex.totalSurplus`.
    On `STATUS_RESOLVED` markets with `totalInsShares == 0`, also sweeps orphan donated
    `m.insurance` into `dex.totalSurplus` so donated-only markets can cleanly tombstone! -/
def sweepResolvedDust (dData mData : Ptr) : SolanaM Unit := do
  if (← loadU64 mData MktOff.totalPosPnl) == 0 then
    let dust ← loadU64 mData MktOff.realizedPool
    if dust > 0 then
      storeU64 mData MktOff.realizedPool 0
      subU64At dData DexOff.totalResidual dust
      if (← loadU64 mData MktOff.totalInsShares) > 0 then
        addU64At mData MktOff.insurance dust
        addU64At dData DexOff.totalInsurance dust
      else
        addU64At dData DexOff.totalSurplus dust
    if (← loadU8 mData MktOff.status) == STATUS_RESOLVED then
      storeU64 mData MktOff.insFronted 0
      if (← loadU64 mData MktOff.totalInsShares) == 0 then
        let orphanIns ← loadU64 mData MktOff.insurance
        if orphanIns > 0 then
          storeU64 mData MktOff.insurance 0
          subU64At dData DexOff.totalInsurance orphanIns
          addU64At dData DexOff.totalSurplus orphanIns

/-! ### Portfolio Multi-Leg Slot Helpers (Loop over `MAX_LEGS = 8`) -/

def legPtrAt (pflData idx : UInt64) : Ptr :=
  pflData + PflOff.headerSize + idx * PflOff.legStride

def findLegLoop (pflData mid idx : UInt64) : SolanaM UInt64 := do
  if h : idx >= MAX_LEGS then
    return MAX_LEGS
  else
    let lp := legPtrAt pflData idx
    let act ← loadU8 lp LegOff.active
    if act != 0 then
      let lmid ← loadU64 lp LegOff.marketId
      if lmid == mid then return idx
    findLegLoop pflData mid (idx + 1)
termination_by (MAX_LEGS - idx).toNat
decreasing_by
  have hlt : idx.toNat < MAX_LEGS.toNat := by
    have : ¬ (idx >= MAX_LEGS) := h
    exact Nat.lt_of_not_ge (fun hge => this (UInt64.le_iff_toNat_le.mpr hge))
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hmax : MAX_LEGS.toNat = 8 := rfl
  have hadd : (idx + 1).toNat = idx.toNat + 1 := by
    rw [UInt64.toNat_add, h1]; exact Nat.mod_eq_of_lt (by omega)
  change (MAX_LEGS - (idx + 1)).toNat < (MAX_LEGS - idx).toNat
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)),
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hadd]
  omega

def findEmptySlotLoop (pflData idx : UInt64) : SolanaM UInt64 := do
  if h : idx >= MAX_LEGS then
    return MAX_LEGS
  else
    if (← loadU8 (legPtrAt pflData idx) LegOff.active) == 0 then return idx
    findEmptySlotLoop pflData (idx + 1)
termination_by (MAX_LEGS - idx).toNat
decreasing_by
  have hlt : idx.toNat < MAX_LEGS.toNat := by
    have : ¬ (idx >= MAX_LEGS) := h
    exact Nat.lt_of_not_ge (fun hge => this (UInt64.le_iff_toNat_le.mpr hge))
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hmax : MAX_LEGS.toNat = 8 := rfl
  have hadd : (idx + 1).toNat = idx.toNat + 1 := by
    rw [UInt64.toNat_add, h1]; exact Nat.mod_eq_of_lt (by omega)
  change (MAX_LEGS - (idx + 1)).toNat < (MAX_LEGS - idx).toNat
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)),
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hadd]
  omega

/-- Verify every active open leg in `pflData` was refreshed in `curSlot` (and optionally that
    every open leg holds its full isolated `lockedMm >= cachedMm` firewall!). -/
def checkAllLegsFreshLoop (pflData curSlot idx : UInt64) (requireLocked : Bool) : SolanaM Unit := do
  if h : idx >= MAX_LEGS then
    return ()
  else
    let lp := legPtrAt pflData idx
    let act ← loadU8 lp LegOff.active
    if act != 0 then
      let side ← loadU8 lp LegOff.side
      if side != SIDE_FLAT then
        let rSlot ← loadU64 lp LegOff.lastRefreshSlot
        SolanaM.require (rSlot == curSlot) PErr.stalePortfolioLeg
        if requireLocked then
          SolanaM.require ((← loadU64 lp LegOff.lockedMm) >= (← loadU64 lp LegOff.cachedMm)) PErr.insufficientMargin
    checkAllLegsFreshLoop pflData curSlot (idx + 1) requireLocked
termination_by (MAX_LEGS - idx).toNat
decreasing_by
  have hlt : idx.toNat < MAX_LEGS.toNat := by
    have : ¬ (idx >= MAX_LEGS) := h
    exact Nat.lt_of_not_ge (fun hge => this (UInt64.le_iff_toNat_le.mpr hge))
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hmax : MAX_LEGS.toNat = 8 := rfl
  have hadd : (idx + 1).toNat = idx.toNat + 1 := by
    rw [UInt64.toNat_add, h1]; exact Nat.mod_eq_of_lt (by omega)
  change (MAX_LEGS - (idx + 1)).toNat < (MAX_LEGS - idx).toNat
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)),
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hadd]
  omega

/-- Require all open legs to be fresh in `curSlot`, fully locked (`lockedMm >= cachedMm`),
    and total portfolio capital (`freeCapital + totalLockedMm`) `>= totalIm`. -/
def requirePortfolioIm (pflData : Ptr) (curSlot : UInt64) : SolanaM Unit := do
  checkAllLegsFreshLoop pflData curSlot 0 true
  let totCap ← checkedAdd64 (← loadU64 pflData PflOff.capital) (← loadU64 pflData PflOff.totalLockedMm)
  SolanaM.require (totCap >= (← loadU64 pflData PflOff.totalIm)) PErr.insufficientMargin

def findOrAllocLegSlot (pflData mktKey : Ptr) (mid : UInt64) : SolanaM UInt64 := do
  let existing ← findLegLoop pflData mid 0
  if existing < MAX_LEGS then
    requireKeyEq mktKey (legPtrAt pflData existing + LegOff.market) PErr.marketMismatch
    return existing
  -- Truly permissionless 8-leg cross-margin: any market sharing this DEX's base collateral mint
  -- may occupy any of the portfolio's 8 leg slots (zero special market 0, zero admin whitelist).
  -- Cross-market solvency is enforced by per-leg `lockedMm` firewalls, per-market K+1=5 compounded
  -- clamps, and `R_m + bounded I_m`-backed realization into `freeCapital`.
  let cnt ← loadU8 pflData PflOff.legCount
  let empty ← findEmptySlotLoop pflData 0
  SolanaM.require (empty < MAX_LEGS) PErr.portfolioFull
  let lp := legPtrAt pflData empty
  storeU8  lp LegOff.active 1
  storeU8  lp LegOff.side SIDE_FLAT
  storeU64 lp LegOff.marketId mid
  pubkeyCopy (lp + LegOff.market) mktKey
  storeU64 lp LegOff.rawBasis 0
  storeU64 lp LegOff.entryK K_ZERO
  storeU64 lp LegOff.posPnl 0
  storeU64 lp LegOff.cachedMm 0
  storeU64 lp LegOff.cachedIm 0
  storeU64 lp LegOff.lastRefreshSlot 0
  storeU64 lp LegOff.lockedMm 0
  storeU8 pflData PflOff.legCount (cnt + 1)
  return empty

def freeLegIfEmpty (pflData slotIdx : UInt64) : SolanaM Unit := do
  let lp := legPtrAt pflData slotIdx
  let act ← loadU8 lp LegOff.active
  if act != 0 then
    let side ← loadU8 lp LegOff.side
    let rawB ← loadU64 lp LegOff.rawBasis
    let pnl  ← loadU64 lp LegOff.posPnl
    let lock ← loadU64 lp LegOff.lockedMm
    if side == SIDE_FLAT && rawB == 0 && pnl == 0 && lock == 0 then
      zeroWordsLoop lp 0 (PflOff.legStride >>> 3)
      let cnt ← loadU8 pflData PflOff.legCount
      let newCnt := if cnt > 0 then cnt - 1 else 0
      storeU8 pflData PflOff.legCount newCnt

/-! ### Exact Verified Economic Kernels (Matching `Percolator.Spec` & `Percolator.Proofs`) -/

def deriveAdlU64 (oi rawBasis : UInt64) : SolanaM UInt64 := do
  if rawBasis == 0 || oi >= rawBasis then return ADL_ONE
  mulDiv64 ADL_ONE oi rawBasis

def haircutPayoutU64 (p realizedPool posPnlTot : UInt64) : SolanaM UInt64 := do
  if posPnlTot == 0 || p == 0 || realizedPool == 0 then return 0
  mulDiv64 p (if realizedPool < posPnlTot then realizedPool else posPnlTot) posPnlTot

def proportionalRawRedU64 (qty rawLeg rawSide oiSide : UInt64) : SolanaM UInt64 := do
  if oiSide == 0 || rawSide == 0 then return rawLeg
  if oiSide == rawSide then
    return if qty < rawLeg then qty else rawLeg
  let ceilR ← mulDiv64Ceil qty rawSide oiSide
  let r1 := if ceilR == 0 then 1 else ceilR
  return if r1 < rawLeg then r1 else rawLeg

/-- Raw-basis minted when opening `qty` effective OI on a side with `(oiSide, rawSide)`.
    Rejects 100%-wiped-out sides (`oiSide == 0 && rawSide > 0`); on healthy sides returns `qty`;
    on partially-ADL'd sides (`0 < oiSide < rawSide`) returns `ceil(qty * rawSide / oiSide)` so
    `(oi + qty) / (raw + rawAdd) <= oi / raw` (monotone non-inflating, re-enabling post-ADL opens!). -/
def postAdlRawAddU64 (qty oiSide rawSide : UInt64) : SolanaM UInt64 := do
  if rawSide == 0 then return qty
  SolanaM.require (oiSide > 0) PErr.adlHaircutActive
  if oiSide == rawSide then return qty
  let r ← mulDiv64Ceil qty rawSide oiSide
  return if r < qty then qty else r

/-- Ceiling proportional OI removal for liquidating `rawClose` rawBasis on `(oiSide, rawSide)`.
    Guarantees `oiSide - eff <= rawSide - rawClose` ALWAYS (even for 1-atom post-ADL dust!). -/
def proportionalOiForRawU64 (rawClose oiSide rawSide : UInt64) : SolanaM UInt64 := do
  if oiSide == 0 || rawSide == 0 then return 0
  if oiSide == rawSide then
    return if rawClose < oiSide then rawClose else oiSide
  let c ← mulDiv64Ceil rawClose oiSide rawSide
  let c1 := if c == 0 then 1 else c
  return if c1 < oiSide then c1 else oiSide

def computeMarginReq (effQty markPrice bps : UInt64) : SolanaM UInt64 := do
  if effQty == 0 then return 0
  mulDiv64Ceil (← mulDiv64Ceil effQty markPrice POS_SCALE) bps BPS_DEN

def computeMarginWithFloor (effQty markPrice bps floor : UInt64) : SolanaM UInt64 := do
  if effQty == 0 then return 0
  let r ← computeMarginReq effQty markPrice bps
  return if r < floor then floor else r

def legEffectiveQty (mktData lp : Ptr) : SolanaM UInt64 := do
  let side ← loadU8 lp LegOff.side
  let rawB ← loadU64 lp LegOff.rawBasis
  if side == SIDE_FLAT || rawB == 0 then return 0
  let adl ← loadU64 mktData (if side == SIDE_LONG then MktOff.adlLong else MktOff.adlShort)
  mulDiv64 rawB adl ADL_ONE

/-- Refresh `cachedMm` / `cachedIm` on `slotIdx`, maintain exact `pfl.totalMm` / `pfl.totalIm`,
    and rebalance this leg's isolated `lockedMm` firewall against `pfl.capital` (`freeCapital`)
    (zero-sum internal transfer: `pfl.capital + pfl.totalLockedMm` and `DexOff.totalCapital`
    are BIT-FOR-BIT INVARIANT, excess is released immediately back to `freeCapital`, and NO other
    leg's `lockedMm` is ever touched!). -/
def syncLegMargins (mktData pflData : Ptr) (slotIdx curSlot : UInt64) : SolanaM Unit := do
  let lp := legPtrAt pflData slotIdx
  let oldMm ← loadU64 lp LegOff.cachedMm
  let oldIm ← loadU64 lp LegOff.cachedIm
  let eff ← legEffectiveQty mktData lp
  let markP ← loadU64 mktData MktOff.markPrice
  let minMm ← loadU64 mktData MktOff.minMm
  let newMm ← computeMarginWithFloor eff markP (← loadU64 mktData MktOff.mmBps) minMm
  let newIm ← computeMarginWithFloor eff markP (← loadU64 mktData MktOff.imBps) minMm
  let totMm ← loadU64 pflData PflOff.totalMm
  let totIm ← loadU64 pflData PflOff.totalIm
  let baseMm := if totMm >= oldMm then totMm - oldMm else 0
  let baseIm := if totIm >= oldIm then totIm - oldIm else 0
  let newTotMm ← checkedAdd64 baseMm newMm
  let newTotIm ← checkedAdd64 baseIm newIm
  storeU64 pflData PflOff.totalMm newTotMm
  storeU64 pflData PflOff.totalIm newTotIm
  storeU64 lp LegOff.cachedMm        newMm
  storeU64 lp LegOff.cachedIm        newIm
  storeU64 lp LegOff.lastRefreshSlot curSlot
  -- Rebalance isolated per-leg `lockedMm` against shared `freeCapital` (`PflOff.capital`):
  let oldLock ← loadU64 lp LegOff.lockedMm
  if oldLock > newMm then
    let rel := oldLock - newMm
    storeU64 lp LegOff.lockedMm newMm
    subU64At pflData PflOff.totalLockedMm rel
    addU64At pflData PflOff.capital rel
  else if newMm > oldLock then
    let need := newMm - oldLock
    let freeCap ← loadU64 pflData PflOff.capital
    let topUp := if need < freeCap then need else freeCap
    if topUp > 0 then
      storeU64 pflData PflOff.capital (freeCap - topUp)
      addU64At pflData PflOff.totalLockedMm topUp
      storeU64 lp LegOff.lockedMm (oldLock + topUp)

/-- Route a loser's `capDeb` USD payment into market `m`, repaying `Mkt.insFronted` senior
    to `Mkt.insurance` (`I_m`) FIRST, then crediting any remainder into `Mkt.realizedPool` (`R_m`).
    Exact conservation: debits `0` from `C` (caller already debited `capDeb` from `C`), adds
    `repay` to `I` and `capDeb - repay` to `R`, so `I + R` increases by exact `capDeb`! -/
def creditMarketFromLoser (dData mData : Ptr) (capDeb : UInt64) : SolanaM Unit := do
  let fronted ← loadU64 mData MktOff.insFronted
  let repay := if capDeb < fronted then capDeb else fronted
  if repay > 0 then
    subU64At mData MktOff.insFronted repay
    addU64At mData MktOff.insurance repay
    addU64At dData DexOff.totalInsurance repay
  let toR := capDeb - repay
  if toR > 0 then
    addU64At mData MktOff.realizedPool toR
    addU64At dData DexOff.totalResidual toR

/-- Helper: execute `I_m`-contained fronted realization once `availIns` is computed. -/
def realizeFrontedPnl (dData mData fData : Ptr) (posPnl rPool totPnl availIns : UInt64) :
    SolanaM UInt64 := do
  let totAvail ← checkedAdd64 rPool availIns
  if totAvail >= totPnl && posPnl <= totPnl then
    let fromR := if posPnl < rPool then posPnl else rPool
    let fromIns := posPnl - fromR
    if fromR > 0 then
      subU64At mData MktOff.realizedPool fromR
      subU64At dData DexOff.totalResidual fromR
    if fromIns > 0 then
      subU64At mData MktOff.insurance fromIns
      subU64At dData DexOff.totalInsurance fromIns
      addU64At mData MktOff.insFronted fromIns
    addU64At fData PflOff.capital posPnl
    addU64At dData DexOff.totalCapital posPnl
    subU64At mData MktOff.totalPosPnl posPnl
    return 0
  return posPnl

/-- Realize `posPnl` into shared cross-margin `pfl.capital` strictly within `R_m + availIns`:
    1. If `R_m >= P^+_m` (or `forceHaircut`): realize from `R_m` (`0` fronting).
    2. Else if `status == ACTIVE && adlLong == ADL_ONE && adlShort == ADL_ONE && maxFrontBps > 0`
       AND NOT inside a saturated outage catch-up ramp (`lastRampSlot == 0 || curSlot > lastRampSlot + RAMP_FRONT_COOLDOWN`):
       compute `availIns` bounded by cumulative `maxFrontBps` of `I_m + insFronted` and call `realizeFrontedPnl`.
    Strictly contained to market `m`'s own `R_m + I_m` (zero cross-market contagion, exact
    `V == C + I + R + S + F`, and `Pfl.capital' >= Pfl.capital` unconditionally)! -/
def realizeWinnerPnl (dData mData fData : Ptr) (posPnl curSlot : UInt64) (forceHaircut : Bool) :
    SolanaM UInt64 := do
  if posPnl == 0 then return 0
  let rPool  ← loadU64 mData MktOff.realizedPool
  let totPnl ← loadU64 mData MktOff.totalPosPnl
  if (rPool >= totPnl && totPnl > 0) || forceHaircut then
    let pay ← haircutPayoutU64 posPnl rPool totPnl
    if pay > 0 then
      subU64At mData MktOff.realizedPool pay
      subU64At dData DexOff.totalResidual pay
      addU64At fData PflOff.capital pay
      addU64At dData DexOff.totalCapital pay
    subU64At mData MktOff.totalPosPnl posPnl
    return 0
  else
    let maxFrontBps ← loadU16 mData MktOff.maxFrontBps
    let rampSlot    ← loadU64 mData MktOff.lastRampSlot
    let notRamping  := rampSlot == 0 || curSlot < rampSlot || (curSlot - rampSlot) > RAMP_FRONT_COOLDOWN
    if maxFrontBps > 0 && totPnl > 0 && notRamping &&
       (← loadU8 mData MktOff.status) == STATUS_ACTIVE &&
       (← loadU64 mData MktOff.adlLong) == ADL_ONE &&
       (← loadU64 mData MktOff.adlShort) == ADL_ONE then
      let ins     ← loadU64 mData MktOff.insurance
      let fronted ← loadU64 mData MktOff.insFronted
      let nav     ← checkedAdd64 ins fronted
      let capIns  ←
        if maxFrontBps.toUInt64 == BPS_DEN then pure nav
        else mulDiv64 nav maxFrontBps.toUInt64 BPS_DEN
      let availIns :=
        if capIns > fronted then
          let remCap := capIns - fronted
          if remCap < ins then remCap else ins
        else 0
      realizeFrontedPnl dData mData fData posPnl rPool totPnl availIns
    else
      return posPnl

/-- Uncollectible bad-debt write-off (generalized across ALL 5 settlement callers):
    - When `allowBankrupt = false` (non-liquidation callers `RefreshLeg`, `Trade`, `TradeWithMatcher`),
      ANY nonzero bad debt (`sf > 0`) is rejected with `PErr.insufficientMargin` BEFORE touching
      `Mkt.insFronted` or advancing `entryK` so bad debt can NEVER bypass `handleLiquidate` (`#109`).
    - When `allowBankrupt = true` (`Liquidate`, `ClearDeadLeg`, `ForceClosePair`), any portion of `sf`
      already fronted out of `I_m` (`insFronted`) is written off so LP NAV is never overstated and
      `I_m` is never double-drawn! -/
def writeOffShortfall (mktData : Ptr) (sf : UInt64) (allowBankrupt : Bool := true) : SolanaM UInt64 := do
  if sf == 0 then return 0
  if !allowBankrupt then SolanaM.fail PErr.insufficientMargin
  let fronted ← loadU64 mktData MktOff.insFronted
  let wo := if sf < fronted then sf else fronted
  if wo > 0 then subU64At mktData MktOff.insFronted wo
  return sf - wo

/-- Pure high 64 bits of unsigned 64×64 multiplication (`⌊a * b / 2^64⌋`, zero stack/mem). -/
@[inline] def mulHi64 (a b : UInt64) : UInt64 :=
  let m : UInt64 := 0xFFFFFFFF
  let aLo := a &&& m; let aHi := a >>> 32
  let bLo := b &&& m; let bHi := b >>> 32
  let p0 := aLo * bLo; let p1 := aLo * bHi; let p2 := aHi * bLo; let p3 := aHi * bHi
  let mid := (p0 >>> 32) + (p1 &&& m) + (p2 &&& m)
  p3 + (p1 >>> 32) + (p2 >>> 32) + (mid >>> 32)

/-- Overflow-immune saturating `⌊a * b / denom⌋` (`denom > 0`): returns `u64::MAX` on `≥ 2^64`,
    preventing self-made market overflow DoS (`#110`) in `settleAndRefreshLeg`. -/
def mulDiv64Sat (a b denom : UInt64) : SolanaM UInt64 := do
  if mulHi64 a b >= denom then return 0xFFFFFFFFFFFFFFFF
  mulDiv64 a b denom

/-- Overflow-immune saturating `⌈a * b / denom⌉` (`denom > 0`): returns `u64::MAX` on `≥ 2^64`,
    preventing self-made market overflow DoS (`#110`) in `settleAndRefreshLeg`. -/
def mulDiv64CeilSat (a b denom : UInt64) : SolanaM UInt64 := do
  if mulHi64 a b >= denom then return 0xFFFFFFFFFFFFFFFF
  let q ← mulDiv64 a b denom
  if q == 0xFFFFFFFFFFFFFFFF then return 0xFFFFFFFFFFFFFFFF
  if (a ||| b) <= 0xFFFFFFFF then
    if (a * b) % denom == 0 then return q else return q + 1
  else
    if q * denom == a * b then return q else return q + 1

/-- Saturating gain cap so `posPnl + gain ≤ u64::MAX` and `totalPosPnl + gain ≤ u64::MAX`
    (prevents winning-leg overflow DoS on self-made markets, `#110`). -/
@[inline] def satAddGain (rawGain posPnl curTotPnl : UInt64) : UInt64 :=
  let roomPos := 0xFFFFFFFFFFFFFFFF - posPnl
  let roomTot := 0xFFFFFFFFFFFFFFFF - curTotPnl
  let room := if roomPos < roomTot then roomPos else roomTot
  if rawGain < room then rawGain else room

/-- Saturating gain credit into `MktOff.totalPosPnl` and `posPnl` (`#110` overflow-immune). -/
def creditSatGain (mktData : Ptr) (posPnl rawGain : UInt64) : SolanaM UInt64 := do
  let curTotPnl ← loadU64 mktData MktOff.totalPosPnl
  let gain := satAddGain rawGain posPnl curTotPnl
  storeU64 mktData MktOff.totalPosPnl (curTotPnl + gain)
  return posPnl + gain

/-- Per-leg `lockedMm` firewall loss settlement + `writeOffShortfall`:
    1. Burns `lp.posPnl` first,
    2. Debits shared `freeCapital` (`PflOff.capital`) second,
    3. Debits ONLY this leg's isolated `lp.lockedMm` third — **NEVER** any other leg's `lockedMm`!
    Returns `(posPnl', shortfall)`. -/
def settleFirewallLoss (dexData mktData pflData lp : Ptr) (posPnl loss : UInt64)
    (allowBankrupt : Bool) : SolanaM (UInt64 × UInt64) := do
  let pnlBurned := if loss < posPnl then loss else posPnl
  let posPnl1 := posPnl - pnlBurned
  if pnlBurned > 0 then subU64At mktData MktOff.totalPosPnl pnlBurned
  let rem1 := loss - pnlBurned
  let freeCap ← loadU64 pflData PflOff.capital
  let freeDeb := if rem1 < freeCap then rem1 else freeCap
  if freeDeb > 0 then
    storeU64 pflData PflOff.capital (freeCap - freeDeb)
  let rem2 := rem1 - freeDeb
  let legLock ← loadU64 lp LegOff.lockedMm
  let lockDeb := if rem2 < legLock then rem2 else legLock
  if lockDeb > 0 then
    storeU64 lp LegOff.lockedMm (legLock - lockDeb)
    subU64At pflData PflOff.totalLockedMm lockDeb
  let capDeb := freeDeb + lockDeb
  if capDeb > 0 then
    subU64At dexData DexOff.totalCapital capDeb
    creditMarketFromLoser dexData mktData capDeb
  let sf ← writeOffShortfall mktData (rem2 - lockDeb) allowBankrupt
  return (posPnl1, sf)

/-- Settle `entryK → kSide` with the per-leg `lockedMm` firewall:
    1. Burns `lp.posPnl` first,
    2. Debits shared `freeCapital` (`PflOff.capital`) second,
    3. Debits ONLY this leg's isolated `lp.lockedMm` third — **NEVER** any other leg's `lockedMm`!
    Guarantees BOTH:
    - **Zero Cross-Market Contagion**: no market `M_atk` can EVER reduce `M_real.lockedMm`, AND
    - **Zero Bug 1B Shielding**: `shortfall > 0 ⇒ freeCapital' == 0 ∧ lp.lockedMm' == 0` ALWAYS!
    Repays `Mkt.insFronted` senior, writes off uncollectible fronted bad debt, realizes backed
    (or `I_m`-fronted) `posPnl` into `freeCapital`, and syncs margins. -/
def settleAndRefreshLeg (dexData mktData pflData : Ptr) (slotIdx curSlot : UInt64)
    (forceHaircut : Bool) (allowBankrupt : Bool := true) : SolanaM UInt64 := do
  let lp := legPtrAt pflData slotIdx
  let side ← loadU8 lp LegOff.side
  let rawB ← loadU64 lp LegOff.rawBasis
  let mut posPnl ← loadU64 lp LegOff.posPnl
  let mut shortfall : UInt64 := 0

  if side != SIDE_FLAT && rawB > 0 then
    let kSide ← loadU64 mktData (if side == SIDE_LONG then MktOff.kLong else MktOff.kShort)
    let entryK ← loadU64 lp LegOff.entryK
    if kSide > entryK then
      let rawGain ← mulDiv64Sat rawB (kSide - entryK) POS_SCALE
      posPnl ← creditSatGain mktData posPnl rawGain
    else if entryK > kSide then
      let loss ← mulDiv64CeilSat rawB (entryK - kSide) POS_SCALE
      let (pp', sf') ← settleFirewallLoss dexData mktData pflData lp posPnl loss allowBankrupt
      posPnl := pp'
      shortfall := sf'
    storeU64 lp LegOff.entryK kSide

  posPnl ← realizeWinnerPnl dexData mktData pflData posPnl curSlot forceHaircut

  storeU64 lp LegOff.posPnl posPnl
  syncLegMargins mktData pflData slotIdx curSlot
  return shortfall

/-! ### Instruction Handlers (All 19 Unified Instructions, Auto-Outlined by `lean-svm`) -/

def handleInitDex (input : Ptr) : SolanaM Unit := do
  let (dex, admin, mint, vaultPda, feeVault, tokProg, sysProg, ix, progId) ← parseStrict7 input PErr.aliasedAccounts
  SolanaM.require (ix.len >= 20) Err.invalidInstructionData
  requireSigner admin; requireWritable vaultPda
  checkFreshAccount dex progId DexOff.size
  checkTokenProg tokProg
  checkSysProg sysProg
  let vaultBump    ← loadU8  ix.ptr 1
  let decimals     ← loadU8  ix.ptr 2
  let allowFreeze  ← loadU8  ix.ptr 3
  let createFee    ← loadU64 ix.ptr 4
  let rentLamports ← loadU64 ix.ptr 12
  SolanaM.require (allowFreeze <= 1 && createFee <= MAX_CREATE_FEE && rentLamports >= 2_039_280) PErr.invalidParams

  -- Validate SPL `quoteMint`: owned by canonical Token Program, exact 82B initialized Mint,
  -- matching `decimals` (byte 44), and by default (`allowFreeze == 0`) require
  -- `freeze_authority == COption::None` (bytes 46..50 == 0). Opt-in `allowFreeze == 1` enables
  -- blessed issuer base mints (e.g. mainnet USDC/USDT) while recording the choice immutably on `Dex`.
  requireKeyEq (AccountView.ownerPtr mint) (AccountView.keyPtr tokProg) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen mint) == 82) Err.invalidAccountData
  let mintData := AccountView.dataPtr mint
  SolanaM.require ((← loadU8 mintData 45) == 1) Err.uninitializedAccount
  SolanaM.require ((← loadU8 mintData 44) == decimals) PErr.invalidParams
  if allowFreeze == 0 then
    SolanaM.require ((← loadU32 mintData 46) == 0) PErr.invalidParams

  -- Create & initialize the `DexVault` PDA token account on-chain (works on real clusters &
  -- immune to 1-lamport pre-funding griefing; runtime enforces PDA seeds ["dvlt", dex, bump]!).
  let curLam ← AccountView.lamports vaultPda
  if curLam < rentLamports then
    systemTransfer sysProg admin vaultPda (rentLamports - curLam)
  systemAllocateSigned sysProg vaultPda 165 TAG_DEX_VAULT (AccountView.keyPtr dex) vaultBump
  systemAssignSigned   sysProg vaultPda (AccountView.keyPtr tokProg) TAG_DEX_VAULT (AccountView.keyPtr dex) vaultBump
  tokenInitializeAccount3 tokProg vaultPda mint (AccountView.keyPtr vaultPda)

  let dData := AccountView.dataPtr dex
  zeroWordsLoop dData 0 (DexOff.size >>> 3)
  storeU32 dData DexOff.magic MAGIC_DEX
  storeU8  dData DexOff.version 2
  storeU8  dData DexOff.vaultBump vaultBump
  storeU8  dData DexOff.decimals decimals
  storeU8  dData DexOff.allowFreeze allowFreeze
  pubkeyCopy (dData + DexOff.admin)     (AccountView.keyPtr admin)
  pubkeyCopy (dData + DexOff.quoteMint) (AccountView.keyPtr mint)
  pubkeyCopy (dData + DexOff.vaultPda)  (AccountView.keyPtr vaultPda)
  pubkeyCopy (dData + DexOff.feeVault)  (AccountView.keyPtr feeVault)
  storeU64 dData DexOff.nextMarketId 1
  storeU64 dData DexOff.nextPortfolioId 1
  storeU64 dData DexOff.createFee createFee

def handleUpdateCreateFee (input : Ptr) : SolanaM Unit := do
  let (n, dex, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 2) Err.notEnoughAccountKeys
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  let admin ← AccountView.nextCursor dex
  requireNonDup dex; requireNonDup admin
  requireSigner admin; requireWritable dex
  checkOwnedMagic dex progId DexOff.size MAGIC_DEX
  let dData := AccountView.dataPtr dex
  requireKeyEq (AccountView.keyPtr admin) (dData + DexOff.admin) PErr.unauthorized
  let newFee ← loadU64 ix.ptr 1
  SolanaM.require (newFee <= MAX_CREATE_FEE) PErr.invalidParams
  storeU64 dData DexOff.createFee newFee
  if n >= 3 then
    let newAdmin ← AccountView.nextCursor admin
    let effNewAdmin ← AccountView.resolveDup newAdmin 1 admin PErr.aliasedAccounts
    SolanaM.require (!(← pubkeyIsZero (AccountView.keyPtr effNewAdmin))) PErr.invalidParams
    pubkeyCopy (dData + DexOff.admin) (AccountView.keyPtr effNewAdmin)

def handleCreateMarket (input : Ptr) : SolanaM Unit := do
  let (dex, mkt, mint, oracleAuth, creatorRaw, creatorTok, feeVaultTokRaw, tokProg, ix, progId) ← parse8 input
  requireNonDup dex; requireNonDup mkt; requireNonDup mint; requireNonDup oracleAuth
  let creator ← AccountView.resolveDup creatorRaw 3 oracleAuth PErr.aliasedAccounts
  requireNonDup creatorTok
  let feeVaultTok ← AccountView.resolveDup feeVaultTokRaw 5 creatorTok PErr.aliasedAccounts
  requireNonDup tokProg
  SolanaM.require (ix.len >= 92) Err.invalidInstructionData
  requireSigner creator; requireWritable dex
  checkOwnedMagic dex progId DexOff.size MAGIC_DEX
  checkFreshAccount mkt progId MktOff.size
  checkTokenProg tokProg

  let dData := AccountView.dataPtr dex
  requireKeyEq (AccountView.keyPtr mint) (dData + DexOff.quoteMint) PErr.mintMismatch

  let maxFrontBps   ← loadU16 ix.ptr 2
  let initPrice     ← loadU64 ix.ptr 4
  let exitWindow    ← loadU64 ix.ptr 12
  let maxStaleness  ← loadU64 ix.ptr 20
  let reservedPad   ← loadU64 ix.ptr 28
  let imBps         ← loadU64 ix.ptr 36
  let mmBps         ← loadU64 ix.ptr 44
  let liqFeeBps     ← loadU64 ix.ptr 52
  let tradeFeeBps   ← loadU64 ix.ptr 60
  let maxMoveBps    ← loadU64 ix.ptr 68
  let maxInsDrawBps ← loadU64 ix.ptr 76
  let maxOi         ← loadU64 ix.ptr 84
  let minMm         ← if ix.len >= 100 then loadU64 ix.ptr 92 else pure 0
  let rewardBps     ← if ix.len >= 140 then loadU64 ix.ptr 100 else pure 0

  SolanaM.require (maxFrontBps.toUInt64 <= maxInsDrawBps && maxInsDrawBps <= BPS_DEN) PErr.invalidParams
  SolanaM.require (rewardBps <= BPS_DEN) PErr.invalidParams
  if rewardBps > 0 then
    SolanaM.require (ix.len >= 140) Err.invalidInstructionData
    SolanaM.require (!(← pubkeyIsZero (ix.ptr + 108))) PErr.invalidParams
  SolanaM.require (initPrice > 0 && initPrice <= MAX_PRICE) PErr.invalidParams
  SolanaM.require (exitWindow >= MIN_EXIT_WINDOW && exitWindow <= MAX_EXIT_WINDOW &&
                   maxStaleness >= 1 && maxStaleness <= MAX_STALENESS && reservedPad == 0) PErr.invalidParams
  SolanaM.require (mmBps > 0 && mmBps < imBps && imBps <= BPS_DEN) PErr.invalidParams
  -- Gap #1 + #7 Fix (Solana K+1 = 5-slot triggering + 4-slot leader window + liqFee at p5!):
  -- `k5MoveBps = 5*m + ceil(12*m^2 / 10000)` strictly bounds `((10000+m)^5 - 10000^5) / 10000^4`
  -- for all `m <= 1500`, `liqAtP5 = liqFeeBps + ceil(liqFeeBps * k5MoveBps / 10000)` bounds
  -- `liqFee` computed at post-jump `p5`, AND Gap B (`mmBps + maxMoveBps <= imBps`) blocks same-slot sandwich!
  SolanaM.require (liqFeeBps <= mmBps && maxMoveBps <= 1500) PErr.invalidParams
  let k5MoveBps := 5 * maxMoveBps + (maxMoveBps * maxMoveBps * 12 + 9999) / 10000
  let liqAtP5   := liqFeeBps + (liqFeeBps * k5MoveBps + 9999) / 10000
  SolanaM.require ((← checkedAdd64 k5MoveBps liqAtP5) <= mmBps &&
                   (← checkedAdd64 mmBps maxMoveBps) <= imBps) PErr.invalidParams
  SolanaM.require (tradeFeeBps <= 1000 && maxOi > 0 && maxOi <= MAX_OI) PErr.invalidParams
  let initNot ← mulDiv64Ceil maxOi initPrice POS_SCALE
  SolanaM.require (initNot <= MAX_MKT_NOTIONAL) PErr.invalidParams

  let createFee ← loadU64 dData DexOff.createFee
  if createFee > 0 then
    requireKeyEq (AccountView.keyPtr feeVaultTok) (dData + DexOff.feeVault) PErr.vaultMismatch
    requireKeyNe (AccountView.keyPtr feeVaultTok) (dData + DexOff.vaultPda) PErr.aliasedAccounts
    let dec ← loadU8 dData DexOff.decimals
    tokenTransferChecked tokProg creatorTok mint feeVaultTok creator createFee dec

  let mid ← loadU64 dData DexOff.nextMarketId
  storeU64 dData DexOff.nextMarketId (← checkedAdd64 mid 1)

  let mData := AccountView.dataPtr mkt
  zeroWordsLoop mData 0 (MktOff.size >>> 3)
  storeU32 mData MktOff.magic MAGIC_MARKET
  storeU8  mData MktOff.status STATUS_ACTIVE
  storeU16 mData MktOff.maxFrontBps maxFrontBps
  storeU64 mData MktOff.marketId mid
  pubkeyCopy (mData + MktOff.dex)         (AccountView.keyPtr dex)
  pubkeyCopy (mData + MktOff.oracleAuth)  (AccountView.keyPtr oracleAuth)
  pubkeyCopy (mData + MktOff.marketAdmin) (AccountView.keyPtr creator)
  storeU64 mData MktOff.markPrice initPrice
  storeU64 mData MktOff.lastOracleSlot (← getClockSlot)
  storeU64 mData MktOff.exitWindow exitWindow
  storeU64 mData MktOff.maxStaleness maxStaleness
  storeU64 mData MktOff.imBps imBps
  storeU64 mData MktOff.mmBps mmBps
  storeU64 mData MktOff.liqFeeBps liqFeeBps
  storeU64 mData MktOff.tradeFeeBps tradeFeeBps
  storeU64 mData MktOff.maxMoveBps maxMoveBps
  storeU64 mData MktOff.maxInsDrawBps maxInsDrawBps
  storeU64 mData MktOff.maxOi maxOi
  storeU64 mData MktOff.adlLong ADL_ONE
  storeU64 mData MktOff.adlShort ADL_ONE
  storeU64 mData MktOff.kLong K_ZERO
  storeU64 mData MktOff.kShort K_ZERO
  storeU64 mData MktOff.minMm minMm
  storeU64 mData MktOff.rewardBps rewardBps
  if rewardBps > 0 then
    pubkeyCopy (mData + MktOff.rewardRecipient) (ix.ptr + 108)

/-- Burn (`n == 2` or zero key) or transfer `marketAdmin` (`role == 0`), or rotate `oracleAuth` (`role == 1`). -/
def handleUpdateMarketAuth (input : Ptr) : SolanaM Unit := do
  let (n, mkt, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 2) Err.notEnoughAccountKeys
  let admin ← AccountView.nextCursor mkt
  requireNonDup mkt; requireNonDup admin
  requireSigner admin; requireWritable mkt
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  let mData := AccountView.dataPtr mkt
  SolanaM.require ((← loadU8 mData MktOff.status) != STATUS_TOMBSTONED) PErr.invalidStatus
  SolanaM.require (!(← pubkeyIsZero (mData + MktOff.marketAdmin))) PErr.unauthorized
  requireKeyEq (AccountView.keyPtr admin) (mData + MktOff.marketAdmin) PErr.unauthorized
  let role ← if ix.len >= 2 then loadU8 ix.ptr 1 else pure 0
  if role == 0 then
    if n >= 3 then
      let newAdmin ← AccountView.nextCursor admin
      let effNewAdmin ← AccountView.resolveDup newAdmin 1 admin PErr.aliasedAccounts
      pubkeyCopy (mData + MktOff.marketAdmin) (AccountView.keyPtr effNewAdmin)
    else
      storeU64 mData (MktOff.marketAdmin + 0)  0
      storeU64 mData (MktOff.marketAdmin + 8)  0
      storeU64 mData (MktOff.marketAdmin + 16) 0
      storeU64 mData (MktOff.marketAdmin + 24) 0
  else
    SolanaM.require (n >= 3) Err.notEnoughAccountKeys
    let newOracle ← AccountView.nextCursor admin
    let effNewOracle ← AccountView.resolveDup newOracle 1 admin PErr.aliasedAccounts
    SolanaM.require (!(← pubkeyIsZero (AccountView.keyPtr effNewOracle))) PErr.invalidParams
    pubkeyCopy (mData + MktOff.oracleAuth) (AccountView.keyPtr effNewOracle)

def handleUpdateOracle (input : Ptr) : SolanaM Unit := do
  let (mkt, oracleAuth, ix, progId) ← parseStrict2 input PErr.aliasedAccounts
  SolanaM.require (ix.len >= 18) Err.invalidInstructionData
  requireSigner oracleAuth; requireWritable mkt
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  let mData := AccountView.dataPtr mkt
  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_ACTIVE) PErr.invalidStatus
  requireKeyEq (AccountView.keyPtr oracleAuth) (mData + MktOff.oracleAuth) PErr.unauthorized

  -- Per-slot rate limit: strictly 1 oracle step per slot (enforces `oracle_clamp_zero_bad_debt`!)
  let curSlot ← getClockSlot
  let lastSlot ← loadU64 mData MktOff.lastOracleSlot
  SolanaM.require (curSlot > lastSlot) PErr.oracleSameSlot

  let newPrice ← loadU64 ix.ptr 1
  let fundSign ← loadU8  ix.ptr 9
  let fundE6   ← loadU64 ix.ptr 10
  SolanaM.require (newPrice > 0 && newPrice <= MAX_PRICE) PErr.invalidParams

  let oldPrice ← loadU64 mData MktOff.markPrice
  let diff := if newPrice >= oldPrice then newPrice - oldPrice else oldPrice - newPrice
  let oiL  ← loadU64 mData MktOff.oiLong
  let oiS  ← loadU64 mData MktOff.oiShort
  let rL   ← loadU64 mData MktOff.rawBasisLong
  let rS   ← loadU64 mData MktOff.rawBasisShort
  let isEmpty := oiL == 0 && oiS == 0 && rL == 0 && rS == 0
  if isEmpty then
    -- Empty market fast-snap: once all positions have closed out (`OI == 0 ∧ rawBasis == 0`),
    -- snap `markPrice` directly to live spot in 1 slot (requiring `fundE6 == 0`) and clear ramp pause!
    SolanaM.require (fundE6 == 0) PErr.oracleClamp
    storeU64 mData MktOff.lastRampSlot 0
  else
    -- Loaded market paced clamp (`dt == 1` half-step pacing): doubles censorship resistance
    -- (5-slot & 8-slot double-leader censorship stay within `mmBps` with 0 bad debt, while `dt >= 2`
    -- keeps full `maxMoveBps`). Saturated ramp ticks (`diff >= 75%` of `maxAllowed`) stamp
    -- `lastRampSlot = curSlot` to pause new `I_m` fronting during outage catch-up without blocking trades!
    let rawMaxMove ← loadU64 mData MktOff.maxMoveBps
    let effMaxMove :=
      if curSlot == lastSlot + 1 && rawMaxMove > 1 then rawMaxMove >>> 1 else rawMaxMove
    let maxAllowed ← mulDiv64 oldPrice effMaxMove BPS_DEN
    SolanaM.require ((← checkedAdd64 diff fundE6) <= maxAllowed) PErr.oracleClamp
    let rampThresh := maxAllowed - (maxAllowed >>> 2)
    if maxAllowed > 0 && diff >= rampThresh then
      storeU64 mData MktOff.lastRampSlot curSlot

  -- Gap #4B Fix (Exact Asymmetric-ADL Zero-Sum Oracle Settlement):
  -- Winning side uses floored `adlW * diff / ADL_ONE` (`rawW * ΔkW ≤ oiW * diff`).
  -- Losing side uses ceiled `oiL * diff / rawL` (`rawL * ΔkL ≥ oiL * diff`), guaranteeing
  -- `∑ gain ≤ ∑ loss` for EVERY asymmetric post-ADL ratio `(oi, rawL, rawS)` and EVERY `diff`!
  let maxOiCur := if oiL > oiS then oiL else oiS
  if maxOiCur > 0 then
    let curNot ← mulDiv64Ceil maxOiCur newPrice POS_SCALE
    SolanaM.require (curNot <= MAX_MKT_NOTIONAL) PErr.oiLimitExceeded
  let adlL ← loadU64 mData MktOff.adlLong
  let adlS ← loadU64 mData MktOff.adlShort
  if newPrice > oldPrice then
    addU64At mData MktOff.kLong  (← mulDiv64 adlL diff ADL_ONE)
    let dkS ← if rS == 0 then pure diff else mulDiv64Ceil oiS diff rS
    subU64At mData MktOff.kShort dkS
  else if oldPrice > newPrice then
    let dkL ← if rL == 0 then pure diff else mulDiv64Ceil oiL diff rL
    subU64At mData MktOff.kLong  dkL
    addU64At mData MktOff.kShort (← mulDiv64 adlS diff ADL_ONE)

  if fundE6 > 0 then
    if fundSign == 0 then
      let dkL ← if rL == 0 then pure fundE6 else mulDiv64Ceil oiL fundE6 rL
      subU64At mData MktOff.kLong  dkL
      addU64At mData MktOff.kShort (← mulDiv64 adlS fundE6 ADL_ONE)
    else
      let dkS ← if rS == 0 then pure fundE6 else mulDiv64Ceil oiS fundE6 rS
      subU64At mData MktOff.kShort dkS
      addU64At mData MktOff.kLong  (← mulDiv64 adlL fundE6 ADL_ONE)

  storeU64 mData MktOff.markPrice newPrice
  storeU64 mData MktOff.lastOracleSlot curSlot
  log64 EvtTag.oracle (← loadU64 mData MktOff.marketId) newPrice fundSign.toUInt64 fundE6

def handleInitPortfolio (input : Ptr) : SolanaM Unit := do
  let (dex, pfl, owner, _, progId) ← parseStrict3 input PErr.aliasedAccounts
  requireSigner owner; requireWritable dex
  checkOwnedMagic dex progId DexOff.size MAGIC_DEX
  checkFreshAccount pfl progId PflOff.size
  let dData := AccountView.dataPtr dex
  let pid ← loadU64 dData DexOff.nextPortfolioId
  storeU64 dData DexOff.nextPortfolioId (← checkedAdd64 pid 1)
  let fData := AccountView.dataPtr pfl
  zeroWordsLoop fData 0 (PflOff.size >>> 3)
  storeU32 fData PflOff.magic MAGIC_PORTFOLIO
  storeU8  fData PflOff.legCount 0
  storeU64 fData PflOff.portfolioId pid
  pubkeyCopy (fData + PflOff.dex)   (AccountView.keyPtr dex)
  pubkeyCopy (fData + PflOff.owner) (AccountView.keyPtr owner)

def handleDepositCollateral (input : Ptr) : SolanaM Unit := do
  let (dex, pfl, owner, ownerTok, mint, vaultPda, tokProg, ix, progId) ← parseStrict7 input PErr.aliasedAccounts
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner owner; requireWritable dex; requireWritable pfl
  checkOwnedMagic dex progId DexOff.size MAGIC_DEX
  checkOwnedMagic pfl progId PflOff.size MAGIC_PORTFOLIO
  let dData := AccountView.dataPtr dex
  let fData := AccountView.dataPtr pfl
  requireKeyEq (AccountView.keyPtr dex) (fData + PflOff.dex) PErr.dexMismatch
  checkDexVaultAndMint dData mint vaultPda tokProg
  requireKeyNe (AccountView.keyPtr ownerTok) (AccountView.keyPtr vaultPda) PErr.aliasedAccounts

  let amount ← loadU64 ix.ptr 1
  SolanaM.require (amount > 0) PErr.invalidParams
  let dec ← loadU8 dData DexOff.decimals
  tokenTransferChecked tokProg ownerTok mint vaultPda owner amount dec

  addU64At dData DexOff.vaultBalance amount
  addU64At dData DexOff.totalCapital amount
  addU64At fData PflOff.capital      amount
  log64 EvtTag.deposit (← loadU64 fData PflOff.portfolioId) amount (← loadU64 fData PflOff.capital) 0

def handleWithdrawCollateral (input : Ptr) : SolanaM Unit := do
  let (dex, pfl, owner, destTok, mint, vaultPda, tokProg, ix, progId) ← parseStrict7 input PErr.aliasedAccounts
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner owner; requireWritable dex; requireWritable pfl
  checkOwnedMagic dex progId DexOff.size MAGIC_DEX
  checkOwnedMagic pfl progId PflOff.size MAGIC_PORTFOLIO
  let dData := AccountView.dataPtr dex
  let fData := AccountView.dataPtr pfl
  requireKeyEq (AccountView.keyPtr dex)   (fData + PflOff.dex)   PErr.dexMismatch
  requireKeyEq (AccountView.keyPtr owner) (fData + PflOff.owner) PErr.ownerMismatch
  checkDexVaultAndMint dData mint vaultPda tokProg
  requireKeyNe (AccountView.keyPtr destTok) (AccountView.keyPtr vaultPda) PErr.aliasedAccounts

  let amount ← loadU64 ix.ptr 1
  SolanaM.require (amount > 0) PErr.invalidParams

  -- Same-slot freshness & per-leg lockedMm integrity: every active open leg must have been
  -- refreshed in `curSlot` AND hold full `lockedMm >= cachedMm`! Flat portfolios pass unconditionally!
  let curSlot ← getClockSlot
  checkAllLegsFreshLoop fData curSlot 0 true

  let freeCap ← loadU64 fData PflOff.capital
  let remFree ← checkedSub64 freeCap amount PErr.insufficientFunds
  let totCap  ← checkedAdd64 remFree (← loadU64 fData PflOff.totalLockedMm)
  SolanaM.require (totCap >= (← loadU64 fData PflOff.totalIm)) PErr.insufficientMargin

  storeU64 fData PflOff.capital remFree
  subU64At dData DexOff.totalCapital amount
  subU64At dData DexOff.vaultBalance amount
  let dec  ← loadU8 dData DexOff.decimals
  let bump ← loadU8 dData DexOff.vaultBump
  tokenTransferCheckedSigned tokProg vaultPda mint destTok vaultPda amount dec
    TAG_DEX_VAULT (AccountView.keyPtr dex) bump
  log64 EvtTag.withdraw (← loadU64 fData PflOff.portfolioId) amount remFree 0

def handleDepositInsurance (input : Ptr) : SolanaM Unit := do
  let (dex, mkt, receipt, lp, lpTok, mint, vaultPda, tokProg, ix, progId) ← parse8 input
  requireNonDup dex; requireNonDup mkt; requireNonDup lp; requireNonDup lpTok
  requireNonDup mint; requireNonDup vaultPda; requireNonDup tokProg
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner lp; requireWritable dex; requireWritable mkt
  checkOwnedMagic dex progId DexOff.size MAGIC_DEX
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  let dData := AccountView.dataPtr dex
  let mData := AccountView.dataPtr mkt
  requireKeyEq (AccountView.keyPtr dex) (mData + MktOff.dex) PErr.dexMismatch
  checkDexVaultAndMint dData mint vaultPda tokProg
  requireKeyNe (AccountView.keyPtr lpTok) (AccountView.keyPtr vaultPda) PErr.aliasedAccounts

  let st ← loadU8 mData MktOff.status
  SolanaM.require (st == STATUS_ACTIVE || st == STATUS_WINDDOWN) PErr.invalidStatus
  let amount ← loadU64 ix.ptr 1
  SolanaM.require (amount > 0) PErr.invalidParams
  let donate ← if ix.len >= 10 then loadU8 ix.ptr 9 else pure 0

  let dec ← loadU8 dData DexOff.decimals
  if donate != 0 then
    -- Permissionless permanent insurance donation (0 LP shares minted!)
    tokenTransferChecked tokProg lpTok mint vaultPda lp amount dec
    addU64At dData DexOff.vaultBalance   amount
    addU64At dData DexOff.totalInsurance amount
    addU64At mData MktOff.insurance      amount
  else
    requireNonDup receipt
    requireWritable receipt
    requireKeyEq (AccountView.ownerPtr receipt) progId Err.illegalOwner
    SolanaM.require ((← AccountView.dataLen receipt) == InsOff.size) Err.invalidAccountData
    let rData := AccountView.dataPtr receipt
    let mid ← loadU64 mData MktOff.marketId
    if (← loadU32 rData InsOff.magic) == 0 then
      zeroWordsLoop rData 0 (InsOff.size >>> 3)
      storeU32 rData InsOff.magic MAGIC_INSURANCE
      storeU64 rData InsOff.marketId mid
      pubkeyCopy (rData + InsOff.owner)  (AccountView.keyPtr lp)
      pubkeyCopy (rData + InsOff.market) (AccountView.keyPtr mkt)
    else
      SolanaM.require ((← loadU32 rData InsOff.magic) == MAGIC_INSURANCE) PErr.invalidMagic
      requireKeyEq (AccountView.keyPtr lp)  (rData + InsOff.owner)  PErr.ownerMismatch
      requireKeyEq (AccountView.keyPtr mkt) (rData + InsOff.market) PErr.marketMismatch
      SolanaM.require ((← loadU64 rData InsOff.marketId) == mid) PErr.marketMismatch

    let totSh   ← loadU64 mData MktOff.totalInsShares
    let ins     ← loadU64 mData MktOff.insurance
    let fronted ← loadU64 mData MktOff.insFronted
    let nav     ← checkedAdd64 ins fronted
    -- Share-pool pricing hardening (with optimistic NAV `I_m + insFronted`!):
    -- 1. If `totSh == 0`, enforce `amount >= MIN_FIRST_INS_DEPOSIT` (blocks 1-atom ERC-4626 inflation!)
    --    and if pre-existing unowned NAV exists (`nav > 0`), lock it behind `nav` unowned dead shares
    --    so the first LP depositor captures 0 donated/fronted funds AND 1-atom donations cannot DoS LPs!
    -- 2. If `totSh > 0`, price shares against `nav = ins + insFronted` (blocking receivable arbitrage
    --    when `I_m` has temporarily fronted USD to winners awaiting loser repayment!) and reject
    --    depositing into a completely wiped-out pool (`nav == 0`).
    let minted ←
      if totSh == 0 then do
        SolanaM.require (amount >= MIN_FIRST_INS_DEPOSIT) PErr.invalidParams
        pure amount
      else do
        SolanaM.require (nav > 0) PErr.nonzeroState
        mulDiv64 amount totSh nav
    SolanaM.require (minted > 0) PErr.invalidParams

    tokenTransferChecked tokProg lpTok mint vaultPda lp amount dec

    addU64At dData DexOff.vaultBalance   amount
    addU64At dData DexOff.totalInsurance amount
    addU64At mData MktOff.insurance      amount
    if totSh == 0 && nav > 0 then
      addU64At mData MktOff.totalInsShares nav
    addU64At mData MktOff.totalInsShares minted
    addU64At rData InsOff.shares         minted

def handleWithdrawInsurance (input : Ptr) : SolanaM Unit := do
  let (dex, mkt, receipt, lp, destTok, mint, vaultPda, tokProg, ix, progId) ← parseStrict8 input PErr.aliasedAccounts
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner lp; requireWritable dex; requireWritable mkt; requireWritable receipt
  checkOwnedMagic dex     progId DexOff.size MAGIC_DEX
  checkOwnedMagic mkt     progId MktOff.size MAGIC_MARKET
  checkOwnedMagic receipt progId InsOff.size MAGIC_INSURANCE
  let dData := AccountView.dataPtr dex
  let mData := AccountView.dataPtr mkt
  let rData := AccountView.dataPtr receipt
  requireKeyEq (AccountView.keyPtr dex) (mData + MktOff.dex)    PErr.dexMismatch
  requireKeyEq (AccountView.keyPtr lp)  (rData + InsOff.owner)  PErr.ownerMismatch
  requireKeyEq (AccountView.keyPtr mkt) (rData + InsOff.market) PErr.marketMismatch
  SolanaM.require ((← loadU64 rData InsOff.marketId) == (← loadU64 mData MktOff.marketId)) PErr.marketMismatch
  checkDexVaultAndMint dData mint vaultPda tokProg
  requireKeyNe (AccountView.keyPtr destTok) (AccountView.keyPtr vaultPda) PErr.aliasedAccounts

  let ins ← loadU64 mData MktOff.insurance
  -- Allow burning worthless shares (`ins == 0`) even on `STATUS_TOMBSTONED` so `InsReceipt` rent
  -- can NEVER be permanently trapped by a permissionless `TombstoneMarket` call!
  SolanaM.require ((← loadU8 mData MktOff.status) != STATUS_TOMBSTONED || ins == 0) PErr.invalidStatus
  -- Insurance CANNOT be withdrawn while ANY OI or post-ADL rawBasis exists on this market!
  SolanaM.require ((← loadU64 mData MktOff.oiLong) == 0 && (← loadU64 mData MktOff.oiShort) == 0 &&
                   (← loadU64 mData MktOff.rawBasisLong) == 0 && (← loadU64 mData MktOff.rawBasisShort) == 0) PErr.nonzeroOi

  let burnShares ← loadU64 ix.ptr 1
  SolanaM.require (burnShares > 0) PErr.invalidParams
  let curSh ← loadU64 rData InsOff.shares
  let totSh ← loadU64 mData MktOff.totalInsShares
  SolanaM.require (curSh <= totSh) PErr.nonzeroState
  SolanaM.require (curSh >= burnShares) PErr.insufficientFunds
  let payout ← mulDiv64 burnShares ins totSh

  storeU64 rData InsOff.shares (curSh - burnShares)
  subU64At mData MktOff.totalInsShares burnShares
  if payout > 0 then
    subU64At mData MktOff.insurance      payout
    subU64At dData DexOff.totalInsurance payout
    subU64At dData DexOff.vaultBalance   payout
    let dec  ← loadU8 dData DexOff.decimals
    let bump ← loadU8 dData DexOff.vaultBump
    tokenTransferCheckedSigned tokProg vaultPda mint destTok vaultPda payout dec
      TAG_DEX_VAULT (AccountView.keyPtr dex) bump

def handleRefreshLeg (input : Ptr) : SolanaM Unit := do
  let (n, dex, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 3) Err.notEnoughAccountKeys
  let mkt ← AccountView.nextCursor dex
  let pfl ← AccountView.nextCursor mkt
  requireNonDup dex; requireNonDup mkt; requireNonDup pfl
  requireWritable dex; requireWritable mkt; requireWritable pfl
  checkOwnedMagic dex progId DexOff.size MAGIC_DEX
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  checkOwnedMagic pfl progId PflOff.size MAGIC_PORTFOLIO
  let dData := AccountView.dataPtr dex
  let mData := AccountView.dataPtr mkt
  let fData := AccountView.dataPtr pfl
  requireKeyEq (AccountView.keyPtr dex) (mData + MktOff.dex) PErr.dexMismatch
  requireKeyEq (AccountView.keyPtr dex) (fData + PflOff.dex) PErr.dexMismatch

  let st ← loadU8 mData MktOff.status
  SolanaM.require (st == STATUS_ACTIVE || st == STATUS_WINDDOWN) PErr.invalidStatus
  let curSlot ← getClockSlot
  -- NOTE: Do NOT call `checkOracleFresh` in `handleRefreshLeg`!
  -- A stale/abandoned market has frozen `markPrice` (`dK = 0`), so refreshing it settles 0 new PnL
  -- while keeping its full `cachedMm`/`cachedIm` locked — preventing an adversarial permissionless
  -- market from stalling its oracle to DoS-freeze `Liquidate` or `Withdraw` on other legs!

  let mid ← loadU64 mData MktOff.marketId
  let slotIdx ← findLegLoop fData mid 0
  SolanaM.require (slotIdx < MAX_LEGS) PErr.legNotFound
  requireKeyEq (AccountView.keyPtr mkt) (legPtrAt fData slotIdx + LegOff.market) PErr.marketMismatch

  -- Opt-in `forceHaircut = true` MUST be signed by `pfl.owner` (4th account) AND only applies to
  -- closed/dead legs (`rawBasis == 0`), so neither a third party nor a malicious portfolio owner can
  -- wipe unbacked `posPnl` on an open leg to intentionally under-collateralize it below `MM`!
  let forceHaircut ← if ix.len >= 2 then do pure ((← loadU8 ix.ptr 1) != 0) else pure false
  if forceHaircut then
    SolanaM.require (n >= 4) Err.notEnoughAccountKeys
    let owner ← AccountView.nextCursor pfl
    requireNonDup owner
    requireSigner owner
    requireKeyEq (AccountView.keyPtr owner) (fData + PflOff.owner) PErr.ownerMismatch
    SolanaM.require ((← loadU64 (legPtrAt fData slotIdx) LegOff.rawBasis) == 0) PErr.nonzeroState
  let _ ← settleAndRefreshLeg dData mData fData slotIdx curSlot forceHaircut false
  freeLegIfEmpty fData slotIdx

/-- Apply optional `execPrice` spread transfer directly between Long & Short `capital`.
    Preserves `C_tot` identically and allows external CLOB/AMM/matcher CPIs with real spreads!
    - `clampSpread = true` (`mode = 0`, `mode = 2/3`, or `limitPrice == 0` matcher closes):
      enforces `|execPrice - markP| <= maxMoveBps` (blocks margin-stripping & unbounded matcher fills).
    - `clampSpread = false` (bilateral signed `mode = 1` closes & limit-guarded `TradeWithMatcher` closes):
      allows users to reprice and exit OI immediately at the real price during oracle catch-up ramps! -/
def applyExecSpread (mData fLData fSData : Ptr) (qty execPrice : UInt64)
    (clampSpread : Bool := true) : SolanaM Unit := do
  if execPrice == 0 then return ()
  let markP ← loadU64 mData MktOff.markPrice
  if execPrice == markP then return ()
  let diff := if execPrice > markP then execPrice - markP else markP - execPrice
  if clampSpread then
    let maxSlip ← mulDiv64 markP (← loadU64 mData MktOff.maxMoveBps) BPS_DEN
    SolanaM.require (diff <= maxSlip) PErr.execPriceClamp
  let spread ← mulDiv64Ceil qty diff POS_SCALE
  if spread > 0 then
    if execPrice > markP then
      let cL ← loadU64 fLData PflOff.capital
      SolanaM.require (cL >= spread) PErr.insufficientFunds
      storeU64 fLData PflOff.capital (cL - spread)
      addU64At fSData PflOff.capital spread
    else
      let cS ← loadU64 fSData PflOff.capital
      SolanaM.require (cS >= spread) PErr.insufficientFunds
      storeU64 fSData PflOff.capital (cS - spread)
      addU64At fLData PflOff.capital spread

/-- Route `totalFee` (already debited from `totalCapital`) into `m.insurance` + `m.rewardAccrued`
    according to immutable `m.rewardBps` (shared identically by `mode = 0` and `mode = 2/3`!). -/
def creditTradeFee (dData mData : Ptr) (totalFee : UInt64) : SolanaM Unit := do
  subU64At dData DexOff.totalCapital totalFee
  let rewBps ← loadU64 mData MktOff.rewardBps
  let rewFee ← if rewBps == 0 then pure 0 else mulDiv64 totalFee rewBps BPS_DEN
  let insFee := totalFee - rewFee
  if insFee > 0 then
    addU64At mData MktOff.insurance      insFee
    addU64At dData DexOff.totalInsurance insFee
  if rewFee > 0 then
    addU64At mData MktOff.rewardAccrued  rewFee
    addU64At dData DexOff.totalRewards   rewFee

/-- Shared core bilateral trade execution (used identically by `Trade` and CPI-Out `TradeWithMatcher`).
    Takes 5 pointer args (`argsPtr` = `[mktKeyPtr:u64, mode:u64, qty:u64, execPrice:u64]`) so both
    paths share 100% identical conservation, `maxMoveBps` spread clamping, fee splitting, and margin checks. -/
@[noinline] def tradeCore (dData mData fLData fSData argsPtr : Ptr) : SolanaM Unit := do
  let mktKeyPtr      ← loadU64 argsPtr 0
  let mode           ← loadU8  argsPtr 8
  let allowWideClose ← loadU8  argsPtr 9
  let qty            ← loadU64 argsPtr 16
  let execPrice      ← loadU64 argsPtr 24
  SolanaM.require (qty > 0) PErr.invalidParams

  let st ← loadU8 mData MktOff.status
  let curSlot ← getClockSlot
  let mid ← loadU64 mData MktOff.marketId

  if mode == 0 then
    -- Open / Increase bilateral trade (supports post-ADL recovery when `oiSide > 0`!)
    SolanaM.require (st == STATUS_ACTIVE) PErr.invalidStatus
    checkOracleFresh mData curSlot

    let slotL ← findOrAllocLegSlot fLData mktKeyPtr mid
    let slotS ← findOrAllocLegSlot fSData mktKeyPtr mid
    let lpL := legPtrAt fLData slotL
    let lpS := legPtrAt fSData slotS
    let sL ← loadU8 lpL LegOff.side
    let sS ← loadU8 lpS LegOff.side
    SolanaM.require (sL == SIDE_FLAT || sL == SIDE_LONG)  PErr.invalidSide
    SolanaM.require (sS == SIDE_FLAT || sS == SIDE_SHORT) PErr.invalidSide

    let _ ← settleAndRefreshLeg dData mData fLData slotL curSlot false false
    let _ ← settleAndRefreshLeg dData mData fSData slotS curSlot false false
    applyExecSpread mData fLData fSData qty execPrice

    let oiL ← loadU64 mData MktOff.oiLong
    let oiS ← loadU64 mData MktOff.oiShort
    let rL  ← loadU64 mData MktOff.rawBasisLong
    let rS  ← loadU64 mData MktOff.rawBasisShort
    let maxOi ← loadU64 mData MktOff.maxOi
    let oiL' ← checkedAdd64 oiL qty
    let oiS' ← checkedAdd64 oiS qty
    SolanaM.require (oiL' <= maxOi && oiS' <= maxOi) PErr.oiLimitExceeded

    let rawAddL ← postAdlRawAddU64 qty oiL rL
    let rawAddS ← postAdlRawAddU64 qty oiS rS
    let rL' ← checkedAdd64 rL rawAddL
    let rS' ← checkedAdd64 rS rawAddS
    SolanaM.require (rL' <= MAX_RAW && rS' <= MAX_RAW && oiL' <= rL' && oiS' <= rS') PErr.oiLimitExceeded

    let markP ← loadU64 mData MktOff.markPrice
    let fee ← computeMarginReq qty markP (← loadU64 mData MktOff.tradeFeeBps)
    if fee > 0 then
      let cL ← loadU64 fLData PflOff.capital
      let cS ← loadU64 fSData PflOff.capital
      SolanaM.require (cL >= fee && cS >= fee) PErr.insufficientFunds
      storeU64 fLData PflOff.capital (cL - fee)
      storeU64 fSData PflOff.capital (cS - fee)
      creditTradeFee dData mData (← checkedAdd64 fee fee)

    if sL == SIDE_FLAT then
      storeU8  lpL LegOff.side SIDE_LONG
      storeU64 lpL LegOff.entryK (← loadU64 mData MktOff.kLong)
      addU64At mData MktOff.activeLegs 1
    if sS == SIDE_FLAT then
      storeU8  lpS LegOff.side SIDE_SHORT
      storeU64 lpS LegOff.entryK (← loadU64 mData MktOff.kShort)
      addU64At mData MktOff.activeLegs 1

    addU64At lpL LegOff.rawBasis rawAddL
    addU64At lpS LegOff.rawBasis rawAddS
    storeU64 mData MktOff.oiLong oiL'
    storeU64 mData MktOff.oiShort oiS'
    storeU64 mData MktOff.rawBasisLong  rL'
    storeU64 mData MktOff.rawBasisShort rS'
    storeU64 mData MktOff.adlLong  (← deriveAdlU64 oiL' rL')
    storeU64 mData MktOff.adlShort (← deriveAdlU64 oiS' rS')

    syncLegMargins mData fLData slotL curSlot
    syncLegMargins mData fSData slotS curSlot

    -- Enforce same-slot freshness, full per-leg `lockedMm >= cachedMm`, and `totalCap >= totalIm`!
    requirePortfolioIm fLData curSlot
    requirePortfolioIm fSData curSlot
  else if mode == 1 then
    -- Mode 1: Bilateral risk-reducing close (works in Active & WindDown, post-ADL proportional,
    -- AND even if the oracle is stale! Pure OI reduction never creates new risk, so consenting
    -- Long & Short can always voluntarily trade out at the real price without killing the market!)
    SolanaM.require (st == STATUS_ACTIVE || st == STATUS_WINDDOWN) PErr.invalidStatus

    let slotL ← findLegLoop fLData mid 0
    let slotS ← findLegLoop fSData mid 0
    SolanaM.require (slotL < MAX_LEGS && slotS < MAX_LEGS) PErr.legNotFound
    let lpL := legPtrAt fLData slotL
    let lpS := legPtrAt fSData slotS
    requireKeyEq mktKeyPtr (lpL + LegOff.market) PErr.marketMismatch
    requireKeyEq mktKeyPtr (lpS + LegOff.market) PErr.marketMismatch
    SolanaM.require ((← loadU8 lpL LegOff.side) == SIDE_LONG && (← loadU8 lpS LegOff.side) == SIDE_SHORT) PErr.invalidSide

    let _ ← settleAndRefreshLeg dData mData fLData slotL curSlot false false
    let _ ← settleAndRefreshLeg dData mData fSData slotS curSlot false false

    let oiL ← loadU64 mData MktOff.oiLong
    let oiS ← loadU64 mData MktOff.oiShort
    let rLegL ← loadU64 lpL LegOff.rawBasis
    let rLegS ← loadU64 lpS LegOff.rawBasis
    let rMktL ← loadU64 mData MktOff.rawBasisLong
    let rMktS ← loadU64 mData MktOff.rawBasisShort
    SolanaM.require (qty <= oiL && qty <= oiS && rLegL > 0 && rLegS > 0 && rMktL > 0 && rMktS > 0) PErr.invalidParams
    let capL ←
      if oiL == rMktL then pure (if rLegL < oiL then rLegL else oiL)
      else do let q ← mulDiv64Ceil rLegL oiL rMktL; pure (if q < oiL then q else oiL)
    let capS ←
      if oiS == rMktS then pure (if rLegS < oiS then rLegS else oiS)
      else do let q ← mulDiv64Ceil rLegS oiS rMktS; pure (if q < oiS then q else oiS)
    SolanaM.require (qty <= capL && qty <= capS) PErr.invalidParams

    let redL ← proportionalRawRedU64 qty rLegL rMktL oiL
    let redS ← proportionalRawRedU64 qty rLegS rMktS oiS
    SolanaM.require (redL > 0 && redS > 0 && rLegL >= redL && rLegS >= redS &&
                     rMktL >= redL && rMktS >= redS) PErr.invalidParams

    let oiL' := oiL - qty
    let oiS' := oiS - qty
    let rMktL' := rMktL - redL
    let rMktS' := rMktS - redS
    SolanaM.require (oiL' <= rMktL' && oiS' <= rMktS') PErr.invalidParams

    storeU64 mData MktOff.oiLong oiL'
    storeU64 mData MktOff.oiShort oiS'
    storeU64 mData MktOff.rawBasisLong rMktL'
    storeU64 mData MktOff.rawBasisShort rMktS'
    storeU64 mData MktOff.adlLong  (← deriveAdlU64 oiL' rMktL')
    storeU64 mData MktOff.adlShort (← deriveAdlU64 oiS' rMktS')

    let rLegL' := rLegL - redL
    let rLegS' := rLegS - redS
    storeU64 lpL LegOff.rawBasis rLegL'
    storeU64 lpS LegOff.rawBasis rLegS'
    if rLegL' == 0 then
      storeU8 lpL LegOff.side SIDE_FLAT
      subU64At mData MktOff.activeLegs 1
    if rLegS' == 0 then
      storeU8 lpS LegOff.side SIDE_FLAT
      subU64At mData MktOff.activeLegs 1

    -- Release freed `lockedMm` back to `freeCapital` FIRST, THEN apply spread strictly from `freeCapital`
    -- (so spread payment on `mode = 1` NEVER touches any other leg's `lockedMm` firewall!).
    syncLegMargins mData fLData slotL curSlot
    syncLegMargins mData fSData slotS curSlot
    -- Mode 1 reduce: `fL` is SELLING to close its Long and `fS` is BUYING to close its Short!
    --   * Ask (`execPrice > markP`): buyer `fS` pays spread to seller `fL`
    --   * Bid (`execPrice < markP`): seller `fL` pays spread to buyer `fS`
    -- Unclamped when `allowWideClose != 0` (bilateral signed `Trade` or explicit `limitPrice > 0`
    -- matcher close): lets users trade out OI immediately at the real price during outage ramps!
    applyExecSpread mData fSData fLData qty execPrice (allowWideClose == 0)
    let markP ← loadU64 mData MktOff.markPrice
    if execPrice != 0 && execPrice != markP then
      if execPrice > markP then
        checkAllLegsFreshLoop fSData curSlot 0 true
      else
        checkAllLegsFreshLoop fLData curSlot 0 true
    freeLegIfEmpty fLData slotL
    freeLegIfEmpty fSData slotS
  else if mode == 2 || mode == 3 then
    -- Mode 2 (Long→Long) / Mode 3 (Short→Short): Position Hand-Off (`pflL` seller → `pflS` buyer).
    -- Leaves `oiLong`, `oiShort`, `rawBasisLong`, `rawBasisShort`, `adlLong`, `adlShort` BIT-FOR-BIT INVARIANT!
    -- Charges buyer `tradeFeeBps` (closing zero-fee hand-off bypass while keeping seller close 0-fee!).
    SolanaM.require (st == STATUS_ACTIVE || st == STATUS_WINDDOWN) PErr.invalidStatus
    if st == STATUS_ACTIVE then checkOracleFresh mData curSlot
    let targetSide := if mode == 2 then SIDE_LONG else SIDE_SHORT
    let oiSide ← loadU64 mData (if mode == 2 then MktOff.oiLong else MktOff.oiShort)
    let rMktSide ← loadU64 mData (if mode == 2 then MktOff.rawBasisLong else MktOff.rawBasisShort)
    SolanaM.require (oiSide > 0 && qty <= oiSide) PErr.invalidParams

    let slotSell ← findLegLoop fLData mid 0
    SolanaM.require (slotSell < MAX_LEGS) PErr.legNotFound
    let lpSell := legPtrAt fLData slotSell
    requireKeyEq mktKeyPtr (lpSell + LegOff.market) PErr.marketMismatch
    SolanaM.require ((← loadU8 lpSell LegOff.side) == targetSide) PErr.invalidSide

    let slotBuy ← findOrAllocLegSlot fSData mktKeyPtr mid
    let lpBuy := legPtrAt fSData slotBuy
    let sBuy ← loadU8 lpBuy LegOff.side
    SolanaM.require (sBuy == SIDE_FLAT || sBuy == targetSide) PErr.invalidSide

    let _ ← settleAndRefreshLeg dData mData fLData slotSell curSlot false false
    let _ ← settleAndRefreshLeg dData mData fSData slotBuy  curSlot false false

    let rSell ← loadU64 lpSell LegOff.rawBasis
    let rawXfer ← proportionalRawRedU64 qty rSell rMktSide oiSide
    SolanaM.require (rawXfer > 0 && rSell >= rawXfer) PErr.invalidParams

    -- Reduce seller & release freed `lockedMm` to seller's `freeCapital` BEFORE spread transfer!
    let rSell' := rSell - rawXfer
    storeU64 lpSell LegOff.rawBasis rSell'
    if rSell' == 0 then
      storeU8 lpSell LegOff.side SIDE_FLAT
      subU64At mData MktOff.activeLegs 1
    syncLegMargins mData fLData slotSell curSlot

    if mode == 2 then
      applyExecSpread mData fSData fLData qty execPrice
    else
      applyExecSpread mData fLData fSData qty execPrice

    -- Charge opening buyer (`fSData`) `tradeFeeBps` from `freeCapital` (closes zero-fee hand-off bypass!).
    let markP ← loadU64 mData MktOff.markPrice
    let fee ← computeMarginReq qty markP (← loadU64 mData MktOff.tradeFeeBps)
    if fee > 0 then
      let cBuy ← loadU64 fSData PflOff.capital
      SolanaM.require (cBuy >= fee) PErr.insufficientFunds
      storeU64 fSData PflOff.capital (cBuy - fee)
      creditTradeFee dData mData fee

    if sBuy == SIDE_FLAT then
      storeU8  lpBuy LegOff.side targetSide
      storeU64 lpBuy LegOff.entryK (← loadU64 mData (if mode == 2 then MktOff.kLong else MktOff.kShort))
      addU64At mData MktOff.activeLegs 1
    addU64At lpBuy LegOff.rawBasis rawXfer
    syncLegMargins mData fSData slotBuy curSlot

    -- Buyer MUST satisfy full fresh/locked IM!
    requirePortfolioIm fSData curSlot
    -- If seller paid an `execPrice` spread, all seller remaining open legs MUST be fresh & fully locked!
    if execPrice != 0 && execPrice != markP then
      let sellerPaid := (mode == 2 && execPrice < markP) || (mode == 3 && execPrice > markP)
      if sellerPaid then
        checkAllLegsFreshLoop fLData curSlot 0 true
    freeLegIfEmpty fLData slotSell
  else
    SolanaM.fail PErr.invalidParams
  log64 EvtTag.trade ((mid <<< 8) ||| mode.toUInt64) qty execPrice (← loadU64 mData MktOff.markPrice)

/-- Exact effective close-out quantity for `pflData`'s leg on `mid` if it holds `targetSide`:
    returns `0` if flat/absent/opposite side, else `min oiSide (ceil(rLeg * oiSide / rawSide))`
    so closing `closeCap` zeroes `rawBasis` completely even under arbitrary post-ADL ratios! -/
def legCloseCapU64 (mData pflData : Ptr) (mid : UInt64) (targetSide : UInt8) : SolanaM UInt64 := do
  let slot ← findLegLoop pflData mid 0
  if slot >= MAX_LEGS then return 0
  let lp := legPtrAt pflData slot
  if (← loadU8 lp LegOff.side) != targetSide then return 0
  let rLeg ← loadU64 lp LegOff.rawBasis
  if rLeg == 0 then return 0
  let oiSide  ← loadU64 mData (if targetSide == SIDE_LONG then MktOff.oiLong else MktOff.oiShort)
  let rawSide ← loadU64 mData (if targetSide == SIDE_LONG then MktOff.rawBasisLong else MktOff.rawBasisShort)
  if oiSide == 0 || rawSide == 0 then return 0
  if oiSide == rawSide then return (if rLeg < oiSide then rLeg else oiSide)
  let q ← mulDiv64Ceil rLeg oiSide rawSide
  return (if q < oiSide then q else oiSide)

/-- Mode 4 (`Trade` & `TradeWithMatcher`): Atomic Auto-Netted Buy/Sell + Position Flip!
    `fBuyer` buys `qty` from `fSeller` at `execPrice` regardless of either side's existing position
    (supports Open, Partial/Full Reduce against ANY counterparty, AND Long↔Short Atomic Flip!):
      1. `cBoth = min(qty, min(closeB, closeS))` -> `tradeCore(mode=1, fSeller, fBuyer, cBoth)`
      2. Remaining opposite leg on either side -> `tradeCore(mode=2/3, ...)` (OI-invariant hand-off!)
      3. Any remaining net quantity -> `tradeCore(mode=0, fBuyer, fSeller, rem2)` (fresh OI!)
    Every sub-step invokes the exact same verified `tradeCore` with identical spread direction
    (`applyExecSpread mData fBuyer fSeller`), preserving 5-bucket conservation `C+I+R+S+F=V`,
    per-market isolation, WindDown safety, and cross-margin IM/MM bounds! -/
@[noinline] def tradeNettedCore (dData mData fBuyer fSeller argsPtr : Ptr) : SolanaM Unit := do
  let mktKeyPtr      ← loadU64 argsPtr 0
  let allowWideClose ← loadU8  argsPtr 9
  let qty            ← loadU64 argsPtr 16
  let execPrice      ← loadU64 argsPtr 24
  SolanaM.require (qty > 0) PErr.invalidParams
  let mid ← loadU64 mData MktOff.marketId
  let closeB ← legCloseCapU64 mData fBuyer  mid SIDE_SHORT
  let closeS ← legCloseCapU64 mData fSeller mid SIDE_LONG
  let minCS  := if closeB < closeS then closeB else closeS
  let cBoth  := if qty < minCS then qty else minCS
  let subArgs ← stackAlloc 32
  storeU64 subArgs 0  mktKeyPtr
  storeU64 subArgs 24 execPrice
  if cBoth > 0 then
    storeU64 subArgs 8  1
    storeU8  subArgs 9  allowWideClose
    storeU64 subArgs 16 cBoth
    tradeCore dData mData fSeller fBuyer subArgs
  let rem1 := qty - cBoth
  let mut rem2 := rem1
  if rem1 > 0 then
    let remS ← legCloseCapU64 mData fSeller mid SIDE_LONG
    let remB ← legCloseCapU64 mData fBuyer  mid SIDE_SHORT
    if remS > 0 then
      let cHo := if rem1 < remS then rem1 else remS
      storeU64 subArgs 8  2
      storeU64 subArgs 16 cHo
      tradeCore dData mData fSeller fBuyer subArgs
      rem2 := rem1 - cHo
    else if remB > 0 then
      let cHo := if rem1 < remB then rem1 else remB
      storeU64 subArgs 8  3
      storeU64 subArgs 16 cHo
      tradeCore dData mData fBuyer fSeller subArgs
      rem2 := rem1 - cHo
  if rem2 > 0 then
    storeU64 subArgs 8  0
    storeU64 subArgs 16 rem2
    tradeCore dData mData fBuyer fSeller subArgs

def handleTrade (input : Ptr) : SolanaM Unit := do
  let (dex, mkt, pflL, ownerL, pflS, ownerSRaw, ix, progId) ← parse6 input
  requireNonDup dex; requireNonDup mkt; requireNonDup pflL; requireNonDup ownerL; requireNonDup pflS
  let ownerS ← AccountView.resolveDup ownerSRaw 3 ownerL PErr.aliasedAccounts
  SolanaM.require (ix.len >= 10) Err.invalidInstructionData
  requireSigner ownerL; requireSigner ownerS
  requireWritable dex; requireWritable mkt; requireWritable pflL; requireWritable pflS
  requireKeyNe (AccountView.keyPtr pflL) (AccountView.keyPtr pflS) PErr.aliasedAccounts
  checkOwnedMagic dex  progId DexOff.size MAGIC_DEX
  checkOwnedMagic mkt  progId MktOff.size MAGIC_MARKET
  checkOwnedMagic pflL progId PflOff.size MAGIC_PORTFOLIO
  checkOwnedMagic pflS progId PflOff.size MAGIC_PORTFOLIO

  let dData  := AccountView.dataPtr dex
  let mData  := AccountView.dataPtr mkt
  let fLData := AccountView.dataPtr pflL
  let fSData := AccountView.dataPtr pflS
  requireKeyEq (AccountView.keyPtr dex)    (mData  + MktOff.dex)   PErr.dexMismatch
  requireKeyEq (AccountView.keyPtr dex)    (fLData + PflOff.dex)   PErr.dexMismatch
  requireKeyEq (AccountView.keyPtr dex)    (fSData + PflOff.dex)   PErr.dexMismatch
  requireKeyEq (AccountView.keyPtr ownerL) (fLData + PflOff.owner) PErr.ownerMismatch
  requireKeyEq (AccountView.keyPtr ownerS) (fSData + PflOff.owner) PErr.ownerMismatch

  let mode      ← loadU8  ix.ptr 1
  let qty       ← loadU64 ix.ptr 2
  let execPrice ← if ix.len >= 18 then loadU64 ix.ptr 10 else pure 0
  SolanaM.require (execPrice <= MAX_PRICE) PErr.invalidParams
  let args ← stackAlloc 32
  storeU64 args 0  (AccountView.keyPtr mkt)
  storeU64 args 8  mode.toUInt64
  storeU8  args 9  1
  storeU64 args 16 qty
  storeU64 args 24 execPrice
  if mode == 4 then
    tradeNettedCore dData mData fLData fSData args
  else
    tradeCore dData mData fLData fSData args

/-- Fair, transparent $O(1)$ liquidation supporting:
    - Partial OR full liquidation (`reqQty = 0` → full leg; `reqQty > 0` → partial `min(reqQty, rawB)`),
    - Gradual deficit-scaled liquidation fee (`min(maxFee, max(maxFee/4, deficit))`, strictly above `otherMm`),
    - `mode = 1`: Transparent HLP/counterparty position takeover (9 accs, **ZERO ADL!**),
    - `mode = 0`: Proportional OI-reduction + capped `I_m` draw + derived ADL fallback (7 accs). -/
def handleLiquidate (input : Ptr) : SolanaM Unit := do
  let (n, dex, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 7) Err.notEnoughAccountKeys
  let mkt      ← AccountView.nextCursor dex
  let pfl      ← AccountView.nextCursor mkt
  let liqTok   ← AccountView.nextCursor pfl
  let mint     ← AccountView.nextCursor liqTok
  let vaultPda ← AccountView.nextCursor mint
  let tokProg  ← AccountView.nextCursor vaultPda
  requireNonDup dex; requireNonDup mkt; requireNonDup pfl; requireNonDup liqTok
  requireNonDup mint; requireNonDup vaultPda; requireNonDup tokProg

  let mode   ← loadOptU8  ix.ptr ix.len 1
  let reqQty ← loadOptU64 ix.ptr ix.len 2

  requireWritable dex; requireWritable mkt; requireWritable pfl
  checkOwnedMagic dex progId DexOff.size MAGIC_DEX
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  checkOwnedMagic pfl progId PflOff.size MAGIC_PORTFOLIO
  let dData := AccountView.dataPtr dex
  let mData := AccountView.dataPtr mkt
  let fData := AccountView.dataPtr pfl
  requireKeyEq (AccountView.keyPtr dex) (mData + MktOff.dex) PErr.dexMismatch
  requireKeyEq (AccountView.keyPtr dex) (fData + PflOff.dex) PErr.dexMismatch
  checkDexVaultAndMint dData mint vaultPda tokProg
  requireKeyNe (AccountView.keyPtr liqTok) (AccountView.keyPtr vaultPda) PErr.aliasedAccounts

  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_ACTIVE) PErr.invalidStatus
  let curSlot ← getClockSlot
  checkOracleFresh mData curSlot

  let mid ← loadU64 mData MktOff.marketId
  let slotIdx ← findLegLoop fData mid 0
  SolanaM.require (slotIdx < MAX_LEGS) PErr.legNotFound
  let lp := legPtrAt fData slotIdx
  requireKeyEq (AccountView.keyPtr mkt) (lp + LegOff.market) PErr.marketMismatch
  let side ← loadU8 lp LegOff.side
  let rawB ← loadU64 lp LegOff.rawBasis
  SolanaM.require (side != SIDE_FLAT && rawB > 0) PErr.invalidSide

  let shortfall ← settleAndRefreshLeg dData mData fData slotIdx curSlot false
  let freeCap ← loadU64 fData PflOff.capital
  let legLock ← loadU64 lp LegOff.lockedMm
  let legMm   ← loadU64 lp LegOff.cachedMm
  let posPnl  ← loadU64 lp LegOff.posPnl
  -- Bug 1C: if bankrupt (`shortfall > 0 || (freeCap == 0 && legLock == 0)`), ALWAYS force full leg close!
  let rawClose := if shortfall > 0 || (freeCap == 0 && legLock == 0) || reqQty == 0 || reqQty >= rawB then rawB else reqQty
  let remRaw   := rawB - rawClose
  -- A1 Fix: require ALL open legs on victim to be refreshed in `curSlot` BEFORE evaluating
  -- per-leg solvency on solvent portfolios, preventing selective liquidation of a hedged spread;
  -- skip ONLY when this leg is already bankrupt (`shortfall > 0 || (freeCap == 0 && legLock == 0)`)
  -- so two bankrupt legs or an overflowing self-made market leg can NEVER deadlock liquidation!
  if shortfall == 0 && (freeCap > 0 || legLock > 0) then
    checkAllLegsFreshLoop fData curSlot 0 false

  let availCap ← checkedAdd64 freeCap legLock
  let eq ← checkedAdd64 availCap posPnl
  SolanaM.require (shortfall > 0 || eq < legMm) PErr.positionHealthy

  -- Fair gradual deficit-scaled liquidation fee strictly bounded by `freeCap + legLock`
  -- (NEVER touches any other leg's `lockedMm` firewall!).
  let markP ← loadU64 mData MktOff.markPrice
  let adlSide ← loadU64 mData (if side == SIDE_LONG then MktOff.adlLong else MktOff.adlShort)
  let closeEff ← mulDiv64 rawClose adlSide ADL_ONE
  let notional ← mulDiv64Ceil closeEff markP POS_SCALE
  let maxFee ← mulDiv64 notional (← loadU64 mData MktOff.liqFeeBps) BPS_DEN
  let deficit := if legMm > eq then legMm - eq else 0
  let feeFloor := maxFee >>> 2
  let targetFee :=
    if shortfall > 0 then maxFee
    else
      let g := if deficit > feeFloor then deficit else feeFloor
      if g < maxFee then g else maxFee
  let liqFee := if targetFee < availCap then targetFee else availCap

  -- Fix #107: Enforce post-fee solvency & exact `minMm` floor on ANY partial liquidation (`remRaw > 0`):
  -- a partial liquidation must NEVER leave `remRaw > 0` under-margined (`postEq < remMm`) or zero-backed (`postAvail == 0`)!
  if remRaw > 0 then
    let minMm  ← loadU64 mData MktOff.minMm
    let mmBps  ← loadU64 mData MktOff.mmBps
    let remEff ← mulDiv64 remRaw adlSide ADL_ONE
    let remMm  ← computeMarginWithFloor remEff markP mmBps minMm
    let postAvail := availCap - liqFee
    let postEq ← checkedAdd64 postAvail posPnl
    SolanaM.require (remEff > 0 && postAvail > 0 && postEq >= remMm && remMm >= minMm) PErr.invalidParams

  if liqFee > 0 then
    let feeFree := if liqFee < freeCap then liqFee else freeCap
    let feeLock := liqFee - feeFree
    if feeFree > 0 then
      storeU64 fData PflOff.capital (freeCap - feeFree)
    if feeLock > 0 then
      storeU64 lp LegOff.lockedMm (legLock - feeLock)
      subU64At fData PflOff.totalLockedMm feeLock
    subU64At dData DexOff.totalCapital liqFee
    subU64At dData DexOff.vaultBalance liqFee
    let dec  ← loadU8 dData DexOff.decimals
    let bump ← loadU8 dData DexOff.vaultBump
    tokenTransferCheckedSigned tokProg vaultPda mint liqTok vaultPda liqFee dec
      TAG_DEX_VAULT (AccountView.keyPtr dex) bump

  -- Pure ADL on bankruptcy (`0` direct `I_m` bankruptcy draw!):
  -- `I_m` is strictly reserved for async cross-backing (`insFronted`, paused during outage ramps).
  -- Any unrecoverable bankruptcy shortfall goes 100% to exact proportional ADL (`deriveAdlU64`),
  -- making #113 N-pair self-trade insurance extraction provably $0 under any outage!

  if mode == 1 then
    -- Tier 1/2 Transparent HLP / Counterparty Takeover (**ZERO ADL!**)
    SolanaM.require (n >= 9) Err.notEnoughAccountKeys
    let liqPfl   ← AccountView.nextCursor tokProg
    let liqOwner ← AccountView.nextCursor liqPfl
    requireNonDup liqPfl; requireNonDup liqOwner
    requireSigner liqOwner; requireWritable liqPfl
    requireKeyNe (AccountView.keyPtr pfl) (AccountView.keyPtr liqPfl) PErr.aliasedAccounts
    checkOwnedMagic liqPfl progId PflOff.size MAGIC_PORTFOLIO
    let lData := AccountView.dataPtr liqPfl
    requireKeyEq (AccountView.keyPtr dex)      (lData + PflOff.dex)   PErr.dexMismatch
    requireKeyEq (AccountView.keyPtr liqOwner) (lData + PflOff.owner) PErr.ownerMismatch
    -- A2 Fix: Takeover preserves `oiSide`, `rawBasisSide`, and `adlSide` bit-for-bit, so it works
    -- even during active partial ADL! Only reject 100%-wiped-out dead legs (`oiSide == 0`).
    let oiSide ← loadU64 mData (if side == SIDE_LONG then MktOff.oiLong else MktOff.oiShort)
    SolanaM.require (oiSide > 0) PErr.adlHaircutActive

    let liqSlot ← findOrAllocLegSlot lData (AccountView.keyPtr mkt) mid
    let liqLp := legPtrAt lData liqSlot
    let liqSide ← loadU8 liqLp LegOff.side
    SolanaM.require (liqSide == SIDE_FLAT || liqSide == side) PErr.invalidSide
    let _ ← settleAndRefreshLeg dData mData lData liqSlot curSlot false false
    if liqSide == SIDE_FLAT then
      storeU8  liqLp LegOff.side side
      storeU64 liqLp LegOff.entryK (← loadU64 mData (if side == SIDE_LONG then MktOff.kLong else MktOff.kShort))
      addU64At mData MktOff.activeLegs 1
    addU64At liqLp LegOff.rawBasis rawClose
    syncLegMargins mData lData liqSlot curSlot
    requirePortfolioIm lData curSlot
  else
    -- Tier 3 Fallback: Proportional OI reduction (`ceil` guarantees `oi' <= rSide'`!) + derived ADL
    let oiL ← loadU64 mData MktOff.oiLong
    let oiS ← loadU64 mData MktOff.oiShort
    let rL  ← loadU64 mData MktOff.rawBasisLong
    let rS  ← loadU64 mData MktOff.rawBasisShort
    let minOi := if oiL < oiS then oiL else oiS
    let oiSide  := if side == SIDE_LONG then oiL else oiS
    let rawSide := if side == SIDE_LONG then rL  else rS
    let effProp ← proportionalOiForRawU64 rawClose oiSide rawSide
    let mut eff := if effProp < minOi then effProp else minOi
    let rL' ← checkedSub64 rL (if side == SIDE_LONG  then rawClose else 0)
    let rS' ← checkedSub64 rS (if side == SIDE_SHORT then rawClose else 0)
    -- Gap #4A Fix: if a >10^9:1 wipeout would leave sub-nanounit dust OI (`adl' == 0` with `oi' > 0`),
    -- snap remaining dust OI to 0 so dead legs clear cleanly via `ClearDeadLeg` (no unclosable zombie!).
    if eff < minOi then
      let remOi := minOi - eff
      if (rL' > 0 && (← deriveAdlU64 remOi rL') == 0) || (rS' > 0 && (← deriveAdlU64 remOi rS') == 0) then
        eff := minOi
    let oiL' := oiL - eff
    let oiS' := oiS - eff
    SolanaM.require (oiL' <= rL' && oiS' <= rS') PErr.invalidParams
    storeU64 mData MktOff.oiLong oiL'
    storeU64 mData MktOff.oiShort oiS'
    storeU64 mData MktOff.rawBasisLong rL'
    storeU64 mData MktOff.rawBasisShort rS'
    storeU64 mData MktOff.adlLong  (← deriveAdlU64 oiL' rL')
    storeU64 mData MktOff.adlShort (← deriveAdlU64 oiS' rS')

  -- Update or flatten victim's leg & sync cached margins
  storeU64 lp LegOff.rawBasis remRaw
  if remRaw == 0 then
    storeU8 lp LegOff.side SIDE_FLAT
    subU64At mData MktOff.activeLegs 1
  syncLegMargins mData fData slotIdx curSlot
  freeLegIfEmpty fData slotIdx
  log64 EvtTag.liquidate ((mid <<< 8) ||| mode.toUInt64) rawClose liqFee shortfall

def handleClearDeadLeg (input : Ptr) : SolanaM Unit := do
  let (dex, mkt, pfl, _, progId) ← parseStrict3 input PErr.aliasedAccounts
  requireWritable dex; requireWritable mkt; requireWritable pfl
  checkOwnedMagic dex progId DexOff.size MAGIC_DEX
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  checkOwnedMagic pfl progId PflOff.size MAGIC_PORTFOLIO
  let dData := AccountView.dataPtr dex
  let mData := AccountView.dataPtr mkt
  let fData := AccountView.dataPtr pfl
  requireKeyEq (AccountView.keyPtr dex) (mData + MktOff.dex) PErr.dexMismatch
  requireKeyEq (AccountView.keyPtr dex) (fData + PflOff.dex) PErr.dexMismatch

  let st ← loadU8 mData MktOff.status
  SolanaM.require (st == STATUS_ACTIVE || st == STATUS_WINDDOWN) PErr.invalidStatus
  let curSlot ← getClockSlot
  let mid ← loadU64 mData MktOff.marketId
  let slotIdx ← findLegLoop fData mid 0
  SolanaM.require (slotIdx < MAX_LEGS) PErr.legNotFound
  let lp := legPtrAt fData slotIdx
  requireKeyEq (AccountView.keyPtr mkt) (lp + LegOff.market) PErr.marketMismatch

  let side ← loadU8 lp LegOff.side
  let rawB ← loadU64 lp LegOff.rawBasis
  SolanaM.require (side != SIDE_FLAT && rawB > 0) PErr.invalidSide
  let _ ← settleAndRefreshLeg dData mData fData slotIdx curSlot false

  if side == SIDE_LONG then
    SolanaM.require ((← loadU64 mData MktOff.oiLong) == 0) PErr.nonzeroOi
    let rL' ← checkedSub64 (← loadU64 mData MktOff.rawBasisLong) rawB
    storeU64 mData MktOff.rawBasisLong rL'
    storeU64 mData MktOff.adlLong (← deriveAdlU64 0 rL')
  else
    SolanaM.require ((← loadU64 mData MktOff.oiShort) == 0) PErr.nonzeroOi
    let rS' ← checkedSub64 (← loadU64 mData MktOff.rawBasisShort) rawB
    storeU64 mData MktOff.rawBasisShort rS'
    storeU64 mData MktOff.adlShort (← deriveAdlU64 0 rS')

  storeU8  lp LegOff.side SIDE_FLAT
  storeU64 lp LegOff.rawBasis 0
  subU64At mData MktOff.activeLegs 1
  syncLegMargins mData fData slotIdx curSlot
  freeLegIfEmpty fData slotIdx

def handleStartWindDown (input : Ptr) : SolanaM Unit := do
  let (mkt, caller, _, progId) ← parseStrict2 input PErr.aliasedAccounts
  requireSigner caller; requireWritable mkt
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  let mData := AccountView.dataPtr mkt
  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_ACTIVE) PErr.invalidStatus

  let curSlot ← getClockSlot
  let isAdmin ← do
    if (← pubkeyIsZero (mData + MktOff.marketAdmin)) then pure false
    else pubkeyEq (AccountView.keyPtr caller) (mData + MktOff.marketAdmin)
  if !isAdmin then
    let lastSlot ← loadU64 mData MktOff.lastOracleSlot
    let maxStale ← loadU64 mData MktOff.maxStaleness
    let age := if curSlot >= lastSlot then curSlot - lastSlot else 0
    SolanaM.require (age > maxStale) PErr.oracleNotStale

  storeU8  mData MktOff.status STATUS_WINDDOWN
  storeU64 mData MktOff.windDownSlot curSlot

def handleForceClosePair (input : Ptr) : SolanaM Unit := do
  let (dex, mkt, pflL, pflS, _, progId) ← parseStrict4 input PErr.aliasedAccounts
  requireWritable dex; requireWritable mkt; requireWritable pflL; requireWritable pflS
  requireKeyNe (AccountView.keyPtr pflL) (AccountView.keyPtr pflS) PErr.aliasedAccounts
  checkOwnedMagic dex  progId DexOff.size MAGIC_DEX
  checkOwnedMagic mkt  progId MktOff.size MAGIC_MARKET
  checkOwnedMagic pflL progId PflOff.size MAGIC_PORTFOLIO
  checkOwnedMagic pflS progId PflOff.size MAGIC_PORTFOLIO
  let dData  := AccountView.dataPtr dex
  let mData  := AccountView.dataPtr mkt
  let fLData := AccountView.dataPtr pflL
  let fSData := AccountView.dataPtr pflS
  requireKeyEq (AccountView.keyPtr dex) (mData  + MktOff.dex) PErr.dexMismatch
  requireKeyEq (AccountView.keyPtr dex) (fLData + PflOff.dex) PErr.dexMismatch
  requireKeyEq (AccountView.keyPtr dex) (fSData + PflOff.dex) PErr.dexMismatch

  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_WINDDOWN) PErr.invalidStatus
  let curSlot ← getClockSlot
  let unlockSlot ← checkedAdd64 (← loadU64 mData MktOff.windDownSlot) (← loadU64 mData MktOff.exitWindow)
  SolanaM.require (curSlot >= unlockSlot) PErr.exitWindowActive

  let mid ← loadU64 mData MktOff.marketId
  let slotL ← findLegLoop fLData mid 0
  let slotS ← findLegLoop fSData mid 0
  SolanaM.require (slotL < MAX_LEGS && slotS < MAX_LEGS) PErr.legNotFound
  let lpL := legPtrAt fLData slotL
  let lpS := legPtrAt fSData slotS
  requireKeyEq (AccountView.keyPtr mkt) (lpL + LegOff.market) PErr.marketMismatch
  requireKeyEq (AccountView.keyPtr mkt) (lpS + LegOff.market) PErr.marketMismatch
  SolanaM.require ((← loadU8 lpL LegOff.side) == SIDE_LONG && (← loadU8 lpS LegOff.side) == SIDE_SHORT) PErr.invalidSide

  let _ ← settleAndRefreshLeg dData mData fLData slotL curSlot false
  let _ ← settleAndRefreshLeg dData mData fSData slotS curSlot false

  let rLegL ← loadU64 lpL LegOff.rawBasis
  let rLegS ← loadU64 lpS LegOff.rawBasis
  SolanaM.require (rLegL > 0 && rLegS > 0) PErr.invalidParams

  let eL0 ← legEffectiveQty mData lpL
  let eS0 ← legEffectiveQty mData lpS
  let effL := if eL0 == 0 then 1 else eL0
  let effS := if eS0 == 0 then 1 else eS0
  let oiL ← loadU64 mData MktOff.oiLong
  let oiS ← loadU64 mData MktOff.oiShort
  let q1 := if effL < effS then effL else effS
  let q2 := if oiL < oiS then oiL else oiS
  let q  := if q1 < q2 then q1 else q2
  SolanaM.require (q > 0) PErr.nonzeroOi

  let rMktL ← loadU64 mData MktOff.rawBasisLong
  let rMktS ← loadU64 mData MktOff.rawBasisShort
  let redL ← proportionalRawRedU64 q rLegL rMktL oiL
  let redS ← proportionalRawRedU64 q rLegS rMktS oiS
  SolanaM.require (redL > 0 && redS > 0 && rLegL >= redL && rLegS >= redS &&
                   rMktL >= redL && rMktS >= redS) PErr.invalidParams

  let oiL' := oiL - q
  let oiS' := oiS - q
  let rMktL' := rMktL - redL
  let rMktS' := rMktS - redS
  SolanaM.require (oiL' <= rMktL' && oiS' <= rMktS') PErr.invalidParams

  storeU64 mData MktOff.oiLong oiL'
  storeU64 mData MktOff.oiShort oiS'
  storeU64 mData MktOff.rawBasisLong rMktL'
  storeU64 mData MktOff.rawBasisShort rMktS'
  storeU64 mData MktOff.adlLong  (← deriveAdlU64 oiL' rMktL')
  storeU64 mData MktOff.adlShort (← deriveAdlU64 oiS' rMktS')

  let rLegL' := rLegL - redL
  let rLegS' := rLegS - redS
  storeU64 lpL LegOff.rawBasis rLegL'
  storeU64 lpS LegOff.rawBasis rLegS'
  if rLegL' == 0 then
    storeU8 lpL LegOff.side SIDE_FLAT
    subU64At mData MktOff.activeLegs 1
  if rLegS' == 0 then
    storeU8 lpS LegOff.side SIDE_FLAT
    subU64At mData MktOff.activeLegs 1

  syncLegMargins mData fLData slotL curSlot
  syncLegMargins mData fSData slotS curSlot
  freeLegIfEmpty fLData slotL
  freeLegIfEmpty fSData slotS
  log64 EvtTag.forceClose mid q oiL' curSlot

def handleResolveMarket (input : Ptr) : SolanaM Unit := do
  let (dex, mkt, _, progId) ← parseStrict2 input PErr.aliasedAccounts
  requireWritable dex; requireWritable mkt
  checkOwnedMagic dex progId DexOff.size MAGIC_DEX
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  let dData := AccountView.dataPtr dex
  let mData := AccountView.dataPtr mkt
  requireKeyEq (AccountView.keyPtr dex) (mData + MktOff.dex) PErr.dexMismatch
  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_WINDDOWN) PErr.invalidStatus
  SolanaM.require ((← loadU64 mData MktOff.oiLong) == 0 && (← loadU64 mData MktOff.oiShort) == 0 &&
                   (← loadU64 mData MktOff.rawBasisLong) == 0 && (← loadU64 mData MktOff.rawBasisShort) == 0 &&
                   (← loadU64 mData MktOff.activeLegs) == 0) PErr.nonzeroOi

  let rPool  ← loadU64 mData MktOff.realizedPool
  let totPnl ← loadU64 mData MktOff.totalPosPnl
  let resNum := if rPool < totPnl then rPool else totPnl
  storeU64 mData MktOff.resolvedNum resNum
  storeU64 mData MktOff.resolvedDen totPnl
  storeU8  mData MktOff.status STATUS_RESOLVED
  sweepResolvedDust dData mData
  log64 EvtTag.resolve (← loadU64 mData MktOff.marketId) resNum totPnl 0

def handleClaimResolved (input : Ptr) : SolanaM Unit := do
  let (dex, mkt, pfl, _, progId) ← parseStrict3 input PErr.aliasedAccounts
  requireWritable dex; requireWritable mkt; requireWritable pfl
  checkOwnedMagic dex progId DexOff.size MAGIC_DEX
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  checkOwnedMagic pfl progId PflOff.size MAGIC_PORTFOLIO
  let dData := AccountView.dataPtr dex
  let mData := AccountView.dataPtr mkt
  let fData := AccountView.dataPtr pfl
  requireKeyEq (AccountView.keyPtr dex) (mData + MktOff.dex) PErr.dexMismatch
  requireKeyEq (AccountView.keyPtr dex) (fData + PflOff.dex) PErr.dexMismatch

  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_RESOLVED) PErr.invalidStatus
  let mid ← loadU64 mData MktOff.marketId
  let slotIdx ← findLegLoop fData mid 0
  SolanaM.require (slotIdx < MAX_LEGS) PErr.legNotFound
  let lp := legPtrAt fData slotIdx
  requireKeyEq (AccountView.keyPtr mkt) (lp + LegOff.market) PErr.marketMismatch
  SolanaM.require ((← loadU8 lp LegOff.side) == SIDE_FLAT && (← loadU64 lp LegOff.rawBasis) == 0) PErr.nonzeroOi

  let posPnl ← loadU64 lp LegOff.posPnl
  let resNum ← loadU64 mData MktOff.resolvedNum
  let resDen ← loadU64 mData MktOff.resolvedDen
  let pay ← if resDen == 0 || posPnl == 0 then pure 0 else mulDiv64 posPnl resNum resDen
  if pay > 0 then
    subU64At mData MktOff.realizedPool pay
    subU64At dData DexOff.totalResidual pay
    addU64At fData PflOff.capital pay
    addU64At dData DexOff.totalCapital pay
  if posPnl > 0 then subU64At mData MktOff.totalPosPnl posPnl

  storeU64 lp LegOff.posPnl 0
  freeLegIfEmpty fData slotIdx
  sweepResolvedDust dData mData

def handleTombstoneMarket (input : Ptr) : SolanaM Unit := do
  let (mkt, _, progId) ← parseStrict1 input PErr.aliasedAccounts
  requireWritable mkt
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  let mData := AccountView.dataPtr mkt
  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_RESOLVED) PErr.invalidStatus
  SolanaM.require ((← loadU64 mData MktOff.oiLong) == 0 && (← loadU64 mData MktOff.oiShort) == 0 &&
                   (← loadU64 mData MktOff.rawBasisLong) == 0 && (← loadU64 mData MktOff.rawBasisShort) == 0 &&
                   (← loadU64 mData MktOff.insurance) == 0 && (← loadU64 mData MktOff.realizedPool) == 0 &&
                   (← loadU64 mData MktOff.rewardAccrued) == 0 &&
                   (← loadU64 mData MktOff.activeLegs) == 0 && (← loadU64 mData MktOff.totalPosPnl) == 0) PErr.nonzeroState
  storeU8 mData MktOff.status STATUS_TOMBSTONED

/-- Unified rent reclaim for empty `Portfolio`, empty `InsReceipt`, or `Tombstoned` `Market`.
    Zeroes ALL account bytes AND writes permanent `MAGIC_CLOSED` ("DEAD", ≠ 0) before draining
    lamports so a closed account can NEVER be revived (neither as initialized nor as fresh `magic == 0`)
    even if rent lamports are refunded in the same transaction! -/
def handleCloseAccount (input : Ptr) : SolanaM Unit := do
  let (acc, authority, destRaw, _, progId) ← parse3 input
  requireNonDup acc; requireNonDup authority
  let dest ← AccountView.resolveDup destRaw 1 authority PErr.aliasedAccounts
  requireSigner authority; requireWritable acc; requireWritable dest
  requireKeyNe (AccountView.keyPtr acc) (AccountView.keyPtr dest) PErr.aliasedAccounts
  requireKeyEq (AccountView.ownerPtr acc) progId Err.illegalOwner
  let dlen ← AccountView.dataLen acc
  let data := AccountView.dataPtr acc
  let magic ← loadU32 data 0
  let closeWords ←
    if magic == MAGIC_PORTFOLIO then do
      SolanaM.require (dlen == PflOff.size) Err.invalidAccountData
      requireKeyEq (AccountView.keyPtr authority) (data + PflOff.owner) PErr.ownerMismatch
      SolanaM.require ((← loadU64 data PflOff.capital) == 0 && (← loadU64 data PflOff.totalLockedMm) == 0 &&
                       (← loadU8 data PflOff.legCount) == 0 &&
                       (← loadU64 data PflOff.totalMm) == 0 && (← loadU64 data PflOff.totalIm) == 0) PErr.nonzeroState
      pure (PflOff.size >>> 3)
    else if magic == MAGIC_INSURANCE then do
      SolanaM.require (dlen == InsOff.size) Err.invalidAccountData
      requireKeyEq (AccountView.keyPtr authority) (data + InsOff.owner) PErr.ownerMismatch
      SolanaM.require ((← loadU64 data InsOff.shares) == 0) PErr.nonzeroState
      pure (InsOff.size >>> 3)
    else if magic == MAGIC_MARKET then do
      SolanaM.require (dlen == MktOff.size) Err.invalidAccountData
      SolanaM.require ((← loadU8 data MktOff.status) == STATUS_TOMBSTONED) PErr.invalidStatus
      if !(← pubkeyIsZero (data + MktOff.marketAdmin)) then
        requireKeyEq (AccountView.keyPtr authority) (data + MktOff.marketAdmin) PErr.unauthorized
      pure (MktOff.size >>> 3)
    else
      SolanaM.fail PErr.invalidMagic

  zeroWordsLoop data 0 closeWords
  storeU32 data 0 MAGIC_CLOSED
  let accLam  ← AccountView.lamports acc
  let destLam ← AccountView.lamports dest
  AccountView.setLamports dest (← checkedAdd64 destLam accLam)
  AccountView.setLamports acc 0

/-- Sweep protocol-owned surplus (`DexOff.totalSurplus`, `S`) ONLY from `DexVault` → `DexOff.feeVault`
    for downstream external `"hl"` distribution (airdrops, buybacks, treasury).
    User capital (`C`), insurance (`I`), and realized pools (`R`) are 100% untouchable,
    and `V == C + I + R + S` holds bit-for-bit (`V -= sweepAmt`, `S -= sweepAmt`)! -/
def handleSweepSurplus (input : Ptr) : SolanaM Unit := do
  let (dex, admin, mint, vaultPda, feeVaultTok, tokProg, ix, progId) ← parseStrict6 input PErr.aliasedAccounts
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner admin; requireWritable dex; requireWritable vaultPda; requireWritable feeVaultTok
  checkOwnedMagic dex progId DexOff.size MAGIC_DEX
  let dData := AccountView.dataPtr dex
  requireKeyEq (AccountView.keyPtr admin) (dData + DexOff.admin) PErr.unauthorized
  checkDexVaultAndMint dData mint vaultPda tokProg
  requireKeyEq (AccountView.keyPtr feeVaultTok) (dData + DexOff.feeVault) PErr.vaultMismatch
  requireKeyNe (AccountView.keyPtr feeVaultTok) (dData + DexOff.vaultPda) PErr.aliasedAccounts

  let reqAmt ← loadU64 ix.ptr 1
  let avail  ← loadU64 dData DexOff.totalSurplus
  let sweepAmt := if reqAmt == 0 then avail else reqAmt
  SolanaM.require (sweepAmt > 0 && sweepAmt <= avail) PErr.invalidParams

  subU64At dData DexOff.totalSurplus sweepAmt
  subU64At dData DexOff.vaultBalance sweepAmt
  let dec  ← loadU8 dData DexOff.decimals
  let bump ← loadU8 dData DexOff.vaultBump
  tokenTransferCheckedSigned tokProg vaultPda mint feeVaultTok vaultPda sweepAmt dec
    TAG_DEX_VAULT (AccountView.keyPtr dex) bump
  log64 EvtTag.sweepSurplus sweepAmt (avail - sweepAmt) 0 0

/-- Claim market-specific accrued reward fees (`MktOff.rewardAccrued`, `F_m`) from `DexVault` → `destTok`.
    ONLY the market's immutable `MktOff.rewardRecipient` (e.g. a per-market `RewardModule` buy-and-burn PDA)
    may sign! User capital (`C`), insurance (`I`), realized pools (`R`), protocol surplus (`S`), and EVERY
    other market's `F_{m'}` are 100% untouchable (`V -= claimAmt`, `F_tot -= claimAmt`, `F_m -= claimAmt`)! -/
def handleClaimReward (input : Ptr) : SolanaM Unit := do
  let (dex, mkt, rewAuth, mint, vaultPda, destTok, tokProg, ix, progId) ← parseStrict7 input PErr.aliasedAccounts
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner rewAuth; requireWritable dex; requireWritable mkt
  requireWritable vaultPda; requireWritable destTok
  checkOwnedMagic dex progId DexOff.size MAGIC_DEX
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  let dData := AccountView.dataPtr dex
  let mData := AccountView.dataPtr mkt
  requireKeyEq (AccountView.keyPtr dex) (mData + MktOff.dex) PErr.dexMismatch
  checkDexVaultAndMint dData mint vaultPda tokProg
  requireKeyNe (AccountView.keyPtr destTok) (dData + DexOff.vaultPda) PErr.aliasedAccounts
  SolanaM.require (!(← pubkeyIsZero (mData + MktOff.rewardRecipient))) PErr.unauthorized
  requireKeyEq (AccountView.keyPtr rewAuth) (mData + MktOff.rewardRecipient) PErr.unauthorized

  let reqAmt ← loadU64 ix.ptr 1
  let avail  ← loadU64 mData MktOff.rewardAccrued
  let claimAmt := if reqAmt == 0 then avail else reqAmt
  SolanaM.require (claimAmt > 0 && claimAmt <= avail) PErr.invalidParams

  subU64At mData MktOff.rewardAccrued claimAmt
  subU64At dData DexOff.totalRewards  claimAmt
  subU64At dData DexOff.vaultBalance  claimAmt
  let dec  ← loadU8 dData DexOff.decimals
  let bump ← loadU8 dData DexOff.vaultBump
  tokenTransferCheckedSigned tokProg vaultPda mint destTok vaultPda claimAmt dec
    TAG_DEX_VAULT (AccountView.keyPtr dex) bump
  let mid ← loadU64 mData MktOff.marketId
  log64 EvtTag.claimReward mid claimAmt (avail - claimAmt) 0

/-- Op 22 (`SetPortfolioMatcher`): LP owner binds or revokes an optional external PropAMM
    `matcherCtx` account on their `Portfolio` while keeping 100% EOA custody over withdrawals!
    Accounts: `0. pfl (W)`, `1. owner (S)`, optional `2. matcherCtx` (omitting unbinds to 0). -/
def handleSetPortfolioMatcher (input : Ptr) : SolanaM Unit := do
  let (n, pfl, _, progId) ← parseIxOnly input
  SolanaM.require (n >= 2) Err.notEnoughAccountKeys
  let owner ← AccountView.nextCursor pfl
  requireNonDup pfl; requireNonDup owner
  requireSigner owner; requireWritable pfl
  checkOwnedMagic pfl progId PflOff.size MAGIC_PORTFOLIO
  let fData := AccountView.dataPtr pfl
  requireKeyEq (AccountView.keyPtr owner) (fData + PflOff.owner) PErr.ownerMismatch
  if n >= 3 then
    let mc ← AccountView.nextCursor owner
    requireNonDup mc
    pubkeyCopy (fData + PflOff.matcherCtx) (AccountView.keyPtr mc)
  else
    storeU64 fData (PflOff.matcherCtx + 0)  0
    storeU64 fData (PflOff.matcherCtx + 8)  0
    storeU64 fData (PflOff.matcherCtx + 16) 0
    storeU64 fData (PflOff.matcherCtx + 24) 0

/-- Pure, verifiable adversarial PropAMM header check (Refinement #25a).
    Validates `MatcherReturn` header at `mcData[0..16]` after a 0-signer CPI-Out call:
    - `magic == MAGIC_MRET` (`"MRET"`), `status == 0`
    - `seq == reqSeq` (blocks `noop.so` and stale quote replay, since `reqSeq = preSeq + 1 != preSeq`!). -/
def validateMatcherHeader (mcData reqSeq : UInt64) : SolanaM Unit := do
  let retMagic  ← loadU32 mcData 0
  let retStatus ← loadU32 mcData 4
  let retSeq    ← loadU64 mcData 8
  SolanaM.require (retMagic == MAGIC_MRET && retStatus == 0 && retSeq == reqSeq) PErr.invalidMatcher

/-- Pure, verifiable per-leg adversarial PropAMM quote check (Refinement #25b).
    Validates `(execPrice, fillQty)` at `legRetPtr[0..16]`:
    - `0 < execPrice <= MAX_PRICE` and `0 < fillQty <= maxQty` (blocks over-fill & zero-fill!)
    - Enforces taker's `limitPrice` inside core `percolator` using true economic buy/sell direction:
      * `takerIsBuying != 0` (open Long OR reduce Short): `execPrice <= limitPrice`
      * `takerIsBuying == 0` (open Short OR reduce Long): `execPrice >= limitPrice`. -/
def validateMatcherLeg (legRetPtr maxQty limitPrice : UInt64) (takerIsBuying : UInt8) :
    SolanaM (UInt64 × UInt64) := do
  let execPrice ← loadU64 legRetPtr 0
  let fillQty   ← loadU64 legRetPtr 8
  SolanaM.require (execPrice > 0 && execPrice <= MAX_PRICE && fillQty > 0 && fillQty <= maxQty) PErr.invalidMatcher
  if limitPrice != 0 then
    if takerIsBuying != 0 then
      SolanaM.require (execPrice <= limitPrice) PErr.execPriceClamp
    else
      SolanaM.require (execPrice >= limitPrice) PErr.execPriceClamp
  return (execPrice, fillQty)

/-- Outlined 0-signer CPI-Out into ANY untrusted external PropAMM (`matcherProg`).
    `packedMeta` packs `(reqLen << 8) | nInfos` (`nInfos ∈ {1, 2}`).
    Passes ONLY `[matcherCtx (W=1, S=0)]` (plus optional `[extraAcc (W=0, S=0)]` if `nInfos == 2`).
    ZERO signer privileges (`seedsLen = 0`), ZERO core accounts exposed → re-entrancy & signer theft
    are structurally impossible! -/
@[noinline] def cpiCallMatcher (matcherProg matcherCtx extraAcc reqPtr : Ptr) (packedMeta : UInt64) : SolanaM Unit := do
  let nInfos := packedMeta &&& 3
  let reqLen := packedMeta >>> 8
  let buf   ← stackAlloc 184
  let metas := buf + 40
  let infos := buf + 72
  writeMeta metas matcherCtx 1 0
  writeAccountInfo infos matcherCtx
  if nInfos == 2 then
    writeMeta (metas + 16) extraAcc 0 0
    writeAccountInfo (infos + 56) extraAcc
  writeInstruction buf (AccountView.keyPtr matcherProg) metas nInfos reqPtr reqLen
  let rc ← sysInvokeSignedC buf infos nInfos 0 0
  SolanaM.require (rc == 0) rc

/-- Verify `mid` does not duplicate any previously validated market `0..j-1` in `mktArr`. -/
def checkDistinctMarketIdLoop (mktArr : Ptr) (mid j count : UInt64) : SolanaM Unit := do
  if h : j < count then
    let prevMkt ← loadU64 mktArr (j * 8)
    let prevMid ← loadU64 (AccountView.dataPtr prevMkt) MktOff.marketId
    SolanaM.require (prevMid != mid) PErr.aliasedAccounts
    checkDistinctMarketIdLoop mktArr mid (j + 1) count
  else
    return ()
termination_by (count.toNat - j.toNat)
decreasing_by
  have hlt : j.toNat < count.toNat := UInt64.lt_iff_toNat_lt.mp h
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hadd : (j + 1).toNat = j.toNat + 1 := by
    rw [UInt64.toNat_add, h1, Nat.mod_eq_of_lt (by have := count.toNat_lt; omega)]
  omega

/-- Validate `k` distinct market accounts & serialize all `k` offers into `reqBuf` in one pass
    so `matcherProg` sees ALL `k` offers simultaneously in ONE CPI (zero tx introspection!).
    `ctxBuf` holds `[dexKeyPtr, progId, ixPtr, mktArr, reqBuf, k]`. Returns cursor after `mkt_{k-1}`. -/
def prepMatcherOffersLoop (curMkt ctxBuf : Ptr) (i : UInt64) : SolanaM Ptr := do
  if h : i < MAX_LEGS then
    let k ← loadU64 ctxBuf 40
    if i < k then
      let dexKeyPtr ← loadU64 ctxBuf 0
      let progId    ← loadU64 ctxBuf 8
      let ixPtr     ← loadU64 ctxBuf 16
      let mktArr    ← loadU64 ctxBuf 24
      let reqBuf    ← loadU64 ctxBuf 32
      SolanaM.require ((← rawLoadU8 curMkt) == ABI.nonDupMarker) PErr.aliasedAccounts
      requireWritable curMkt
      checkOwnedMagic curMkt progId MktOff.size MAGIC_MARKET
      let mData := AccountView.dataPtr curMkt
      requireKeyEq dexKeyPtr (mData + MktOff.dex) PErr.dexMismatch
      let mid ← loadU64 mData MktOff.marketId
      checkDistinctMarketIdLoop mktArr mid 0 i
      storeU64 mktArr (i * 8) curMkt

      let ixOff := 2 + i * 18
      let mode        ← loadU8  ixPtr ixOff
      let takerIsLong ← loadU8  ixPtr (ixOff + 1)
      let maxQty      ← loadU64 ixPtr (ixOff + 2)
      let limitPrice  ← loadU64 ixPtr (ixOff + 10)
      SolanaM.require ((mode == 0 || mode == 1 || mode == 4) && maxQty > 0) PErr.invalidParams

      let rOff := reqBuf + 32 + i * 48
      storeU8  rOff 0  mode
      storeU8  rOff 1  takerIsLong
      storeU64 rOff 8  mid
      storeU64 rOff 16 maxQty
      storeU64 rOff 24 limitPrice
      storeU64 rOff 32 (← loadU64 mData MktOff.markPrice)
      storeU64 rOff 40 (← loadU64 mData MktOff.maxMoveBps)

      let nxt ← AccountView.nextCursor curMkt
      prepMatcherOffersLoop nxt ctxBuf (i + 1)
    else
      return curMkt
  else
    return curMkt
termination_by (MAX_LEGS.toNat - i.toNat)
decreasing_by
  have hlt : i.toNat < MAX_LEGS.toNat := UInt64.lt_iff_toNat_lt.mp h
  have h8 : MAX_LEGS.toNat = 8 := rfl
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hadd : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Validate & settle all `k` PropAMM quotes atomically via shared `tradeCore`. -/
def settleMatcherOffersLoop (dData takerData lpData ctxBuf : Ptr) (i : UInt64) : SolanaM Unit := do
  if _h : i < MAX_LEGS then
    let k ← loadU64 ctxBuf 24
    if i < k then
      let ixPtr   ← loadU64 ctxBuf 0
      let mktArr  ← loadU64 ctxBuf 8
      let mcData  ← loadU64 ctxBuf 16
      let argsBuf ← loadU64 ctxBuf 32
      let mkt     ← loadU64 mktArr (i * 8)
      let ixOff := 2 + i * 18
      let mode        ← loadU8  ixPtr ixOff
      let takerIsLong ← loadU8  ixPtr (ixOff + 1)
      let maxQty      ← loadU64 ixPtr (ixOff + 2)
      let limitPrice  ← loadU64 ixPtr (ixOff + 10)
      let takerIsBuying : UInt8 :=
        if (mode != 1 && takerIsLong != 0) || (mode == 1 && takerIsLong == 0) then 1 else 0
      let (execPrice, fillQty) ← validateMatcherLeg (mcData + 16 + i * 16) maxQty limitPrice takerIsBuying
      let fLData := if takerIsLong != 0 then takerData else lpData
      let fSData := if takerIsLong != 0 then lpData    else takerData
      storeU64 argsBuf 0  (AccountView.keyPtr mkt)
      storeU64 argsBuf 8  mode.toUInt64
      storeU8  argsBuf 9  (if limitPrice != 0 then 1 else 0)
      storeU64 argsBuf 16 fillQty
      storeU64 argsBuf 24 execPrice
      if mode == 4 then
        tradeNettedCore dData (AccountView.dataPtr mkt) fLData fSData argsBuf
      else
        tradeCore dData (AccountView.dataPtr mkt) fLData fSData argsBuf
      settleMatcherOffersLoop dData takerData lpData ctxBuf (i + 1)
    else
      return ()
  else
    return ()
termination_by (MAX_LEGS.toNat - i.toNat)
decreasing_by
  have hlt : i.toNat < MAX_LEGS.toNat := UInt64.lt_iff_toNat_lt.mp _h
  have h8 : MAX_LEGS.toNat = 8 := rfl
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hadd : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Op 23 (`TradeWithMatcher`): Unified Single- OR Multi-Market (`k ∈ [1..8]`) Legacy-Percolator
    0-Signer CPI-Out Trade against ANY untrusted/closed-source external PropAMM!
    ALL `k` market offers are passed in ONE single CPI call so the PropAMM sees the full basket
    without tx introspection (e.g. tight correlated pair spreads on Long BTC + Short ETH!).
    Accounts (`n >= 6 + k`, optional readonly non-signer `extraAcc` at index `6 + k`):
      0. `dex` (W), 1. `takerPfl` (W), 2. `takerOwner` (S — NEVER passed to matcher!),
      3. `lpPfl` (W, MUST have `lpPfl.matcherCtx == matcherCtx.key`),
      4. `matcherProg` (executable, `!= progId`),
      5. `matcherCtx` (W, `owner == matcherProg`, `dataLen >= 16 + 16 * k`),
      6..6+k-1. `mkt_0 .. mkt_{k-1}` (all W, distinct markets belonging to `dex`),
      6+k. *(optional)* `extraAcc` (R, non-signer).
    Ix data (`2 + 18 * k` B): `[23:u8, k:u8, (mode:u8, takerIsLong:u8, maxQty:u64, limitPrice:u64) × k]`. -/
def handleTradeWithMatcher (input : Ptr) : SolanaM Unit := do
  let (n, dex, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 7 && ix.len >= 20) Err.invalidInstructionData
  let k8 ← loadU8 ix.ptr 1
  let k := k8.toUInt64
  SolanaM.require (k >= 1 && k <= MAX_LEGS) PErr.invalidParams
  SolanaM.require (n >= 6 + k) Err.notEnoughAccountKeys
  SolanaM.require (ix.len >= 2 + k * 18) Err.invalidInstructionData

  let takerPfl    ← AccountView.nextCursor dex
  let takerOwner  ← AccountView.nextCursor takerPfl
  let lpPfl       ← AccountView.nextCursor takerOwner
  let matcherProg ← AccountView.nextCursor lpPfl
  let matcherCtx  ← AccountView.nextCursor matcherProg
  let mkt0        ← AccountView.nextCursor matcherCtx

  requireNonDup dex; requireNonDup takerPfl; requireNonDup takerOwner; requireNonDup lpPfl
  requireNonDup matcherProg; requireNonDup matcherCtx
  requireSigner takerOwner
  requireWritable dex; requireWritable takerPfl
  requireWritable lpPfl; requireWritable matcherCtx
  requireKeyNe (AccountView.keyPtr takerPfl) (AccountView.keyPtr lpPfl) PErr.aliasedAccounts
  checkOwnedMagic dex      progId DexOff.size MAGIC_DEX
  checkOwnedMagic takerPfl progId PflOff.size MAGIC_PORTFOLIO
  checkOwnedMagic lpPfl    progId PflOff.size MAGIC_PORTFOLIO

  let dData     := AccountView.dataPtr dex
  let takerData := AccountView.dataPtr takerPfl
  let lpData    := AccountView.dataPtr lpPfl
  requireKeyEq (AccountView.keyPtr dex)        (takerData + PflOff.dex)   PErr.dexMismatch
  requireKeyEq (AccountView.keyPtr dex)        (lpData    + PflOff.dex)   PErr.dexMismatch
  requireKeyEq (AccountView.keyPtr takerOwner) (takerData + PflOff.owner) PErr.ownerMismatch

  -- Pin LP-authorized `matcherCtx` owned by executable external `matcherProg != progId`!
  SolanaM.require (!(← pubkeyIsZero (lpData + PflOff.matcherCtx))) PErr.invalidMatcher
  requireKeyEq (AccountView.keyPtr matcherCtx) (lpData + PflOff.matcherCtx) PErr.invalidMatcher
  SolanaM.require (← AccountView.isExecutable matcherProg) PErr.invalidMatcher
  requireKeyNe (AccountView.keyPtr matcherProg) progId PErr.invalidMatcher
  requireKeyEq (AccountView.ownerPtr matcherCtx) (AccountView.keyPtr matcherProg) PErr.invalidMatcher
  SolanaM.require ((← AccountView.dataLen matcherCtx) >= 16 + k * 16) PErr.invalidMatcher

  let mcData  := AccountView.dataPtr matcherCtx
  let preSeq  ← loadU64 mcData 8
  let reqSeq  := preSeq + 1
  let curSlot ← getClockSlot

  let mktArr  ← stackAlloc 64
  let reqBuf  ← stackAlloc 416
  let ctxBuf  ← stackAlloc 48
  storeU8  reqBuf 0  2
  storeU8  reqBuf 1  k8
  storeU64 reqBuf 8  (← loadU64 lpData PflOff.capital)
  storeU64 reqBuf 16 curSlot
  storeU64 reqBuf 24 reqSeq
  storeU64 ctxBuf 0  (AccountView.keyPtr dex)
  storeU64 ctxBuf 8  progId
  storeU64 ctxBuf 16 ix.ptr
  storeU64 ctxBuf 24 mktArr
  storeU64 ctxBuf 32 reqBuf
  storeU64 ctxBuf 40 k

  let afterMkts ← prepMatcherOffersLoop mkt0 ctxBuf 0
  let reqLen := 32 + k * 48
  if n >= 7 + k then
    -- Reject duplicate account markers (blocks stub-overread AND aliasing core/signer accounts as extraAcc!)
    SolanaM.require ((← rawLoadU8 afterMkts) == ABI.nonDupMarker) PErr.aliasedAccounts
    cpiCallMatcher matcherProg matcherCtx afterMkts reqBuf ((reqLen <<< 8) ||| 2)
  else
    cpiCallMatcher matcherProg matcherCtx 0 reqBuf ((reqLen <<< 8) ||| 1)

  validateMatcherHeader mcData reqSeq

  let argsBuf ← stackAlloc 32
  storeU64 ctxBuf 0  ix.ptr
  storeU64 ctxBuf 8  mktArr
  storeU64 ctxBuf 16 mcData
  storeU64 ctxBuf 24 k
  storeU64 ctxBuf 32 argsBuf
  settleMatcherOffersLoop dData takerData lpData ctxBuf 0

/-! ### Top-Level Solana Entrypoint (`lean-svm` lowers opcode dispatch to O(log2 24) binary search!) -/

def dispatch (input : Ptr) : SolanaM Unit := do
  let (_, _, ix, _) ← parseIxOnly input
  SolanaM.require (ix.len >= 1) Err.invalidInstructionData
  let op ← loadU8 ix.ptr 0
  if op == IxOp.initDex                 then handleInitDex input
  else if op == IxOp.updateCreateFee    then handleUpdateCreateFee input
  else if op == IxOp.createMarket       then handleCreateMarket input
  else if op == IxOp.updateMarketAuth   then handleUpdateMarketAuth input
  else if op == IxOp.updateOracle       then handleUpdateOracle input
  else if op == IxOp.initPortfolio      then handleInitPortfolio input
  else if op == IxOp.depositCollateral  then handleDepositCollateral input
  else if op == IxOp.withdrawCollateral then handleWithdrawCollateral input
  else if op == IxOp.depositInsurance   then handleDepositInsurance input
  else if op == IxOp.withdrawInsurance  then handleWithdrawInsurance input
  else if op == IxOp.refreshLeg         then handleRefreshLeg input
  else if op == IxOp.trade              then handleTrade input
  else if op == IxOp.liquidate          then handleLiquidate input
  else if op == IxOp.clearDeadLeg       then handleClearDeadLeg input
  else if op == IxOp.startWindDown      then handleStartWindDown input
  else if op == IxOp.forceClosePair     then handleForceClosePair input
  else if op == IxOp.resolveMarket      then handleResolveMarket input
  else if op == IxOp.claimResolved      then handleClaimResolved input
  else if op == IxOp.tombstoneMarket    then handleTombstoneMarket input
  else if op == IxOp.closeAccount       then handleCloseAccount input
  else if op == IxOp.sweepSurplus       then handleSweepSurplus input
  else if op == IxOp.claimReward        then handleClaimReward input
  else if op == IxOp.setPortfolioMatcher then handleSetPortfolioMatcher input
  else if op == IxOp.tradeWithMatcher   then handleTradeWithMatcher input
  else SolanaM.fail PErr.invalidInstruction

def entrypoint (input : Ptr) (s : SvmState) : UInt64 × SvmState :=
  SolanaM.runEntry (dispatch input) s

end Percolator.Program
