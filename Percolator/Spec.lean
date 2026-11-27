/-
  Percolator.Spec
  Pure mathematical state-transition model for `percolator-lean` v2:
  Realizable Shared Cross-Margin (Hyperliquid capital efficiency on healthy markets)
  + Exact Global Stock Equality (`C_tot + I_tot + R_tot + S_tot = V`)
  + Per-Market Isolated Risk & Insurance Domains (`R_m`, `I_m`, `S_m`, `A_m`)
  + Per-Leg Loss Containment (`capAvailableForLeg = capital - otherMm`, zero reverse contagion!)
-/

namespace Percolator.Spec

/-! ### Exact Constants (Matching `Percolator.Layout`) -/

def posScaleNat   : Nat := 1_000_000
def adlOneNat     : Nat := 1_000_000_000
def bpsDenNat     : Nat := 10_000
def minExitWinNat : Nat := 10
def maxExitWinNat : Nat := 216_000
def maxStaleNat   : Nat := 9_000
def maxLegsNat    : Nat := 8

/-! ### Core Exact Arithmetic Primitives -/

def mulDivDown (a b d : Nat) : Nat :=
  if d = 0 then 0 else (a * b) / d

def mulDivUp (a b d : Nat) : Nat :=
  if d = 0 then 0 else (a * b + d - 1) / d

/-- Exact floor haircut payout `⌊p * min(R_m, P^+_m) / P^+_m⌋`. -/
def haircutPayout (p realizedPool posPnlTot : Nat) : Nat :=
  if posPnlTot = 0 then 0
  else (p * min realizedPool posPnlTot) / posPnlTot

/-- Exact derived side ADL index `⌊ADL_ONE * oi / rawBasis⌋` (unconditional `effectiveQty ≤ oi`
    without artificial `max 1` floor-clamp!). -/
def deriveAdl (oi rawBasis : Nat) : Nat :=
  if rawBasis = 0 then adlOneNat
  else if oi >= rawBasis then adlOneNat
  else (adlOneNat * oi) / rawBasis

/-- Exact compounded 4-slot Solana leader-window upper bound in bps:
    for EVERY `m ≤ 2500`, `(10000 + m)^4 - 10000^4 ≤ k4CompoundedBps m * 10000^3`! -/
def k4CompoundedBps (maxMoveBps : Nat) : Nat :=
  4 * maxMoveBps + (maxMoveBps * maxMoveBps + 999) / 1000

/-- Exact compounded 5-slot (triggering slot + K = 4 adversarial leader window) upper bound in bps:
    for EVERY `m ≤ 1500`, `(10000 + m)^5 - 10000^5 ≤ k5CompoundedBps m * 10000^4`! -/
def k5CompoundedBps (maxMoveBps : Nat) : Nat :=
  5 * maxMoveBps + (maxMoveBps * maxMoveBps * 12 + 9999) / 10000

/-- Upper bound on liquidation fee bps computed at post-5-step price `p5 = p0 * (1 + k5Move / 10000)`! -/
def liqFeeAtP5Bps (liqFeeBps maxMoveBps : Nat) : Nat :=
  let k5 := k5CompoundedBps maxMoveBps
  liqFeeBps + (liqFeeBps * k5 + 9999) / 10000

/-- Effective position quantity `⌊rawBasis * adlSide / ADL_ONE⌋`. -/
def effectiveQty (rawBasis adlSide : Nat) : Nat :=
  (rawBasis * adlSide) / adlOneNat

/-- Proportional raw-basis reduction on an ADL-haircutted side (Percolator §5):
    removes at least `⌈qty * rawSide / oiSide⌉` raw basis (clamped to `[1, rawLeg]`)
    so `oi' ≤ rawSide'` is preserved! -/
def proportionalRawReduction (qty rawLeg rawSide oiSide : Nat) : Nat :=
  if oiSide = 0 ∨ rawSide = 0 then rawLeg
  else if oiSide = rawSide then min qty rawLeg
  else min rawLeg (max 1 (mulDivUp qty rawSide oiSide))

/-- Proportional OI removal for liquidating `rawClose` rawBasis on a side with `(oiSide, rawSide)`.
    Uses ceiling division so `oiSide - eff ≤ rawSide - rawClose` holds ALWAYS (even for 1-atom dust!). -/
def proportionalOiForRaw (rawClose oiSide rawSide : Nat) : Nat :=
  if oiSide = 0 ∨ rawSide = 0 then 0
  else if oiSide = rawSide then min rawClose oiSide
  else min oiSide (max 1 (mulDivUp rawClose oiSide rawSide))

/-- Fair gradual liquidation fee: scales smoothly from `maxFee / 4` up to `maxFee` with margin deficit. -/
def gradualLiqFee (maxFee deficit : Nat) : Nat :=
  min maxFee (max (maxFee / 4) deficit)
def marginNotional (qty price : Nat) : Nat :=
  mulDivUp qty price posScaleNat

def marginReq (notional bps : Nat) : Nat :=
  mulDivUp notional bps bpsDenNat

def oracleClampOk (oldP newP maxMoveBps : Nat) : Prop :=
  let diff := if newP ≥ oldP then newP - oldP else oldP - newP
  diff * bpsDenNat ≤ oldP * maxMoveBps

/-! ### State Types -/

inductive MarketStatus where
  | active | windDown | resolved | tombstoned
  deriving DecidableEq, Repr

inductive Side where
  | flat | long | short
  deriving DecidableEq, Repr

structure MarketState where
  marketId       : Nat
  status         : MarketStatus
  marketAdmin    : Nat           -- 0 = burned (adminless)
  markPrice      : Nat
  lastOracleSlot : Nat
  windDownSlot   : Nat
  exitWindow     : Nat
  maxStaleness   : Nat
  imBps          : Nat
  mmBps          : Nat
  liqFeeBps      : Nat
  tradeFeeBps    : Nat
  maxMoveBps     : Nat
  maxInsDrawBps  : Nat
  maxOi          : Nat
  realizedPool   : Nat           -- R_m (isolated loser backing for Market m!)
  insurance      : Nat           -- I_m (isolated insurance for Market m!)
  feeSurplus     : Nat           -- S_m (explicit rounding residue sink!)
  totalPosPnl    : Nat           -- P^+_m
  totalInsShares : Nat
  oiLong         : Nat
  oiShort        : Nat
  rawBasisLong   : Nat
  rawBasisShort  : Nat
  adlLong        : Nat
  adlShort       : Nat
  resolvedNum    : Nat
  resolvedDen    : Nat
  activeLegs      : Nat
  maxFrontBps     : Nat  := 0
  insFronted      : Nat  := 0
  rewardBps       : Nat  := 0
  rewardAccrued   : Nat  := 0
  rewardRecipient : Nat  := 0
  deriving DecidableEq, Repr

structure LegState where
  marketId        : Nat
  side            : Side
  rawBasis        : Nat
  posPnl          : Nat          -- positive PnL claim on Market `marketId`'s `realizedPool`
  cachedMm        : Nat
  cachedIm        : Nat
  lastRefreshSlot : Nat
  lockedMm        : Nat := 0     -- isolated per-leg MM firewall; NEVER raidable by other markets!
  deriving DecidableEq, Repr

structure PortfolioState where
  portfolioId   : Nat
  owner         : Nat
  capital       : Nat            -- free shared cross-margin collateral (deposits + excess + realized PnL!)
  totalMm       : Nat            -- sum of active legs' `cachedMm`
  totalIm       : Nat            -- sum of active legs' `cachedIm`
  legs          : Nat → Option LegState   -- marketId → active LegState
  legCount      : Nat := 0
  totalLockedMm : Nat := 0       -- sum of active legs' isolated `lockedMm`!

structure DexState where
  protocolAdmin   : Nat
  nextMarketId    : Nat
  nextPortfolioId : Nat
  createFee       : Nat
  vault           : Nat          -- V: exact SPL balance in shared DexVault
  totalCapital    : Nat          -- C_tot = Σ pfl.capital
  totalInsurance  : Nat          -- I_tot = Σ m.insurance
  totalResidual   : Nat          -- R_tot = Σ m.realizedPool
  totalSurplus    : Nat          -- S_tot = DEX protocol surplus
  totalRewards    : Nat := 0     -- F_tot = Σ m.rewardAccrued (per-market buy-and-burn reward fees!)
  markets         : Nat → Option MarketState
  portfolios      : Nat → Option PortfolioState
  insShares       : Nat → Nat → Nat

/-! ### Core Invariant Predicates -/

/-- EXACT 5-bucket global stock equality: every single atom in `DexVault` belongs to
    exactly one disjoint class (`C_tot`, `I_tot`, `R_tot`, `S_tot`, or `F_tot`)! -/
def DexState.stockExact (st : DexState) : Prop :=
  st.totalCapital + st.totalInsurance + st.totalResidual + st.totalSurplus + st.totalRewards = st.vault

def MarketState.oiBalanced (m : MarketState) : Prop :=
  (m.status = .active ∨ m.status = .windDown) →
    m.oiLong = m.oiShort ∧ m.oiLong ≤ m.maxOi

def MarketState.adlValid (m : MarketState) : Prop :=
  m.oiLong ≤ m.rawBasisLong ∧
  m.oiShort ≤ m.rawBasisShort ∧
  m.adlLong ≤ adlOneNat ∧
  m.adlShort ≤ adlOneNat

def MarketState.solvencyEnvelope (m : MarketState) : Prop :=
  m.maxMoveBps + m.liqFeeBps ≤ m.mmBps ∧
  m.mmBps < m.imBps ∧
  m.imBps ≤ bpsDenNat ∧
  m.exitWindow ≥ minExitWinNat ∧
  m.exitWindow ≤ maxExitWinNat ∧
  m.maxStaleness ≥ 1 ∧
  m.maxStaleness ≤ maxStaleNat

def MarketState.wf (m : MarketState) : Prop :=
  m.oiBalanced ∧ m.adlValid ∧ m.solvencyEnvelope

/-- Per-leg loss containment rule: a loss on leg `j` (with `cachedMm`) can debit AT MOST
    `capital - (totalMm - cachedMm)` from shared `capital`, ALWAYS preserving the maintenance
    margin protecting every OTHER leg in the portfolio! -/
def capAvailableForLeg (capital totalMm legMm : Nat) : Nat :=
  let otherMm := totalMm - legMm
  capital - otherMm

/-- Apply a loss `loss` on leg `leg` inside portfolio `pfl`:
    1. First burns `leg.posPnl` (own leg's positive PnL in Market `m`).
    2. Next debits at most `capAvailableForLeg pfl.capital pfl.totalMm leg.cachedMm`
       from shared `capital` (NEVER touching other legs' maintenance margin!).
    Returns `(newCapital, newLegPosPnl, pnlBurned, capDebited, shortfall)`. -/
def applyContainedLoss (capital totalMm : Nat) (leg : LegState) (loss : Nat) :
    Nat × Nat × Nat × Nat × Nat :=
  let pnlBurned := min loss leg.posPnl
  let rem1      := loss - pnlBurned
  let availCap  := capAvailableForLeg capital totalMm leg.cachedMm
  let capDeb    := min rem1 availCap
  let shortfall := rem1 - capDeb
  (capital - capDeb, leg.posPnl - pnlBurned, pnlBurned, capDeb, shortfall)

/-- Exact per-leg `lockedMm` firewall loss settlement (1-to-1 with `Program.settleAndRefreshLeg`!):
    1. Burns `legPosPnl` first,
    2. Debits shared `freeCap` second,
    3. Debits ONLY this leg's isolated `legLock` third — NEVER any other leg's `lockedMm`!
    Returns `(freeCap', legLock', legPosPnl', freeDeb, lockDeb, shortfall)`. -/
def applyFirewallLoss (freeCap legLock legPosPnl loss : Nat) :
    Nat × Nat × Nat × Nat × Nat × Nat :=
  let pnlBurned := min loss legPosPnl
  let rem1      := loss - pnlBurned
  let freeDeb   := min rem1 freeCap
  let rem2      := rem1 - freeDeb
  let lockDeb   := min rem2 legLock
  let shortfall := rem2 - lockDeb
  (freeCap - freeDeb, legLock - lockDeb, legPosPnl - pnlBurned, freeDeb, lockDeb, shortfall)

/-- Exact zero-sum per-leg `lockedMm` rebalance against `freeCap` (1-to-1 with `Program.syncLegMargins`!):
    Releases excess immediately back to `freeCap` when `newMm < oldLock` (zero ratchet!),
    or tops up `min(newMm - oldLock, freeCap)` from `freeCap` when `newMm > oldLock`.
    Returns `(freeCap', totalLockedMm', legLock')`. -/
def syncLegLock (freeCap totalLockedMm oldLock newMm : Nat) : Nat × Nat × Nat :=
  if oldLock > newMm then
    let rel := oldLock - newMm
    (freeCap + rel, totalLockedMm - rel, newMm)
  else if newMm > oldLock then
    let topUp := min (newMm - oldLock) freeCap
    (freeCap - topUp, totalLockedMm + topUp, oldLock + topUp)
  else
    (freeCap, totalLockedMm, oldLock)

/-- Order-independent resolved payout for one leg in a `Resolved` market. -/
def resolvedLegPayout (m : MarketState) (legPnl : Nat) : Nat :=
  if m.resolvedDen = 0 then 0
  else (legPnl * m.resolvedNum) / m.resolvedDen

/-! ### Pure Multi-Market State Transitions -/

def updateFn {α β : Type} [DecidableEq α] (f : α → β) (k : α) (v : β) : α → β :=
  fun x => if x = k then v else f x

def stepUpdateCreateFee (st : DexState) (signer newFee newAdmin : Nat) : Option DexState :=
  if signer = st.protocolAdmin then
    some { st with
      createFee := newFee
      protocolAdmin := if newAdmin = 0 then st.protocolAdmin else newAdmin }
  else none

def stepCreateMarket (st : DexState)
    (admin initPrice exitWin maxStale imBps mmBps liqBps tradeBps maxMove maxIns maxOi curSlot : Nat) :
    Option DexState :=
  if initPrice > 0 ∧ exitWin ≥ minExitWinNat ∧ exitWin ≤ maxExitWinNat ∧
     maxStale ≥ 1 ∧ maxStale ≤ maxStaleNat ∧
     mmBps > 0 ∧ mmBps < imBps ∧ imBps ≤ bpsDenNat ∧
     maxMove + liqBps ≤ mmBps ∧ maxOi > 0 then
    let mid := st.nextMarketId
    let m : MarketState := {
      marketId := mid, status := .active, marketAdmin := admin,
      markPrice := initPrice, lastOracleSlot := curSlot, windDownSlot := 0,
      exitWindow := exitWin, maxStaleness := maxStale,
      imBps := imBps, mmBps := mmBps, liqFeeBps := liqBps, tradeFeeBps := tradeBps,
      maxMoveBps := maxMove, maxInsDrawBps := maxIns, maxOi := maxOi,
      realizedPool := 0, insurance := 0, feeSurplus := 0, totalPosPnl := 0,
      totalInsShares := 0, oiLong := 0, oiShort := 0,
      rawBasisLong := 0, rawBasisShort := 0, adlLong := adlOneNat, adlShort := adlOneNat,
      resolvedNum := 0, resolvedDen := 0, activeLegs := 0
    }
    some { st with
      nextMarketId := mid + 1
      markets := updateFn st.markets mid (some m) }
  else none

/-- Burn or transfer `marketAdmin` (`role = 0`) or rotate `oracleAuth` (`role = 1`).
    Never modifies balances, OI, positions, or other markets; rejected on tombstoned markets. -/
def stepUpdateMarketAuth (st : DexState) (mid signer role newKey : Nat) : Option DexState := do
  let m ← st.markets mid
  if m.status ≠ .tombstoned ∧ m.marketAdmin ≠ 0 ∧ signer = m.marketAdmin then
    if role = 0 then
      some { st with markets := updateFn st.markets mid (some { m with marketAdmin := newKey }) }
    else if newKey ≠ 0 then
      some { st with markets := updateFn st.markets mid (some m) }
    else none
  else none

def stepDepositCollateral (st : DexState) (pid amount : Nat) : Option DexState := do
  let pfl ← st.portfolios pid
  if amount > 0 then
    let pfl' := { pfl with capital := pfl.capital + amount }
    some { st with
      vault        := st.vault + amount
      totalCapital := st.totalCapital + amount
      portfolios   := updateFn st.portfolios pid (some pfl') }
  else none

def legFreshAt (o : Option LegState) (curSlot : Nat) : Bool :=
  match o with
  | none => true
  | some leg => leg.lastRefreshSlot == curSlot

def stepWithdrawCollateral (st : DexState) (pid amount curSlot : Nat) : Option DexState := do
  let pfl ← st.portfolios pid
  if amount > 0 ∧ pfl.capital ≥ amount ∧ st.totalCapital ≥ amount ∧ st.vault ≥ amount ∧
     pfl.capital - amount ≥ pfl.totalIm ∧
     (List.range st.nextMarketId).all (fun mid => legFreshAt (pfl.legs mid) curSlot) = true then
    let pfl' := { pfl with capital := pfl.capital - amount }
    some { st with
      vault        := st.vault - amount
      totalCapital := st.totalCapital - amount
      portfolios   := updateFn st.portfolios pid (some pfl') }
  else none

def stepDepositInsurance (st : DexState) (mid lp amount : Nat) (donate : Bool := false) : Option DexState := do
  let m ← st.markets mid
  if (m.status = .active ∨ m.status = .windDown) ∧ amount > 0 then
    if donate then
      let m' := { m with insurance := m.insurance + amount }
      some { st with
        vault          := st.vault + amount
        totalInsurance := st.totalInsurance + amount
        markets        := updateFn st.markets mid (some m') }
    else
      let minted :=
        if m.totalInsShares = 0 ∨ m.insurance = 0 then amount
        else (amount * m.totalInsShares) / m.insurance
      if minted = 0 then none
      let m' := { m with insurance := m.insurance + amount, totalInsShares := m.totalInsShares + minted }
      some { st with
        vault          := st.vault + amount
        totalInsurance := st.totalInsurance + amount
        markets        := updateFn st.markets mid (some m')
        insShares      := updateFn st.insShares mid (updateFn (st.insShares mid) lp (st.insShares mid lp + minted)) }
  else none

def stepWithdrawInsurance (st : DexState) (mid lp burnShares : Nat) : Option DexState := do
  let m ← st.markets mid
  let curSh := st.insShares mid lp
  if m.status ≠ .tombstoned ∧ m.oiLong = 0 ∧ m.oiShort = 0 ∧
     m.rawBasisLong = 0 ∧ m.rawBasisShort = 0 ∧
     burnShares > 0 ∧ curSh ≥ burnShares ∧ m.totalInsShares ≥ burnShares then
    let pay := (burnShares * m.insurance) / m.totalInsShares
    if st.totalInsurance < pay ∨ st.vault < pay then none
    let m' := { m with insurance := m.insurance - pay, totalInsShares := m.totalInsShares - burnShares }
    some { st with
      vault          := st.vault - pay
      totalInsurance := st.totalInsurance - pay
      markets        := updateFn st.markets mid (some m')
      insShares      := updateFn st.insShares mid (updateFn (st.insShares mid) lp (curSh - burnShares)) }
  else none

/-- Realize positive PnL on Market `mid`'s leg directly into Portfolio `pid`'s shared `capital`!
    Paid strictly from Market `mid`'s own `realizedPool` `R_m`, preserving exact stock equality
    `C_tot + I_tot + R_tot + S_tot = V` and leaving every other market untouched! -/
def stepRealizeLegPnl (st : DexState) (mid pid : Nat) : Option DexState := do
  let m ← st.markets mid
  let pfl ← st.portfolios pid
  let leg ← pfl.legs mid
  if (m.status = .active ∨ m.status = .windDown) ∧
     leg.posPnl > 0 ∧ m.totalPosPnl ≥ leg.posPnl ∧ st.totalResidual ≥ m.realizedPool then
    let pay := haircutPayout leg.posPnl m.realizedPool m.totalPosPnl
    let m' := { m with
      realizedPool := m.realizedPool - pay
      totalPosPnl  := m.totalPosPnl - leg.posPnl }
    let leg' := { leg with posPnl := 0 }
    let pfl' := { pfl with
      capital := pfl.capital + pay
      legs    := updateFn pfl.legs mid (some leg') }
    some { st with
      totalCapital  := st.totalCapital + pay
      totalResidual := st.totalResidual - pay
      markets       := updateFn st.markets mid (some m')
      portfolios    := updateFn st.portfolios pid (some pfl') }
  else none

/-- Settle a contained loss `loss` on Market `mid`'s leg inside Portfolio `pid`:
    Moves `capDeb` from `pfl.capital` (`C_tot`) directly into `m.realizedPool` (`R_tot`),
    preserving exact `C_tot + I_tot + R_tot + S_tot = V` AND preserving `pfl.capital' ≥ otherMm`! -/
def stepSettleContainedLoss (st : DexState) (mid pid loss : Nat) : Option DexState := do
  let m ← st.markets mid
  let pfl ← st.portfolios pid
  let leg ← pfl.legs mid
  let (cap', pnl', pnlBurned, capDeb, _) := applyContainedLoss pfl.capital pfl.totalMm leg loss
  if (m.status = .active ∨ m.status = .windDown) ∧
     st.totalCapital ≥ capDeb ∧ m.totalPosPnl ≥ pnlBurned then
    let m' := { m with
      realizedPool := m.realizedPool + capDeb
      totalPosPnl  := m.totalPosPnl - pnlBurned }
    let leg' := { leg with posPnl := pnl' }
    let pfl' := { pfl with capital := cap', legs := updateFn pfl.legs mid (some leg') }
    some { st with
      totalCapital  := st.totalCapital - capDeb
      totalResidual := st.totalResidual + capDeb
      markets       := updateFn st.markets mid (some m')
      portfolios    := updateFn st.portfolios pid (some pfl') }
  else none

/-- Bilateral matched open/increase trade on Market `mid` between `pidL ≠ pidS` with optional
    bounded `execPrice` spread (`spreadLToS` / `spreadSToL` transferred strictly between `pL` and `pS`):
    Fees move from `totalCapital` into Market `mid`'s isolated `insurance`; spread transfer leaves
    `totalCapital` unchanged — preserving exact `C_tot + I_tot + R_tot + S_tot = V` and `oiLong = oiShort`! -/
def stepTradeOpen (st : DexState) (mid pidL pidS qty spreadLToS spreadSToL : Nat) : Option DexState := do
  if pidL = pidS then none
  let m ← st.markets mid
  let pL ← st.portfolios pidL
  let pS ← st.portfolios pidS
  let fee := marginReq (marginNotional qty m.markPrice) m.tradeFeeBps
  if m.status = .active ∧ qty > 0 ∧
     m.adlLong = adlOneNat ∧ m.adlShort = adlOneNat ∧
     m.oiLong + qty ≤ m.maxOi ∧ m.oiShort + qty ≤ m.maxOi ∧
     pL.capital + spreadSToL ≥ fee + spreadLToS ∧
     pS.capital + spreadLToS ≥ fee + spreadSToL ∧
     st.totalCapital ≥ 2 * fee then
    let m' := { m with
      insurance     := m.insurance + 2 * fee
      oiLong        := m.oiLong + qty
      oiShort       := m.oiShort + qty
      rawBasisLong  := m.rawBasisLong + qty
      rawBasisShort := m.rawBasisShort + qty }
    let pL' := { pL with capital := pL.capital + spreadSToL - spreadLToS - fee }
    let pS' := { pS with capital := pS.capital + spreadLToS - spreadSToL - fee }
    let ps1 := updateFn st.portfolios pidL (some pL')
    let ps2 := updateFn ps1 pidS (some pS')
    some { st with
      totalCapital   := st.totalCapital - 2 * fee
      totalInsurance := st.totalInsurance + 2 * fee
      markets        := updateFn st.markets mid (some m')
      portfolios     := ps2 }
  else none

/-- Bilateral risk-reducing trade on Market `mid` (works in `Active` & `WindDown`, bypasses IM,
    uses proportional raw-basis reduction on ADL-haircutted sides!). `qty` never exceeds either
    closing leg's `rawBasis` (`Program.tradeCore` bounds it by the tighter `legCloseCapU64`). -/
def stepTradeReduce (st : DexState) (mid pidL pidS qty : Nat) : Option DexState := do
  if pidL = pidS then none
  let m ← st.markets mid
  let pL ← st.portfolios pidL
  let pS ← st.portfolios pidS
  let lL ← pL.legs mid
  let lS ← pS.legs mid
  if (m.status = .active ∨ m.status = .windDown) ∧ qty > 0 ∧
     lL.side = .long ∧ lS.side = .short ∧
     m.oiLong ≥ qty ∧ m.oiShort ≥ qty ∧
     qty ≤ lL.rawBasis ∧ qty ≤ lS.rawBasis then
    let redL := proportionalRawReduction qty lL.rawBasis m.rawBasisLong m.oiLong
    let redS := proportionalRawReduction qty lS.rawBasis m.rawBasisShort m.oiShort
    if m.rawBasisLong < redL ∨ m.rawBasisShort < redS then none
    let oiL' := m.oiLong - qty
    let oiS' := m.oiShort - qty
    let rL'  := m.rawBasisLong - redL
    let rS'  := m.rawBasisShort - redS
    if oiL' > rL' ∨ oiS' > rS' then none
    let m' := { m with
      oiLong        := oiL'
      oiShort       := oiS'
      rawBasisLong  := rL'
      rawBasisShort := rS'
      adlLong       := deriveAdl oiL' rL'
      adlShort      := deriveAdl oiS' rS' }
    let lL' := { lL with rawBasis := lL.rawBasis - redL, side := if lL.rawBasis = redL then .flat else .long }
    let lS' := { lS with rawBasis := lS.rawBasis - redS, side := if lS.rawBasis = redS then .flat else .short }
    let ps1 := updateFn st.portfolios pidL (some { pL with legs := updateFn pL.legs mid (some lL') })
    let ps2 := updateFn ps1 pidS (some { pS with legs := updateFn pS.legs mid (some lS') })
    some { st with markets := updateFn st.markets mid (some m'), portfolios := ps2 }
  else none

/-- Permissionless $O(1)$ liquidation of a distressed leg on Market `mid` inside Portfolio `pid`:
    - Uses `applyContainedLoss` so victim's OTHER legs NEVER lose their `otherMm`!
    - Pays `liqFee` ONLY from remaining available capital above `otherMm` (zero fee seniority!).
    - Draws capped `insDraw ≤ min(shortfall, cap, I_m)` from Market `mid`'s OWN insurance `I_m` into `R_m`.
    - Reduces both sides' OI symmetrically & derives opposing `A_side`!
    - Preserves EXACT global stock equality `C_tot + I_tot + R_tot + S_tot = V`! -/
def stepLiquidate (st : DexState) (mid pid liqFeeCap loss : Nat) : Option DexState := do
  let m ← st.markets mid
  let pfl ← st.portfolios pid
  let leg ← pfl.legs mid
  if m.status = .active ∧ leg.side ≠ .flat ∧ leg.rawBasis > 0 then
    let (cap1, pnl1, pnlBurned, capDeb, shortfall) := applyContainedLoss pfl.capital pfl.totalMm leg loss
    let availForFee := cap1 - (pfl.totalMm - leg.cachedMm)
    let liqFee := min liqFeeCap availForFee
    let cap2 := cap1 - liqFee
    let maxInsDraw := (m.insurance * m.maxInsDrawBps) / bpsDenNat
    let insDraw := min shortfall (min maxInsDraw m.insurance)
    let (eff, oiL', oiS', rL', rS') :=
      match leg.side with
      | .long =>
        let e := min (effectiveQty leg.rawBasis m.adlLong) (min m.oiLong m.oiShort)
        (e, m.oiLong - e, m.oiShort - e, m.rawBasisLong - leg.rawBasis, m.rawBasisShort)
      | .short =>
        let e := min (effectiveQty leg.rawBasis m.adlShort) (min m.oiLong m.oiShort)
        (e, m.oiLong - e, m.oiShort - e, m.rawBasisLong, m.rawBasisShort - leg.rawBasis)
      | .flat => (0, m.oiLong, m.oiShort, m.rawBasisLong, m.rawBasisShort)
    if st.totalCapital ≥ capDeb + liqFee ∧ st.vault ≥ liqFee ∧
       st.totalInsurance ≥ insDraw ∧ m.totalPosPnl ≥ pnlBurned ∧
       (leg.side = .long → m.rawBasisLong ≥ leg.rawBasis ∧ oiL' ≤ rL') ∧
       (leg.side = .short → m.rawBasisShort ≥ leg.rawBasis ∧ oiS' ≤ rS') ∧
       eff > 0 then
      let m' := { m with
        realizedPool  := m.realizedPool + capDeb + insDraw
        insurance     := m.insurance - insDraw
        totalPosPnl   := m.totalPosPnl - pnlBurned
        oiLong        := oiL'
        oiShort       := oiS'
        rawBasisLong  := rL'
        rawBasisShort := rS'
        adlLong       := deriveAdl oiL' rL'
        adlShort      := deriveAdl oiS' rS' }
      let leg' := { leg with side := .flat, rawBasis := 0, posPnl := pnl1, cachedMm := 0, cachedIm := 0 }
      let pfl' := { pfl with
        capital := cap2
        totalMm := pfl.totalMm - leg.cachedMm
        totalIm := pfl.totalIm - leg.cachedIm
        legs    := updateFn pfl.legs mid (some leg') }
      some { st with
        vault          := st.vault - liqFee
        totalCapital   := st.totalCapital - capDeb - liqFee
        totalInsurance := st.totalInsurance - insDraw
        totalResidual  := st.totalResidual + capDeb + insDraw
        markets        := updateFn st.markets mid (some m')
        portfolios     := updateFn st.portfolios pid (some pfl') }
    else none
  else none

/-- Clear a post-ADL dead leg once its side's `oi = 0`, resetting `adl = ADL_ONE` when `rawBasis = 0`! -/
def stepClearDeadLeg (st : DexState) (mid pid : Nat) : Option DexState := do
  let m ← st.markets mid
  let pfl ← st.portfolios pid
  let leg ← pfl.legs mid
  if (m.status = .active ∨ m.status = .windDown) ∧ leg.side ≠ .flat ∧ leg.rawBasis > 0 then
    match leg.side with
    | .long =>
      if m.oiLong = 0 ∧ m.rawBasisLong ≥ leg.rawBasis then
        let rL' := m.rawBasisLong - leg.rawBasis
        let m' := { m with rawBasisLong := rL', adlLong := deriveAdl 0 rL', activeLegs := m.activeLegs - 1 }
        let leg' := { leg with side := .flat, rawBasis := 0, cachedMm := 0, cachedIm := 0 }
        let pfl' := { pfl with totalMm := pfl.totalMm - leg.cachedMm, totalIm := pfl.totalIm - leg.cachedIm,
                               legs := updateFn pfl.legs mid (some leg') }
        some { st with markets := updateFn st.markets mid (some m'), portfolios := updateFn st.portfolios pid (some pfl') }
      else none
    | .short =>
      if m.oiShort = 0 ∧ m.rawBasisShort ≥ leg.rawBasis then
        let rS' := m.rawBasisShort - leg.rawBasis
        let m' := { m with rawBasisShort := rS', adlShort := deriveAdl 0 rS', activeLegs := m.activeLegs - 1 }
        let leg' := { leg with side := .flat, rawBasis := 0, cachedMm := 0, cachedIm := 0 }
        let pfl' := { pfl with totalMm := pfl.totalMm - leg.cachedMm, totalIm := pfl.totalIm - leg.cachedIm,
                               legs := updateFn pfl.legs mid (some leg') }
        some { st with markets := updateFn st.markets mid (some m'), portfolios := updateFn st.portfolios pid (some pfl') }
      else none
    | .flat => none
  else none

/-- Permissionless `ForceClosePair` in `WindDown` after `exitWindow`: strictly reduces `oiLong = oiShort`! -/
def stepForceClosePair (st : DexState) (mid pidL pidS curSlot : Nat) : Option DexState := do
  if pidL = pidS then none
  let m ← st.markets mid
  let pL ← st.portfolios pidL
  let pS ← st.portfolios pidS
  let lL ← pL.legs mid
  let lS ← pS.legs mid
  if m.status = .windDown ∧ curSlot ≥ m.windDownSlot + m.exitWindow ∧
     lL.side = .long ∧ lS.side = .short ∧ lL.rawBasis > 0 ∧ lS.rawBasis > 0 then
    let effL := max 1 (effectiveQty lL.rawBasis m.adlLong)
    let effS := max 1 (effectiveQty lS.rawBasis m.adlShort)
    let q := min effL (min effS (min m.oiLong m.oiShort))
    if q = 0 then none
    let redL := proportionalRawReduction q lL.rawBasis m.rawBasisLong m.oiLong
    let redS := proportionalRawReduction q lS.rawBasis m.rawBasisShort m.oiShort
    if m.rawBasisLong < redL ∨ m.rawBasisShort < redS then none
    let oiL' := m.oiLong - q
    let oiS' := m.oiShort - q
    let rL'  := m.rawBasisLong - redL
    let rS'  := m.rawBasisShort - redS
    if oiL' > rL' ∨ oiS' > rS' then none
    let m' := { m with
      oiLong := oiL', oiShort := oiS',
      rawBasisLong := rL', rawBasisShort := rS',
      adlLong := deriveAdl oiL' rL', adlShort := deriveAdl oiS' rS' }
    let lL' := { lL with rawBasis := lL.rawBasis - redL, side := if lL.rawBasis = redL then .flat else .long }
    let lS' := { lS with rawBasis := lS.rawBasis - redS, side := if lS.rawBasis = redS then .flat else .short }
    let ps1 := updateFn st.portfolios pidL (some { pL with legs := updateFn pL.legs mid (some lL') })
    let ps2 := updateFn ps1 pidS (some { pS with legs := updateFn pS.legs mid (some lS') })
    some { st with markets := updateFn st.markets mid (some m'), portfolios := ps2 }
  else none

/-- Strict `ResolveMarket`: requires `oi = 0 ∧ rawBasis = 0 ∧ activeLegs = 0` so EVERY leg settled first! -/
def stepResolveMarket (st : DexState) (mid : Nat) : Option DexState := do
  let m ← st.markets mid
  if m.status = .windDown ∧ m.oiLong = 0 ∧ m.oiShort = 0 ∧
     m.rawBasisLong = 0 ∧ m.rawBasisShort = 0 ∧ m.activeLegs = 0 then
    let m' := { m with
      status      := .resolved
      resolvedNum := min m.realizedPool m.totalPosPnl
      resolvedDen := m.totalPosPnl }
    some { st with markets := updateFn st.markets mid (some m') }
  else none

/-- Order-independent resolved claim: credits `resolvedLegPayout` from `R_m` directly into `pfl.capital`! -/
def stepClaimResolved (st : DexState) (mid pid : Nat) : Option DexState := do
  let m ← st.markets mid
  let pfl ← st.portfolios pid
  let leg ← pfl.legs mid
  if m.status = .resolved ∧ leg.side = .flat ∧ leg.rawBasis = 0 ∧
     m.totalPosPnl ≥ leg.posPnl ∧ st.totalResidual ≥ m.realizedPool then
    let pay := resolvedLegPayout m leg.posPnl
    if m.realizedPool < pay then none
    let m' := { m with
      realizedPool := m.realizedPool - pay
      totalPosPnl  := m.totalPosPnl - leg.posPnl }
    let pfl' := { pfl with
      capital := pfl.capital + pay
      legs    := updateFn pfl.legs mid none }
    some { st with
      totalCapital  := st.totalCapital + pay
      totalResidual := st.totalResidual - pay
      markets       := updateFn st.markets mid (some m')
      portfolios    := updateFn st.portfolios pid (some pfl') }
  else none

def stepTombstone (st : DexState) (mid : Nat) : Option DexState := do
  let m ← st.markets mid
  if m.status = .resolved ∧ m.oiLong = 0 ∧ m.oiShort = 0 ∧
     m.rawBasisLong = 0 ∧ m.rawBasisShort = 0 ∧
     m.insurance = 0 ∧ m.activeLegs = 0 ∧ m.totalPosPnl = 0 then
    some { st with markets := updateFn st.markets mid (some { m with status := .tombstoned }) }
  else none

/-- Owner-only collateral withdrawal (delegates CANNOT withdraw!). -/
def stepWithdrawCollateralAuth (st : DexState) (pid signer amount curSlot : Nat) : Option DexState := do
  let pfl ← st.portfolios pid
  if signer = pfl.owner then
    stepWithdrawCollateral st pid amount curSlot
  else none

/-- Aggregate-sum coherence predicate over finite lists of active portfolio & market IDs. -/
def getCap (ps : Nat → Option PortfolioState) (pid : Nat) : Nat :=
  match ps pid with | some p => p.capital | none => 0

def getIns (ms : Nat → Option MarketState) (mid : Nat) : Nat :=
  match ms mid with | some m => m.insurance | none => 0

def getRes (ms : Nat → Option MarketState) (mid : Nat) : Nat :=
  match ms mid with | some m => m.realizedPool | none => 0

def getRew (ms : Nat → Option MarketState) (mid : Nat) : Nat :=
  match ms mid with | some m => m.rewardAccrued | none => 0

def sumCaps (st : DexState) (pids : List Nat) : Nat := (pids.map (getCap st.portfolios)).sum
def sumIns  (st : DexState) (mids : List Nat) : Nat := (mids.map (getIns st.markets)).sum
def sumRes  (st : DexState) (mids : List Nat) : Nat := (mids.map (getRes st.markets)).sum
def sumRew  (st : DexState) (mids : List Nat) : Nat := (mids.map (getRew st.markets)).sum

def DexState.coherent (st : DexState) (mids pids : List Nat) : Prop :=
  st.stockExact ∧
  st.totalCapital = sumCaps st pids ∧
  st.totalInsurance = sumIns st mids ∧
  st.totalResidual = sumRes st mids ∧
  st.totalRewards = sumRew st mids

/-- HLP / Counterparty Liquidation Takeover (ZERO ADL!): transfers `rawClose` from victim `pid`
    to well-collateralized liquidator `liqPid ≠ pid`, preserving `oiLong == oiShort` and `stockExact`! -/
def stepLiquidateTakeover (st : DexState) (mid pid liqPid rawClose liqFeeCap loss : Nat) : Option DexState := do
  if pid = liqPid then none
  let m ← st.markets mid
  let pfl ← st.portfolios pid
  let liqPfl ← st.portfolios liqPid
  let leg ← pfl.legs mid
  if m.status = .active ∧ leg.side ≠ .flat ∧ rawClose > 0 ∧ rawClose ≤ leg.rawBasis ∧
     m.adlLong = adlOneNat ∧ m.adlShort = adlOneNat then
    let (cap1, pnl1, pnlBurned, capDeb, shortfall) := applyContainedLoss pfl.capital pfl.totalMm leg loss
    let availForFee := cap1 - (pfl.totalMm - leg.cachedMm)
    let liqFee := min liqFeeCap availForFee
    let cap2 := cap1 - liqFee
    let maxInsDraw := (m.insurance * m.maxInsDrawBps) / bpsDenNat
    let insDraw := min shortfall (min maxInsDraw m.insurance)
    if st.totalCapital ≥ capDeb + liqFee ∧ st.vault ≥ liqFee ∧
       st.totalInsurance ≥ insDraw ∧ m.totalPosPnl ≥ pnlBurned then
      let m' := { m with
        realizedPool := m.realizedPool + capDeb + insDraw
        insurance    := m.insurance - insDraw
        totalPosPnl  := m.totalPosPnl - pnlBurned }
      let remRaw := leg.rawBasis - rawClose
      let leg' := { leg with rawBasis := remRaw, side := if remRaw = 0 then .flat else leg.side, posPnl := pnl1 }
      let pfl' := { pfl with capital := cap2, legs := updateFn pfl.legs mid (some leg') }
      let ps1 := updateFn st.portfolios pid (some pfl')
      let ps2 := updateFn ps1 liqPid (some liqPfl)
      some { st with
        vault          := st.vault - liqFee
        totalCapital   := st.totalCapital - capDeb - liqFee
        totalInsurance := st.totalInsurance - insDraw
        totalResidual  := st.totalResidual + capDeb + insDraw
        markets        := updateFn st.markets mid (some m')
        portfolios     := ps2 }
    else none
  else none

/-- Bounded `execPrice` spread check for `Trade(mode=1)` reduce: payer MUST keep `capital - spread ≥ newTotalMm`! -/
def stepTradeReduceWithSpread (st : DexState) (mid pidL pidS qty spreadLToS spreadSToL newMmL newMmS : Nat) :
    Option DexState := do
  if pidL = pidS then none
  let pL ← st.portfolios pidL
  let pS ← st.portfolios pidS
  if pL.capital + spreadSToL ≥ spreadLToS ∧
     pS.capital + spreadLToS ≥ spreadSToL ∧
     pL.capital + spreadSToL - spreadLToS ≥ newMmL ∧
     pS.capital + spreadLToS - spreadSToL ≥ newMmS then
    let st1 ← stepTradeReduce st mid pidL pidS qty
    let pL1 ← st1.portfolios pidL
    let pS1 ← st1.portfolios pidS
    let ps1 := updateFn st1.portfolios pidL (some { pL1 with capital := pL.capital + spreadSToL - spreadLToS })
    let ps2 := updateFn ps1 pidS (some { pS1 with capital := pS.capital + spreadLToS - spreadSToL })
    some { st1 with portfolios := ps2 }
  else none

/-- Raw-basis minted when opening `qty` effective OI on a side with `(oiSide, rawSide)`.
    On partially-ADL'd sides (`0 < oiSide < rawSide`), mints `max(qty, ⌈qty * rawSide / oiSide⌉)`. -/
def postAdlRawAdd (qty oiSide rawSide : Nat) : Nat :=
  if rawSide = 0 ∨ oiSide = rawSide then qty
  else max qty (mulDivUp qty rawSide oiSide)

/-- Post-ADL bilateral open (`Trade` mode = 0): allows opening even when `0 < oiSide < rawSide`
    (rejecting only 100%-wiped-out sides `oiSide = 0 ∧ rawSide > 0`), minting `postAdlRawAdd`! -/
def stepTradeOpenPostAdl (st : DexState) (mid pidL pidS qty spreadLToS spreadSToL : Nat) : Option DexState := do
  if pidL = pidS then none
  let m ← st.markets mid
  let pL ← st.portfolios pidL
  let pS ← st.portfolios pidS
  let fee := marginReq (marginNotional qty m.markPrice) m.tradeFeeBps
  let rewFee := (2 * fee * m.rewardBps) / bpsDenNat
  let insFee := 2 * fee - rewFee
  if m.status = .active ∧ qty > 0 ∧ m.rewardBps ≤ bpsDenNat ∧
     (m.rawBasisLong = 0 ∨ m.oiLong > 0) ∧
     (m.rawBasisShort = 0 ∨ m.oiShort > 0) ∧
     m.oiLong + qty ≤ m.maxOi ∧ m.oiShort + qty ≤ m.maxOi ∧
     pL.capital + spreadSToL ≥ fee + spreadLToS ∧
     pS.capital + spreadLToS ≥ fee + spreadSToL ∧
     st.totalCapital ≥ 2 * fee then
    let rAddL := postAdlRawAdd qty m.oiLong m.rawBasisLong
    let rAddS := postAdlRawAdd qty m.oiShort m.rawBasisShort
    let oiL' := m.oiLong + qty
    let oiS' := m.oiShort + qty
    let rL'  := m.rawBasisLong + rAddL
    let rS'  := m.rawBasisShort + rAddS
    let m' := { m with
      insurance     := m.insurance + insFee
      rewardAccrued := m.rewardAccrued + rewFee
      oiLong        := oiL'
      oiShort       := oiS'
      rawBasisLong  := rL'
      rawBasisShort := rS'
      adlLong       := deriveAdl oiL' rL'
      adlShort      := deriveAdl oiS' rS' }
    let pL' := { pL with capital := pL.capital + spreadSToL - spreadLToS - fee }
    let pS' := { pS with capital := pS.capital + spreadLToS - spreadSToL - fee }
    let ps1 := updateFn st.portfolios pidL (some pL')
    let ps2 := updateFn ps1 pidS (some pS')
    some { st with
      totalCapital   := st.totalCapital - 2 * fee
      totalInsurance := st.totalInsurance + insFee
      totalRewards   := st.totalRewards + rewFee
      markets        := updateFn st.markets mid (some m')
      portfolios     := ps2 }
  else none

/-- Same-side position hand-off (`Trade` mode = 2 Long→Long / mode = 3 Short→Short):
    transfers `rawXfer` within the same side between `pidSell ≠ pidBuy`, leaving
    `oiLong`, `oiShort`, `rawBasisLong`, `rawBasisShort`, `adlLong`, `adlShort` BIT-FOR-BIT INVARIANT! -/
def stepTradeHandoff (st : DexState) (mid pidSell pidBuy qty spreadBuyToSell spreadSellToBuy : Nat) :
    Option DexState := do
  if pidSell = pidBuy then none
  let m ← st.markets mid
  let pSell ← st.portfolios pidSell
  let pBuy  ← st.portfolios pidBuy
  let lSell ← pSell.legs mid
  if (m.status = .active ∨ m.status = .windDown) ∧ qty > 0 ∧
     lSell.side ≠ .flat ∧ lSell.rawBasis > 0 ∧
     (lSell.side = .long → m.oiLong ≥ qty) ∧
     (lSell.side = .short → m.oiShort ≥ qty) ∧
     pBuy.capital + spreadSellToBuy ≥ spreadBuyToSell ∧
     pSell.capital + spreadBuyToSell ≥ spreadSellToBuy then
    let (oiSide, rMktSide) :=
      if lSell.side = .long then (m.oiLong, m.rawBasisLong) else (m.oiShort, m.rawBasisShort)
    let rawXfer := proportionalRawReduction qty lSell.rawBasis rMktSide oiSide
    if rawXfer = 0 ∨ rawXfer > lSell.rawBasis then none
    let remSell := lSell.rawBasis - rawXfer
    let lSell' := { lSell with rawBasis := remSell, side := if remSell = 0 then .flat else lSell.side }
    let pSell' := { pSell with
      capital := pSell.capital + spreadBuyToSell - spreadSellToBuy
      legs    := updateFn pSell.legs mid (some lSell') }
    let pBuy' := { pBuy with
      capital := pBuy.capital + spreadSellToBuy - spreadBuyToSell }
    let ps1 := updateFn st.portfolios pidSell (some pSell')
    let ps2 := updateFn ps1 pidBuy (some pBuy')
    some { st with portfolios := ps2 }
  else none

/-- Post-ADL Liquidation Takeover (`Liquidate` mode = 1): transfers `rawClose` within the same side
    even during active partial ADL (`oiSide > 0`), leaving `oi`/`rawBasis`/`adl` BIT-FOR-BIT INVARIANT! -/
def stepLiquidateTakeoverPostAdl (st : DexState) (mid pid liqPid rawClose liqFeeCap loss : Nat) : Option DexState := do
  if pid = liqPid then none
  let m ← st.markets mid
  let pfl ← st.portfolios pid
  let liqPfl ← st.portfolios liqPid
  let leg ← pfl.legs mid
  if m.status = .active ∧ leg.side ≠ .flat ∧ rawClose > 0 ∧ rawClose ≤ leg.rawBasis ∧
     (leg.side = .long → m.oiLong > 0) ∧ (leg.side = .short → m.oiShort > 0) then
    let (cap1, pnl1, pnlBurned, capDeb, shortfall) := applyContainedLoss pfl.capital pfl.totalMm leg loss
    let availForFee := cap1 - (pfl.totalMm - leg.cachedMm)
    let liqFee := min liqFeeCap availForFee
    let cap2 := cap1 - liqFee
    let maxInsDraw := (m.insurance * m.maxInsDrawBps) / bpsDenNat
    let insDraw := min shortfall (min maxInsDraw m.insurance)
    if st.totalCapital ≥ capDeb + liqFee ∧ st.vault ≥ liqFee ∧
       st.totalInsurance ≥ insDraw ∧ m.totalPosPnl ≥ pnlBurned then
      let m' := { m with
        realizedPool := m.realizedPool + capDeb + insDraw
        insurance    := m.insurance - insDraw
        totalPosPnl  := m.totalPosPnl - pnlBurned }
      let remRaw := leg.rawBasis - rawClose
      let leg' := { leg with rawBasis := remRaw, side := if remRaw = 0 then .flat else leg.side, posPnl := pnl1 }
      let pfl' := { pfl with capital := cap2, legs := updateFn pfl.legs mid (some leg') }
      let ps1 := updateFn st.portfolios pid (some pfl')
      let ps2 := updateFn ps1 liqPid (some liqPfl)
      some { st with
        vault          := st.vault - liqFee
        totalCapital   := st.totalCapital - capDeb - liqFee
        totalInsurance := st.totalInsurance - insDraw
        totalResidual  := st.totalResidual + capDeb + insDraw
        markets        := updateFn st.markets mid (some m')
        portfolios     := ps2 }
    else none
  else none

/-- Same-slot freshness + solvency-checked liquidation gate (A1 Fix):
    requires EVERY open leg of `pid` to be refreshed at `curSlot`, AND requires
    `shortfall > 0 ∨ cap1 + pnl1 < pfl.totalMm`! -/
def stepLiquidateChecked (st : DexState) (mid pid curSlot liqFeeCap loss : Nat) : Option DexState := do
  let pfl ← st.portfolios pid
  let leg ← pfl.legs mid
  let (cap1, pnl1, _, _, shortfall) := applyContainedLoss pfl.capital pfl.totalMm leg loss
  if (List.range st.nextMarketId).all (fun k => legFreshAt (pfl.legs k) curSlot) = true ∧
     (shortfall > 0 ∨ cap1 + pnl1 < pfl.totalMm) then
    stepLiquidate st mid pid liqFeeCap loss
  else none

/-- Sweep orphan donated insurance (`totalInsShares = 0`) on a `Resolved` market into `totalSurplus`,
    preserving exact `C_tot + I_tot + R_tot + S_tot = V` and enabling clean market tombstoning. -/
def stepSweepOrphanInsurance (st : DexState) (mid : Nat) : Option DexState := do
  let m ← st.markets mid
  if m.status = .resolved ∧ m.totalPosPnl = 0 ∧ m.totalInsShares = 0 ∧
     m.insurance > 0 ∧ st.totalInsurance ≥ m.insurance then
    let m' := { m with insurance := 0 }
    some { st with
      totalInsurance := st.totalInsurance - m.insurance
      totalSurplus   := st.totalSurplus + m.insurance
      markets        := updateFn st.markets mid (some m') }
  else none

/-- Permissionless `StartWindDown` gate (adminless/stale path): succeeds iff active and `curSlot - lastOracleSlot > maxStaleness`. -/
def canPermissionlessWindDown (m : MarketState) (curSlot : Nat) : Prop :=
  m.status = .active ∧ (curSlot - m.lastOracleSlot) > m.maxStaleness

/-- `RefreshLeg` oracle-freshness gate: succeeds immediately when active with fresh oracle OR already in `WindDown`. -/
def canRefreshAtSlot (m : MarketState) (curSlot : Nat) : Prop :=
  (m.status = .active ∧ (curSlot - m.lastOracleSlot) ≤ m.maxStaleness) ∨ m.status = .windDown

/-- Exact capital-backed `reservedMm` update (`syncLegMargins` in `Program.lean`).
    Maintains the unconditional inductive invariant `totalReservedMm ≤ capital` and prevents
    any untrusted market from inflating its MM reservation to shield collateral from other legs. -/
def syncReservedMm (cap totRes oldRes newTotMm newMm : Nat) : Nat × Nat :=
  let baseRes   := totRes - oldRes
  let availRes  := cap - baseRes
  let capTarget := if cap ≥ newTotMm then newMm else min oldRes newMm
  let newRes    := min capTarget availRes
  (newRes, baseRes + newRes)

/-- One arbitrary adversarial step on an untrusted `RUG` leg `(rugLoss, rugFee, newTotMm, newRugMm)`
    updating `(cap, totRes, rugRes)` while preserving every other leg's `reservedMm`. -/
def stepRugReservedState (cap totRes rugRes rugLoss rugFee newTotMm newRugMm : Nat) : Nat × Nat × Nat :=
  let otherRes := totRes - rugRes
  let avail1   := cap - otherRes
  let capDeb   := min rugLoss avail1
  let cap1     := cap - capDeb
  let avail2   := cap1 - otherRes
  let feeDeb   := min rugFee avail2
  let cap2     := cap1 - feeDeb
  let (rugRes', totRes') := syncReservedMm cap2 totRes rugRes newTotMm newRugMm
  (cap2, totRes', rugRes')

/-! ### Gap #5 Sync: v2.1 Full-Capital Settlement, Cumulative `I_m`-Fronting, `SweepSurplus`, & Clamped Oracle Step -/

/-- Exact v2.1 Full-Capital Loss Settlement (`Program.settleAndRefreshLeg` + `creditMarketFromLoser`
    + `writeOffShortfall`):
    1. Debits FULL `pfl.capital` (`capDeb = min rem1 pfl.capital`, NEVER shielding capital behind other legs!).
    2. Repays `m.insFronted` senior into `m.insurance` (`I_m`), remainder to `m.realizedPool` (`R_m`).
    3. Writes off any uncollectible fronted bad debt `wo = min (rem1 - capDeb) (m.insFronted - repay)`. -/
def stepSettleFullCapitalLoss (st : DexState) (mid pid loss : Nat) : Option DexState := do
  let m ← st.markets mid
  let pfl ← st.portfolios pid
  let leg ← pfl.legs mid
  let pnlBurned := min loss leg.posPnl
  let rem1      := loss - pnlBurned
  let capDeb    := min rem1 pfl.capital
  let repay     := min capDeb m.insFronted
  let toR       := capDeb - repay
  let sfRaw     := rem1 - capDeb
  let wo        := min sfRaw (m.insFronted - repay)
  if (m.status = .active ∨ m.status = .windDown) ∧
     st.totalCapital ≥ capDeb ∧ m.totalPosPnl ≥ pnlBurned then
    let m' := { m with
      insurance    := m.insurance + repay
      insFronted   := m.insFronted - repay - wo
      realizedPool := m.realizedPool + toR
      totalPosPnl  := m.totalPosPnl - pnlBurned }
    let leg' := { leg with posPnl := leg.posPnl - pnlBurned }
    let pfl' := { pfl with capital := pfl.capital - capDeb, legs := updateFn pfl.legs mid (some leg') }
    some { st with
      totalCapital   := st.totalCapital - capDeb
      totalInsurance := st.totalInsurance + repay
      totalResidual  := st.totalResidual + toR
      markets        := updateFn st.markets mid (some m')
      portfolios     := updateFn st.portfolios pid (some pfl') }
  else none

/-- Exact v2.1 `I_m`-Contained Cross-PnL Fronting (`Program.realizeWinnerPnl` + `realizeFrontedPnl`
    with Gap #2 cumulative NAV-based cap `availIns = min(ins, floor((ins + insFronted) * maxFrontBps / 10000) - insFronted)`). -/
def stepRealizeFrontedPnl (st : DexState) (mid pid : Nat) : Option DexState := do
  let m ← st.markets mid
  let pfl ← st.portfolios pid
  let leg ← pfl.legs mid
  let nav      := m.insurance + m.insFronted
  let capIns   := (nav * m.maxFrontBps) / bpsDenNat
  let availIns := min (capIns - m.insFronted) m.insurance
  if m.status = .active ∧ m.adlLong = adlOneNat ∧ m.adlShort = adlOneNat ∧
     m.maxFrontBps > 0 ∧ m.maxFrontBps ≤ m.maxInsDrawBps ∧
     leg.posPnl > 0 ∧ m.totalPosPnl ≥ leg.posPnl ∧
     m.realizedPool + availIns ≥ m.totalPosPnl ∧
     st.totalResidual ≥ min leg.posPnl m.realizedPool ∧
     st.totalInsurance ≥ leg.posPnl - min leg.posPnl m.realizedPool then
    let fromR   := min leg.posPnl m.realizedPool
    let fromIns := leg.posPnl - fromR
    let m' := { m with
      realizedPool := m.realizedPool - fromR
      insurance    := m.insurance - fromIns
      insFronted   := m.insFronted + fromIns
      totalPosPnl  := m.totalPosPnl - leg.posPnl }
    let leg' := { leg with posPnl := 0 }
    let pfl' := { pfl with capital := pfl.capital + leg.posPnl, legs := updateFn pfl.legs mid (some leg') }
    some { st with
      totalCapital   := st.totalCapital + leg.posPnl
      totalResidual  := st.totalResidual - fromR
      totalInsurance := st.totalInsurance - fromIns
      markets        := updateFn st.markets mid (some m')
      portfolios     := updateFn st.portfolios pid (some pfl') }
  else none

/-- Exact v2.1 `SweepSurplus` (`Program.handleSweepSurplus`): admin sweeps `sweepAmt ≤ S_tot`,
    leaving `C_tot`, `I_tot`, `R_tot`, and all markets/portfolios bit-for-bit invariant. -/
def stepSweepSurplus (st : DexState) (signer sweepAmt : Nat) : Option DexState :=
  if signer = st.protocolAdmin ∧ sweepAmt > 0 ∧ sweepAmt ≤ st.totalSurplus ∧ sweepAmt ≤ st.vault then
    some { st with
      vault        := st.vault - sweepAmt
      totalSurplus := st.totalSurplus - sweepAmt }
  else none

/-- Exact v2.1 Clamped `UpdateOracle` (`Program.handleUpdateOracle` with per-slot rate limit):
    updates `markPrice` and `lastOracleSlot` within `maxMoveBps`, leaving all vault/pool balances
    bit-for-bit unchanged! -/
def stepUpdateOracle (st : DexState) (mid newPrice fundE6 curSlot : Nat) : Option DexState := do
  let m ← st.markets mid
  let diff := if newPrice ≥ m.markPrice then newPrice - m.markPrice else m.markPrice - newPrice
  if m.status = .active ∧ curSlot > m.lastOracleSlot ∧ newPrice > 0 ∧
     diff + fundE6 ≤ (m.markPrice * m.maxMoveBps) / bpsDenNat then
    let m' := { m with markPrice := newPrice, lastOracleSlot := curSlot }
    some { st with markets := updateFn st.markets mid (some m') }
  else none

/-- Exact v2.1 Hardened `Liquidate` (`Program.handleLiquidate` Bug 1B full-capital + `cap == 0` guard
    + Bug 1C bankrupt full-close). -/
def stepLiquidateFullCap (st : DexState) (mid pid liqFeeCap loss : Nat) : Option DexState := do
  let m ← st.markets mid
  let pfl ← st.portfolios pid
  let leg ← pfl.legs mid
  let pnlBurned := min loss leg.posPnl
  let rem1      := loss - pnlBurned
  let capDeb    := min rem1 pfl.capital
  let cap1      := pfl.capital - capDeb
  let repay     := min capDeb m.insFronted
  let toR       := capDeb - repay
  let sfRaw     := rem1 - capDeb
  let wo        := min sfRaw (m.insFronted - repay)
  let shortfall := sfRaw - wo
  let liqFee    := min liqFeeCap cap1
  let cap2      := cap1 - liqFee
  let insAfterRepay := m.insurance + repay
  let maxDraw   := (insAfterRepay * m.maxInsDrawBps) / bpsDenNat
  let insDraw   := if shortfall > 0 ∧ cap1 = 0 then min shortfall (min maxDraw insAfterRepay) else 0
  if m.status = .active ∧ leg.side ≠ .flat ∧ leg.rawBasis > 0 ∧
     st.totalCapital ≥ capDeb + liqFee ∧ st.vault ≥ liqFee ∧
     st.totalInsurance + repay ≥ insDraw ∧ m.totalPosPnl ≥ pnlBurned then
    let m' := { m with
      insurance    := insAfterRepay - insDraw
      insFronted   := m.insFronted - repay - wo
      realizedPool := m.realizedPool + toR + insDraw
      totalPosPnl  := m.totalPosPnl - pnlBurned }
    let leg' := { leg with side := .flat, rawBasis := 0, posPnl := leg.posPnl - pnlBurned, cachedMm := 0, cachedIm := 0 }
    let pfl' := { pfl with
      capital := cap2
      totalMm := pfl.totalMm - leg.cachedMm
      totalIm := pfl.totalIm - leg.cachedIm
      legs    := updateFn pfl.legs mid (some leg') }
    some { st with
      vault          := st.vault - liqFee
      totalCapital   := st.totalCapital - capDeb - liqFee
      totalInsurance := st.totalInsurance + repay - insDraw
      totalResidual  := st.totalResidual + toR + insDraw
      markets        := updateFn st.markets mid (some m')
      portfolios     := updateFn st.portfolios pid (some pfl') }
  else none

/-- Exact `ClaimReward` (`Program.handleClaimReward`): ONLY market `mid`'s immutable
    `rewardRecipient` can withdraw `claimAmt ≤ m.rewardAccrued` out of `DexVault`,
    leaving `C_tot`, `I_tot`, `R_tot`, `S_tot`, and EVERY other market's `F_{m'}` unchanged! -/
def stepClaimReward (st : DexState) (mid signer reqAmt : Nat) : Option DexState := do
  let m ← st.markets mid
  let claimAmt := if reqAmt = 0 then m.rewardAccrued else reqAmt
  if m.rewardRecipient ≠ 0 ∧ signer = m.rewardRecipient ∧
     claimAmt > 0 ∧ claimAmt ≤ m.rewardAccrued ∧
     claimAmt ≤ st.totalRewards ∧ claimAmt ≤ st.vault then
    let m' := { m with rewardAccrued := m.rewardAccrued - claimAmt }
    some { st with
      vault        := st.vault - claimAmt
      totalRewards := st.totalRewards - claimAmt
      markets      := updateFn st.markets mid (some m') }
  else none

end Percolator.Spec
