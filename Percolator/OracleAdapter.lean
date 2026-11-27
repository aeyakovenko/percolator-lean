/-
  Percolator.OracleAdapter
  Minimal, formally verified permissionless external oracle + on-chain funding bridge
  that composes with `percolator-lean` via CPI (`sol_invoke_signed_c`).

  Zero changes to core `percolator-lean`:
  - Supports 4 native on-chain feed formats (all with pinned account key & owner):
    * `0` (`Custom`)      : 32-byte `FEED` record (`magic`, `price`, `conf`, `publishSlot`)
    * `1` (`PythV2`)      : Official Pyth Pull Oracle `PriceUpdateV2` (Anchor disc, `Full`
                            verification, optional 32-byte `feed_id` pinning, `i64`/`i32`
                            exponent scaling to E6, `publish_time` vs `Clock.unix_timestamp`)
    * `2` (`Chainlink`)   : Official Chainlink Solana OCR2 `Transmissions` (Anchor disc,
                            `version == 2`, ring-buffer `live_cursor`, `i128` decimals → E6)
    * `3` (`Switchboard`) : Official Switchboard On-Demand `PullFeedAccountData` (Anchor disc,
                            `CurrentResult` at byte 2264, `PRECISION = 18` 128-bit scaling → E6,
                            `num_samples >= 1`, `std_dev` confidence bound)
  - Supports optional 2-leg composite ratio pricing (`base / quote`, e.g. `STOXX/SOL`, `BTC/ETH`)
    across any combination of feed formats!
  - Supports optional on-chain EWMA smoothing & Hybrid After-Hours mode (`FLAG_HYBRID_AH`):
    * Live hours: updates `ewmaPrice` via exact integer EWMA `(prev*(10000-α) + spot*α) / 10000`.
    * After-hours (base feed stale/wide-conf, e.g. closed equity markets): carries `ewmaPrice`
      automatically while STILL repricing 24/7 against a live `quoteFeed` (e.g. `STOXX/SOL`)!
    * Optional admin-signed `PushEwmaMark` (`op = 3`) bounded per-slot by `±ewmaMaxDevBps`.
  - Auto-clamps the price step to `±mkt.maxMoveBps`, computes on-chain premium funding strictly
    within the remaining clamp budget, and CPIs `percolator::UpdateOracle` via PDA `["orac", adp, bump]`.
-/
import LeanSVM
import Percolator.Layout

namespace Percolator.OracleAdapter

open LeanSVM
open LeanSVM.Input
open LeanSVM.Math
open LeanSVM.CPI
open Percolator

def MAGIC_ADAPTER : UInt32 := 0x5044414F -- "OADP"
def MAGIC_FEED    : UInt32 := 0x44454546 -- "FEED"
def TAG_ORAC_AUTH : UInt32 := 0x6361726F -- "orac"

/-- Supported on-chain oracle account formats. -/
def FEED_CUSTOM      : UInt8 := 0
def FEED_PYTH_V2     : UInt8 := 1
def FEED_CHAINLINK   : UInt8 := 2
def FEED_SWITCHBOARD : UInt8 := 3

/-- Exact Anchor 8-byte account discriminators (`sha256("account:<Name>")[..8]` LE). -/
def DISC_PYTH_V2     : UInt64 := 0xCDF47E9D6323F122 -- sha256("account:PriceUpdateV2")[..8]
def DISC_CHAINLINK   : UInt64 := 0x754981804245B360 -- sha256("account:Transmissions")[..8]
def DISC_SWITCHBOARD : UInt64 := 0x28DBD70AC46C1BC4 -- sha256("account:PullFeedAccountData")[..8]

/-- Adapter flag bits (`AdpOff.flags`). -/
def FLAG_HAS_QUOTE : UInt8 := 1
def FLAG_PIN_FID   : UInt8 := 2
def FLAG_PIN_QFID  : UInt8 := 4
def FLAG_HYBRID_AH : UInt8 := 8  -- Hybrid after-hours EWMA fallback when base feed is stale/wide-conf

namespace OErr
  def feedStale       : UInt64 := 300
  def feedWideConf    : UInt64 := 301
  def feedMismatch    : UInt64 := 302
  def progMismatch    : UInt64 := 303
  def badFeedFormat   : UInt64 := 304
  def badFeedId       : UInt64 := 305
  def ewmaDevExceeded : UInt64 := 306
  def ewmaNotEnabled  : UInt64 := 307
  def ewmaSameSlot    : UInt64 := 308
end OErr

namespace AdpOff
  def size              : UInt64 := 352
  def magic             : UInt64 := 0   -- u32 ("OADP")
  def pdaBump           : UInt64 := 4   -- u8
  def feedType          : UInt64 := 5   -- u8 (0=Custom, 1=PythV2, 2=Chainlink, 3=Switchboard)
  def quoteFeedType     : UInt64 := 6   -- u8 (same enum when FLAG_HAS_QUOTE set)
  def flags             : UInt64 := 7   -- u8 (bit0=hasQuote, bit1=pinFeedId, bit2=pinQuoteFeedId, bit3=hybridAH)
  def admin             : UInt64 := 8   -- Pubkey (32)
  def percProg          : UInt64 := 40  -- Pubkey (32)
  def market            : UInt64 := 72  -- Pubkey (32)
  def feedAccount       : UInt64 := 104 -- Pubkey (32)
  def maxFeedAge        : UInt64 := 136 -- u64 (slots for Custom/Chainlink/Switchboard; secs for Pyth)
  def maxConfBps        : UInt64 := 144 -- u64
  def fundingBpsPerStep : UInt64 := 152 -- u64
  def feedOwner         : UInt64 := 160 -- Pubkey (32) — pinned owner of `feedAccount`
  def feedId            : UInt64 := 192 -- [u8; 32]    — pinned Pyth `feed_id` (if FLAG_PIN_FID)
  def quoteFeed         : UInt64 := 224 -- Pubkey (32) — optional denominator feed (`base / quote`)
  def quoteFeedOwner    : UInt64 := 256 -- Pubkey (32) — pinned owner of `quoteFeed`
  def quoteFeedId       : UInt64 := 288 -- [u8; 32]    — pinned Pyth `feed_id` for `quoteFeed`
  def ewmaAlphaBps      : UInt64 := 320 -- u64 (0=pass-through; 1..=10000 = EWMA weight on latest spot)
  def ewmaPrice         : UInt64 := 328 -- u64 (E6 current EWMA base price; 0 until seeded)
  def ewmaMaxDevBps     : UInt64 := 336 -- u64 (max per-slot deviation in bps for PushEwmaMark)
  def lastEwmaSlot      : UInt64 := 344 -- u64 (slot of last EWMA update)
end AdpOff

namespace FeedOff
  def size        : UInt64 := 32
  def magic       : UInt64 := 0  -- u32 ("FEED")
  def price       : UInt64 := 8  -- u64 (E6)
  def conf        : UInt64 := 16 -- u64 (E6)
  def publishSlot : UInt64 := 24 -- u64
end FeedOff

/- Exact Pyth `PriceUpdateV2` offsets (`verification_level == Full` (1 byte at 40)). -/
namespace PythOff
  def minSize     : UInt64 := 133
  def verLevel    : UInt64 := 40  -- u8 (1 = Full)
  def feedId      : UInt64 := 41  -- [u8; 32]
  def price       : UInt64 := 73  -- i64 LE
  def conf        : UInt64 := 81  -- u64 LE
  def expo        : UInt64 := 89  -- i32 LE
  def publishTime : UInt64 := 93  -- i64 LE
  def postedSlot  : UInt64 := 125 -- u64 LE
end PythOff

/- Exact Chainlink Solana OCR2 `Transmissions` offsets (`HEADER_SIZE = 192`, `Transmission = 48 B`). -/
namespace ChainlinkOff
  def headerTotal   : UInt64 := 200 -- 8-byte discriminator + 192-byte header
  def entrySize     : UInt64 := 48  -- sizeof(Transmission)
  def version       : UInt64 := 8   -- u8 (must be 2)
  def decimals      : UInt64 := 138 -- u8
  def latestRoundId : UInt64 := 143 -- u32
  def liveLength    : UInt64 := 148 -- u32
  def liveCursor    : UInt64 := 152 -- u32
  def entrySlot     : UInt64 := 0   -- u64 inside Transmission
  def entryAnswerLo : UInt64 := 16  -- i128 low 64 bits
  def entryAnswerHi : UInt64 := 24  -- i128 high 64 bits
end ChainlinkOff

/- Exact Switchboard On-Demand `PullFeedAccountData` offsets (`PRECISION = 18`). -/
namespace SwitchboardOff
  def minSize     : UInt64 := 2392 -- 8 + 2256 + 128 (`CurrentResult` end)
  def resValLo    : UInt64 := 2264 -- i128 low 64 bits (`CurrentResult.value`)
  def resValHi    : UInt64 := 2272 -- i128 high 64 bits
  def resStdLo    : UInt64 := 2280 -- i128 low 64 bits (`CurrentResult.std_dev`)
  def resStdHi    : UInt64 := 2288 -- i128 high 64 bits
  def numSamples  : UInt64 := 2360 -- u8 (`CurrentResult.num_samples`)
  def resSlot     : UInt64 := 2368 -- u64 (`CurrentResult.slot`)
  def scaleToE6   : UInt64 := 1_000_000_000_000 -- 10^(18 - 6) = 10^12
end SwitchboardOff

/-- Compile-time layout bounds proof: every field across `AdpOff`, `FeedOff`, `PythOff`,
    `ChainlinkOff`, and `SwitchboardOff` fits strictly inside its checked account size! -/
theorem oracle_layout_sizes_valid :
    AdpOff.lastEwmaSlot + 8 ≤ AdpOff.size ∧ AdpOff.size % 8 == 0 ∧
    FeedOff.publishSlot + 8 ≤ FeedOff.size ∧ FeedOff.size % 8 == 0 ∧
    PythOff.postedSlot + 8 ≤ PythOff.minSize ∧
    ChainlinkOff.liveCursor + 4 ≤ ChainlinkOff.headerTotal ∧
    ChainlinkOff.entryAnswerHi + 8 ≤ ChainlinkOff.entrySize ∧
    SwitchboardOff.resSlot + 8 ≤ SwitchboardOff.minSize := by
  decide

/-! ### Pure Specifications & Formal Proofs -/

def clampedStepNat (oldP targetP maxMoveBps : Nat) : Nat × Nat :=
  let maxAllowed := (oldP * maxMoveBps) / 10_000
  if targetP ≥ oldP then
    let step := min (targetP - oldP) maxAllowed
    (oldP + step, step)
  else
    let step := min (oldP - targetP) maxAllowed
    if oldP > step then (oldP - step, step) else (1, oldP - 1)

def clampedFundingNat (oldP step maxMoveBps fundBps : Nat) : Nat :=
  let maxAllowed := (oldP * maxMoveBps) / 10_000
  let remBudget  := maxAllowed - step
  min ((oldP * fundBps) / 10_000) remBudget

/-- Pure model of Chainlink OCR2 ring-buffer latest index `(cursor + len - 1) % len`. -/
def ringBufferPrevIdx (cursor len : Nat) : Nat :=
  (cursor + len - 1) % len

/-- Pure model of decimal scaling `val * 10^(6 - dec)` to E6 fixed-point. -/
def scaleToE6Nat (val dec : Nat) : Nat :=
  if dec ≥ 6 then val / (10 ^ (dec - 6))
  else val * (10 ^ (6 - dec))

/-- Formal Proof #1: `clampedStepNat` + `clampedFundingNat` ALWAYS satisfies `percolator-lean`'s
    per-slot oracle clamp `|newP - oldP| + fundE6 ≤ ⌊oldP * maxMoveBps / 10_000⌋`! -/
theorem crank_step_and_funding_within_clamp (oldP targetP maxMoveBps fundBps : Nat) (ho : oldP ≥ 1) :
    let (newP, step) := clampedStepNat oldP targetP maxMoveBps
    let fundE6 := clampedFundingNat oldP step maxMoveBps fundBps
    let diff := if newP ≥ oldP then newP - oldP else oldP - newP
    diff + fundE6 ≤ (oldP * maxMoveBps) / 10_000 := by
  unfold clampedStepNat clampedFundingNat
  dsimp only
  by_cases h1 : targetP ≥ oldP
  · simp only [h1, ↓reduceIte]
    split <;> omega
  · simp only [h1, ↓reduceIte]
    by_cases h2 : oldP > min (oldP - targetP) (oldP * maxMoveBps / 10_000)
    · simp only [h2, ↓reduceIte]; split <;> omega
    · simp only [h2, ↓reduceIte]; split <;> omega

/-- Formal Proof #2: Chainlink OCR2 ring-buffer index is ALWAYS strictly in-bounds (`< len`)
    for every `liveLength > 0` and any `liveCursor` (zero out-of-bounds reads!). -/
theorem ringBufferPrevIdx_lt (cursor len : Nat) (hlen : 0 < len) :
    ringBufferPrevIdx cursor len < len :=
  Nat.mod_lt _ hlen

/-- Formal Proof #3: E6 decimal scaling preserves monotonicity (`a ≤ b → scaleToE6Nat a d ≤ scaleToE6Nat b d`)
    and identity at `d = 6` (`scaleToE6Nat v 6 = v`). -/
theorem scaleToE6Nat_mono_and_id (a b d : Nat) (hab : a ≤ b) :
    scaleToE6Nat a d ≤ scaleToE6Nat b d ∧ scaleToE6Nat a 6 = a := by
  constructor
  · unfold scaleToE6Nat
    split
    · exact Nat.div_le_div_right hab
    · exact Nat.mul_le_mul_right _ hab
  · unfold scaleToE6Nat; simp

/-- Pure model of exact integer EWMA blend: `⌊(prev * (10_000 - α) + spot * α) / 10_000⌋`. -/
def ewmaBlendNat (prev spot alphaBps : Nat) : Nat :=
  if prev = 0 ∨ alphaBps = 0 ∨ alphaBps ≥ 10_000 then spot
  else (prev * (10_000 - alphaBps) + spot * alphaBps) / 10_000

/-- Formal Proof #4: 2-leg composite ratio pricing (`⌊baseE6 * 10^6 / quoteE6⌋`) fed into
    `clampedStepNat` + `clampedFundingNat` ALWAYS obeys the core per-slot clamp! -/
theorem ratio_crank_within_clamp (oldP baseE6 quoteE6 maxMoveBps fundBps : Nat) (ho : oldP ≥ 1) :
    let targetP := (baseE6 * 1_000_000) / quoteE6
    let (newP, step) := clampedStepNat oldP targetP maxMoveBps
    let fundE6 := clampedFundingNat oldP step maxMoveBps fundBps
    let diff := if newP ≥ oldP then newP - oldP else oldP - newP
    diff + fundE6 ≤ (oldP * maxMoveBps) / 10_000 :=
  crank_step_and_funding_within_clamp oldP ((baseE6 * 1_000_000) / quoteE6) maxMoveBps fundBps ho

/-- Formal Proof #5 (EWMA Convexity / No-Overshoot / Strictly Positive):
    `ewmaBlendNat` ALWAYS lies inside `[min prev spot, max prev spot]` for all `prev, spot`,
    guaranteeing zero underflow to 0 and zero overshoot past `MAX_PRICE`! -/
theorem ewmaBlendNat_bounds (prev spot alphaBps : Nat) :
    min prev spot ≤ ewmaBlendNat prev spot alphaBps ∧
    ewmaBlendNat prev spot alphaBps ≤ max prev spot := by
  unfold ewmaBlendNat
  by_cases h : prev = 0 ∨ alphaBps = 0 ∨ alphaBps ≥ 10_000
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]
    have ha : alphaBps < 10_000 := by omega
    have hlo : min prev spot * 10_000 ≤ prev * (10_000 - alphaBps) + spot * alphaBps := by
      have h1 : min prev spot * (10_000 - alphaBps) ≤ prev * (10_000 - alphaBps) :=
        Nat.mul_le_mul_right _ (Nat.min_le_left prev spot)
      have h2 : min prev spot * alphaBps ≤ spot * alphaBps :=
        Nat.mul_le_mul_right _ (Nat.min_le_right prev spot)
      have hsum : min prev spot * (10_000 - alphaBps) + min prev spot * alphaBps =
                  min prev spot * 10_000 := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt ha)]
      omega
    have hhi : prev * (10_000 - alphaBps) + spot * alphaBps ≤ max prev spot * 10_000 := by
      have h1 : prev * (10_000 - alphaBps) ≤ max prev spot * (10_000 - alphaBps) :=
        Nat.mul_le_mul_right _ (Nat.le_max_left prev spot)
      have h2 : spot * alphaBps ≤ max prev spot * alphaBps :=
        Nat.mul_le_mul_right _ (Nat.le_max_right prev spot)
      have hsum : max prev spot * (10_000 - alphaBps) + max prev spot * alphaBps =
                  max prev spot * 10_000 := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt ha)]
      omega
    constructor
    · exact (Nat.le_div_iff_mul_le (by omega : 0 < 10_000)).mpr hlo
    · exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm 10_000 (max prev spot)]; exact hhi)

/-- Formal Proof #6 (EWMA Exact Fixed Point): constant spot price has zero integer rounding drift! -/
theorem ewmaBlendNat_fixed_point (p alphaBps : Nat) :
    ewmaBlendNat p p alphaBps = p := by
  unfold ewmaBlendNat
  by_cases h : p = 0 ∨ alphaBps = 0 ∨ alphaBps ≥ 10_000
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    have ha : alphaBps ≤ 10_000 := by omega
    rw [← Nat.mul_add, Nat.sub_add_cancel ha]
    exact Nat.mul_div_cancel p (by omega : 0 < 10_000)

/-- Formal Proof #7 (Hybrid After-Hours EWMA + Ratio Clamp Safety):
    Whether using live EWMA or carried after-hours EWMA (single-leg or 2-leg ratio),
    `clampedStepNat` + `clampedFundingNat` ALWAYS satisfies `percolator-lean`'s core clamp! -/
theorem ewma_ratio_crank_within_clamp
    (oldP prevEwma spotBase quoteE6 alphaBps maxMoveBps fundBps : Nat)
    (ho : oldP ≥ 1) (isAfterHours : Bool) :
    let effBase := if isAfterHours then prevEwma else ewmaBlendNat prevEwma spotBase alphaBps
    let targetP := if quoteE6 = 0 then effBase else (effBase * 1_000_000) / quoteE6
    let (newP, step) := clampedStepNat oldP targetP maxMoveBps
    let fundE6 := clampedFundingNat oldP step maxMoveBps fundBps
    let diff := if newP ≥ oldP then newP - oldP else oldP - newP
    diff + fundE6 ≤ (oldP * maxMoveBps) / 10_000 := by
  dsimp only
  exact crank_step_and_funding_within_clamp oldP _ maxMoveBps fundBps ho

/-! ### Exact 128-bit & Decimal Scaling Helpers -/

private def div128StepLoop (rem lo q denom : UInt64) (steps : UInt64) : UInt64 :=
  if h : steps = 0 then q
  else
    let topBit := lo >>> 63
    let remCarry := rem >>> 63
    let rem1 := (rem <<< 1) ||| topBit
    let lo1 := lo <<< 1
    let q1 := q <<< 1
    if remCarry != 0 || rem1 >= denom then
      div128StepLoop (rem1 - denom) lo1 (q1 ||| 1) denom (steps - 1)
    else
      div128StepLoop rem1 lo1 q1 denom (steps - 1)
termination_by steps.toNat
decreasing_by
  all_goals
    have h1 : (1 : UInt64).toNat = 1 := rfl
    have hpos : 0 < steps.toNat := by
      have hne : steps.toNat ≠ 0 := fun hz => h (UInt64.toNat_inj.mp (by rw [hz]; rfl))
      omega
    change (steps - 1).toNat < steps.toNat
    rw [UInt64.toNat_sub_of_le, h1]
    · omega
    · exact UInt64.le_iff_toNat_le.mpr (by rw [h1]; omega)

/-- Overflow-checked `⌊(hi * 2^64 + lo) / denom⌋` for non-negative 128-bit oracle values. -/
def divU128By64 (hi lo denom : UInt64) : SolanaM UInt64 := do
  SolanaM.require (denom != 0) Err.arithmeticOverflow
  if hi == 0 then
    return lo / denom
  else
    SolanaM.require (hi < denom) Err.arithmeticOverflow
    return div128StepLoop hi lo 0 denom 64

/-- Exact `10^n` for `0 <= n <= 18`. -/
def pow10Loop (acc n : UInt64) : UInt64 :=
  if h : n = 0 then acc
  else pow10Loop (acc * 10) (n - 1)
termination_by n.toNat
decreasing_by
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hpos : 0 < n.toNat := by
    have hne : n.toNat ≠ 0 := fun hz => h (UInt64.toNat_inj.mp (by rw [hz]; rfl))
    omega
  change (n - 1).toNat < n.toNat
  rw [UInt64.toNat_sub_of_le, h1]
  · omega
  · exact UInt64.le_iff_toNat_le.mpr (by rw [h1]; omega)

/-- Scale a positive `u64` value with `10^(-negExp)` decimals to `E6` (`10^(-6)`). -/
def scaleU64ToE6 (val negExp : UInt64) : SolanaM UInt64 := do
  SolanaM.require (negExp <= 18) OErr.badFeedFormat
  if negExp == 6 then
    return val
  else if negExp > 6 then
    let div := pow10Loop 1 (negExp - 6)
    return val / div
  else
    let mult := pow10Loop 1 (6 - negExp)
    let res := val * mult
    SolanaM.require (res / mult == val) Err.arithmeticOverflow
    return res

/-- Scale a positive `u128` `(hi, lo)` value with `10^(-dec)` decimals to `E6` (`10^(-6)`). -/
def scaleU128ToE6 (hi lo dec : UInt64) : SolanaM UInt64 := do
  SolanaM.require (dec <= 18) OErr.badFeedFormat
  if dec >= 6 then
    if dec == 6 then
      SolanaM.require (hi == 0) Err.arithmeticOverflow
      return lo
    else
      divU128By64 hi lo (pow10Loop 1 (dec - 6))
  else
    SolanaM.require (hi == 0) Err.arithmeticOverflow
    scaleU64ToE6 lo dec

/-- Exact 64-bit integer EWMA blend: `⌊(prev * (10_000 - α) + spot * α) / 10_000⌋`.
    Safe in native `UInt64` for all `prev, spot ≤ MAX_PRICE (10^12)` and `α ≤ 10_000` (`≤ 10^16 ≪ 2^64`). -/
def ewmaBlendU64 (prev spot alphaBps : UInt64) : UInt64 :=
  if prev == 0 || alphaBps == 0 || alphaBps >= BPS_DEN then spot
  else (prev * (BPS_DEN - alphaBps) + spot * alphaBps) / BPS_DEN

/-! ### Unified On-Chain Oracle Feed Parser (Custom / Pyth V2 / Chainlink OCR2 / Switchboard) -/

/-- Parse and validate one oracle account according to `feedType`, returning `(priceE6, confE6)`.
    Always enforces account key, pinned owner, Anchor discriminator, format constraints, and `feed_id`.
    When `allowStale == true` (hybrid after-hours mode), a stale feed returns `(0, 0)` so the caller
    can cleanly fall back to the carried EWMA mark instead of aborting! -/
def parseOracleFeed (feed : AccountView) (expectedKeyPtr expectedOwnerPtr expectedFidPtr : Ptr)
    (feedType : UInt8) (pinFid allowStale : Bool) (maxAge curSlot curTs : UInt64) :
    SolanaM (UInt64 × UInt64) := do
  SolanaM.require (← pubkeyEq (AccountView.keyPtr feed)   expectedKeyPtr)   OErr.feedMismatch
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr feed) expectedOwnerPtr) Err.illegalOwner
  let dLen  ← AccountView.dataLen feed
  let fData := AccountView.dataPtr feed

  if feedType == FEED_CUSTOM then
    SolanaM.require (dLen >= FeedOff.size) Err.accountDataTooSmall
    SolanaM.require ((← loadU32 fData FeedOff.magic) == MAGIC_FEED) PErr.invalidMagic
    let price   ← loadU64 fData FeedOff.price
    let conf    ← loadU64 fData FeedOff.conf
    let pubSlot ← loadU64 fData FeedOff.publishSlot
    let fresh := curSlot >= pubSlot && (curSlot - pubSlot) <= maxAge
    if !fresh then
      if allowStale then return (0, 0)
      else SolanaM.fail OErr.feedStale
    SolanaM.require (price > 0 && price <= MAX_PRICE) PErr.invalidParams
    return (price, conf)

  else if feedType == FEED_PYTH_V2 then
    -- Official Pyth Pull Oracle `PriceUpdateV2` (Anchor Borsh LE, VerificationLevel::Full = 1)
    SolanaM.require (dLen >= PythOff.minSize) Err.accountDataTooSmall
    SolanaM.require ((← loadU64 fData 0) == DISC_PYTH_V2) OErr.badFeedFormat
    SolanaM.require ((← loadU8 fData PythOff.verLevel) == 1) OErr.badFeedFormat
    if pinFid then
      SolanaM.require (← pubkeyEq (fData + PythOff.feedId) expectedFidPtr) OErr.badFeedId
    let rawPrice ← loadU64 fData PythOff.price
    let rawConf  ← loadU64 fData PythOff.conf
    let rawExpo  ← loadU32 fData PythOff.expo
    let pubTime  ← loadU64 fData PythOff.publishTime
    let postSlot ← loadU64 fData PythOff.postedSlot
    -- Reject negative/zero `i64` price
    SolanaM.require (rawPrice > 0 && (rawPrice >>> 63) == 0) OErr.badFeedFormat
    let fresh := (pubTime >>> 63) == 0 && (curTs >>> 63) == 0 &&
                 curTs >= pubTime && (curTs - pubTime) <= maxAge && postSlot <= curSlot
    if !fresh then
      if allowStale then return (0, 0)
      else SolanaM.fail OErr.feedStale
    -- Convert `i32` exponent to E6 scale
    if (rawExpo &&& 0x80000000) != 0 then
      let negExp := (0 - rawExpo).toUInt64
      let pE6 ← scaleU64ToE6 rawPrice negExp
      let cE6 ← scaleU64ToE6 rawConf  negExp
      SolanaM.require (pE6 > 0 && pE6 <= MAX_PRICE) PErr.invalidParams
      return (pE6, cE6)
    else
      let posExp := rawExpo.toUInt64
      SolanaM.require (posExp <= 6) OErr.badFeedFormat
      let mult := pow10Loop 1 (posExp + 6)
      let pE6 := rawPrice * mult
      let cE6 := rawConf  * mult
      SolanaM.require (pE6 / mult == rawPrice && pE6 > 0 && pE6 <= MAX_PRICE) PErr.invalidParams
      SolanaM.require (rawConf == 0 || cE6 / mult == rawConf) Err.arithmeticOverflow
      return (pE6, cE6)

  else if feedType == FEED_CHAINLINK then
    -- Official Chainlink Solana OCR2 `Transmissions` (Anchor disc + 192B header + 48B Transmission ring)
    SolanaM.require (dLen >= ChainlinkOff.headerTotal + ChainlinkOff.entrySize) Err.accountDataTooSmall
    SolanaM.require ((← loadU64 fData 0) == DISC_CHAINLINK) OErr.badFeedFormat
    SolanaM.require ((← loadU8 fData ChainlinkOff.version) == 2) OErr.badFeedFormat
    let dec      := (← loadU8  fData ChainlinkOff.decimals).toUInt64
    let roundId  := (← loadU32 fData ChainlinkOff.latestRoundId).toUInt64
    let liveLen  := (← loadU32 fData ChainlinkOff.liveLength).toUInt64
    let liveCur  := (← loadU32 fData ChainlinkOff.liveCursor).toUInt64
    SolanaM.require (roundId > 0 && liveLen > 0) OErr.badFeedFormat
    let idx := (liveCur + liveLen - 1) % liveLen
    let entryOff := ChainlinkOff.headerTotal + idx * ChainlinkOff.entrySize
    SolanaM.require (dLen >= entryOff + ChainlinkOff.entrySize) Err.accountDataTooSmall
    let slot   ← loadU64 fData (entryOff + ChainlinkOff.entrySlot)
    let ansLo  ← loadU64 fData (entryOff + ChainlinkOff.entryAnswerLo)
    let ansHi  ← loadU64 fData (entryOff + ChainlinkOff.entryAnswerHi)
    -- Reject negative `i128` answers (`ansHi` sign bit set) or zero answer
    SolanaM.require ((ansHi >>> 63) == 0 && (ansHi != 0 || ansLo != 0)) OErr.badFeedFormat
    let fresh := curSlot >= slot && (curSlot - slot) <= maxAge
    if !fresh then
      if allowStale then return (0, 0)
      else SolanaM.fail OErr.feedStale
    let pE6 ← scaleU128ToE6 ansHi ansLo dec
    SolanaM.require (pE6 > 0 && pE6 <= MAX_PRICE) PErr.invalidParams
    return (pE6, 0)

  else if feedType == FEED_SWITCHBOARD then
    -- Official Switchboard On-Demand `PullFeedAccountData` (`CurrentResult` at byte 2264, `PRECISION = 18`)
    SolanaM.require (dLen >= SwitchboardOff.minSize) Err.accountDataTooSmall
    SolanaM.require ((← loadU64 fData 0) == DISC_SWITCHBOARD) OErr.badFeedFormat
    let valLo   ← loadU64 fData SwitchboardOff.resValLo
    let valHi   ← loadU64 fData SwitchboardOff.resValHi
    let stdLo   ← loadU64 fData SwitchboardOff.resStdLo
    let stdHi   ← loadU64 fData SwitchboardOff.resStdHi
    let samples ← loadU8  fData SwitchboardOff.numSamples
    let resSlot ← loadU64 fData SwitchboardOff.resSlot
    SolanaM.require (samples >= 1 && resSlot > 0) OErr.badFeedFormat
    SolanaM.require ((valHi >>> 63) == 0 && (valHi != 0 || valLo != 0)) OErr.badFeedFormat
    SolanaM.require ((stdHi >>> 63) == 0) OErr.badFeedFormat
    let fresh := curSlot >= resSlot && (curSlot - resSlot) <= maxAge
    if !fresh then
      if allowStale then return (0, 0)
      else SolanaM.fail OErr.feedStale
    let pE6 ← divU128By64 valHi valLo SwitchboardOff.scaleToE6
    let cE6 ← divU128By64 stdHi stdLo SwitchboardOff.scaleToE6
    SolanaM.require (pE6 > 0 && pE6 <= MAX_PRICE) PErr.invalidParams
    return (pE6, cE6)

  else
    SolanaM.fail OErr.badFeedFormat

/-! ### CPI Signer & Clock Helpers -/

def writeOracPdaSeeds (sbuf : Ptr) (adpKeyPtr : Ptr) (bump : UInt8) : SolanaM Ptr := do
  let seedsArr   := sbuf + 8
  let signersArr := sbuf + 56
  storeU32 sbuf 0 TAG_ORAC_AUTH
  storeU8  sbuf 4 bump
  storeU64 seedsArr 0  sbuf;       storeU64 seedsArr 8  4
  storeU64 seedsArr 16 adpKeyPtr;  storeU64 seedsArr 24 32
  storeU64 seedsArr 32 (sbuf + 4); storeU64 seedsArr 40 1
  storeU64 signersArr 0 seedsArr
  storeU64 signersArr 8 3
  return signersArr

/-- Read both `Clock.slot` (offset 0) and `Clock.unix_timestamp` (offset 32) in one syscall. -/
def getClockSlotAndTs : SolanaM (UInt64 × UInt64) := do
  let buf ← stackAlloc 40
  let rc ← sysGetClock buf
  SolanaM.require (rc == 0) Err.invalidAccountData
  let sl ← loadU64 buf 0
  let ts ← loadU64 buf 32
  return (sl, ts)

/-! ### 2 Minimal Instructions -/

def zeroAdapterWords (base off nWords : UInt64) : SolanaM Unit := do
  if h : nWords == 0 then return ()
  else
    storeU64 base off 0
    zeroAdapterWords base (off + 8) (nWords - 1)
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

/-- Op 0: Initialize `OracleAdapter` binding `(percolatorProg, market, feedAccount[, quoteFeed])`.
    Supports all 4 feed formats (`0=Custom`, `1=PythV2`, `2=Chainlink`, `3=Switchboard`),
    optional Pyth `feed_id` pinning (`ix.len >= 60` / `92`), and optional 2-leg ratio mode (`n >= 6`)! -/
def handleInitAdapter (input : Ptr) : SolanaM Unit := do
  let (n, adp, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 5) Err.notEnoughAccountKeys
  SolanaM.require (ix.len >= 28) Err.invalidInstructionData
  let admin    ← AccountView.nextCursor adp
  let percProg ← AccountView.nextCursor admin
  let mkt      ← AccountView.nextCursor percProg
  let feed     ← AccountView.nextCursor mkt

  SolanaM.require ((← rawLoadU8 adp) == ABI.nonDupMarker &&
                   (← rawLoadU8 admin) == ABI.nonDupMarker &&
                   (← rawLoadU8 percProg) == ABI.nonDupMarker &&
                   (← rawLoadU8 mkt) == ABI.nonDupMarker &&
                   (← rawLoadU8 feed) == ABI.nonDupMarker) PErr.aliasedAccounts
  SolanaM.require (← AccountView.isSigner admin) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable adp) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr adp) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen adp) == AdpOff.size) Err.invalidAccountData
  SolanaM.require ((← loadU32 (AccountView.dataPtr adp) 0) == 0) Err.accountAlreadyInitialized
  -- Pin adapter initialization strictly to the bound market's active `marketAdmin`
  -- (blocks unauthorized claim/hijack of an uninitialized adapter PDA bound to a market!).
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr mkt) (AccountView.keyPtr percProg)) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen mkt) == MktOff.size) Err.invalidAccountData
  let mData := AccountView.dataPtr mkt
  SolanaM.require ((← loadU32 mData MktOff.magic) == MAGIC_MARKET) PErr.invalidMagic
  SolanaM.require ((← loadU8 mData MktOff.status) != STATUS_TOMBSTONED) PErr.invalidStatus
  let ma0 ← loadU64 mData (MktOff.marketAdmin + 0)
  let ma1 ← loadU64 mData (MktOff.marketAdmin + 8)
  let ma2 ← loadU64 mData (MktOff.marketAdmin + 16)
  let ma3 ← loadU64 mData (MktOff.marketAdmin + 24)
  SolanaM.require ((ma0 ||| ma1 ||| ma2 ||| ma3) != 0) PErr.unauthorized
  SolanaM.require (← pubkeyEq (AccountView.keyPtr admin) (mData + MktOff.marketAdmin)) PErr.unauthorized

  let pdaBump     ← loadU8  ix.ptr 1
  let feedType    ← loadU8  ix.ptr 2
  let qFeedType   ← loadU8  ix.ptr 3
  let maxFeedAge  ← loadU64 ix.ptr 4
  let maxConfBps  ← loadU64 ix.ptr 12
  let fundBpsStep ← loadU64 ix.ptr 20
  SolanaM.require (feedType <= FEED_SWITCHBOARD) OErr.badFeedFormat
  SolanaM.require (maxFeedAge >= 1 && maxConfBps <= BPS_DEN && fundBpsStep <= BPS_DEN) PErr.invalidParams

  let aData := AccountView.dataPtr adp
  zeroAdapterWords aData 0 (AdpOff.size >>> 3)
  let mut flags : UInt8 := 0
  if ix.len >= 60 then
    pubkeyCopy (aData + AdpOff.feedId) (ix.ptr + 28)
    flags := flags ||| FLAG_PIN_FID
  if n >= 6 then
    SolanaM.require (qFeedType <= FEED_SWITCHBOARD) OErr.badFeedFormat
    let qFeed ← AccountView.nextCursor feed
    SolanaM.require ((← rawLoadU8 qFeed) == ABI.nonDupMarker) PErr.aliasedAccounts
    pubkeyCopy (aData + AdpOff.quoteFeed)      (AccountView.keyPtr qFeed)
    pubkeyCopy (aData + AdpOff.quoteFeedOwner) (AccountView.ownerPtr qFeed)
    flags := flags ||| FLAG_HAS_QUOTE
    if ix.len >= 92 then
      pubkeyCopy (aData + AdpOff.quoteFeedId) (ix.ptr + 60)
      flags := flags ||| FLAG_PIN_QFID

  storeU32 aData AdpOff.magic MAGIC_ADAPTER
  storeU8  aData AdpOff.pdaBump pdaBump
  storeU8  aData AdpOff.feedType feedType
  storeU8  aData AdpOff.quoteFeedType qFeedType
  storeU8  aData AdpOff.flags flags
  pubkeyCopy (aData + AdpOff.admin)       (AccountView.keyPtr admin)
  pubkeyCopy (aData + AdpOff.percProg)    (AccountView.keyPtr percProg)
  pubkeyCopy (aData + AdpOff.market)      (AccountView.keyPtr mkt)
  pubkeyCopy (aData + AdpOff.feedAccount) (AccountView.keyPtr feed)
  pubkeyCopy (aData + AdpOff.feedOwner)   (AccountView.ownerPtr feed)
  storeU64 aData AdpOff.maxFeedAge        maxFeedAge
  storeU64 aData AdpOff.maxConfBps        maxConfBps
  storeU64 aData AdpOff.fundingBpsPerStep fundBpsStep

/-- Op 1: 100% Permissionless `Crank` — parses Custom / Pyth V2 / Chainlink OCR2 / Switchboard
    (single-leg or 2-leg composite ratio `base / quote`), validates staleness & confidence,
    auto-clamps the price step, computes bounded funding, and CPIs `percolator::UpdateOracle`! -/
def handleCrank (input : Ptr) : SolanaM Unit := do
  let (n, adp, _, progId) ← parseIxOnly input
  SolanaM.require (n >= 5) Err.notEnoughAccountKeys
  let mkt         ← AccountView.nextCursor adp
  let feed        ← AccountView.nextCursor mkt
  let oracAuthPda ← AccountView.nextCursor feed
  let percProg    ← AccountView.nextCursor oracAuthPda

  SolanaM.require ((← rawLoadU8 adp) == ABI.nonDupMarker &&
                   (← rawLoadU8 mkt) == ABI.nonDupMarker &&
                   (← rawLoadU8 feed) == ABI.nonDupMarker &&
                   (← rawLoadU8 oracAuthPda) == ABI.nonDupMarker &&
                   (← rawLoadU8 percProg) == ABI.nonDupMarker) PErr.aliasedAccounts
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr adp) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen adp) == AdpOff.size) Err.invalidAccountData
  let aData := AccountView.dataPtr adp
  SolanaM.require ((← loadU32 aData AdpOff.magic) == MAGIC_ADAPTER) PErr.invalidMagic
  SolanaM.require (← pubkeyEq (AccountView.keyPtr percProg) (aData + AdpOff.percProg)) OErr.progMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr mkt)      (aData + AdpOff.market))   PErr.marketMismatch

  let (curSlot, curTs) ← getClockSlotAndTs
  let maxAge     ← loadU64 aData AdpOff.maxFeedAge
  let maxConfBps ← loadU64 aData AdpOff.maxConfBps
  let feedType   ← loadU8  aData AdpOff.feedType
  let flags      ← loadU8  aData AdpOff.flags
  let alphaBps   ← loadU64 aData AdpOff.ewmaAlphaBps
  let prevEwma   ← loadU64 aData AdpOff.ewmaPrice
  let isHybrid   := (flags &&& FLAG_HYBRID_AH) != 0
  let useEwma    := alphaBps > 0 || isHybrid

  -- Parse & validate primary feed (with optional EWMA smoothing & Hybrid After-Hours fallback!)
  let (rawBaseP, baseC) ← parseOracleFeed feed
    (aData + AdpOff.feedAccount) (aData + AdpOff.feedOwner) (aData + AdpOff.feedId)
    feedType ((flags &&& FLAG_PIN_FID) != 0) isHybrid maxAge curSlot curTs
  let baseConfOk : Bool ← if rawBaseP > 0 then do
      let maxBaseC ← mulDiv64 rawBaseP maxConfBps BPS_DEN
      if baseC <= maxBaseC then pure true else pure false
    else pure false
  let baseP ← if rawBaseP > 0 && baseConfOk then do
      if useEwma then
        SolanaM.require (← AccountView.isWritable adp) Err.invalidAccountData
        let nextEwma := ewmaBlendU64 prevEwma rawBaseP alphaBps
        storeU64 aData AdpOff.ewmaPrice nextEwma
        storeU64 aData AdpOff.lastEwmaSlot curSlot
        pure nextEwma
      else pure rawBaseP
    else if isHybrid then do
      -- Hybrid After-Hours fallback: carry last EWMA base mark while underlying market is closed!
      if rawBaseP == 0 then
        SolanaM.require (prevEwma > 0) OErr.feedStale
      else
        SolanaM.require (prevEwma > 0) OErr.feedWideConf
      pure prevEwma
    else SolanaM.fail OErr.feedWideConf

  -- Optional 2-leg composite ratio (`base / quote`, e.g. `STOXX/SOL` or `BTC/ETH`)
  -- Quote feed (`SOL/USD`) is ALWAYS strictly live-validated (24/7 crypto quote!)
  let feedPrice ← if (flags &&& FLAG_HAS_QUOTE) != 0 then do
      SolanaM.require (n >= 6) Err.notEnoughAccountKeys
      let qFeed ← AccountView.nextCursor percProg
      SolanaM.require ((← rawLoadU8 qFeed) == ABI.nonDupMarker) PErr.aliasedAccounts
      let qType ← loadU8 aData AdpOff.quoteFeedType
      let (qP, qC) ← parseOracleFeed qFeed
        (aData + AdpOff.quoteFeed) (aData + AdpOff.quoteFeedOwner) (aData + AdpOff.quoteFeedId)
        qType ((flags &&& FLAG_PIN_QFID) != 0) false maxAge curSlot curTs
      let maxQC ← mulDiv64 qP maxConfBps BPS_DEN
      SolanaM.require (qC <= maxQC) OErr.feedWideConf
      let ratioP ← mulDiv64 baseP POS_SCALE qP
      SolanaM.require (ratioP > 0 && ratioP <= MAX_PRICE) PErr.invalidParams
      pure ratioP
    else pure baseP

  -- Read `oldPrice` & `maxMoveBps` from `percolator::Market`
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr mkt) (AccountView.keyPtr percProg)) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen mkt) == MktOff.size) Err.invalidAccountData
  let mData := AccountView.dataPtr mkt
  SolanaM.require ((← loadU32 mData MktOff.magic) == MAGIC_MARKET) PErr.invalidMagic
  let oldP ← loadU64 mData MktOff.markPrice
  let lastSlot ← loadU64 mData MktOff.lastOracleSlot
  let rawMaxMove ← loadU64 mData MktOff.maxMoveBps
  let effMaxMove :=
    if curSlot == lastSlot + 1 && rawMaxMove > 1 then rawMaxMove >>> 1 else rawMaxMove
  let maxAllowed ← mulDiv64 oldP effMaxMove BPS_DEN

  -- Clamp price step smoothly toward `feedPrice`
  let (newP, step) : UInt64 × UInt64 :=
    if feedPrice >= oldP then
      let raw := feedPrice - oldP
      let s := if raw < maxAllowed then raw else maxAllowed
      (oldP + s, s)
    else
      let raw := oldP - feedPrice
      let s := if raw < maxAllowed then raw else maxAllowed
      if oldP > s then (oldP - s, s) else (1, oldP - 1)

  -- Compute on-chain premium funding strictly within remaining clamp budget
  let remBudget := if maxAllowed >= step then maxAllowed - step else 0
  let fundBps ← loadU64 aData AdpOff.fundingBpsPerStep
  let (fundSign, fundE6) ← if feedPrice != oldP && remBudget > 0 && fundBps > 0 then do
      let rawF ← mulDiv64 oldP fundBps BPS_DEN
      let f := if rawF < remBudget then rawF else remBudget
      let sign : UInt8 := if oldP > feedPrice then 0 else 1
      pure (sign, f)
    else pure (0, 0)

  -- CPI `percolator::UpdateOracle(mkt[W], oracAuthPda[S])`
  let buf ← stackAlloc 280
  let metas := buf + 40
  let infos := buf + 72
  let data  := buf + 184
  let sbuf  := buf + 208
  storeU8  data 0  IxOp.updateOracle
  storeU64 data 1  newP
  storeU8  data 9  fundSign
  storeU64 data 10 fundE6
  writeMeta metas        mkt         1 0
  writeMeta (metas + 16) oracAuthPda 0 1
  writeAccountInfo infos        mkt
  writeAccountInfo (infos + 56) oracAuthPda
  writeInstruction buf (AccountView.keyPtr percProg) metas 2 data 18
  let bump ← loadU8 aData AdpOff.pdaBump
  let signersArr ← writeOracPdaSeeds sbuf (AccountView.keyPtr adp) bump
  let rc ← sysInvokeSignedC buf infos 2 signersArr 1
  SolanaM.require (rc == 0) rc

/-- Op 2: One-shot immutable `InitEwma` configuring EWMA smoothing & Hybrid After-Hours mode.
    Accounts: `[adp(W), admin(S)]`.
    Data (26 B): `[op=2, hybridAfterHours(u8), ewmaAlphaBps(u64), ewmaMaxDevBps(u64), initEwmaPrice(u64)]`. -/
def handleInitEwma (input : Ptr) : SolanaM Unit := do
  let (n, adp, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 2) Err.notEnoughAccountKeys
  SolanaM.require (ix.len >= 26) Err.invalidInstructionData
  let admin ← AccountView.nextCursor adp

  SolanaM.require ((← rawLoadU8 adp) == ABI.nonDupMarker &&
                   (← rawLoadU8 admin) == ABI.nonDupMarker) PErr.aliasedAccounts
  SolanaM.require (← AccountView.isSigner admin) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable adp) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr adp) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen adp) == AdpOff.size) Err.invalidAccountData
  let aData := AccountView.dataPtr adp
  SolanaM.require ((← loadU32 aData AdpOff.magic) == MAGIC_ADAPTER) PErr.invalidMagic
  SolanaM.require (← pubkeyEq (AccountView.keyPtr admin) (aData + AdpOff.admin)) PErr.ownerMismatch

  -- Strictly one-shot immutable configuration!
  let curFlags ← loadU8  aData AdpOff.flags
  let curAlpha ← loadU64 aData AdpOff.ewmaAlphaBps
  let curEwma  ← loadU64 aData AdpOff.ewmaPrice
  SolanaM.require (curAlpha == 0 && curEwma == 0 && (curFlags &&& FLAG_HYBRID_AH) == 0) Err.accountAlreadyInitialized

  let hybridAh    ← loadU8  ix.ptr 1
  let alphaBps    ← loadU64 ix.ptr 2
  let maxDevBps   ← loadU64 ix.ptr 10
  let initEwma    ← loadU64 ix.ptr 18
  SolanaM.require (alphaBps <= BPS_DEN && maxDevBps <= BPS_DEN && initEwma <= MAX_PRICE) PErr.invalidParams
  SolanaM.require (alphaBps > 0 || hybridAh != 0) PErr.invalidParams

  if hybridAh != 0 then
    storeU8 aData AdpOff.flags (curFlags ||| FLAG_HYBRID_AH)
  storeU64 aData AdpOff.ewmaAlphaBps  alphaBps
  storeU64 aData AdpOff.ewmaMaxDevBps maxDevBps
  storeU64 aData AdpOff.ewmaPrice     initEwma
  storeU64 aData AdpOff.lastEwmaSlot  0

/-- Op 3: Bounded per-slot `PushEwmaMark` (`[adp(W), admin(S)]`, 9 B `[op=3, markE6(u64)]`).
    Allows the adapter admin to smoothly nudge the carried EWMA base mark during after-hours
    (e.g. from futures/book pricing while equity cash markets are closed), strictly clamped
    to `±ewmaMaxDevBps` per slot and blended via `ewmaAlphaBps`! -/
def handlePushEwmaMark (input : Ptr) : SolanaM Unit := do
  let (n, adp, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 2) Err.notEnoughAccountKeys
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  let admin ← AccountView.nextCursor adp

  SolanaM.require ((← rawLoadU8 adp) == ABI.nonDupMarker &&
                   (← rawLoadU8 admin) == ABI.nonDupMarker) PErr.aliasedAccounts
  SolanaM.require (← AccountView.isSigner admin) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable adp) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr adp) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen adp) == AdpOff.size) Err.invalidAccountData
  let aData := AccountView.dataPtr adp
  SolanaM.require ((← loadU32 aData AdpOff.magic) == MAGIC_ADAPTER) PErr.invalidMagic
  SolanaM.require (← pubkeyEq (AccountView.keyPtr admin) (aData + AdpOff.admin)) PErr.ownerMismatch

  let flags    ← loadU8  aData AdpOff.flags
  let prevEwma ← loadU64 aData AdpOff.ewmaPrice
  SolanaM.require ((flags &&& FLAG_HYBRID_AH) != 0 && prevEwma > 0) OErr.ewmaNotEnabled

  let (curSlot, _) ← getClockSlotAndTs
  let lastSlot ← loadU64 aData AdpOff.lastEwmaSlot
  SolanaM.require (curSlot > lastSlot) OErr.ewmaSameSlot

  let markE6 ← loadU64 ix.ptr 1
  SolanaM.require (markE6 > 0 && markE6 <= MAX_PRICE) PErr.invalidParams

  let maxDevBps ← loadU64 aData AdpOff.ewmaMaxDevBps
  let maxDev ← mulDiv64 prevEwma maxDevBps BPS_DEN
  let diff := if markE6 >= prevEwma then markE6 - prevEwma else prevEwma - markE6
  SolanaM.require (diff <= maxDev) OErr.ewmaDevExceeded

  let alphaBps ← loadU64 aData AdpOff.ewmaAlphaBps
  let nextEwma := ewmaBlendU64 prevEwma markE6 alphaBps
  storeU64 aData AdpOff.ewmaPrice    nextEwma
  storeU64 aData AdpOff.lastEwmaSlot curSlot

def dispatch (input : Ptr) : SolanaM Unit := do
  let (_, _, ix, _) ← parseIxOnly input
  SolanaM.require (ix.len >= 1) Err.invalidInstructionData
  let op ← loadU8 ix.ptr 0
  if op == 0 then handleInitAdapter input
  else if op == 1 then handleCrank input
  else if op == 2 then handleInitEwma input
  else if op == 3 then handlePushEwmaMark input
  else SolanaM.fail PErr.invalidInstruction

def entrypoint (input : Ptr) (s : SvmState) : UInt64 × SvmState :=
  SolanaM.runEntry (dispatch input) s

end Percolator.OracleAdapter
