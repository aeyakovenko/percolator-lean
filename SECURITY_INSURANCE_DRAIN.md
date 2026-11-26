# Security review — cross-margin insurance drain (reservedMm vs cachedMm)

Status: **fixed in `a056eee`**. This note documents the root cause, why the formal proofs did not
catch it, a runnable pure-model repro, and a suggested regression test that pins the fix.

## Root cause (the refinement gap)

Before `a056eee`, the compiled handler debited a settlement loss against the *reserved* margin,
not the *cached* maintenance margin:

```
-- Program.lean (settleAndRefreshLeg, pre-a056eee)
let totRes  := pfl.totalReservedMm
let legRes  := leg.reservedMm
let otherRes := totRes - legRes
let availCap := capital - otherRes      -- other legs' *reserved* margin
let capDeb   := min rem1 availCap
let shortfall := rem1 - capDeb          -- drawn from I_m in handleLiquidate
```

and `syncLegMargins` only grew `reservedMm` when `capital >= newTotMm` (a ratchet). Meanwhile the
*proven* model — `Spec.applyContainedLoss` / `capAvailableForLeg` — defines containment over the
real maintenance margin:

```
def capAvailableForLeg (capital totalMm legMm : Nat) : Nat :=
  capital - (totalMm - legMm)           -- totalMm = Σ cachedMm
```

Because `reservedMm` could be inflated by a leg on an attacker-controlled-oracle market, a loss on
a *different* market surfaced as unbacked `shortfall` (drawn from that market's `I_m`) instead of
debiting the trader's capital, and the recovery leg claimed it back. Bouncing real volatility on a
shielded portfolio therefore walked insurance out while `C + I + R + S == V` still held.

## Why the proofs missed it

`Refinement.lean` proved leaf functions (`settleAndRefreshLeg`, `syncLegMargins`, `sweepResolvedDust`,
`applyExecSpread`) at an earlier point, but the containment arithmetic used in the deployed
handler (`reservedMm`) diverged from `Spec` (`cachedMm`). The `cross_margin_isolation_envelope`
theorem is stated over `cachedMm`; nothing proved `Program` implements that same quantity.

## The fix that landed (`a056eee`)

`syncLegMargins` now zeroes reservations (`reservedMm := 0`, `totalReservedMm := 0`) and both
`settleAndRefreshLeg` and `handleLiquidate` bound loss/fee by `capital` (the proven `cachedMm`
semantics), removing the ratchet. That is sufficient: no sheet of `reservedMm` remains to shield
capital from a real-market loss.

## Runnable repro (pure BigInt model, no chain)

`percolator-bounty/poc/` models the handlers exactly (`mulDiv64`, `syncLegMargins`,
`settleAndRefreshLeg`, trade/liquidate). See the companion gist: scenarios reproduce the matcher
LP drain, the insurance-draw threshold, and the cross-market firewall. Recommended addition below.

## Suggested regression test (would have caught this)

A LiteSVM test that:
1. Creates an attacker market `N` with a caller-controlled oracle and a large `mmBps`.
2. Opens a portfolio with a shield leg on `N` and a real leg on a market `M`.
3. Bounces `M`'s mark (dip → rally) for several cycles while refreshing/liquidating.
4. Asserts `M.insurance` is **unchanged** and `capital' >= totalMm` after every settle.

On the pre-`a056eee` build this drains `I_m`; on the current build it is a no-op. That is the
regression that locks the fix.
