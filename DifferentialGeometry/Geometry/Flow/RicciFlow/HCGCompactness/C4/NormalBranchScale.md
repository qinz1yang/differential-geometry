# NormalBranchScale

## Role

This module is the relative-scale acceptance layer for the explicit selected
normal branch.  It combines the proportional phase-radius producer, the
fixed-`q` normal endpoint worker, and the transported intrinsic branch.

## Current state

- `normalBrHat` is the direct covering-scale inequality: if `c < a * D`, then
  `c * lambda D R < a * mu R`.
- `normalBrAccept` chooses global positive coefficients `aq`, `aδ`, and `aρ`.
  For every `R >= 0` it selects one `q = aq * mu R` and one explicit target
  radius `δ >= aδ * mu R`, uniformly before quantifying over the sequence index
  and center.
- Its `HasNormalBrFull` conclusion explicitly retains `NormalDiagFence`, the
  common consumer ball, the whole quantitative `δ` target ball in the intrinsic
  branch domain, both full transport equalities, and the inverse formula on the
  whole target and on `closedBall 0 δ`.
- `normalBrScale` is the compatibility projection to the older
  `HasNormalBranchDom` consumer interface, so existing cage code is unchanged.
- The transported intrinsic branch contains the image under `normalPair` of the
  common closed model ball of radius `aρ * mu R`.  The proof takes
  `aρ = min aδ (aq / 2)`, preserving a positive relative coefficient while
  satisfying both the target-ball and normal-coordinate source fences.
- Focused verification and the targeted module build passed without local
  warnings or local `sorry`s.  The finite-cage downstream focused check also
  passed after refreshing its missing upstream object; the cage module itself
  was not targeted-built.

## Frontier and accounting

- The architecture-2 acceptance theorem is complete: quantifier order,
  relative scales, full transport, whole-target domain, inverse formula, and
  backward-compatible consumers are all checked.
- `normalBrAccept`/`normalBrScale` are producer machinery.  The concrete
  theorem producing the already-stated `StepB1RawInput`, and textbook B1, are
  still unstated and 0% complete.
- Dedicated Step-B/B1 machinery is about 79%; Chapter 4 machinery about 75%;
  whole HCG compactness machinery about 52%.  Conditional and final compactness
  endpoints remain 0%.

## 2026-07-13 minimizing scale specialization

`HasNormalBrFull.mono` shrinks only the final closed-ball consumer radius while
retaining the selected branch, fence, target ball, transport identities, and
inverse formula.  `normalMinScale` consumes `normalBrAccept`, shrinks its
coefficient by both the phase and `gpRatio` budgets, and returns the full branch
together with the normal-coordinate radius bound and
`(aMin * mu R) / 2 <= expRadiusGp`.

Focused verification and the targeted refresh passed without a local `sorry`.
This completes Gate 6's sequence-uniform minimizing scale; it does not choose
the later physical finite-cage radius or prove `StepB1RawInput`.
# Relative selected normal-branch scale

`HasNormalBrFull` now retains an error `η < 1` and the quantitative inverse
approximation for the exact partial homeomorphism used by its selected
`IsNormalDiag` witness.  `normalBrAccept` obtains both from the strengthened
phase-scale and fixed-radius producers; `mono` preserves them unchanged.
This adds producer evidence only, not an endpoint assumption or a second
branch hierarchy.  Focused verification passed: `mono`, `toDom`,
`normalBrAccept`, and `normalMinScale` all retain or deliberately forget the
new witness at their stated API boundary.  The target theorem
`StepB1RawInput` remains unstated/unproved (0%); its dedicated Step-B/B1
machinery is about 88%, Chapter 4 machinery about 82%, and whole-HCG machinery
about 54%.
