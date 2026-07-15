# StepCAtomConv

## 2026-07-09 quadratic readout convergence

- Added the calculus producer taking simultaneous `C^infty` convergence of a
  bilinear-form field and a vector-valued coordinate map to convergence of
  `B(v,v)`.
- Added the fixed smooth scalar postcomposition used by the intrinsic Step-C
  bump atoms.
- The remaining Step-C frontier is to supply, on one shared finite-hat
  subsequence, the concrete transition-map convergence inputs and then join
  them to the already extracted origin metrics.
- Added `normalMetric_zero`, the origin-only moving-centre metric extraction,
  and its finite-slot common-subsequence form.  The origin-only route avoids
  the unavailable uniform lower bound for full normal-coordinate domains.
- Added the overlap formula for intrinsic atoms and the concrete conditional
  `stepCAtom_conv` producer from one shared metric/transition subsequence.
- Added `cutRaw_conv`, `rawWeights_conv`, and `cutWeights_conv`.  The last
  theorem proves its own uniform denominator bound: covered atoms force one
  base-killed raw numerator to be at least `1/2`, and this passes to the limit.
- The finite-dimensional composition wrapper avoids the continuous-linear-map
  `ProperSpace` instance diamond without adding an artificial hypothesis.
- Added the totalized `seqCenterD`, eventual live/dead center equalities, and
  chart-pulled sequence atoms.  `seqAtom_live_conv`, `seqAtom_dead_conv`, and
  `seqAtoms_conv` use tail locality to give every finite slot its honest limit;
  dead slots are zero and never require artificial transition-domain inputs.
- Added `LiveSlot` and `existsLiveMetric0`, so origin metrics are extracted on
  exactly the finite live subtype along one further subsequence of `L.phi`.
- Added `seqAtomChart_smooth`, routing source-atom smoothness through the
  globally smooth intrinsic atom and the exponential chart's smooth ball.
- The canonical tail-locality lemma lives in `MapConvergenceDeriv.lean` as
  `MapCInfConvOnCompacts.congr_eventually` and was independently verified.
- The live/dead wrappers, finite-slot assembly, and live origin-metric
  extraction passed focused verification. The former upstream Derivation wall
  was repaired on 2026-07-10; this module and the downstream atom package now
  also pass targeted builds.
- Added `seqCenterD_subseq` and `seqAtomChart_subseq`, the reindex adapters used
  to keep final strict-subsequence expressions in public `L.subseq` form.

## Progress accounting

- This metric/atom/weight convergence sub-brick: 100%.
- `StepB1RawInput` producer theorem: 0% (not yet stated or proved).
- Dedicated Step-B1 machinery: about 63%.
- Chapter 4 machinery: about 66%.
- Whole HCG compactness machinery: about 46%.
- Conditional and final compactness endpoints: 0%.

## 2026-07-13 lower-layer relocation

`normalMetric_zero` was moved without renaming to `StepBInputs.lean`, its
canonical home next to `normalCoordMetric`.  This module now consumes the
imported theorem and no longer carries a duplicate definition.  Focused
verification passed; the atom-convergence API and all consumer names are
unchanged.

## 2026-07-13 fixed-index scale input

`seqAtomChart_smooth` now takes the exact fixed-index
`Item3GpScaleAt ... pb r k` fact used by `seqAtom_contMDiff`. It no longer
requires a scale theorem for unrelated indices or ordered-net slots. Focused
verification and the narrow refresh passed.

The atom-convergence theorem remains complete as infrastructure. The concrete
`StepB1RawInput` producer and textbook B1 theorem remain 0%; dedicated
Step-B/B1 machinery is about 80%, Chapter 4 machinery about 76%, whole-HCG
machinery about 53%, and compactness endpoints remain 0%.

## 2026-07-13 totalized-centre distance readout

Added `seqCenterD_dist_eq`.  In the realized proper metric it identifies the
ordered-net radius exactly with the distance from the totalized centre
`seqCenterD` to the pointed basepoint.  The equality includes the dead-slot
case: `seqCenterD` is then the basepoint and both sides reduce to zero, so later
canonical-centre radius arguments do not need an artificial live-slot split.

The focused verification passed.  This helper is complete (100%) and supplies
only a radial readout for existing net data; it does not construct an arbitrary
partner-centre family or discharge `StrictDistInput`/Hessian estimates.
`StepB1RawInput`, textbook B1, and the compactness endpoints remain 0%.

## 2026-07-13 canonical finite-Pi derivative API

The atom-convergence proof now uses
`Analysis/Calculus/PiDeriv.iteratedFDeriv_pi` after the generic theorem was
moved out of `StepB1Producers`. This is a name/import-layer migration only;
focused verification passed and the convergence statement is unchanged.

## 2026-07-13 stable-disjoint atom branch

Added `atom_disjoint_conv`.  If the source chart maps into one finite source
hat and a target five-lambda ball is eventually disjoint from it, the target
chart-pulled atom converges in C-infinity to zero on the source domain.  The
proof combines `seqAtom_mem_hat` with `binter_of_mem_hat`; it needs no transition
map for the noninteracting target.  Focused verification passed.

This closes the low-level live-but-noninteracting branch that the earlier
live/dead split omitted.  Sparse atom packaging still has to combine this zero
branch with `InterSlot` transition limits on one common subsequence; that is
infrastructure, while `StepB1RawInput` and all endpoint theorems remain 0%.

## 2026-07-13 live origin-metric equivalence

Added `liveMetric0_equiv`.  Given the common `MapCInfConvOnCompacts` limit
returned by the live-slot origin-metric extraction, it proves at the common
origin that every live coefficient retains
`(1/2) * ‖v‖^2 ≤ gInf 0 alpha v v ≤ 2 * ‖v‖^2`.  The proof first takes the
finite-Pi coordinate of the pointwise limit and then evaluates the resulting
bilinear form, avoiding an expensive combined dependent-Pi elaboration.
Focused verification passed.

This prerequisite is complete (100%).  The producer-owned finite live-source
cover theorem is still not stated or proved (0%); this lemma supplies only its
limit-metric equivalence input.  The current broader accounting remains:
dedicated Step-B/B1 machinery about 80%, Chapter 4 machinery about 76%, whole
HCG machinery about 53%, and all compactness endpoint theorems 0%.
