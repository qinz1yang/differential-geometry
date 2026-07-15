# GoodCoveringItem3.lean — `lbl383` item 3 net-level wiring (B5)

Verification passed, sorry-free (2026-06-13). The B5 layer-bridge from the Step A net
(over `PointedRiemannianManifold`s) to the unconditional exp ball diffeomorphism
(`ExpBallDiffeo.exists_expBall_diffeo_of_lt`, item 3a).

## What's here

- **`PointedRiemannianManifold.exists_expBall_diffeo`** — the layer bridge: for a bundled
  pointed manifold `Y`, center `c`, radius `ρ ≤ expMapC2Radius Y.metric c` with
  `ofReal ρ < injRadius Y.metric c`, exp is a `C^1` partial diffeomorphism on `ball 0 ρ`.
  Installs `Y`'s stored instances (`Y.topology`…`Y.t2TangentBundle`) via `letI` (the
  `MetricComplete` pattern), then calls `exists_expBall_diffeo_of_lt`.
- **`Item3RadiusAt` / `Item3RadiusTail`** — the canonical finite-slot book
  scale. `item3RadiusFactor` records the exact multiplier, and the profile
  producer proves the injectivity/`expMapC2Radius` tail after packing.
- **`Item3RadiusInput` / `exists_seqItem3Diffeo`** — legacy all-index
  compatibility API. New assembly uses `exists_item3Diffeo` at a fixed slot.

## Status

The exp-ball diffeomorphism brick is complete: 3a is
`exists_expBall_diffeo_of_lt`, and the net-level compatibility consumer is
`exists_seqItem3Diffeo`.  The canonical finite-slot route below no longer asks
for the legacy all-index radius input.  Full textbook item 3 is not complete:
the geodesic-convexity scale and its §5 Hessian/physical-cage assembly remain a
separate theorem-level frontier.

Targeted build of `GoodCoveringItem3` passed after the Hopf--Rinow proper-realization
replacement, confirming the new `properMetricOn` producer assumptions do not affect this
packaged-data consumer.

## 2026-07-01, subsequence projection

Added `Item3RadiusInput.subseq`.  It reindexes the item-3 exp-ball radius
discipline along a subsequence, using `InjRadiusDecayInput.subseq` and the
reindexed proper-metric family `fun k => P (f k)`.

This is a producer-closure brick for the finite-hat Step-C pipeline: later
diagonal/refinement steps can carry the item-3 radius input to the reindexed
sequence without restating the exp-ball hypotheses.  Verification passed.

## Lean gotchas

- The `𝓘(ℝ, E)` model-with-corners notation needs `open scoped Manifold`; without it,
  `𝓘(Real, E)` is a parse error (`𝓘` read as a function applied to a pair).
- Bundle instances are `letI`'d from `Y`'s fields BOTH in the statement (so `injRadius`/
  `expMapC2Radius`/`PartialDiffeomorph` elaborate) and re-`letI`'d in the proof body.
- No ProperMetricOn-vs-manifold topology diamond bites here: the net center is just an
  element of `Y.M`; only `realizes` is needed to relate the radius scales (absorbed into
  the honest-input).

## 2026-07-13 finite-slot `g_p` scale API

The old `Item3GpScaleInput` quantified over every sequence index and every
natural-numbered ordered-net slot. No live consumer required that strength.
It remains as a compatibility declaration, with `at` and `to_tail`
projections.

The canonical construction API is now `Item3GpScaleAt`, for one fixed index
and `Fin (pb.A r)`, together with `Item3GpScaleTail`, its eventual form.
`Item3GpScaleTail.subseq` preserves the tail under later refinements. Focused
verification and the narrow refresh passed.

This closes only the `g_p` finite-slot quantifier split. `SigmaScaleField` and
the physical cage remain separate, and compactness endpoints remain 0%.

## 2026-07-13 finite-slot item-3 radius

Added the canonical radius factor `item3RadiusFactor`, its positivity theorem,
`Item3RadiusAt` / `Item3RadiusTail`, subsequence stability, and the fixed-index
consumer `exists_item3Diffeo`.  The legacy all-index `Item3RadiusInput` remains
only for compatibility.

The finite tail uses radius
`item3RadiusFactor hd D * L.lamInf γ`.  Its two strict bounds are produced in
`MetricCompactnessInputs.radiusScaleTail`; no endpoint radius field was added.
Focused verification and the targeted refresh passed.  This closes the
exp-diffeomorphism radius quantifiers, not the book's full geodesic-convexity
claim, which remains theorem-level 0%.
