# HarmonicMassRegularity

## Status

Source implementation is present on `codex/analytic-producers-e87b` but has
not yet been checked by Lean.  A unique shared Edge build was still active
while this file was written, so the required lock discipline prohibited a
focused check or targeted build.  Nothing below is claimed green until that
check is run.

Endpoint status is unchanged: `ricci_flow_forward_unique` remains theorem
level **0%**.  This file is intermediate harmonic-map heat-flow machinery.

## Concrete producers written

* `hmfSpecMassPt_cd` reconstructs the full pointwise bilinear mass from its
  finitely many canonical-basis coefficients and states joint `C¹` regularity
  on `ball 0 R × univ` for one positive, spatially uniform radius.
* `hmfSpecMassPt_lip` gives a single pointwise state Lipschitz constant valid
  for every `x : M` on one smaller closed coefficient ball.
* `hmfSpecMass_lip` integrates that estimate against an arbitrary fixed
  Riemannian volume measure.  The coefficient radius is independent of the
  chosen domain metric; the Lipschitz constant includes its finite volume.
* `hmfMassFam_lip` packages the genuinely uniform-in-time version: one upper
  bound for the total volumes on `K` yields one radius and one state
  Lipschitz constant for every `t ∈ K`.
* `hmfSpecMassQ_lip` is the exact fixed-background specialization
  `u ↦ hmfSpecMassOp q q S u` requested by the solver lane.
* `hmfSpecMass_zero` identifies the faithful mass at state zero with the
  existing `hmfFinMass` restricted along `hmfSpecIncl`.
* `hmfSpecMass_lower` combines that identity with `hmfFinMass_lower`, giving
  the consumer-shaped zero-state coercive lower bound under reverse volume
  domination.  This is designed to feed `StateCoerciveMass.coerOn_of_lip`
  without choosing a separate radius for each time.
* `hmfStateTime_cont` uses the real-time `integral_family_cont` theorem
  directly.  Its radius is chosen before the metric family and the compact
  time set; only the moving Riemannian volume depends on time.

## Mathematical route

For every canonical coefficient basis vector, `hmfSpecCoeff_cd` supplies a
jointly `C²` tangent-bundle section.  The proof also includes the zero
direction.  Since the direction index is the finite type `Option {i // i ∈
S}`, taking the finite infimum of the returned positive radii is valid even
when `S` is empty.  On that common ball, the two derivative sections are
paired by the jointly regular target metric.  The resulting scalar matrix
entries are `C¹`, and finite-dimensional matrix-unit expansion reconstructs
the complete bilinear continuous-linear-map value.

For Lipschitz control, the partial coefficient Fréchet derivative is jointly
continuous on a smaller closed ball times the compact manifold.  Compactness
gives one derivative bound, the convex mean-value theorem gives one
pointwise Lipschitz constant, and the Bochner integral norm estimate inserts
the finite domain volume.  This avoids differentiating a moving measure and
does not use `FamilyContinuityParam`.

## Static checks completed

* the implementation was added only through `apply_patch`;
* no `sorry`, `admit`, `axiom`, or `opaque` declaration occurs in the new
  Lean source;
* all new public theorem names are at most 20 characters;
* the file is below the 3000-line hand-maintained-file limit;
* `HarmonicStateMass.lean` was not edited by this lane.

## Elaboration risks to check once the shared build releases

1. `ContMDiffAt.mfderiv` must simplify through
   `inTangentCoordinates_model_space` and `mfderiv_eq_fderiv` for the generic
   Banach-valued coefficient slice in `partialFderiv_cont`.
2. The finite-infimum proof uses the inferred `Fintype (Option ι)` and may
   need explicit `s := Finset.univ` arguments at one elaboration site.
3. The `Bundle.contMDiffWithinAt_totalSpace` readout of the scalar trivial
   bundle may need the same explicit bundle-family annotation used in other
   geometric files.
4. The `change` step in `hmfSpecMass_lip` relies on reducibility of
   `hmfSpecMassOp`; if Lean does not unfold it automatically, an explicit
   `simp only [hmfSpecMassOp]` is the intended local repair.
5. The zero-state proof composes the joint map theorem with the fixed-spatial
   inclusion.  Its smoothness order and open-ball neighbourhood are explicit,
   but product-model coercions may require a `simpa` at the composition line.

## Remaining consumer-level issue

`hmfSpecMass_lower` supplies the time-uniform zero-state lower bound as soon
as one common reverse-volume constant is available.  `hmfMassFam_lip`
supplies the matching common state-Lipschitz estimate from a common upper
bound on total moving volume.  The one-sided reverse-volume hypothesis does
not by itself imply that upper bound.  The compact chart-Gram family route in
`CompactVolumeEquiv` is the natural producer, but it is a separate, currently
source-only file and was not imported here.

## Honest percentages

* mathematical/source assembly in this file: **85%**;
* Lean elaboration and repair: **0%** until the focused check runs;
* verified producer completion: **0%**;
* `ricci_flow_forward_unique`: **0%**;
* `ricci_flow_unif_existence`: unaffected by this file.
