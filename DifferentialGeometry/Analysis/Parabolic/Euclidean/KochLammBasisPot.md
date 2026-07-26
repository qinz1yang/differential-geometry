# KochLammBasisPot

## Durable value-level result

This file replaces the informal phrase "sum `heatPot1` over a basis" by an
honest operator-valued divergence source

`f₁ : ℝ × V → V →L[ℝ] F`.

The canonical `stdOrthonormalBasis` components define `klBasisPot` and the
finite sum `klBasisGrad` candidate.  `klFluxComp` proves that evaluation on
each unit basis vector preserves the two `KLSource1` radii.  Consequently:

- `klBasisPot_eq` identifies the realized finite sum with `heatPot0` plus the
  genuine finite directional `heatPot1` sum;
- `klBasisPot_zero` gives zero initial value;
- `klHeat0_sub`, `klHeat1_sub`, and `klBasisPot_sub` give linear subtraction
  after discharging the required Bochner integrability from source bounds;
- `klBasisPot_norm` gives the existing ordinary value constant plus
  `finrank ℝ V` times the existing unit-directional flux value constant.

No PDE identity, spatial derivative realization, or gradient estimate is
asserted here.

## Exact interface defect found

The current `KLSplit` takes `f₀ f₁ : ℝ × V → F` with one common codomain.
It therefore packages only one directional flux component; it cannot express
an `F`-valued ordinary source together with the genuine operator-valued flux
`V →L[ℝ] F`.  This file avoids modifying the claimed `KochLammSpaces.lean`
by accepting separate `KLSource0` and operator-valued `KLSource1` hypotheses.
A future consumer carrier must make those two codomains different (or store
the components explicitly); that is a statement-design change, not an
estimate proved in this file.

## Remaining analytic producer

`heatGrad0`, `heatGrad1`, and `klBasisGrad` are only candidates.  The existing
`heatTerm0_fderiv` and `heatTerm1_fderiv` identify derivatives of individual
integrands, but there is no theorem passing the flux derivative through the
terminal space-time integral under `KLSource1`.  A naive absolute
second-Gaussian-derivative majorant has the nonintegrable time singularity
`(t-s)^{-1}`.

The next faithful producer is therefore a weak spatial-gradient realization
for the finite sum together with the local cylinder `L²` and late-cylinder
`L^(n+4)` estimates.  The present generic `KLPath` has no weak-derivative
compatibility field, while the available `HasWeakPartialDeriv` API is scalar
and tied to coordinate Euclidean spaces.  This requires a generic
vector-valued weak-gradient bridge or an approved component carrier, followed
by the genuine parabolic energy / Calderon--Zygmund estimate.  A pointwise
`HasFDerivAt` theorem for every rough `KLSource1` input would be stronger than
the current hypotheses justify and was intentionally not fabricated.

## Verification state

- Source implementation and static placeholder/name checks: complete.
- Focused Lean verification: pending because the shared Edge check still owns
  the serialized Lean lane.
- `ricci_flow_unif_existence`: theorem-level 0%.
- `ricci_flow_forward_unique`: theorem-level 0%.
