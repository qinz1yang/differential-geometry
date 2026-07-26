# KochLammGerms

## Proved-in-source content

This file realizes each exact Koch--Lamm cylinder bound as a coordinate in the
complete dependent `lp ∞` ambients from `KochLammData`.

- `klScaleMemLp` derives local `MemLp` from a finite scaled norm bound and the
  strict positivity of the radius scale.
- `klScaleToLpLe` transfers the same `ENNReal` estimate to the real norm of the
  scaled `Lp` class.
- `klMkGerm` packages a uniformly bounded family of scaled local classes in
  dependent `lp ∞`, and `klMkGermNormLe` proves its uniform norm bound.
- `src0Data` and `src1Data` realize the two source arms.
- `pathGradData` realizes the two gradient arms of a path.  The bounded
  continuous value arm is intentionally separate: `KLPath` stores only its
  quantitative value bound.

No coordinate is postulated and no heat mapping estimate is assumed.

## Honest boundary

The ambient germs still need a closed compatibility predicate.  Overlapping
germs must agree, and the path germs must be the weak spatial derivative of
the bounded continuous value field.  The natural closed-graph proof uses the
local `L²` arm and the integration-by-parts stability APIs already present in
the Euclidean Sobolev library.

The late `L^(n+4)` heat-potential arm additionally requires a genuine
parabolic Calderón--Zygmund producer.  Repository search found only spatial
slice `Lp` heat-kernel bounds; those do not imply the needed spacetime
singular-integral estimate.

## Verification state

- Source realization layer: 80%.
- Focused Lean check: pending until the upstream `KochLammSpaces` export
  completes.
- Realized compatible carrier: 45% (ambient plus realization source; closed
  graph missing).
- Heat potential `Y_T → X_T`: 15% machinery, 0% as a complete theorem.
- Endpoint `ricci_flow_forward_unique`: 0%.

