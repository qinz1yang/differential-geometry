# B1 minimizing-branch ruling and executor handoff

Status: 2026-07-13, aligned branch `codex/short-time-existence-align`; Gates
1--6 are focused-green.  The true `expRadiusGp` floor, minimizing scale,
D-independent packing producer, canonical sigma tail, and finite-hat physical
cage/readout are checked.  The next B/C scale frontiers are full geodesic
convexity, the concrete outer source-slot diagonal, and the independent
Hessian/Neumann producer.

This file records the GPT Pro response to
`B1_INTRINSIC_REALIZED_CONSULT.md`, reconciled with the current live tree.  It
is an executor handoff, not a replacement for `B1_JOIN_HANDOFF.md`,
`CHAPTER4_PLAN.md`, or `PROJECT_MAP.md`.

## Ruling

Use the fourth route: capture the existing Hopf-Rinow minimizing intrinsic
tangent inside the explicit source of the selected quantitative branch.

For a controlled pair `(y, pt)`, obtain `v : TangentSpace I y` with

```lean
expMapIntrinsic (I := I) g hEnorm y v = pt
Real.sqrt (g.inner y v v) = (riemannianEDist I y pt).toReal
```

from `hopf_rinow_expMapIntrinsic_surjective_minimizing`.  Prove that
`<y, v>` belongs to the selected branch source by H6 metric equivalence and
the exact source transport.  Then use the branch left inverse to conclude

```lean
B.inv (y, pt) = (⟨y, v⟩ : TangentBundle I M).
```

The finite-hat critical path should use this minimizing tangent equality, not

```lean
B.inv (y, pt) = ⟨y, normalChartAt g y pt⟩.
```

This removes `expDiffeoRadius` and the qualitative
`expMapIntrinsic = expMap` radius from the selected-branch root equation.

Do not:

- prove quantitative `expMapIntrinsic = expMap` on the whole H6 tube;
- replace the global realized normal-coordinate API;
- infer minimization from a branch endpoint identity alone;
- add a uniform `expDiffeoRadius` lower bound as an endpoint or consumer input.

## Live implementation state

The ruling is implemented through Gate 6.  Continue from the post-packing
finite-cage/Item-3 frontier below; do not restart the completed gates.

1. `DiagInvBranch.inv_eq_of_exp` is present in
   `Geometry/Exponential/DiagInvBranch.lean` and focused-check passed.  Its
   stable proof is:

   ```lean
   simpa only [diagExp_apply, hexp] using B.left_inv hvsrc
   ```

   A broad `simp` is intentionally avoided because it unfolds the intrinsic
   exponential too far.

2. `C4/NormalBranchMin.lean` now has focused-green, sorry-free proofs of:

   - `normalTan_metric`;
   - `normalTanHome_target`;
   - Gate 1, `IsNormalDiag.tan_mem_of_small`;
   - Gate 2, `IsNormalDiag.inv_is_min`;
   - Gate 3a, `IsNormalDiag.halfSq_eq_inv`;
   - Gate 3b, `IsNormalDiag.halfSq_inf`;
   - Gate 4, `IsNormalDiag.grad_half_inv`.

3. The comparison layer now exports the focused-green producer
   `grad_halfSqDist_min`, which proves the gradient formula from an arbitrary
   minimizing intrinsic exponential tangent and has no qualitative-radius or
   realized-exp agreement input.

4. Gate 5 is focused-green: `centerOfMass.invB_eqn` is the generic finite-sum
   minimizer equation and `centerReadoutB_min` transports the selected inverse
   tangent sum to `chartCmEqnB = 0`. The route no longer uses
   `centerOfMass.eqnRadius`, `expDiffeoRadius`, or a normal-chart inverse at the
   moving center.

5. Gate 6 is focused-green: `normalMinScale` retains the full branch/fence/
   transport package while shrinking to a real H6-derived `expRadiusGp` floor.
   `NormalBranchCage.exists_slot_min` chooses that coefficient once before
   `D`, specializes it at the slotwise radius `rInf + 1`, and keeps the full
   branch data on one live-center tail.  The concrete `StepB1RawInput`,
   textbook B1, and compactness endpoints remain theorem-level 0%.

## Important correction to the Pro response -- RESOLVED 2026-07-13

The original response conflated the profile's `expMapC2Radius` floor with
`expRadiusGp`.  The repair was made at the canonical producer layers rather
than by adding an endpoint assumption:

- `gpCoerciveConst` is now the optimal unit-sphere coefficient and
  `le_gpCoerciveConst` compares every valid quadratic lower bound with it;
- H6 origin metric equivalence plus low-layer `normalMetric_zero` proves
  `(1 / 2 : Real) <= gpCoerciveConst`;
- `NormalRadiusProfile.gpRatio`, `floor_le_expGp`, and
  `mul_lambda_lt_expGp` give the actual relative intrinsic-radius floor;
- `tan_mem_of_small` retains its explicit pointwise hypothesis, while
  `normalMinScale` now supplies that hypothesis honestly on the sequence
  profile.

## Implementation order

### Gate 1: verify pointwise source capture -- COMPLETE

Focused-check `NormalBranchMin.lean` as saved.  The intended proof is:

1. convert `riemannianEDist I x y < ENNReal.ofReal (rho / 2)` to a finite
   real-distance bound;
2. use `hb.chart_mem_norm_le` to obtain normal-chart source membership and
   `norm (normalChartAt g x y) < rho`;
3. use `NormalDiagFence` to put that base coordinate in `normalExpPD.source`;
4. invert `normalTanHome` at `<y, v>`;
5. use `normalTan_metric` plus `hb.metric_equiv` to prove the model fibre norm
   is below `2 * rho`;
6. use `2 * rho < q` and `IsNormalDiag.full_transport` to enter
   `B.hom.source`.

The saved theorem currently uses non-strict `rho <= hb.radius k x` and
`rho / 2 <= expRadiusGp ...`; that is sufficient because the point and tangent
bounds are strict.

### Gate 2: capture the minimizing tangent -- COMPLETE

Add `IsNormalDiag.inv_is_min` in `NormalBranchMin.lean` only after Gate 1 is
green.  For pairs controlled by

```lean
max (riemannianEDist I x y) (riemannianEDist I x pt) <
  ENNReal.ofReal (rho / 2),
```

use the triangle inequality and Hopf-Rinow to obtain `v`, then apply
`tan_mem_of_small` and `B.inv_eq_of_exp`.

Prefer the witness conclusion:

```lean
exists v : TangentSpace I y,
  B.inv (y, pt) = (⟨y, v⟩ : TangentBundle I (X.obj k).M) /\
  expMapIntrinsic (I := I) (X.obj k).metric
    (normal_enorm (I := I) (X.obj k)) y v = pt /\
  Real.sqrt ((X.obj k).metric.inner y v v) =
    (riemannianEDist I y pt).toReal
```

Also export branch-domain membership or the selected-inverse norm equality if
that materially shortens the next theorem.  Do not create a wrapper that merely
renames all of these hypotheses.

### Gate 3: identify half squared distance on the branch -- COMPLETE

Still in `NormalBranchMin.lean`, prove:

```lean
IsNormalDiag.halfSq_eq_inv
```

using `inv_is_min`, the Hopf-Rinow metric realization, and nonnegativity when
squaring.  Then prove:

```lean
IsNormalDiag.halfSq_inf
```

on the explicit half-cage by agreement with

```lean
fun y =>
  (1 / 2 : Real) *
    g.inner (B.inv (y, pt)).proj
      (B.inv (y, pt)).snd (B.inv (y, pt)).snd.
```

Use the selected branch's existing all-order inverse smoothness.  This replaces
the HCG use of the qualitative `exists_halfSqDist_md` radius.

Both `halfSq_eq_inv` and `halfSq_inf` are focused-green and sorry-free.

### Gate 4: branch-native first variation -- COMPLETE

Prove:

```lean
IsNormalDiag.grad_half_inv
```

The minimizing identity is essential.  For `pt != y`, rescale the minimizing
tangent to unit speed and reuse the intrinsic fixed-endpoint variation and
`halfSqDist_dir_deriv`.  For `pt = y`, use the existing local-minimum argument
and the selected inverse of the diagonal zero tangent.

Do not infer the gradient formula from smoothness plus an intrinsic endpoint
identity; that would omit minimization.

Implemented through the generic producer `grad_halfSqDist_min`, then consumed
by `IsNormalDiag.grad_half_inv` together with `inv_is_min` and `halfSq_inf`.

### Gate 5: center equation and readout root -- COMPLETE

At the generic center layer, add the shortest branch-parametric analogue of the
existing center first-order equation, preferably named

```lean
centerOfMass.invB_eqn
```

It should reuse the current minimizer and finite-sum derivative proof and accept
the branch-native summand gradient identities.

Then add in `StepCCmDomain.lean`:

```lean
centerReadoutB_min
```

with proof route:

```text
grad_half_inv for every summand
-> centerOfMass.invB_eqn
-> fixed-trivialization fibre equivalence
-> chartCmEqnB = 0.
```

The finite-hat path should migrate to this theorem.  Keep
`centerReadoutB_zero` only as a compatibility entrypoint while it still has
users; do not route the new producer back through `normalChartAt` or
`centerOfMass.eqnRadius`.

The checked implementation is `centerOfMass.invB_eqn` plus
`centerReadoutB_min`. The latter derives branch-domain and fixed-trivialization
base membership from the half-cage and uses the selected branch directly.

### Gate 6: sequence-uniform scale -- COMPLETE

The checked chain is:

1. the exponential layer selects the optimal `gpCoerciveConst` and exports
   `le_gpCoerciveConst`;
2. `StepBInputs` proves the H6 origin bound `half_le_gpConst`;
3. `NormalRadiusProfile` defines positive `gpRatio` and proves the relative
   `expRadiusGp` floor;
4. `HasNormalBrFull.mono` shrinks only the consumer ball, and
   `normalMinScale` returns the full branch/fence/transport package together
   with `(aMin * mu R) / 2 <= expRadiusGp`;
5. `NormalBranchCage.exists_live_min` specializes that result to every live
   center on one common tail.
6. `Item3GpScaleAt` / `Item3GpScaleTail` record only the finite packing slots,
   `NormalRadiusProfile.gpScaleTail` proves the tail with the exact `c = 8`
   budget from `lambda_window`, and the Step-C atom/package/join consumers now
   use those weaker facts.
7. `Item3RadiusAt` / `Item3RadiusTail` record the finite exp-diffeomorphism
   radii, and `NormalRadiusProfile.radiusScaleTail` proves their injectivity and
   `expMapC2Radius` bounds.
8. `MetricCompactBase.exists_item3D` aggregates the book factor and all current
   scalar constraints before packing; `exists_item3OfBase` and
   `item3ScaleTails` return the original fixed-`D` bundle and both tails.
9. The same one-shot selector accepts an arbitrary extra scalar budget.  With
   `physScale_of_extra` it gives `8 * exp C < aMin * D`, while also choosing
   `16 < ratio * D` and `8 * lambda D 0 < r₁` before packing.
10. `NormalRadiusProfile.sigmaCenterTail` and
    `MetricCompactnessInputs.exists_sigmaField` close the canonical
    `seqCenterD` sigma family, including its `r₁` bound.
11. `lamInf_lt_halfMin`, `exists_rad_cage`, and
    `HasNormalBrFull.exists_cm_eqn` close the physical half-cage.  The
    dead-slot-aware `hat_mem_live`/`hat_dist_centerD` bridge and
    `exists_hat_cm_eqn` then select a positive-weight live slot and produce the
    actual selected-branch center equation without a strict radius floor.

The fixed-`D` order is also checked without modifying downstream consumers:
`MetricCompactBase` carries `forall D > 0, PackingBound D`,
`MetricCompactBase.exists_item3D` makes one scalar choice satisfying the
`gpRatio`, item-3 radius, and `stepA_cap_le` budgets, and
`MetricCompactnessInputs.ofBase` instantiates packing only after that choice.

The post-packing `g_p` ledger is now checked. Direct `4 * lambda` uses budget
`c = 4`, while `lambda_window` makes finite-slot `4 * lamInf` require `c = 8`;
the producer chooses that budget before packing and proves the common finite
tail after `A_D(r)` is available. The old all-index `Item3GpScaleInput` remains
only as compatibility API.

The legacy all-index `Item3RadiusInput` is no longer needed on the canonical
finite-slot route.  The canonical sigma and configuration-dependent physical
cage/readout ledgers are now checked.  The selected-branch Hessian/Neumann
estimate is checked separately; the full geodesic-convexity scale remains open.
No endpoint radius field is to be added.

## Independent frontier

The selected-branch Hessian/Neumann producer is now closed.  The independent
frontier is the `lbl413` positive Hessian lower bound needed for
`StrictDistInput`; center-equation invertibility alone does not imply the
per-target geodesic strict-convexity field.

The physical scalar and pair-index ledgers are no longer missing:
`exists_rad_cage` produces the common threshold and `exists_hat_cm_eqn`
consumes the actual stabilized configuration.  `StepCHatReadout` now intersects
the sequence tail with `exists_hat_radius`, constructs the filled
`CenterInput`, and leaves `StrictDistInput` as the final honest continuation.

The canonical sigma family is also closed.  The finite source-slot diagonal has
now migrated completely to H6 and the temporary S6 endpoint field is gone.
`InterSlot` plus `exists_pair_trans` extracts only stably intersecting live
targets, while `atom_disjoint_conv` supplies the genuine zero branch for stable
nonintersection.  `atom_trans_small` and `weight_trans_small` prove that actual
active support maps into the reverse six-lambda ball.

The support-local capstone choice is now settled and its reusable consumer is
focused-green. `hatSuppPtsOfComp`, `unifHatSuppData`, and `hatSuppCageData`
restrict decoded composition to actual nonzero-weight support and fill zero
entries by the identity. `HasAtomWeightLim.weight_data` supplies normalized
limit weights, while `exists_supp_fin` extracts one common H6 subsequence for
all dependent source/interaction pairs. No whole-cage `hKV0` inference or
stronger endpoint radius field was introduced.

The approved source-local/global architecture is now implemented and
focused-green. `existsAtomWeightH6_of_innerCover` and
`weight_data_of_innerCover` expose the strict-inner-ball normalization premise;
`exists_live_source_cover` produces the finite source-chart cover;
`exists_supp_pts_fin` retains old-`L` `InterSlot`s and totalizes only points;
and `exists_hat_cm_tail_support` consumes the pulled-back limit weights on
their nonzero support. `StepCSupportCapstone.exists_supp_cm_fin` takes one
master subsequence and the two required finite maxima, while
`exists_cm_on_source` gives the global-ball existential-source witness.  No
global chart selector, glued weight, overlap equality, parallel radius API, or
arbitrary-`y` endpoint field was introduced.

`StepB1RawInput`, textbook B1, and the conditional compactness endpoint remain
theorem-level 0%.  The source-local/global conditional capstone is 100%, but
its `StrictDistInput` continuation still requires the independent Item-3 full
convexity producer before it can feed the concrete B1 raw package.  The selected
minimizing-branch Gates 1--6 and Hessian/Neumann machinery are 100%; dedicated
Step-B/B1 machinery is about 90%, Chapter 4 machinery about 83%, and whole-HCG
machinery about 55%.

## Ownership and coordination

The completed Gate 1--6 files remain the B/C lane's settled base:
`DiagInvBranch.lean`, `NormalBranchMin.lean`, `StepCCenterOfMass.lean`,
`StepCCmDomain.lean`, `NormalBranchScale.lean`, `NormalBranchCage.lean`, and
`StepCHatReadout.lean`, `StepCSourceCover.lean`, `StepCProducers.lean`, and
`StepCSupportCapstone.lean`.  Future work should claim only the concrete
Item-3 or independent `StrictDistInput` files it actually edits,
coordinate with Step D through file claims, and preserve these checked
interfaces unless a live contradiction is found.

## 2026-07-14 strict-distance frontier audit

The routine Hopf--Rinow part is now closed in
`Geometry/Comparison/GeodesicConvexity.lean`: `minimizingVec` and `minJoin`
give a focused-green two-point minimizing selector with its length, endpoints,
and time-continuity facts.  It uses the unconditional
`hopf_rinow_expMapIntrinsic_surjective_minimizing` endpoint and does not enter
the older sorry-tainted headline in `Comparison/HopfRinow.lean`.

The branch-native `lbl412` identity is now checked as
`IsNormalDiag.hess_half_inv`.  The separate Neumann route is also closed:
`cm_deriv_inv` proves the selected readout has an invertible center derivative,
`cm_sol_strict` invokes the strict IFT on the same branch, and
`HasHatCmStrict` retains the root, derivative, and strict local solution through
the support-local and global finite-cover capstones.  No branch-specific input,
glued weight, chart selector, or endpoint radius assumption was added.

The remaining `StrictDistInput` producer is not a local packaging proof.  The
current second-variation layer proves only nonnegativity of the index form for
a minimizing geodesic.  The missing comparison producer is now precisely the
`lbl413` uniform positive lower bound for the Hessian of `halfSqDist` on the
controlled cut-locus-free ball.  Its along-`minJoin` consequence must prove
small-ball confinement and the per-target `StrictConvexOn` field.  A live API
audit found three materially different routes; the quantitative normal-chart
and Koszul route is the leading candidate, while compactness/continuity and
Jacobi/Rauch require substantially more infrastructure.  This is the next
consult point.

The selected-branch Hessian/Neumann support route is 100%; the
`StrictDistInput` producer, concrete `StepB1RawInput`, textbook B1, and
compactness endpoints remain theorem-level 0%.  Dedicated Step-B/B1 machinery
is about 90%, Chapter 4 machinery about 83%, and whole-HCG machinery about 55%.

## 2026-07-14 strict-distance producer checked

This section supersedes the consult frontier immediately above.  The leading
quantitative normal-chart/Koszul route has now been implemented and verified:

1. `IsNormalDiag.hess_inv_sixth` proves the uniform positive Hessian lower
   bound in the controlled normal chart.
2. `HasNormalBrFull.hess_pos` transports it to the retained selected branch.
3. `deriv2_comp_geo_on` and `strictConvex_geo` convert the local Hessian bound
   into strict convexity along minimizing geodesics.
4. `HasNormalBrFull.strict_dist` proves the complete `StrictDistInput`,
   including nonzero speed, endpoint identities, and midpoint confinement.
5. `exists_hat_cm_min` and the canonical support/global capstones consume that
   producer directly with the fixed `minJoin`.

The scale ledger is `R + 6 * rad < rho / 2`, obtained from the existing
finite cage by applying it once to `3 * rad`.  The quarter-ball premise is
derived inside `exists_slot_min`; no endpoint-radius assumption or parallel
branch API was added.

The next honest frontier is the concrete `StepB1RawInput` producer.  That
producer, the textbook B1 theorem, and every compactness endpoint remain
theorem-level **0%**.  The selected-branch Gates 1--6 and
Hessian/Neumann/strict-distance machinery are **100%**; dedicated Step-B/B1
machinery is about **94%**, Chapter 4 machinery about **86%**, and whole-HCG
machinery about **57%**.
