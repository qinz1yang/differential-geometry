# Regularized L-action

## Implemented surface

`RegAction.lean` defines the direct square-root-time Lagrangian `lRegLag` and
its oriented interval action `lRegAction`. The bridge theorems
`lRegDensity_eq`, `lLength_reg`, and `lLength_reg_ae` identify these definitions
with the earlier square-reparameterized density and ordinary L-length. The AE
version requires no curve differentiability assumptions.

`lRegAction_congr` shows that the action depends only on the curve on the
unordered open interval. It transports the manifold derivative from genuine
neighborhood equality and discards the remaining endpoint as a null singleton.
Consequently `lLength_sqrt` proves

```text
lLength (sqrtReparam alpha) 0 tau = lRegAction alpha 0 (sqrt tau)
```

for every raw `alpha` and `tau >= 0`; it never asks for differentiability of
the singular backward-time curve at `tau = 0`.

The variation layer provides:

- `lRegLag_deriv` and `lRegAction_deriv`, with compact-interval domination
  produced internally;
- `lRegEuler_var_c1`, joint `C¹` regularity of the regularized Euler residual
  throughout the regular flow-time region, including square-root time zero;
- `lRegAction_first`, the endpoint-pairing minus Euler-integral formula;
- `lRegEulerInt_deriv`, the derivative of the negative Euler-residual integral,
  and `lRegJacobi_contOn`, compact-interval continuity of the resulting Jacobi
  pairing; these genuine producers are public for moving-node second variation;
- `lRegAction_second`, the supplied-smooth-variation, fixed-endpoint second
  variation formula along an `IsLRegCurveOn` central curve.

The direct-method preparation now also provides:

- `lRegAction_add` and `lRegAction_sum`, the adjacent-interval and finite
  subdivision identities with honest interval-integrability hypotheses. These
  are the algebraic bridge used when local chart lower bounds are assembled
  into the action on the whole curve;
- `lScalar_lower`, a uniform lower bound for the complete scalar-potential
  term on a compact square-root-time interval and compact manifold, using only
  `ScalarSTContOn` and carrier membership;
- `lRegAction_lower`, the scalar interval-integral inequality obtained from
  pointwise metric coercivity and a potential lower bound, with explicit and
  honest integrability hypotheses;
- `lAction_consts`, which moves the compact-slab constants outside the curve
  quantifier. Thus one pair of constants controls an entire bounded-action
  sequence rather than being re-chosen curve by curve;
- `lRegAction_bound`, which produces both constants for an actual
  `IsSolutionOn` from the native compact moving-metric time slab and scalar
  continuity.  It controls the fixed-reference `L²` kinetic energy without
  claiming that scalar curvature is nonnegative;
- `lRefEnergy_bound`, which combines that coercive lower bound with an action
  upper bound and solves explicitly for the canonical fixed-reference
  `curveEnergy`. This is the uniform estimate consumed by the compactness
  stage;
- `lEdistOf_bound`, which restricts that global energy budget to arbitrary
  nested subintervals and applies the fixed-metric energy--distance estimate.
  It gives the intrinsic reference-metric square-root modulus required by
  Arzela--Ascoli for every smooth competitor in the bounded-action family.

The final formula is

```text
d/du|_0 (d/dv lRegAction(f(v,-))|_u) = 2 lRegIndex(Y,Y).
```

It is valid on oriented intervals whose endpoints may include `s = 0`.  The
proof does not use an epsilon limit and does not ask the caller for domination,
integrability, minimizing, or semidefiniteness hypotheses.

## Regularity route

The first variation is obtained from joint `C²` regularity of the Lagrangian,
the fixed-metric variation formula, and the regularized moving-metric product
rule.  The second variation differentiates the Euler integral under the
integral sign on a compact parameter-time rectangle.

For the endpoint-zero index integrability, the proof uses the exported
`lVarMetric_c2` with metric time and curve time independent.  Differentiating
the squared norm only in the curve-time direction identifies
`dQ(s^2,s)/2` with `<D_s Y,Y>` by `inner_deriv_at`.  This makes the boundary
pairing `C¹`; `lRegIndex_balance` then expresses the index density as a
continuous combination of its derivative and the Jacobi pairing.

## Verification and frontier

Focused verification passes without warnings, including the adjacent-interval
and finite-subdivision action identities. The two variation-specific producers
used by moving-node second variation were exposed without changing their proof
bodies, and the file plus its targeted module refresh pass. The newly used time-slab export
also passes its targeted module refresh. The downstream `lAction_subseq`
consumer is focused-green, so the family-uniform constants and reference-energy
bound have also been checked in their intended compactness use.
The inverse square-root bridge was also independently audited for both interval
orientations and the degenerate case `tau = 0`. The file contains no `sorry`,
`admit`, new axiom, reference-tree import, supplied domination wrapper, or
epsilon-to-zero argument.

This completes the regularized action, second-variation, inverse square-root
bridge, compact-slab coercivity, action-to-energy estimate, and the resulting
reference-distance square-root modulus. Together with `ActionCompact.lean`, it
also completes the bounded-action C0 subsequence stage. It does not prove
existence of an L-minimizer or reduced-volume monotonicity. `redVolume_anti`
remains unstated and unproved (0%); `exists_lMinimizer` remains unstated and
unproved (0%), with its dedicated direct-method machinery about 35--45%.
Dedicated L-geometry machinery is approximately 68--72% complete, while
reusable generic prerequisites are approximately 97--99% complete. P2 remains
below 1%, and the full Poincare program remains approximately 3--5% complete.
