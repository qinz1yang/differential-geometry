# GPT Pro consultation: the minimizing half-segment inverse branch

> **Resolved 2026-07-24.**  The ruling selects a fixed early split
> `s₀ = 1 / 4`, a canonical fixed-first `ExpInvBranch`, nonconjugacy extended
> slightly past endpoint time `1`, and a whole-tail intrinsic Bishop theorem
> with an explicit dimension-one branch.  Implementation status is maintained
> in `CALABI_BRANCH_PLAN.md`.

## Repository visibility

Repository:

```text
https://github.com/liao9yuan/differential-geometry
```

Branch:

```text
codex/short-time-existence-align
```

Remote-visible commit:

```text
00fd26cb1d4b4ced391847aac4b4baa9f22b3520
```

The aligned local tree is currently at
`5329be63a9a5322eb2c4c53ed26e4fca605c5f3b`, and the implementation described
below also includes uncommitted changes.  In particular, the new fixed-first
branch-radius/Hessian/Laplacian modules and the latest weakest-assumption
cleanup are not all visible on GitHub.  Treat the signatures and verification
status quoted here as authoritative; use the remote repository only for the
surrounding APIs.

## Requested ruling

We need the smallest honest producer chain for the fixed-metric Calabi upper
support used by the no-extra-input complete Shi estimate.

Please rule on all of the following together:

1. the canonical branch object for a fixed-source exponential inverse around a
   **nonzero** minimizing launch vector;
2. the minimizing-geodesic theorem that produces this branch at an early
   interior Calabi point;
3. the global intrinsic mean-curvature comparison along that minimizing tail;
4. the exact Lean-facing declarations and file order;
5. whether the proposed `ExpInvBranch` factoring below is the correct canonical
   repair, or whether a smaller existing-object route is available.

Do not solve the problem by adding a branch, no-conjugacy, cut-time,
injectivity-radius, `ConnectedSpace`, or Laplacian-comparison hypothesis to the
final support theorem.  These must be produced.

## Final fixed-metric target

For a complete finite-dimensional Riemannian manifold, a Ricci lower bound

```text
Ric >= -(d - 1) * q^2 * g,
```

points `O != x`, and finite positive distance

```text
r = edist_g(O,x).toReal,
```

we need a smooth local upper support `rho` for the distance at `x` with

```text
rho x = r,
eventually near x: edist_g(O,y).toReal <= rho y,
|grad rho|^2 <= 1 at x,
Delta rho x <= 2 * (d - 1) / r + (d - 1) * q.
```

The Ricci-flow consumer writes the curvature scale as
`q = sqrt (Lambda / (d - 1))`, yielding the equivalent displayed bound

```text
2 * (d - 1) / r + sqrt ((d - 1) * Lambda).
```

The final theorem should be a fixed-metric theorem in
`Geometry/Comparison/DistanceCalabi.lean`.  Ricci-flow time differentiation
belongs later in `Evolution/DistanceBarrier.lean`.

## Verified lower geometry

The complete fixed-first radial bridge is focused- and exact-green:

```text
IntrinsicGauss.intrinsic_gauss
BranchRadius.exp_inv_mfderiv
BranchRadius.inv_exp_mfderiv
BranchRadius.grad_branchEnergy
BranchRadius.grad_branchRadius
EndpointShape.branchHess_jacobi
EndpointShape.branchHess_shape
MetricTrace.LineSplit.trace_eq_line_add
ChartBridge.Laplacian.lap_eq_hess_on
RadialLaplacian.branchLap_eq_mean
RadialLaplacian.radialLap_eq_mean
```

The raw capstone has the required normalization:

```text
Delta r_B (radialCurve g p x t)
  = curveMean g gamma V t / sqrt (g_p(x,x)).
```

No extra radius hierarchy or `ConnectedSpace` assumption was added.

The following comparison chain has also been weakened to remove its stale
`ConnectedSpace` requirement and is focused- and exact-current:

```text
JacobiVariation.jacobi_zero_of_lt
JacobiVariation.exists_jacobi_zero
NormalChartMeasure.exists_radialJacobi_zero_radius
RadialGram.radial_wronsk_zero
BishopRadial.exists_radial_cmp
BishopRadial.exists_radial_mean
```

`intrinsic_jacobi_d0` was weakened at the same time.

## Why the current terminal-tail helper is insufficient

`DistanceCalabi.calabi_tail_of` starts with a minimizing geodesic
`gamma : O -> x` and a `DiagInvBranch` centered at the zero vector over `x`.
Openness at that zero vector selects `s0` close to `1`, so that

```text
q   = gamma s0,
ell = (1 - s0) * r
```

and the short terminal launch from `q` to `x` lies in the branch source.

There is no lower bound `r / 2 <= ell`.  Bishop comparison on this tail gives

```text
(d - 1) / ell + (d - 1) * q,
```

which becomes worse as the selected tail becomes shorter and cannot imply the
required `2 * (d - 1) / r` pole term.

The correct Calabi point must be early:

```text
0 < s0 < 1 / 2,
q = gamma s0,
ell = (1 - s0) * r >= r / 2.
```

At such a point the launch vector in `T_q M` is nonzero and need not lie in a
zero-centered normal neighborhood.

## A second mismatch: the current radial comparison is local

`BishopRadial.exists_radial_mean` is not a global minimizing-segment theorem.
It produces one small radius and assumes, among other things,

```text
norm x < radius,
b < 1,
t in (0,b),
norm (t * x) < expMapC2Radius g p.
```

Scaling the transverse family does not enlarge the permitted radial launch.
Therefore constructing a nonzero inverse branch alone is not enough for an
arbitrarily long Calabi tail.

The lower generic theorem `BishopJacobi.curveMean_le_hyp` is already stated for
an abstract constant-speed Jacobi family on `(0,b)`.  The pole input
`BishopRadial.radialRatio_auto` is only eventual near zero.  The likely honest
route is:

1. use intrinsic geodesic/Jacobi fields along the whole minimizing tail;
2. use raw/intrinsic germ agreement only near zero to transfer the positive
   density-ratio pole input;
3. obtain linear independence on the whole open tail from no conjugacy;
4. apply `curveMean_le_hyp` globally;
5. use `HyperbolicModel.hypMeanCurv_le` at the endpoint.

Please confirm this or identify a smaller checked route.

## Existing no-conjugacy and IFT APIs do not yet compose

The checked theorem

```lean
Variation.not_conj_of_min
```

proves that a unit-speed minimizing geodesic from its original base has no
conjugate vector at an interior radial time.  The Calabi branch instead needs
nonconjugacy of the tail vector for

```text
exp_q : T_q M -> M,
q = gamma s0,
exp_q(uTail) = x.
```

The missing step is a segment-shift/reversal theorem.  One natural proof is:

1. reverse the original minimizing geodesic from `x` to `O`;
2. apply `not_conj_of_min` at the interior point `q`;
3. transport nonconjugacy through reversal to conclude that `x` is not
   conjugate to `q` along the forward tail.

No checked conjugacy-symmetry/reversal adapter currently packages this.

There is then a second API seam.  `not IsConjVec g hEnorm q uTail` says that
the vector-slot `mfderiv` of `expMapIntrinsic q` is injective.  The generic
manifold IFT in `Geometry/Coordinates/LocalDiffeoIFT.lean` wants an invertible
chart `fderiv`.  The finite-dimensional mfderiv-to-chart-invertibility bridge
and the resulting local partial diffeomorphism at an arbitrary vector are not
packaged.

## Branch-object architecture choice

The current object is:

```lean
structure DiagInvBranch (g) (hEnorm) (p : M) where
  hom : OpenPartialHomeomorph (TangentBundle I M) (M x M)
  zero_mem : <p, 0> in hom.source
  hom_eq : EqOn hom (diagExp g hEnorm) hom.source
  inv_inf : ContMDiffOn (I.prod I) I.tangent infinity hom.symm hom.target
```

Its `zero_mem` field is essential to its current zero-section role, but is
irrelevant to the fixed-first Hessian calculation once a nonzero source vector
is supplied.  Gluing a local branch around a nonzero vector to an unrelated
zero branch merely to satisfy `zero_mem` looks artificial.

The candidate canonical lower object is:

```lean
structure ExpInvBranch
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall y w,
      normE w = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) where
  hom : PartialDiffeomorph selfModel I E M infinity
  hom_eq :
    Set.EqOn
      (fun u : E =>
        expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from u))
      hom
      hom.source
```

The intended factoring would be:

```text
DiagInvBranch.fixed p : ExpInvBranch g hEnorm p
not IsConjVec g hEnorm p u
  -> exists B : ExpInvBranch g hEnorm p, u in B.hom.source
```

Then `branchEnergy`, `branchRadius`, their first/second variation theorems, and
`branchLap_eq_mean` would consume `ExpInvBranch`; current diagonal consumers
would use the `.fixed` projection.

Please decide whether this is the correct one-canonical-API factoring.  In
particular:

- Should `ExpInvBranch` be a `PartialDiffeomorph`, an
  `OpenPartialHomeomorph` plus inverse smoothness, or a smaller explicit germ?
- Can every `DiagInvBranch` be sliced canonically at a fixed first point
  without adding a non-open singleton-product source?
- Is it better to generalize `DiagInvBranch` itself, and if so, how should its
  now-misleading zero-section parameter and `zero_mem` field be handled?
- Is there a smaller way to construct the needed arbitrary-point diagonal
  branch without gluing unrelated local branches?

Do not create two independent branch-radius/Hessian hierarchies.

## Requested Lean-facing chain

Please give corrected declarations, preferably with public names at most twenty
characters, for the following roles.

### 1. Shift/reversal of no conjugacy

A theorem of the form

```lean
tail_not_conj_of_min
    (v : TangentSpace I O)
    (hvMin : v realizes the finite distance O -> x)
    {s0 : Real} (hs0 : s0 in Ioo 0 1) :
  let velocity := intrinsicVelocityLift g hEnorm O v
  let uTail := (1 - s0) * (velocity s0).snd
  not IsConjVec g hEnorm (velocity s0).proj uTail
```

No new minimizing predicate should be introduced unless it is genuinely the
smallest reusable way to state segment minimality.

### 2. Nonconjugacy to a fixed-first branch

A theorem of the form

```lean
branch_of_not_conj
    {p : M} {u : TangentSpace I p}
    (hu : not IsConjVec g hEnorm p u) :
  exists B : ExpInvBranch g hEnorm p,
    (u : E) in B.hom.source
```

State the exact finite-dimensional mfderiv/chart-IFT bridge needed internally.

### 3. Global intrinsic minimizing-tail comparison

A theorem which concludes at the tail endpoint

```text
curveMean / ell
  <= (d - 1) / ell + (d - 1) * q
```

under the Ricci lower bound, with no raw C2-radius restriction.  Please say
whether this should be:

- an intrinsic analogue/generalization of `exists_radial_mean`;
- a theorem specialized to a minimizing tail;
- or a direct assembly in `DistanceCalabi`.

Dimension one must be handled without assuming `0 < d - 1`; the transverse
family is `Fin 0` and the mean is zero.

### 4. Calabi branch producer

Ideally the preceding results should yield a producer with

```text
exists v s0 B,
  0 < s0
  and s0 < 1 / 2
  and ell = (1 - s0) * r
  and r / 2 <= ell
  and the tail launch belongs to B.source
  and B sends that launch to x.
```

Please give the smallest theorem statement that avoids repeating branch and
minimizing bookkeeping in the final support proof.

## Constraints

- No `ConnectedSpace M` in the final support or comparison theorem.
- No new endpoint injectivity-radius, cut-time, or branch assumption.
- No extra raw/intrinsic agreement radius for a long minimizing segment.
- No HCG/C4 import in the lower exponential/comparison layer.
- No support-side wrapper that merely assumes the missing Laplacian estimate.
- Preserve the current `DiagInvBranch` API for existing consumers unless a
  carefully staged canonical factoring is required.
- Keep the Ricci-flow time derivative and cutoff assembly downstream.
- Separate theorem completion from supporting machinery in the accounting.

## Current accounting

- Fixed-first radial Hessian/Laplacian route: theorem and machinery **100%**.
- Bishop connectedness cleanup: **100%**, focused- and exact-current.
- `calabiDist_support`: unstated, theorem-level **0%**.
- Dedicated fixed-metric Calabi-support machinery: approximately **55%**.
- `scaledDist_calabiUpperSupport_of_sol`: theorem-level **0%**.
- Selected Route B-prime complete-Shi producer machinery: approximately
  **45%** after this deeper length/global-comparison audit.
- Barrier Bernstein consumer: **100%**.
- Dedicated P4 consumer/assembly machinery: approximately **98%**.
- Whole HCG supporting machinery: approximately **60%**.
- Unconditional `compactnessSol`: theorem-level **0%**.

The requested answer is an architecture ruling plus the next concrete
declarations, not a restatement of the classical Calabi trick.
