# P4 complete-Shi cutoff architecture consultation

## 2026-07-23 ruling

The selected architecture is **Route B-prime**: use a point-centered
Calabi/barrier cutoff and a compact-support maximum principle which asks for a
smooth upper support only at a selected negative minimizer.  A globally smooth
solution-generated `ShiCutoffData` is no longer the mandatory producer.

The first two implementation bricks are checked and exact-current:

- `ParabolicUpperSupportAt` and
  `strict_barrier_cpt_of_upperSupport` in `MaximumPrinciple/ScalarWeak.lean`;
- the extracted smooth `ShiCutoffData`, the local
  `ShiCutoffLowerSupportAt`, the point-centered `ShiBarrierCutoffData`, and
  `ShiCutoffData.toBarrierAt` in `Evolution/ShiCutoffData.lean`.

Both support structures are necessarily data structures in `Type`, rather
than the `Prop` structures displayed below, because consumers project the
selected support function.  The separate pointwise spatial differentiability
fields were omitted as redundant consequences of the neighborhood fields.

The basepoint-free completeness package, connectivity-free intrinsic-geodesic
producer spine, point-pair Hopf--Rinow endpoint, and finite closed-eball
compactness are now focused- and exact-current.  The next true producer
frontier is therefore the evolving-distance Calabi upper support.  In
particular, `scaledDist_calabiUpperSupport_of_sol` and
`shiBarrierCutoff_of_sol` remain theorem-level 0%, while
`BernsteinTower.estimate_barrier_at` is under source implementation.  The
legacy `estimate_complete` is not to be filled.

Repository: `https://github.com/liao9yuan/differential-geometry`

Branch: `codex/short-time-existence-align`

GitHub-visible branch commit and local aligned-tree HEAD:
`f84a3cc8574e6b52cb2a4a58930bffd0fd139b4d`

The remote branch contains the surrounding repository at that commit.  The
fixed-order Bernstein capstone, the conditional HCG cutoff adapter, and the
route-neutral preparation described below are newer uncommitted aligned-tree
changes and therefore are not visible on GitHub.  Treat the exact signatures
quoted here as authoritative when reviewing the architecture; use the remote
tree for their existing dependencies and consumers.

## Question

We need an architecture ruling for the independent Bernstein-localization
blocker in the arbitrary-dimensional complete-noncompact Shi route: producing
localization data from a complete bounded-curvature Ricci flow.  The separate
direct curvature tower (`rmResidual_cost`, `towerHeatSol_raw`, and
`towerHeatSol_any`) is now focused- and exact-green.  The later
`srcCovLip_of_soln` producer is now independently focused- and exact-green and
is not part of this cutoff ruling.

### Verified consumer state

File:
`DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/BernsteinComplete.lean`

The checked cutoff interface is:

```lean
structure ShiCutoffData
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) where
  chi : Nat -> Real -> M -> Real
  err : Nat -> Real
  support : Nat -> Set M
  err_nonneg : forall n, 0 <= err n
  err_tendsto : Filter.Tendsto err Filter.atTop (nhds 0)
  support_compact : forall n, IsCompact (support n)
  support_zero : forall n t, t ∈ Set.Icc 0 T ->
    forall x, x ∉ support n -> chi n t x = 0
  range : forall n t x, t ∈ Set.Icc 0 T ->
    chi n t x ∈ Set.Icc (0 : Real) 1
  exhausts : forall t x, t ∈ Set.Icc 0 T ->
    exists n0, forall n, n0 <= n -> chi n t x = 1
  joint_cont : forall n, ContinuousOn
    (fun p : Real × M => chi n p.1 p.2)
    (spacetimeSlab (M := M) T)
  time_diff : forall n t, t ∈ Set.Icc 0 T -> 0 < t -> forall x,
    DifferentiableWithinAt Real
      (fun s => chi n s x) (Set.Icc 0 T) t
  space_smooth : forall n t, t ∈ Set.Icc 0 T ->
    ContMDiff I 𝓘(Real, Real) ∞ (chi n t)
  grad_sq_le : forall n t, t ∈ Set.Icc 0 T -> 0 < t -> forall x,
    (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (chi n t) x)
        (gradientFun (I := I) (G.metric t) (chi n t) x)
      <= err n * chi n t x
  parabolic_le : forall n t, t ∈ Set.Icc 0 T -> 0 < t -> forall x,
    parabolicOperatorWithDrift (I := I) G T
      (fun _ y => (0 : TangentSpace I y)) (chi n) t x
      <= err n
```

The sign is intentional: the operator is `P = partial_t - Delta`, and the
localized upper estimate needs `P chi <= err`.

The localized Bernstein algebra is focused- and exact-green.  The capstone has
also been strengthened at source level to the fixed-order interface actually
needed by the solution wrapper:

```lean
theorem GfunCut_parabolic_le
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n : Nat} (hm : 1 <= m)
    (hgrad : TowerNormGradUpTo (I := I) B m)
    {t : Real} (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t)
    (x : M)
    (hIH : forall j, j < m ->
      t ^ j * B.w j t x <=
        (towerConst B.c B.alpha j) ^ 2 * B.K ^ 2)
    (hsmall : 2 * cut.err n * B.T * cutErrCoeff m <= 1) :
    parabolicOperatorWithDrift ... (GfunCut ... m n) t x <=
      textbookForce * B.K ^ 3 +
        9 * cut.err n * BernsteinTower.Gcoef (I := I) B m 0 * B.K ^ 2

theorem BernsteinTower.estimate_cutoff_at
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (m : Nat)
    (hgrad : TowerNormGradUpTo (I := I) B m) :
    forall t, t ∈ Set.Icc 0 B.T -> 0 < t -> forall x,
      t ^ m * B.w m t x <=
        (towerConst B.c B.alpha m) ^ 2 * B.K ^ 2
```

The previous `estimate_of_cutoff` is now only the all-order compatibility
wrapper obtained from `hgrad.upTo m`.  `MovingShiOpen` now contains the
finite-truncation design that retains the genuine tower through `m + 1` and
feeds only the Kato prefix through `m` to this capstone.  Both the fixed-order
capstone and this conditional adapter are focused- and exact-green.

The finite telescope absorbs every positive-level cutoff error.  The capstone
uses strong induction, `strict_barrier_cpt` on each uniform compact support,
eventual exact exhaustion at the requested point, and `err n -> 0`.  Thus the
Bernstein consumer should not be redesigned unless genuine `ShiCutoffData` is
too strong or false.

The curvature Kato input is also checked: every requested finite prefix is
produced for the solution by `towerNorm_grad_le` in
`Evolution/IteratedRmTowerHeatEq.lean`.

The old `BernsteinTower.estimate_complete` still has an intentional `sorry` and
an invalid interface.  Completeness, metric equivalence, and a Ricci lower bound
alone do not produce its localization.  It must not be filled or treated as a
trusted theorem.

### Desired producer role

The ideal solution theorem would live below HCG, probably in a new file
`DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ShiCutoff.lean`:

```lean
theorem shiCutoff_of_sol
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (O : M)
    {T K : Real}
    (hT : 0 < T)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hreg : Set.Ioc 0 T ⊆ D.regular)
    (hcomplete :
      -- canonical completeness of the metric S.base.metric 0
      MetricCompleteAtTheAnchor (I := I) (S.base.metric 0))
    (hK : 0 <= K)
    (hcurv : forall t ∈ Set.Icc 0 T, forall x : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 t x <= K) :
    Nonempty (ShiCutoffData (I := I) (flowG (I := I) S) T)
```

Please correct the exact lower-level completeness packaging.  Do not import
`HCGCompactness` merely to reuse its pointed `MetricComplete` predicate.  The
producer should need only one complete anchor slice plus the curvature bound.

In `MovingShiOpen`, the shifted solution already supplies the solution proof,
the closed slab and positive-time regularity, a global level-zero curvature
bound, anchor completeness, and slabwise metric equivalence.  It should adapt
these facts to the producer and then call the checked private
`complete_of_cutoff`, whose final analytic call is `estimate_cutoff_at`.

### Existing relevant APIs

- `BernsteinTower.estimate_cutoff_at` (with `estimate_of_cutoff` as its
  compatibility wrapper), `GfunCut_parabolic_le`, all graded
  cutoff-power/product/cross algebra, and `strict_barrier_cpt` are checked.
- `towerNorm_grad_le` supplies the exact Kato estimate.
- `Geometry/Comparison/HopfRinowProper.lean` supplies properness and compact
  closed balls for a complete fixed Riemannian metric.
- `Geometry/Metric/DistanceTent.lean` supplies `riemDistTent`, values in
  `[0,1]`, an exact inner plateau, controlled support, and a scale-sharp
  Lipschitz estimate `4/r`.
- `Analysis/Calculus/CompactCutoff.lean` supplies `exists_mfd_bump`, a smooth
  compactly supported plateau subordinate to a compact-in-open pair.
- `MovingShiOpen.lean` already proves private metric-PDE and slabwise metric
  equivalence facts from a curvature bound.
- `ricci_quad_sol` converts the curvature bound into a two-sided quadratic
  Ricci bound.
- Intrinsic gradient/Laplacian and parabolic product/sum/power APIs exist.

The local aligned tree also has the following route-neutral preparation.  These
declarations are newer than the GitHub-visible commit, so use the signatures
described here rather than expecting them in the remote tree:

- `Analysis/Calculus/CutoffProfile.lean` gives a smooth scalar plateau
  `CutoffProfile.value`, its exact one/zero regions, range in `[0,1]`,
  `deriv value s <= 0`, `(deriv value s)^2 <= C * value s`, and uniform
  first/second derivative bounds.
- `Geometry/Operator/Operators.lean` has `laplacian_comp`.
- `Geometry/Curvature/Realized/Operators.lean` has `heatDrift_comp`.
- `MaximumPrinciple/ScalarWeak.lean` has `parabolic_comp` for
  `P = partial_t - Delta + drift`.
- `Geometry/Metric/DistanceScaling.lean` has `edistOf_le_of_quad` and
  `le_edistOf_of_quad`, deriving `sqrt C` distance comparison from pointwise
  quadratic metric comparison.

All five pieces are focused-green and sorry-free; the three existing-module
chain rules are also exact-current.  They close scalar composition and
metric-to-distance plumbing only.  They provide neither a quantitative smooth
spacetime exhaustion nor a cut-locus barrier theorem.

### Missing APIs found by repository audit

No checked native theorem currently supplies:

1. a smooth proper exhaustion with quantitative global gradient and
   Hessian/Laplacian bounds;
2. a smooth spacetime exhaustion with `|grad chi_n|^2 <= err_n chi_n` and
   `(partial_t - Delta_g(t)) chi_n <= err_n`, `err_n -> 0`;
3. a global or barrier-form distance Laplacian comparison theorem;
4. a time-derivative estimate for `d_g(t)(O,x)` under Ricci flow;
5. a Calabi cut-locus support construction for evolving distance;
6. a barrier/viscosity version of `strict_barrier_cpt` using a smooth local
   support only at the selected bad minimum;
7. a quantitative smoothing theorem preserving range, compact support,
   exhaustion, gradient control, and the one-sided parabolic inequality;
8. a local Shi theorem with constants independent of injectivity radius and
   noncollapse.

`riemDistTent` is Lipschitz but not smooth.  `exists_mfd_bump` is smooth but
has no quantitative derivative bounds.  Properness gives compact supports but
no differential estimates.  A fixed-anchor bump estimate appears circular:
controlling `Delta_g(t)` through connection differences risks using precisely
the curvature-derivative estimates that Shi is meant to prove.

## Architecture decision requested

Choose the smallest mathematically honest route, or propose a better fourth
route.

### Route A: smooth spacetime exhaustion

Prove a genuine smooth exhaustion for a complete bounded-curvature Ricci flow,
then define `chi_n` through a one-dimensional profile and keep
`ShiCutoffData` unchanged.

If choosing A, state the precise theorem producing a smooth proper `rho(t,x)`
with estimates strong enough to make both cutoff errors tend to zero.  Explain
why bounded curvature plus completeness suffices without injectivity radius or
noncollapse, and how the proof avoids circular use of Shi derivatives.

The smallest sufficient output found by the local audit would have one
nonnegative `rho : Real -> M -> Real`, joint continuity, positive-time
time-differentiability, spatial smoothness, and one constant `A` such that on
the slab

```text
|grad rho|^2 <= A,
(partial_t - Delta_g(t)) rho >= -A,
```

together with uniformly compact spacetime sublevels

```text
{x | exists t in [0,T], rho(t,x) <= R}.
```

Composing this with the checked decreasing scalar profile gives
`grad_sq_le = O(R^-2) * chi` and `parabolic_le = O(R^-1) + O(R^-2)`.
Please decide whether bounded curvature and one complete anchor slice really
produce this package noncircularly.  If not, reject Route A explicitly rather
than adding it as a new assumption.

### Route B: Calabi/barrier consumer

Use a distance-based cutoff and Calabi's trick at the selected spacetime
minimum.  Replace or supplement `estimate_cutoff_at` with a barrier-localized
consumer only if the smooth record is genuinely too strong.

If choosing B, specify the weakest barrier-cutoff predicate and show exactly
how the checked graded recurrence is reused.  Determine whether a profile like
`eta (exp (A*t) * d_g(t)(O,x) / R)` has the correct sign for
`P = partial_t - Delta`, which distance inequalities are required, and how the
cut locus is handled without falsely asserting global smoothness.

### Route C: local Shi estimate

Bypass `ShiCutoffData`, prove a local curvature-derivative estimate on
parabolic balls, and exhaust the complete manifold.

If choosing C, explain how the constants avoid injectivity-radius, harmonic-
radius, or noncollapse dependence, and whether this route actually avoids the
same distance-Laplacian/Calabi infrastructure.

## Constraints

- arbitrary finite dimension;
- no `CompactSpace M`;
- no injectivity-radius, volume noncollapse, connectedness, or higher initial
  derivative assumptions;
- only one complete anchor slice and one global curvature bound on the larger
  left-buffered slab;
- no new HCG input field;
- do not preserve the unsupported `estimate_complete` as a trusted theorem;
- do not hide the analysis in a new assumption or polished wrapper;
- generic metric/comparison facts stay below Ricci flow;
- the solution cutoff/local-Shi producer belongs under `Evolution/`;
- `MovingShiOpen` should only assemble these producers;
- state explicitly if `shiCutoff_of_sol` is too strong or false as written.

## Required answer

Give a decisive architecture verdict and then the next five Lean-facing
declarations in dependency order.  For each declaration give:

- exact theorem/definition signature;
- canonical file/module and import direction;
- minimal hypotheses;
- mathematical proof route;
- which checked theorem it consumes;
- whether it is routine Lean work, a missing API theorem, or substantial new
  analysis.

Also give:

1. the exact final replacement call inside `movingShi_of_bound`;
2. which current declarations become obsolete or compatibility-only;
3. whether `ShiCutoffData` should remain unchanged;
4. the first theorem to implement immediately;
5. an honest feasibility estimate for Routes A, B, and C, including the largest
   expected formalization obstacle.

Do not answer merely "use standard Shi cutoffs".  The answer must identify the
actual distance, Laplacian, time-variation, cut-locus, smoothing, or local-
estimate theorems that need to be formalized.
