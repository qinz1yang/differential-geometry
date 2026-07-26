# GPT Pro consultation: the missing radial Laplacian--Jacobi bridge

## Repository visibility

Repository:

<https://github.com/liao9yuan/differential-geometry>

Branch:

`codex/short-time-existence-align`

Remote-visible baseline commit:

`00fd26cb1d4b4ced391847aac4b4baa9f22b3520`

Important visibility caveat:

The live shared worktree contains substantial uncommitted work after that
commit. In particular, several APIs named below are newer locally than the
remote baseline. Please reason from the declarations and summaries quoted in
this prompt, and clearly distinguish anything that can be checked against
GitHub from anything that depends on the uncommitted live tree.

## Requested ruling

We are implementing the point-centred Calabi/barrier route for the
complete-noncompact Bernstein maximum principle. The next unique second-order
geometry frontier is a fixed-metric theorem identifying the spatial Laplacian
of a locally smooth radial function with the trace of the radial Jacobi shape
operator.

Please give:

1. the mathematically correct normalization and theorem statement;
2. the smallest honest chain of reusable Lean declarations;
3. the canonical file/layer for each declaration;
4. a proof route using the existing endpoint variation, selected inverse
   branch, Hessian, and Laplacian APIs;
5. an explicit ruling on whether the fixed-first inverse branch or the
   moving-base half-squared-distance route is smaller;
6. exact additional hypotheses, if any, that are genuinely mathematical;
7. a list of which existing declarations should be generalized or moved
   lower, rather than wrapped at the HCG layer.

Do not solve the gap by adding an assumed Hessian comparison, assumed
Laplacian comparison, or another polished input predicate. The goal is the
actual geometric producer.

## Critical normalization correction

The current volume-comparison radial curve is

```lean
def radialCurve
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) (t : Real) : M :=
  expMap (I := I) g p (show TangentSpace I p from t • x)
```

and the corresponding field is

```lean
def radialJacobiField
    (g : SmoothRiemannianMetric I M) (p : M)
    (x w : E) (t : Real) :
    TangentSpace I (expMap (I := I) g p (t • x)) :=
  mfderiv 𝓘(Real, Real) I
    (fun s : Real => expMap (I := I) g p (t • (x + s • w))) 0 1
```

Thus `radialCurve g p x` has constant speed

```lean
a := Real.sqrt (g.inner p x x),
```

not unit speed. This is already exposed by

```lean
radial_speed_sq_eq :
  g.inner (radialCurve g p x t)
    (curveVelocity (radialCurve g p x) t)
    (curveVelocity (radialCurve g p x) t)
  = g.inner p x x
```

inside the local exponential range.

Consequently, for

```lean
V i t := radialJacobiField g p x (v i) t
```

the correct spatial identity should be

```text
Δ distance_p (radialCurve g p x t)
  = curveMean g (radialCurve g p x) V t / a,
```

not the unnormalised equality with `curveMean`.

The Euclidean check is decisive:

```text
V_i(t) = t v_i,
curveShape(t) = (1/t) Id,
curveMean(t) = (d - 1)/t,
Δ distance_p(exp_p(t x)) = (d - 1)/(t |x|).
```

This normalization also matches the checked comparison theorem

```lean
exists_radial_mean
```

whose model term is

```lean
hypMeanCurv
  (q * Real.sqrt (g.inner p x x))
  (Module.finrank Real E - 1) t.
```

Dividing by `a` converts this to the usual spatial model
`(d - 1) q coth(q a t)`.

An alternative is to state the bridge for a unit-speed geodesic
`γ(s) = exp_p(s u)`, `g_p(u,u)=1`, evaluated at physical time `s=r`.
Then the division by `a` disappears. Please rule which parameterization should
be canonical. Existing Bishop/Jacobi consumers use the first one, so a
unit-speed theorem still needs a short rescaling corollary.

## Existing checked API

### Selected intrinsic inverse branch

File:

`DifferentialGeometry/Geometry/Exponential/DiagInvBranch.lean`

The structure

```lean
DiagInvBranch g hEnorm p
```

stores a smooth local inverse of

```lean
diagExp g hEnorm : TangentBundle I M → M × M.
```

Relevant declarations:

```lean
DiagInvBranch.inv
DiagInvBranch.dom
DiagInvBranch.right_inv
DiagInvBranch.left_inv
DiagInvBranch.inv_eq_of_exp
DiagInvBranch.proj_eq
DiagInvBranch.inv_snd_inf
DiagInvBranch.inv_fst_inf
DiagInvBranch.exp_eq
```

The parameter `p` is the centre at which the branch was selected. A later
fixed source point `q` may be any nearby point whose relevant pairs lie in the
same branch domain. This distinction matters in the Calabi construction:
the branch can be selected near `(x,x)`, while the short final segment starts
at a nearby midpoint `q`.

`inv_fst_inf` gives smoothness of

```lean
z ↦ B.inv (q, z)
```

as a tangent-bundle-valued map on any set where `(p,z) ∈ B.dom`.

What is not present:

- the derivative of this fixed-first inverse;
- a gradient theorem for its fiber norm;
- a relation between that derivative and endpoint Jacobi fields;
- a radial Hessian or radial Laplacian theorem.

### Intrinsic endpoint Jacobi variation

Files:

```text
DifferentialGeometry/Geometry/Exponential/IntrinsicVelocity.lean
DifferentialGeometry/Geometry/Exponential/JacobiVariation.lean
```

Relevant declarations:

```lean
intrinsicGeodesic
intrinsicVar_smooth
intrinsicFiber_smooth
intrinsic_jacobi
intrinsic_jacobi_one
intrinsic_jacobi_d0
commute_ds_dt_intrinsic
```

`intrinsic_jacobi` supplies the all-time Jacobi field obtained by varying the
initial velocity. `intrinsic_jacobi_one` identifies its endpoint with the
vector-slot manifold derivative of `expMapIntrinsic`.

What is not present:

- differentiation of a local inverse of `expMapIntrinsic`;
- a theorem saying that the derivative of the terminal unit radial field in
  an endpoint direction is the terminal covariant derivative of the
  corresponding Jacobi field, divided by the launch speed.

### Jacobi shape and comparison

Files:

```text
DifferentialGeometry/Geometry/Comparison/Variation/JacobiShape.lean
DifferentialGeometry/Geometry/Comparison/Volume/BishopJacobi.lean
DifferentialGeometry/Geometry/Comparison/Volume/BishopRadial.lean
DifferentialGeometry/Geometry/Comparison/Volume/RadialGronwall.lean
```

Definitions:

```lean
curveShape g γ V t := (curveGram g γ V t)⁻¹ * curveMixedGram g γ V t
curveMean  g γ V t := Matrix.trace (curveShape g γ V t)
```

Checked consumers include:

```lean
shape_eq_coeff
mean_riccati_le
curveMean_le_hyp
exists_radial_mean
radial_speed_sq_eq
```

They establish the Riccati comparison for a chosen transverse Jacobi family,
but do not identify its trace with the geometric Laplacian of a radial scalar.

### Scalar Hessian and Laplacian

Files:

```text
DifferentialGeometry/Geometry/Operator/Hessian.lean
DifferentialGeometry/Geometry/Operator/HessianTrace.lean
DifferentialGeometry/Geometry/Operator/HessianTraceRealization.lean
DifferentialGeometry/Geometry/Connection/ChartBridge/Hessian.lean
DifferentialGeometry/Geometry/Comparison/HessianAlongGeodesic.lean
```

Relevant declarations:

```lean
hessFun
hessFun_eq_cov_grad
hessFun_congr
scalarLap_canon
scalarLapTraceAt_of_nablaDu
deriv2_comp_geo
deriv2_comp_geo_on
```

These realize a smooth scalar's Laplacian as the metric trace of its Hessian,
and identify a Hessian diagonal value along a geodesic with the second
ordinary derivative of the scalar along that geodesic.

What is not present:

- the mixed endpoint Hessian/Jacobi identity;
- a trace theorem for a non-orthonormal transverse Jacobi basis using its Gram
  inverse;
- the radial Hessian vanishing statement in the unit radial direction.

### Existing high-level half-squared-distance facts

File:

`DifferentialGeometry/Geometry/Flow/RicciFlow/HCGCompactness/C4/NormalBranchMin.lean`

The C4-specific selected-minimizing-branch layer already has:

```lean
IsNormalDiag.halfSq_eq_inv
IsNormalDiag.grad_half_inv
IsNormalDiag.hess_half_inv
```

In particular, `hess_half_inv` writes the Hessian of
`CenterOfMass.halfSqDist pt` as the metric pairing with the covariant
derivative of the negative moving-base inverse vector

```lean
z ↦ -(B.inv (z, pt)).snd.
```

This is useful evidence for the first-variation side, but it is in a
sequence-specific C4 layer and still does not identify the derivative of that
inverse vector with an endpoint Jacobi shape. A lower geometric theorem may be
extracted from its proof, but the final missing second-order identity cannot
be obtained by merely importing this C4 theorem.

### Second variation

Files:

```text
DifferentialGeometry/Geometry/Comparison/Variation/SecondVariation.lean
DifferentialGeometry/Geometry/Comparison/Variation/SecondVariationMinimiser.lean
```

Available:

```lean
indexForm
second_variation_of_arcLength_eq_indexForm
indexForm_nonneg_of_minimising_geodesic
```

No checked theorem was found that reduces the index form of a Jacobi field to
its endpoint boundary pairing, and the current second-variation theorem is not
already packaged as the endpoint-varying Hessian of distance.

## Three audited proof routes and their exact stop points

### Route 1: gradient of branch radius, then commute the endpoint variation

Define locally

```lean
rB z :=
  Real.sqrt
    (g.inner (B.inv (p,z)).proj
      (B.inv (p,z)).snd (B.inv (p,z)).snd).
```

On the branch domain, `B.proj_eq` reduces the base to `p`.

Desired steps:

1. prove `rB` is smooth near a nonzero endpoint;
2. prove `gradientFun g rB (γ t) = curveVelocity γ t / a`;
3. vary the endpoint through the exponential map;
4. use torsion-freeness / `commute_ds_dt_intrinsic` to show

   ```text
   Hess rB (V_i(t), V_j(t))
     = g(D_t V_i(t), V_j(t)) / a;
   ```

5. trace this identity with the inverse transverse Gram matrix;
6. prove the unit radial Hessian term is zero;
7. use the transverse-plus-radial orthogonal decomposition to identify the
   full Laplacian.

Stop point:

No existing theorem supplies step 2, step 4, or the trace decomposition in
step 7. `intrinsic_jacobi_one` only identifies endpoint differentials, and
`commute_ds_dt_intrinsic` applies to a smooth two-parameter geodesic variation;
the endpoint branch must still be differentiated and matched to that
variation.

### Route 2: half squared distance and a square-root Hessian chain rule

Let `e = (1/2) rB^2`. Use the existing first-variation pattern for
half-squared distance and aim for

```text
Hess rB
  = (1 / rB) • (Hess e - drB ⊗ drB).
```

On transverse directions the rank-one term vanishes, so it would suffice to
identify `Hess e` with the Jacobi boundary form.

Stop point:

The high-level `hess_half_inv` only rewrites `Hess e` as a derivative of the
moving-base inverse field. The repository still lacks the theorem relating
that derivative to the endpoint Jacobi derivative (or, equivalently, the
reverse-geodesic/fixed-first branch relation). A generic Hessian square-root
chain-rule adapter also appears to be missing, although it is routine once the
geometric derivative theorem exists.

This route does not avoid the main geometric frontier.

### Route 3: second variation / index form

Use the second variation of length for an endpoint-varying geodesic variation,
then use the Jacobi equation to reduce the index form to the endpoint boundary
pairing.

Stop point:

The present second-variation theorem is not an endpoint-Hessian theorem, and
there is no checked Jacobi index-form boundary reduction. This route therefore
requires at least two new substantial geometric declarations before reaching
the same trace step. It is not presently smaller than Route 1.

## Proposed canonical intermediate theorem

The most reusable missing theorem appears to be the bilinear endpoint
shape/Hessian identity, not the final trace equality.

In mathematical notation, let

```text
γ(t) = exp_p(t x),
a = sqrt(g_p(x,x)) > 0,
J_w(t) = ∂_s|₀ exp_p(t(x+s w)),
rB(z) = |B.inv(p,z)|_g.
```

For perpendicular `w₁,w₂` and a time `t>0` in the selected nonconjugate
branch:

```text
Hess(rB)_{γ(t)}(J_{w₁}(t), J_{w₂}(t))
  = g_{γ(t)}(D_t J_{w₁}(t), J_{w₂}(t)) / a.
```

A possible short public name is:

```lean
radialHess_eq_shape
```

Its natural home seems to be a new lower module such as:

```text
DifferentialGeometry/Geometry/Comparison/RadialLaplacian.lean
```

or a still-lower endpoint-variation module if the theorem does not use any
comparison inequality.

Please give a Lean-facing signature using the current
`DiagInvBranch`/`intrinsicGeodesic` APIs. In particular, decide:

- whether the theorem should use the total branch scalar `rB` above or accept
  an arbitrary local scalar equal to it on a neighborhood;
- whether the time should be general `t` or normalized to `1`;
- whether the Jacobi field should use `radialJacobiField` or the intrinsic
  variation from `intrinsic_jacobi`;
- whether perpendicularity is needed in the bilinear theorem itself or only
  in its trace corollary;
- whether minimality is unnecessary for this identity, with only local
  invertibility/nonconjugacy required.

## Proposed corrected trace theorem

After the bilinear theorem, the intended corollary is approximately:

```lean
theorem radialLap_eq_mean
    -- standard finite-dimensional Riemannian manifold instances
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ y w,
      ‖w‖₊ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (c p : M)
    (B : DiagInvBranch (I := I) g hEnorm c)
    (x : E) (v : ι → E) (t : Real)
    (hxne : x ≠ 0)
    (ht : 0 < t)
    (hsrc : -- ⟨p, t • x⟩ lies in B.hom.source;
            -- equivalently the endpoint pair lies in B.dom)
    (hvLI : LinearIndependent Real v)
    (hperp : ∀ i, g.inner p x (v i) = 0)
    (hcard : Fintype.card ι = Module.finrank Real E - 1) :
    let γ := radialCurve (I := I) g p x
    let V := fun i => radialJacobiField (I := I) g p x (v i)
    let rB := fun z =>
      Real.sqrt
        (g.inner (B.inv (p,z)).proj
          (B.inv (p,z)).snd (B.inv (p,z)).snd)
    laplacian (I := I) (LeviCivita (I := I) g) g rB (γ t) =
      curveMean (I := I) g γ V t /
        Real.sqrt (g.inner p x x)
```

This is schematic, not claimed to elaborate. Please provide the exact
minimal binder/domain shape.

In particular:

1. Is `hcard` plus `hvLI` plus `hperp` the cleanest way to express that the
   fields span the transverse subspace?
2. Can the final trace be proved directly from `curveGram⁻¹ *
   curveMixedGram`, avoiding the construction of an endpoint orthonormal
   basis?
3. Is a small finite-dimensional linear-algebra theorem needed:

   ```text
   full metric trace of a symmetric bilinear form
   = radial value + trace(G⁻¹ B)
   ```

   for a basis of the perpendicular hyperplane?
4. Which existing theorem should establish the radial value is zero?
   `deriv2_comp_geo` gives the diagonal Hessian along a geodesic, but the
   local branch radius must first be shown affine along the radial curve.

## Desired downstream result

Combining the corrected identity with `exists_radial_mean` should yield,
schematically,

```text
Δ rB (radialCurve g p x t)
  ≤ hypMeanCurv (q*a) (d-1) t / a
  ≤ (d-1)/(a*t) + (d-1)*q.
```

This is the fixed-time spatial input for a local Calabi upper support at a
point away from the cut locus. It must then be composed with the separate
fixed-path metric-time derivative. Neither that later parabolic assembly nor
the compactly supported maximum-principle consumer should be imported into
the lower radial geometry module.

## Architecture constraints

- Keep `DistanceCalabi.lean`, `DistanceBarrier.lean`, and Bernstein files as
  downstream consumers.
- Do not import an HCG/C4 file into a lower comparison or exponential module.
- Do not add a new assumption saying the desired Hessian or Laplacian estimate
  already holds.
- Do not create a second Jacobi-shape API parallel to `curveShape` and
  `curveMean`.
- Prefer intrinsic exponential/geodesic APIs for the canonical theorem.
  A compatibility corollary may serve the current raw-model
  `radialCurve`/`radialJacobiField` consumers.
- Do not add `ConnectedSpace M` unless a cited mathematical/API step genuinely
  requires it.
- Preserve the distinction between local invertibility/nonconjugacy and
  minimizing-distance equality. The shape identity should use the weakest
  correct condition; the Calabi support producer can separately prove that
  its branch radius agrees with distance at the touching point.
- Public theorem names should remain at most twenty characters.
- Please identify any statement above that is false or missing a scale,
  sign, transpose, endpoint-time, or basis condition.

## Pre-ruling accounting snapshot (historical)

The following figures are the snapshot that was submitted with the
consultation.  They are retained only to record the decision input; the live
verified accounting is in the implementation section below.

- `radialLap_eq_mean`: not implemented, theorem-level **0%**.
- Dedicated second-order bridge: API audit complete, proof machinery roughly
  **10--15%**; the actual endpoint Hessian/Jacobi identity is absent.
- Route B-prime Calabi/barrier producer machinery: roughly **35%**.  The
  terminal Calabi inverse-branch helper is checked.
- Final Calabi upper-support theorem: not implemented, theorem-level **0%**.
- The point-centred barrier Bernstein consumer `estimate_barrier_at` is
  focused/exact-green (**100%**), and its private HCG fixed-order adapter is
  focused-green.  The trusted no-extra-input complete-Shi theorem remains
  theorem-level **0%** until the solution-generated barrier cutoff is proved
  and the legacy `estimate_complete` path is removed.
- Whole HCG supporting machinery: approximately **60%**.
- Unconditional HCG compactness endpoint: theorem-level **0%**.

At that snapshot, the request was a ruling on the smallest correct lower
geometric producer and its exact Lean signature.

## 2026-07-23 ruling received and live implementation

The approved route is the fixed-first selected inverse branch.  The canonical
lower statement uses the time-one intrinsic geodesic; the existing raw radial
family is only a rescaling/compatibility corollary.  The general endpoint
Hessian formula includes the negative rank-one radial correction, and the
final raw Laplacian identity has the mandatory denominator
`Real.sqrt (g.inner p x x)`.

Current live-tree status:

- `IntrinsicGauss.intrinsic_gauss`, the selected inverse derivative and
  `BranchRadius` calculus, and `EndpointShape.branchHess_jacobi` /
  `branchHess_shape` are focused- and exact-green.
- `MetricTrace.LineSplit.trace_eq_line_add` and the cycle-free
  `ChartBridge.Laplacian.lap_eq_hess_on` adapter are focused- and exact-green.
- `RawIntrinsicC2.exp_eq_intr_of_c2` and `exp_germ_eq_intr` are focused- and
  exact-green.  They identify the raw and intrinsic maps on the named C2 ball;
  no smaller agreement radius or wrapper assumption was introduced.
- `RadialLaplacian.branchLap_eq_mean` and the raw compatibility capstone
  `radialLap_eq_mean` are focused- and exact-green.  The raw theorem retains
  the mandatory denominator `Real.sqrt (g.inner p x x)` and assumes neither
  `ConnectedSpace M` nor an extra radius hierarchy.

Honest accounting:

- `branchLap_eq_mean`: theorem and dedicated machinery **100%**.
- `radialLap_eq_mean`: theorem and dedicated machinery **100%**.
- The complete fixed-first second-order/radial-Laplacian route selected by
  this consultation: **100%** checked.
- Selected Route B-prime no-extra-input Shi producer machinery: approximately
  **45%** after the deeper half-length/global-comparison audit.  The spatial
  evolving-distance Calabi upper support, the
  solution-generated barrier cutoff, and the final `MovingShiOpen` switch
  remain open.
- The point-centred barrier Bernstein consumer is **100%** and exact-current;
  dedicated P4 consumer/assembly machinery remains approximately **98%**.
- Whole HCG supporting machinery remains approximately **60%**.
- Unconditional `compactnessSol`: theorem-level **0%**.

The initial terminal-tail plan was too optimistic: `calabi_tail_of` gives no
lower bound on the selected tail length, while the existing radial comparison
is restricted to a small raw/C2 launch.  The exact next architecture frontier
is now recorded in `CALABI_BRANCH_CONSULT.md`: an early minimizing-tail
nonconjugacy/local-inverse producer and a global intrinsic minimizing-tail
comparison.  Only after those producers land can the fixed-metric spatial
Calabi support be assembled.  It must remain separate from the later
Ricci-flow time derivative and barrier-cutoff assembly.
