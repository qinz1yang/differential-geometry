import DifferentialGeometry.Integral.Connection.Tensor3rdCurvFiberNormBound
import DifferentialGeometry.Integral.Connection.TensorThirdOrderWeitzenbock
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovGrad

/-!
# Uniform curvature and differentiated-curvature fibre-norm bounds on a closed manifold

For a smooth Riemannian metric `g` on a closed manifold `M` (modelled on a real
inner-product space `E`), this file packages the genuine Riemann curvature contraction of a
smooth tensor section as a smooth section, and derives the two base-point-uniform
fibre-norm bounds — `‖R‖_∞` and `‖∇R‖_∞` — that the integrated tensor Bochner / Gårding
cross term consumes.

## The curvature contraction as a smooth section

For smooth global tangent fields `X, Y` and a smooth compactly-supported `(0, s)`-tensor
section `Z`, the bundled tensor curvature operator `riemannOp (tensorCov g 0 s)` applied
pointwise to the fibre values `(X x, Y x, Z x)` agrees with the section-level Riemann
curvature `riemannSec (tensorCov g 0 s) X Y Z` (`riemannOp_apply_smooth`). The latter is a
smooth section (`riemannSec_contMDiff`), and on a closed manifold it has compact support.
We package it as a `SmoothCcTensor g 0 s` named `curvatureContraction`. Its underlying
section value is the curvature contraction `R_x(X x, Y x)(Z x)`.

## Why the bounds are genuinely uniform (frame-free)

The intrinsic Riemannian fibre norm `riemannianFiberNormSq` of *any* smooth
compactly-supported tensor section is bounded above by a single nonnegative constant,
uniformly over the closed manifold
(`exists_bound_riemannianFiberNormSq_smoothCcTensor`). That bound is proved through the
chart-locality-free forward-Gram Rayleigh route — the intrinsic fibre norm is controlled by
the smooth raw chart-frame components on the compact partition-of-unity supports — and never
through the model-fibre operator norm of the chart trivialisation, which is genuinely
unbounded on multi-chart manifolds. Applying it to `curvatureContraction` and to its
covariant gradient `covGrad … curvatureContraction` yields the two uniform bounds with no
`BddAbove` hypothesis and no per-point frame scalar.

## Main definitions

* `curvatureContraction g s Z hX hY` — the curvature contraction `R(X, Y) Z` of a smooth
  `(0, s)`-tensor section `Z` along smooth tangent fields `X, Y`, as a smooth
  compactly-supported `(0, s)`-tensor section.
* `covGradCurvatureContraction g s Z hX hY` — its covariant gradient `∇(R(X, Y) Z)`, a
  smooth compactly-supported `(0, s + 1)`-tensor section (the differentiated curvature
  `∇R` along the contracted section).

## Main results

* `curvatureContraction_toSection_apply` — the underlying section value of
  `curvatureContraction` equals the bundled curvature contraction
  `riemannOp (tensorCov g 0 s) x (X x) (Y x) (Z x)`.
* `exists_uniform_riemannianFiberNormSq_riemannOp_bound` (**`‖R‖_∞`**) — a single
  nonnegative `K_R`, uniform over `M`, bounding the intrinsic fibre norm of the curvature
  contraction `R_x(X x, Y x)(Z x)` at every base point.
* `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound` (**`‖∇R‖_∞`**) — a single
  nonnegative `K_∇R`, uniform over `M`, bounding the intrinsic fibre norm of the covariant
  gradient `∇(R(X, Y) Z)` at every base point.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-- **The curvature contraction `R(X, Y) Z` as a smooth section.** For smooth global tangent
fields `X, Y` and a smooth compactly-supported `(0, s)`-tensor section `Z`, the section-level
Riemann curvature `b ↦ riemannSec (tensorCov g 0 s) X Y Z b` is smooth
(`riemannSec_contMDiff`); on a closed manifold it has compact support. Packaged as a
`SmoothCcTensor g 0 s`. -/
def curvatureContraction
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun b : M => riemannSec (tensorCov (I := I) g 0 s) X Y
        (fun y : M => Z.toSection y) b
      contMDiff_toFun :=
        riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) hX hY Z.toSection.contMDiff }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The underlying section value of `curvatureContraction` is the section-level Riemann
curvature. This is definitional. -/
@[simp] lemma curvatureContraction_toSection_eq_riemannSec
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (x : M) :
    (curvatureContraction (I := I) (M := M) g s Z hX hY).toSection x =
      riemannSec (tensorCov (I := I) g 0 s) X Y (fun y : M => Z.toSection y) x := rfl

set_option linter.unusedSectionVars false in
/-- **The underlying section value of `curvatureContraction` is the bundled curvature
contraction.** At each base point `x`, it equals
`riemannOp (tensorCov g 0 s) x (X x) (Y x) (Z x)`. This converts the section-level Riemann
formula to the bundled curvature operator via `riemannOp_apply_smooth`. -/
theorem curvatureContraction_toSection_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (x : M) :
    (curvatureContraction (I := I) (M := M) g s Z hX hY).toSection x =
      riemannOp (tensorCov (I := I) g 0 s) x (X x) (Y x) (Z.toSection x) := by
  rw [curvatureContraction_toSection_eq_riemannSec]
  exact riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 s) hX hY
    Z.toSection.contMDiff

set_option linter.unusedSectionVars false in
/-- **Uniform curvature fibre-norm bound `‖R‖_∞`.** For smooth global tangent fields `X, Y`
and a smooth compactly-supported `(0, s)`-tensor section `Z` on a closed Riemannian manifold,
there is a single nonnegative constant `K_R`, uniform over `M`, such that for every `x : M`,

```
riemannianFiberNormSq g 0 s x (R_x(X x, Y x)(Z x)) ≤ K_R,
```

where `R = riemannOp (tensorCov g 0 s)` is the bundled tensor curvature operator. The
constant is base-point-independent: it is the uniform fibre-norm bound for the smooth
section `curvatureContraction`, obtained through the chart-locality-free forward-Gram route
on the compact partition-of-unity supports — no per-point frame scalar, no `BddAbove`
hypothesis. -/
theorem exists_uniform_riemannianFiberNormSq_riemannOp_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ∃ K_R : ℝ, 0 ≤ K_R ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (riemannOp (tensorCov (I := I) g 0 s) x (X x) (Y x) (Z.toSection x)) ≤ K_R := by
  obtain ⟨K_R, hK_nonneg, hK⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor g 0 s
      (curvatureContraction (I := I) (M := M) g s Z hX hY)
  refine ⟨K_R, hK_nonneg, fun x => ?_⟩
  have hx := hK x
  rwa [curvatureContraction_toSection_apply (I := I) (M := M) g s Z hX hY x] at hx

/-- **The covariant gradient of the curvature contraction `∇(R(X, Y) Z)`.** Applying the
section-level covariant gradient `covGrad g 0 s` to the smooth curvature-contraction section
`curvatureContraction g s Z hX hY` produces a smooth compactly-supported
`(0, s + 1)`-tensor section: the covariantly-differentiated curvature, with the new leftmost
covariant slot carrying the differentiation direction. This is the differentiated-curvature
field `∇R` along the contracted section that the integrated tensor Bochner cross term
requires. -/
def covGradCurvatureContraction
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    SmoothCcTensor g 0 (s + 1) :=
  covGrad g 0 s (curvatureContraction (I := I) (M := M) g s Z hX hY)

set_option linter.unusedSectionVars false in
/-- The underlying section of `covGradCurvatureContraction` is the covariant gradient of the
curvature-contraction section. This is definitional. -/
lemma covGradCurvatureContraction_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (covGradCurvatureContraction (I := I) (M := M) g s Z hX hY).toSection =
      (covGrad g 0 s (curvatureContraction (I := I) (M := M) g s Z hX hY)).toSection := rfl

set_option linter.unusedSectionVars false in
/-- **Uniform differentiated-curvature fibre-norm bound `‖∇R‖_∞`.** For smooth global tangent
fields `X, Y` and a smooth compactly-supported `(0, s)`-tensor section `Z` on a closed
Riemannian manifold, there is a single nonnegative constant `K_∇R`, uniform over `M`, such
that for every `x : M`,

```
riemannianFiberNormSq g 0 (s + 1) x ((∇(R(X, Y) Z)) x) ≤ K_∇R,
```

where `∇(R(X, Y) Z) = covGrad g 0 s (curvatureContraction g s Z hX hY)` is the
covariantly-differentiated curvature contraction. As with `‖R‖_∞`, the constant is
base-point-independent and obtained through the chart-locality-free uniform fibre-norm bound
for smooth sections applied to the smooth section `covGradCurvatureContraction`. -/
theorem exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ∃ KgradR : ℝ, 0 ≤ KgradR ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((covGradCurvatureContraction (I := I) (M := M) g s Z hX hY).toSection x) ≤ KgradR :=
  exists_bound_riemannianFiberNormSq_smoothCcTensor g 0 (s + 1)
    (covGradCurvatureContraction (I := I) (M := M) g s Z hX hY)

end Connection
end Integral
end DifferentialGeometry

end
