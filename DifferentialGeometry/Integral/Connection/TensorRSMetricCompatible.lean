import DifferentialGeometry.Integral.Connection.TensorMetricCompatible
import DifferentialGeometry.Tensor.Multilinear.MetricLowering

/-!
# Directional metric compatibility of the mixed `(r, s)`-tensor inner product

For a smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, the pointwise metric-induced inner product on mixed `(r, s)`-tensor
fibres `tensorInnerPointwise g r s` is defined by lowering the `r` upper slots
through the metric and reducing to the covariant `(0, r + s)` inner product
`tensorInnerPointwise_0s`.

This file establishes the **directional metric-compatibility identity** for the
mixed inner product:

  `∇_v ⟨W, S⟩ = ⟨∇_v W, S⟩ + ⟨W, ∇_v S⟩`,

where `∇` on the right-hand side is the `(0, r + s)`-tensor covariant derivative
of the metric-lowered tensor sections induced by the Levi-Civita connection.

The proof is a direct reduction to the proven covariant-rank `(0, r + s)` case
`tensorInnerPointwise_0s_mfderiv_metricCompatible`. The bridge is the
*lifted section*: for a smooth `(r, s)`-tensor section `S`, the assignment
`y ↦ ofModel (lowerAllUpperIndices g r s y (toModel (S y)))` is a smooth
section of the `(0, r + s)`-tensor bundle (`contMDiff_lifted_section`), so the
covariant-rank-`(0, r + s)` metric-compatibility identity applies to it
verbatim.

## Main results

* `liftedTensorSection g r s S` — the metric-lowered `(0, r + s)`-tensor
  section attached to a smooth `(r, s)`-tensor section `S`.
* `liftedTensorSection_mdiffAt` — the lifted section is manifold-differentiable
  everywhere (in total-space form).
* `tensorInnerPointwise_eq_liftedTensorSection_inner` — the mixed `(r, s)`
  pointwise inner product equals the `(0, r + s)` inner product of the lifted
  sections.
* `tensorInnerPointwise_hasMFDerivAt_metricCompatible` — **the directional
  metric-compatibility identity for the mixed `(r, s)`-tensor inner product.**
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open TensorMetricLowering
open Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The metric-lowered `(0, r + s)`-tensor section attached to a smooth
`(r, s)`-tensor section `S`: at a point `y`, it is the model `(0, r + s)`-tensor
`ofModel (lowerAllUpperIndices g r s y (toModel (S y)))`. -/
def liftedTensorSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯) :
    Π y : M, Tensor0SSpace (r + s) I y :=
  fun y => Tensor0SSpace.ofModel
    (lowerAllUpperIndices (I := I) (M := M) g r s y (TensorRSSpace.toModel (S y)))

@[simp]
lemma liftedTensorSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    liftedTensorSection (I := I) (M := M) g r s S y =
      Tensor0SSpace.ofModel
        (lowerAllUpperIndices (I := I) (M := M) g r s y
          (TensorRSSpace.toModel (S y))) := rfl

/-- The model coercion of the lifted section recovers the metric-lowered
covariant `(0, r + s)`-model tensor. -/
@[simp]
lemma toModel_liftedTensorSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s S y) =
      lowerAllUpperIndices (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (S y)) := by
  rw [liftedTensorSection_apply, Tensor0SSpace.toModel_ofModel]

/-- **Smoothness of the lifted section.** The metric-lowered `(0, r + s)`-tensor
section of a smooth `(r, s)`-tensor section is itself a smooth section of the
`(0, r + s)`-tensor bundle, in total-space form. -/
lemma liftedTensorSection_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (r + s) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
        (E := fun z : M => Tensor0SSpace (r + s) I z) y
        (liftedTensorSection (I := I) (M := M) g r s S y)) :=
  contMDiff_lifted_section (I := I) (M := M) g r s S

/-- **Differentiability of the lifted section** at a point, in the total-space
form required by `TensorSectionMDiffAt`. -/
lemma liftedTensorSection_mdiffAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) :
    TensorSectionMDiffAt (I := I) (r + s)
      (liftedTensorSection (I := I) (M := M) g r s S) x :=
  ((liftedTensorSection_contMDiff (I := I) (M := M) g r s S) x).mdifferentiableAt
    (by simp)

/-- The mixed `(r, s)` pointwise inner product of two `(r, s)`-tensor section
values is the covariant `(0, r + s)` inner product of their metric-lowered
`(0, r + s)`-tensor section values. -/
lemma tensorInnerPointwise_eq_liftedTensorSection_inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    tensorInnerPointwise (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y)) =
      tensorInnerPointwise_0s (I := I) (M := M) (r + s) g y
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s W y))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s S y)) := by
  rw [toModel_liftedTensorSection, toModel_liftedTensorSection]
  rfl

/-- The metric-lowered directional covariant derivative of a smooth
`(r, s)`-tensor section `S` at a point `x` along a direction `v`: the
directional covariant derivative of the lifted `(0, r + s)`-tensor section,
valued in the `(0, r + s)`-tensor fibre. -/
def loweredCovDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) (v : TangentSpace I x) :
    Tensor0SSpace (r + s) I x :=
  tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g)
    (liftedTensorSection (I := I) (M := M) g r s S) x v

@[simp]
lemma loweredCovDerivAt_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) (v : TangentSpace I x) :
    loweredCovDerivAt (I := I) (M := M) g r s S x v =
      tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g)
        (liftedTensorSection (I := I) (M := M) g r s S) x v := rfl

open Tensor0SNabla in
/-- **Directional metric compatibility of the mixed `(r, s)`-tensor inner
product.** For two smooth `(r, s)`-tensor sections `W`, `S`, every point `x`
and every tangent vector `v`, the directional derivative of the pointwise
metric-induced inner product `y ↦ ⟨W y, S y⟩` decomposes by the covariant
Leibniz rule:

  `∇_v ⟨W, S⟩ = ⟨∇_v W, S⟩ + ⟨W, ∇_v S⟩`,

where `∇_v` denotes the metric-lowered directional covariant derivative
`loweredCovDerivAt` (the directional covariant derivative of the lifted
`(0, r + s)`-tensor section, induced by the Levi-Civita connection of `g`), and
`⟨·, ·⟩` on the right-hand side is the covariant `(0, r + s)` inner product
`tensorInnerPointwise_0s`.

The proof is a direct reduction to the proven covariant-rank-`(0, r + s)`
metric-compatibility identity
`tensorInnerPointwise_0s_mfderiv_metricCompatible`, applied to the smooth
lifted sections `liftedTensorSection g r s W`, `liftedTensorSection g r s S`. -/
theorem tensorInnerPointwise_hasMFDerivAt_metricCompatible
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => tensorInnerPointwise (I := I) (M := M) g r s y
          (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y))) x v =
      tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g r s W x v))
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s S x))
        + tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s W x))
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g r s S x v)) := by
  have hfun : (fun y : M => tensorInnerPointwise (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y))) =
      fun y : M => tensorInnerPointwise_0s (I := I) (M := M) (r + s) g y
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s W y))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s S y)) := by
    funext y
    exact tensorInnerPointwise_eq_liftedTensorSection_inner
      (I := I) (M := M) g r s W S y
  rw [hfun]
  exact tensorInnerPointwise_0s_mfderiv_metricCompatible
    (I := I) (M := M) g (r + s)
    (liftedTensorSection (I := I) (M := M) g r s W)
    (liftedTensorSection (I := I) (M := M) g r s S)
    (liftedTensorSection_mdiffAt (I := I) (M := M) g r s W x)
    (liftedTensorSection_mdiffAt (I := I) (M := M) g r s S x) v

open Tensor0SNabla in
/-- **`HasMFDerivAt` form of directional metric compatibility.** The pointwise
mixed inner product `y ↦ ⟨W y, S y⟩` of two smooth `(r, s)`-tensor sections has
manifold-derivative `tensorMetricCompatDiff g (r + s) (lift W) (lift S) x` at
`x`; evaluating this differential on `v` yields the covariant Leibniz
decomposition. -/
theorem tensorInnerPointwise_hasMFDerivAt_metricCompatible'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) :
    HasMFDerivAt I 𝓘(ℝ, ℝ)
      (fun y : M => tensorInnerPointwise (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y))) x
      (tensorMetricCompatDiff (I := I) (M := M) g (r + s)
        (liftedTensorSection (I := I) (M := M) g r s W)
        (liftedTensorSection (I := I) (M := M) g r s S) x) := by
  have hfun : (fun y : M => tensorInnerPointwise (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y))) =
      fun y : M => tensorInnerPointwise_0s (I := I) (M := M) (r + s) g y
        (Tensor0SSpace.toModel (liftedTensorSection (I := I) (M := M) g r s W y))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s S y)) := by
    funext y
    exact tensorInnerPointwise_eq_liftedTensorSection_inner
      (I := I) (M := M) g r s W S y
  rw [hfun]
  exact tensorInnerPointwise_0s_hasMFDerivAt_metricCompatible_aux
    (I := I) (M := M) g (r + s)
    (liftedTensorSection (I := I) (M := M) g r s W)
    (liftedTensorSection (I := I) (M := M) g r s S)
    (liftedTensorSection_mdiffAt (I := I) (M := M) g r s W x)
    (liftedTensorSection_mdiffAt (I := I) (M := M) g r s S x)

end Connection
end Integral
end DifferentialGeometry

end
