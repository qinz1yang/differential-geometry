import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannianBundle

/-!
# Fibre norm vs. pointwise inner product: the installed `RiemannianBundle` norm

For a smooth Riemannian metric `g` on a manifold `M`, the `(r, s)`-tensor bundle carries the
installed `RiemannianBundle` instance `tensorRS_riemannianBundle g r s`, whose fibre inner
product is `tensorRSRiemannianInnerCLM g r s x`.  The resulting fibre norm `‖T‖` (taken in the
`InnerProductSpace` structure that the `RiemannianBundle` instance supplies) is, by definition,
the square root of the diagonal inner product `⟪T, T⟫`.

This file records the bridge between that installed fibre norm and the model
Gram-matrix-based pointwise inner product `tensorInnerPointwise`:

```
‖T‖ = Real.sqrt (tensorInnerPointwise g r s x T.toModel T.toModel).
```

The diagonal inner product `⟪T, T⟫` is, by `rfl`, the diagonal value
`tensorRSRiemannianInnerCLM g r s x T T`, which equals the frame-based fibre norm squared
`riemannianFiberNormSq g r s x T` (`tensorRSRiemannianInnerCLM_apply` /
`riemannianFiberNormSq_eq_tensorInnerPointwise`), itself the model inner product
`tensorInnerPointwise g r s x T.toModel T.toModel`.  Taking square roots and using
`real_inner_self_eq_norm_sq` gives the headline.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle
open DifferentialGeometry.Tensor.TensorRSRiemannianBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The diagonal `g`-fibre inner product equals the model pointwise inner product.**  For the
installed `RiemannianBundle` instance `tensorRS_riemannianBundle g r s`, the diagonal fibre
inner product `⟪T, T⟫` of an `(r, s)`-tensor `T` is the model Gram-matrix-based pointwise inner
product `tensorInnerPointwise g r s x T.toModel T.toModel`.

The diagonal fibre inner product is, by `rfl`, the value `tensorRSRiemannianInnerCLM g r s x T T`
of the metric defining the `RiemannianBundle` instance; this value is the model inner product
by `tensorRSRiemannianInnerCLM_apply`. -/
theorem inner_self_eq_tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (T : TensorRSSpace r s I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    (inner ℝ T T : ℝ) =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel T) (TensorRSSpace.toModel T) := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  have hclm : (tensorRSRiemannianInnerCLM (I := I) (M := M) g r s x T T : ℝ) =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel T) (TensorRSSpace.toModel T) :=
    tensorRSRiemannianInnerCLM_apply (I := I) (M := M) g r s x T T
  rw [← hclm]
  rfl

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The installed `g`-fibre norm is the square root of the model pointwise inner product.**
For the installed `RiemannianBundle` instance `tensorRS_riemannianBundle g r s`, the fibre norm
`‖T‖` of an `(r, s)`-tensor `T` equals `Real.sqrt (tensorInnerPointwise g r s x T.toModel
T.toModel)`. -/
theorem norm_eq_sqrt_tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (T : TensorRSSpace r s I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ‖T‖ =
      Real.sqrt
        (tensorInnerPointwise (I := I) (M := M) g r s x
          (TensorRSSpace.toModel T) (TensorRSSpace.toModel T)) := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [← inner_self_eq_tensorInnerPointwise (I := I) (M := M) g r s x T]
  rw [real_inner_self_eq_norm_sq]
  exact (Real.sqrt_sq (norm_nonneg T)).symm

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Two `(r, s)`-tensors with equal model pointwise self-inner product have equal fibre
norm.**  The convenient consumer form: if the model Gram-matrix-based diagonal pointwise inner
products of `T` and `S` agree, then so do their installed `RiemannianBundle` fibre norms. -/
theorem norm_eq_of_tensorInnerPointwise_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T S : TensorRSSpace r s I x)
    (h : tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel T) (TensorRSSpace.toModel T) =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel S) (TensorRSSpace.toModel S)) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ‖T‖ = ‖S‖ := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g r s x T,
    norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g r s x S, h]

end Connection
end Integral
end DifferentialGeometry

end
