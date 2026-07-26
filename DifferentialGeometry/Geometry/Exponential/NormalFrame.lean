import DifferentialGeometry.Geometry.Metric.InnerExpansion

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Orthonormal frames for normal coordinates

This file supplies the pointwise orthonormal linear normalization that turns
the exponential parametrization of a tangent fiber into genuine Riemannian
normal coordinates.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

open Module Tensor0SBundle
open scoped Manifold ContDiff RealInnerProductSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-- A chosen `g_x`-orthonormal basis of the tangent fiber at `x`. -/
noncomputable def normalBasis (g : SmoothRiemannianMetric I M) (x : M) :
    Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := by
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  exact (stdOrthonormalBasis Real (TangentSpace I x)).toBasis

/-- The chosen tangent basis is orthonormal for the Riemannian metric. -/
theorem normalBasis_inner (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank Real (TangentSpace I x))) :
    g.inner x (normalBasis (I := I) g x i) (normalBasis (I := I) g x j) =
      if i = j then (1 : Real) else 0 := by
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner D (ob i) (ob j)
  have hob := ob.inner_eq_ite i j
  change g.inner x (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← TangentMetricData_gen.inner_eq_gen
    (tangentMetricData_gen (I := I) g x) (ob i) (ob j)]
  change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← hinner]
  exact hob

/-- The linear normalization from the fixed model inner-product space to the
`g_x`-orthonormal tangent coordinates at `x`. -/
noncomputable def normalFrame (g : SmoothRiemannianMetric I M) (x : M) :
    E ≃L[Real] TangentSpace I x :=
  ((stdOrthonormalBasis Real E).toBasis.equiv
    (normalBasis (I := I) g x)
    (Equiv.refl (Fin (Module.finrank Real E)))).toContinuousLinearEquiv

/-- The normalizing equivalence sends the fixed orthonormal basis to the chosen
`g_x`-orthonormal tangent basis. -/
@[simp] theorem normalFrame_basis (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank Real E)) :
    normalFrame (I := I) g x ((stdOrthonormalBasis Real E) i) =
      normalBasis (I := I) g x i := by
  change ((stdOrthonormalBasis Real E).toBasis.equiv
      (normalBasis (I := I) g x)
      (Equiv.refl (Fin (Module.finrank Real E))))
        ((stdOrthonormalBasis Real E).toBasis i) =
    normalBasis (I := I) g x i
  rw [Basis.equiv_apply]
  rfl

/-- The metric at the center, pulled back through `normalFrame`. -/
noncomputable def frameMetric (g : SmoothRiemannianMetric I M) (x : M) :
    E →L[Real] E →L[Real] Real :=
  let L := (normalFrame (I := I) g x).toContinuousLinearMap
  (ContinuousLinearMap.precomp Real L).comp ((g.inner x).comp L)

/-- Evaluation of the metric pulled back through `normalFrame`. -/
theorem frameMetric_apply (g : SmoothRiemannianMetric I M) (x : M) (v w : E) :
    frameMetric (I := I) g x v w =
      g.inner x (normalFrame (I := I) g x v) (normalFrame (I := I) g x w) := by
  simp [frameMetric]

/-- Pulling `g_x` back through `normalFrame` gives the fixed model inner
product exactly. -/
theorem frameMetric_eq (g : SmoothRiemannianMetric I M) (x : M) :
    frameMetric (I := I) g x = (innerSL Real : E →L[Real] E →L[Real] Real) := by
  classical
  let b := (stdOrthonormalBasis Real E).toBasis
  apply LinearMap.toLinearMap_injective
  apply b.ext
  intro i
  apply LinearMap.toLinearMap_injective
  apply b.ext
  intro j
  change frameMetric (I := I) g x (b i) (b j) =
    (innerSL Real : E →L[Real] E →L[Real] Real) (b i) (b j)
  dsimp only [b]
  change g.inner x
      (normalFrame (I := I) g x ((stdOrthonormalBasis Real E) i))
      (normalFrame (I := I) g x ((stdOrthonormalBasis Real E) j)) =
    Inner.inner Real ((stdOrthonormalBasis Real E) i)
      ((stdOrthonormalBasis Real E) j)
  rw [normalFrame_basis, normalFrame_basis, normalBasis_inner]
  exact ((stdOrthonormalBasis Real E).inner_eq_ite i j).symm

/-- The normalizing equivalence is an isometry from the fixed model inner
product to the Riemannian inner product at the center. -/
theorem normalFrame_inner (g : SmoothRiemannianMetric I M) (x : M) (v w : E) :
    g.inner x (normalFrame (I := I) g x v) (normalFrame (I := I) g x w) =
      Inner.inner Real v w := by
  rw [← frameMetric_apply (I := I) g x, frameMetric_eq (I := I) g x]
  rfl

/-- The squared Riemannian length of a framed vector is its squared model
norm. -/
theorem normalFrame_normSq (g : SmoothRiemannianMetric I M) (x : M) (v : E) :
    g.inner x (normalFrame (I := I) g x v) (normalFrame (I := I) g x v) =
      ‖v‖ ^ 2 := by
  rw [normalFrame_inner, real_inner_self_eq_norm_sq]

/-- The normal frame identifies the Riemannian radial norm with the fixed
Euclidean model norm exactly. -/
theorem normalFrame_sqrt (g : SmoothRiemannianMetric I M) (x : M) (v : E) :
    Real.sqrt
        (g.inner x (normalFrame (I := I) g x v)
          (normalFrame (I := I) g x v)) =
      ‖v‖ := by
  rw [normalFrame_normSq, Real.sqrt_sq (norm_nonneg v)]

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
