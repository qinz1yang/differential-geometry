import DifferentialGeometry.Geometry.Metric.MetricFiberData.Defs
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def tangentFlatLinear (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[Real] Module.Dual Real (TangentSpace I x) where
  toFun v := (g.inner x v).toLinearMap
  map_add' v w := by
    ext u
    change g.inner x (v + w) u = g.inner x v u + g.inner x w u
    simp
  map_smul' c v := by
    ext u
    change g.inner x (c • v) u = c • g.inner x v u
    simp

omit [FiniteDimensional ℝ E] in
@[simp] theorem tangentFlatLinear_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    tangentFlatLinear (I := I) g x v w = g.inner x v w := by
  rfl

omit [FiniteDimensional ℝ E] in
theorem tangentFlatLinear_injective
    (g : SmoothRiemannianMetric I M) (x : M) :
    Function.Injective (tangentFlatLinear (I := I) g x) := by
  intro v w hvw
  have hzero : forall z : TangentSpace I x, g.inner x (v - w) z = 0 := by
    intro z
    have h := congrArg (fun L : Module.Dual Real (TangentSpace I x) => L z) hvw
    simp only [tangentFlatLinear_apply] at h
    have hsub : g.inner x (v - w) z = g.inner x v z - g.inner x w z := by
      rw [map_sub]
      rfl
    rw [hsub, sub_eq_zero]
    exact h
  by_contra hne
  have hvw_ne : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < g.inner x (v - w) (v - w) := g.pos x (v - w) hvw_ne
  exact (lt_irrefl (0 : Real)) ((hzero (v - w)) ▸ hpos)

def tangentFlatEquiv (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[Real] Module.Dual Real (TangentSpace I x) :=
  LinearMap.linearEquivOfInjective
    (tangentFlatLinear (I := I) g x)
    (tangentFlatLinear_injective (I := I) g x)
    Subspace.dual_finrank_eq.symm

@[simp] theorem tangentFlatEquiv_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    tangentFlatEquiv (I := I) g x v w = g.inner x v w := by
  rfl

structure TangentMetricData
    (g : SmoothRiemannianMetric I M) (x : M) where
  metric : MetricFiberData (TangentSpace I x)
  realizes_inner : forall X Y : TangentSpace I x,
    metric.inner X Y = g.inner x X Y

def tangentMetricData (g : SmoothRiemannianMetric I M) (x : M) :
    TangentMetricData (I := I) g x where
  metric :=
    { flat := tangentFlatEquiv (I := I) g x
      symm := by
        intro X Y
        exact g.symm x X Y
      nonneg := by
        intro X
        by_cases hX : X = 0
        · simp [hX]
        · exact le_of_lt (g.pos x X hX) }
  realizes_inner := by
    intro X Y
    rfl

namespace TangentMetricData

theorem inner_eq
    {g : SmoothRiemannianMetric I M} {x : M} (D : TangentMetricData (I := I) g x)
    (X Y : TangentSpace I x) :
    D.metric.inner X Y = g.inner x X Y :=
  D.realizes_inner X Y

end TangentMetricData

end

end Tensor0SBundle
end DifferentialGeometry
