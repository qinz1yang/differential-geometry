import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def fiberNormSqComponent
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (S : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) : ℝ :=
  Tensor0SSpace.eval
    ((S : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
      ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) r b).symm
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k => g.inner b (e (K k))))))
    (fun k => e (J k))

lemma fiberNormSqSummand_eq_component_sq
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (S : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqSummand (I := I) (M := M) g b r s S n e K J =
      fiberNormSqComponent (I := I) (M := M) g b r s S n e K J ^ 2 := rfl

lemma fiberNormSqComponent_add
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (S S' : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g b r s (S + S') n e K J =
      fiberNormSqComponent (I := I) (M := M) g b r s S n e K J +
        fiberNormSqComponent (I := I) (M := M) g b r s S' n e K J := by
  unfold fiberNormSqComponent
  rfl

lemma fiberNormSqComponent_smul
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (c : ℝ) (S : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g b r s (c • S) n e K J =
      c * fiberNormSqComponent (I := I) (M := M) g b r s S n e K J := by
  unfold fiberNormSqComponent
  rfl

lemma fiberNormSqComponent_zero
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g b r s
      (0 : TensorRSSpace r s I b) n e K J = 0 := rfl

lemma fiberNormSqComponent_sum
    {ι : Type*} (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (t : Finset ι) (F : ι → TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g b r s (∑ i ∈ t, F i) n e K J =
      ∑ i ∈ t, fiberNormSqComponent (I := I) (M := M) g b r s (F i) n e K J := by
  classical
  refine Finset.cons_induction ?_ ?_ t
  · simp [fiberNormSqComponent_zero]
  · intro a s' ha ih
    rw [Finset.sum_cons, Finset.sum_cons, fiberNormSqComponent_add, ih]

end Elliptic
end Analysis
end DifferentialGeometry

end
