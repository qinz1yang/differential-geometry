import DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Curvature.Metric.SectionalCone
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Convex
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [LocallyPathConnectedSpace M]
  [SemilocallySimplyConnectedSpace M] [Inhabited M]

theorem metricRmNormSq_lifted_bound_on
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (C : ℝ)
    (hbound : ∀ t ∈ J, ∀ x : M,
      normSq0S (I := I) (g t) x 4 (metricRm04At (I := I) (g t) x) ≤ C) :
    ∀ t ∈ J, ∀ x' : UniversalCover M,
      normSq0S (I := I) (UniversalCover.liftedMetric (I := I) (g t)) x' 4
        (metricRm04At (I := I) (UniversalCover.liftedMetric (I := I) (g t)) x') ≤
          C := by
  intro t ht x'
  rw [UniversalCover.normSq0S_metricRm04At_liftedMetric]
  exact hbound t ht (UniversalCover.proj x')

theorem metricRm04_lifted_mem_sectionalNonnegativeCone_iff
    (g : SmoothRiemannianMetric I M) (x' : UniversalCover M) :
    metricRm04At (I := I) (UniversalCover.liftedMetric (I := I) g) x' ∈
        tensor04SectionalNonnegativeCone (I := I) ↔
      metricRm04At (I := I) g (UniversalCover.proj x') ∈
        tensor04SectionalNonnegativeCone (I := I) := by
  rw [metricRm04At_mem_tensor04SectionalNonnegativeCone_iff,
    metricRm04At_mem_tensor04SectionalNonnegativeCone_iff]
  constructor
  · intro h v w
    exact (h v w).trans_eq (UniversalCover.metricRm_lifted (I := I) g x' v w w v)
  · intro h v w
    exact (h v w).trans_eq (UniversalCover.metricRm_lifted (I := I) g x' v w w v).symm

theorem metricAlgebraicCurvatureTensorAt_lifted_mem_operatorNonnegativeCone_iff
    (g : SmoothRiemannianMetric I M) (x' : UniversalCover M) :
    metricAlgebraicCurvatureTensorAt (I := I)
        (UniversalCover.liftedMetric (I := I) g) x' ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) ↔
      metricAlgebraicCurvatureTensorAt (I := I) g (UniversalCover.proj x') ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  have heval (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → E) :
      (∑ i, ∑ j, c i * c j * metricRm04StandardAt (I := I)
        (UniversalCover.liftedMetric (I := I) g) x' (v i) (w i) (w j) (v j)) =
      ∑ i, ∑ j, c i * c j * metricRm04StandardAt (I := I)
        g (UniversalCover.proj x') (v i) (w i) (w j) (v j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun a : ℝ => c i * c j * a)
      (UniversalCover.metricRm_lifted (I := I) g x' (v i) (w i) (w j) (v j))
  rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff,
    metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff]
  constructor
  · intro h n c v w
    exact (h n c v w).trans_eq (heval n c v w)
  · intro h n c v w
    exact (h n c v w).trans_eq (heval n c v w).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
