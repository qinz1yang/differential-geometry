import DifferentialGeometry.Geometry.Comparison.DistanceFamily
import DifferentialGeometry.Geometry.Metric.Family.QuadraticBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

theorem exists_ricci_bound_on_distance_ball_on_compact
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {J : Set ℝ} (hJ : IsCompact J)
    (hslab : J ⊆ D.carrier)
    (hcomplete : ∀ t ∈ J, RiemannianMetricComplete (I := I) (S.base.metric t))
    (O : M) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ J, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric t) O y ≤ ENNReal.ofReal R →
      ∀ v : TangentSpace I y, |ricciTensor (I := I) (S.base.metric t) y v v| ≤
        K * (S.base.metric t).inner y v v := by
  obtain ⟨L, hL, hcover⟩ := exists_compact_riemannianEDistOf_le_of_isCompact
    (I := I) S.base.metric (hS.smoothMetric.metricTensor_cont.mono hslab)
    hJ Set.Subset.rfl hcomplete O R
  obtain ⟨K, hK, hbound⟩ := exists_tensor_quadratic_bound_on_compact
    S.base.metric (fun t y => S.ricci t y) hJ hL
    (hS.smoothMetric.metricTensor_cont.mono hslab) (hS.ricciCont.mono hslab)
  refine ⟨K, hK, ?_⟩
  intro t ht y hy v
  have hyL : y ∈ L := hcover t ht y hy
  have hquad : quad02 (I := I) (M := M) (S.ricci t y) v =
      ricciTensor (I := I) (S.base.metric t) y v v := by
    simp only [quad02, SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt]
    convert metricRicciAt_apply_eq_ricciTensor (I := I) (S.base.metric t) y v v using 2
    funext i
    fin_cases i <;> rfl
  rw [← hquad]
  exact hbound t ht y hyL v

end DifferentialGeometry.PDE.RicciFlow
