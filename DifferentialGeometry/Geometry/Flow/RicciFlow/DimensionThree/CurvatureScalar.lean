import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureKernel
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ScalarPositivity

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metricScalarAt_pos_of_curvatureOperatorImage_rank_eq_one_at_later_time
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {s t : ℝ} (hst : s < t) (hreg : Set.Icc s t ⊆ D.regular)
    (hR : ∀ r ∈ Set.Icc s t, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {x₀ : M} (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x₀
      ⟨metricRm04At (S.family.metric t) x₀,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x₀⟩) = 1) (x : M) :
    0 < metricScalarAt (S.family.metric t) x := by
  apply DimensionThree.metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
    hdim (S.family.metric t) x (hR t (Set.right_mem_Icc.mpr hst.le) x)
  exact (curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim hst hreg hR x x₀).trans hrank

end DifferentialGeometry.PDE.RicciFlow
