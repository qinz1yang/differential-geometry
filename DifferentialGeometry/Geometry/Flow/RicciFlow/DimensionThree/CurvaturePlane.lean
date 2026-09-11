import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureKernel
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ImagePlane

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_parallel_curvatureOperatorImagePlane_at_later_time
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
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x₀⟩) = 1) :
    ∃ P : ContMDiffVectorSubbundle (I := I) (F := E) (V := TangentSpace I) (n := ∞),
      P.rank = 2 ∧
      (∀ x, P.fiber x =
        (DifferentialGeometry.Tensor0SBundle.tangentMetricData (S.family.metric t) x).metric.orthogonal
          (curvatureOperatorImageAnnihilatorAt (S.family.metric t) x
            ⟨metricRm04At (S.family.metric t) x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩)) ∧
      IsParallelSubmoduleFamily (S.family.metric t) P.fiber := by
  exact exists_smooth_parallel_curvatureOperatorImagePlane hdim (S.family.metric t)
    (metricRm04 (S.family.metric t))
    (fun x => metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x)
    (fun x => (curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim hst hreg hR x x₀).trans hrank)
    (curvatureOperatorKernelAt_parallel_at_later_time S hS hdim hst hreg hR)

end DifferentialGeometry.PDE.RicciFlow
