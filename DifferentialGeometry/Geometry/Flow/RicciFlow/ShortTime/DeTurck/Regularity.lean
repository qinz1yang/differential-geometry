import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHS.Defs

open DifferentialGeometry.Geometry.Curvature


open DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metric_inner_continuousOn_time_of_deTurck_solution
    (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hsol : IsQuasilinearMetricParabolicSolution (I := I)
              (deTurckRicciRHS (I := I) g_bg) (g_DT 0) T g_DT) :
    ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : ℝ => (g_DT t).inner x v w)
        (Set.Ico (0 : ℝ) T) := by
  obtain ⟨_hT, _hinit, hderiv⟩ := hsol
  intro x v w t ht
  have hcont_within_Ici :
      ContinuousWithinAt (fun s : ℝ => (g_DT s).inner x v w) (Set.Ici (0 : ℝ)) t :=
    (hderiv t ht x v w).continuousWithinAt
  exact hcont_within_Ici.mono Set.Ico_subset_Ici_self
end DifferentialGeometry.PDE.RicciFlow
