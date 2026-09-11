import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ImageLine
import DifferentialGeometry.Geometry.Connection.GlobalParallelLine

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle Set
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_common_global_parallel_unit_section_of_curvatureOperatorImageAnnihilator_eq
    [SimplyConnectedSpace M]
    {A : Type*} (g : A → SmoothRiemannianMetric I M) (a₀ : A)
    (hdim : Module.finrank ℝ E = 3)
    (hrank : ∀ a y, Module.finrank ℝ (curvatureOperatorImageAt (g a) y
      ⟨metricRm04At (g a) y, metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a) y⟩) = 1)
    (hkernel : ∀ a, IsParallelContinuousAlternatingSubmoduleFamily (g a)
      (fun y => curvatureOperatorKernelAt (g a) y
        ⟨metricRm04At (g a) y, metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a) y⟩))
    (hline : ∀ a y, curvatureOperatorImageAnnihilatorAt (g a) y
      ⟨metricRm04At (g a) y, metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a) y⟩ =
        curvatureOperatorImageAnnihilatorAt (g a₀) y
          ⟨metricRm04At (g a₀) y, metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a₀) y⟩)
    (hdual : ∀ a y, ∀ v ∈ curvatureOperatorImageAnnihilatorAt (g a₀) y
      ⟨metricRm04At (g a₀) y, metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a₀) y⟩,
      ∀ w, (g a).inner y v w = (g a₀).inner y v w) :
    ∃ s : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ a y, s y ∈ curvatureOperatorImageAnnihilatorAt (g a) y
        ⟨metricRm04At (g a) y, metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a) y⟩) ∧
      (∀ a y, (g a).inner y (s y) (s y) = 1) ∧
      (∀ a y, ∀ v : TangentSpace I y, (LeviCivita (g a)) s y v = 0) ∧
      ∀ a y, ∀ v : TangentSpace I y,
        (g a).inner y (s y) v = (g a₀).inner y (s y) v := by
  have hex a := exists_smooth_parallel_curvatureOperatorImageLine hdim (g a) (metricRm04 (g a))
    (fun y => metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a) y)
    (hrank a) (hkernel a)
  obtain ⟨L, hLrank, hLfiber, hLparallel⟩ := hex a₀
  obtain ⟨s, hs_mem, hs_unit, -⟩ :=
    L.exists_global_parallel_unit_section_of_rank_eq_one (g a₀) hLrank hLparallel
  have hmem a y : s y ∈ curvatureOperatorImageAnnihilatorAt (g a) y
      ⟨metricRm04At (g a) y, metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a) y⟩ := by
    rw [hline a y]
    exact hLfiber y ▸ hs_mem y
  have hinner a y v : (g a).inner y (s y) v = (g a₀).inner y (s y) v :=
    hdual a y (s y) (hmem a₀ y) v
  have hunit a y : (g a).inner y (s y) (s y) = 1 :=
    (hinner a y (s y)).trans (hs_unit y)
  refine ⟨s, hmem, hunit, ?_, hinner⟩
  intro a y v
  obtain ⟨La, hLarank, hLafiber, hLaparallel⟩ := hex a
  exact La.covariantDerivative_eq_zero_of_unit_of_rank_eq_one (g a) hLarank hLaparallel
    univ isOpen_univ s (fun z _ => (hLafiber z).symm ▸ hmem a z)
    (fun z _ => hunit a z) y (mem_univ y) v

end DifferentialGeometry.Geometry.Curvature
