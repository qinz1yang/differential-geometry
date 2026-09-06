import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Bundle.SmoothScalarGerm

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

theorem contMDiffOn_laplacian_leviCivita
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (laplacian (Connection.LeviCivita g) g f) U := by
  intro x hx
  obtain ⟨F, hF, hFf⟩ := exists_smooth_germ hU hx hf
  have hLF : ContMDiff I 𝓘(ℝ, ℝ) ∞ (laplacian (Connection.LeviCivita g) g F) := by
    apply (Δ_g_contMDiff g ⟨F, hF⟩).congr
    intro y
    exact laplacian_levi_eq g hF y
  have heq : laplacian (Connection.LeviCivita g) g F =ᶠ[𝓝 x]
      laplacian (Connection.LeviCivita g) g f := by
    filter_upwards [hFf.eventuallyEq_nhds, hU.mem_nhds hx] with y hy hyU
    exact laplacian_congr_of_eventuallyEq (Connection.LeviCivita g) g hF.contMDiffAt
      (hf.contMDiffAt (hU.mem_nhds hyU)) hy
  exact (hLF.contMDiffAt.congr_of_eventuallyEq heq.symm).contMDiffWithinAt

theorem contMDiff_laplacian_leviCivita
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (laplacian (Connection.LeviCivita g) g f) := by
  rw [← contMDiffOn_univ]
  exact contMDiffOn_laplacian_leviCivita g isOpen_univ hf.contMDiffOn

end DifferentialGeometry.Geometry.Operator
