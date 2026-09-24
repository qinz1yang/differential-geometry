import Mathlib.Geometry.Manifold.BumpFunction

section

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace SmoothBumpFunction

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

theorem exists_tsupport_subset_interior_one {center : M} (χ : SmoothBumpFunction I center) :
    ∃ ρ : SmoothBumpFunction I center,
      tsupport (ρ : M → ℝ) ⊆ interior {p | χ p = 1} ∩ (chartAt H center).source := by
  have hone : {p : M | χ p = 1} ∈ 𝓝 center := χ.eventuallyEq_one
  have hnhds : interior {p : M | χ p = 1} ∩ (chartAt H center).source ∈ 𝓝 center :=
    inter_mem (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hone))
      ((chartAt H center).open_source.mem_nhds (mem_chart_source H center))
  obtain ⟨ρ, _, hρ⟩ := (nhds_basis_tsupport (I := I) center).mem_iff.mp hnhds
  exact ⟨ρ, hρ⟩

end SmoothBumpFunction

end

end
