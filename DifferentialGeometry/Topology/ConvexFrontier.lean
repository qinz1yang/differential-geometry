import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.Compact

open Set

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem subset_of_isCompact_of_frontier_subset_open_convex {D U : Set E}
    (hD : IsCompact D) (hU : IsOpen U) (hUconv : Convex ℝ U) (hUne : U.Nonempty)
    (hfront : frontier D ⊆ U) : D ⊆ U := by
  intro p hp
  by_contra hpU
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hUconv hU hpU
  have hfne : f ≠ 0 := by
    intro h
    obtain ⟨z, hz⟩ := hUne
    have hlt := hf z hz
    simp only [h, zero_apply, lt_self_iff_false] at hlt
  obtain ⟨q, hqD, hqmax⟩ := hD.exists_isMaxOn ⟨p, hp⟩ f.continuous.continuousOn
  have hqU : q ∉ U := fun h => (hf q h).not_ge (hqmax hp)
  have hqint : q ∈ interior D := by
    by_contra h
    exact hqU (hfront ⟨subset_closure hqD, h⟩)
  have himage : f '' interior D ⊆ Iic (f q) := by
    rintro y ⟨x, hx, rfl⟩
    exact hqmax (interior_subset hx)
  have hmax := interior_maximal himage (f.isOpenMap_of_ne_zero hfne _ isOpen_interior)
    (mem_image_of_mem f hqint)
  rw [interior_Iic] at hmax
  exact (lt_irrefl (f q)) hmax

end DifferentialGeometry.Topology
