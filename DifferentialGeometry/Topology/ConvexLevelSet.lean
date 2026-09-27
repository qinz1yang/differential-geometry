import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.IntermediateValue

open Set

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_mem_interior_fiber_of_convex {C : Set E} (hC : Convex ℝ C)
    (hinter : (interior C).Nonempty) {f : E → ℝ} (hf : Continuous f) {r : ℝ}
    (hbelow : ∃ x ∈ C, f x < r) (habove : ∃ y ∈ C, r < f y) :
    ∃ x ∈ interior C, f x = r := by
  have hdense : C ⊆ closure (interior C) := by
    rw [hC.closure_interior_eq_closure_of_nonempty_interior hinter]
    exact subset_closure
  obtain ⟨x, hx, hxr⟩ := hbelow
  obtain ⟨y, hy, hry⟩ := habove
  obtain ⟨u, hu, hur⟩ :=
    (closure_inter_open_nonempty_iff (isOpen_lt hf continuous_const)).mp ⟨x, hdense hx, hxr⟩
  obtain ⟨v, hv, hrv⟩ :=
    (closure_inter_open_nonempty_iff (isOpen_lt continuous_const hf)).mp ⟨y, hdense hy, hry⟩
  exact hC.interior.isPreconnected.intermediate_value hu hv hf.continuousOn ⟨hur.le, hrv.le⟩

theorem exists_mem_interior_preimage_Ioo_of_convex {C : Set E} (hC : Convex ℝ C)
    (hinter : (interior C).Nonempty) {f : E → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hbelow : ∃ x ∈ C, f x < b) (habove : ∃ y ∈ C, a < f y) :
    ∃ x ∈ interior C, f x ∈ Ioo a b := by
  have hpoint : (C ∩ f ⁻¹' Ioo a b).Nonempty := by
    obtain ⟨x, hx, hxb⟩ := hbelow
    by_cases hax : a < f x
    · exact ⟨x, hx, hax, hxb⟩
    obtain ⟨y, hy, hay⟩ := habove
    by_cases hyb : f y < b
    · exact ⟨y, hy, hay, hyb⟩
    obtain ⟨z, hz, hzm⟩ := hC.isPreconnected.intermediate_value hx hy hf.continuousOn
      (show (a + b) / 2 ∈ Icc (f x) (f y) by constructor <;> linarith)
    exact ⟨z, hz, by change a < f z ∧ f z < b; rw [hzm]; constructor <;> linarith⟩
  have hdense : C ⊆ closure (interior C) := by
    rw [hC.closure_interior_eq_closure_of_nonempty_interior hinter]
    exact subset_closure
  exact (closure_inter_open_nonempty_iff (isOpen_Ioo.preimage hf)).mp
    (hpoint.mono (inter_subset_inter_left _ hdense))
end DifferentialGeometry.Topology
