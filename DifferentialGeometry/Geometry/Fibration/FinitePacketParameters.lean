import DifferentialGeometry.Analysis.ParameterSelection.Acyclic
import Mathlib.Order.Interval.Set.Basic

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Geometry.Fibration

/-- Finite primitive upper, lower and mixed interval bounds have one dependent assignment. -/
theorem finite_packet_parameters {ι κ : Type*} [Finite ι] {r : ι → ι → Prop}
    (hacyclic : ∀ i, ¬ Relation.TransGen r i i) (mode : ι → Fin 3)
    (upper lower : ι → Finset κ)
    (bound : ∀ i, (∀ j, r j i → ℝ) → κ → ℝ)
    (lo hi : ∀ i, (∀ j, r j i → ℝ) → ℝ)
    (hupper : ∀ i, mode i = 0 → ∀ v, ∀ j ∈ upper i, 0 < bound i v j)
    (hmixed : ∀ i, mode i = 2 → ∀ v, lo i v < hi i v) :
    ∃ f : ι → ℝ, ∀ i,
      (mode i = 0 → 0 < f i ∧ ∀ j ∈ upper i, f i < bound i (fun j _ => f j) j) ∧
      (mode i = 1 → ∀ j ∈ lower i, bound i (fun j _ => f j) j < f i) ∧
      (mode i = 2 → f i ∈ Ioo (lo i (fun j _ => f j)) (hi i (fun j _ => f j))) := by
  classical
  let P (i : ι) (v : ∀ j, r j i → ℝ) (x : ℝ) :=
    (mode i = 0 → 0 < x ∧ ∀ j ∈ upper i, x < bound i v j) ∧
    (mode i = 1 → ∀ j ∈ lower i, bound i v j < x) ∧
    (mode i = 2 → x ∈ Ioo (lo i v) (hi i v))
  have hnode (i : ι) (v : ∀ j, r j i → ℝ) : ∃ x : ℝ, P i v x := by
    have hm : mode i = 0 ∨ mode i = 1 ∨ mode i = 2 := by omega
    rcases hm with hm | hm | hm
    · obtain ⟨x, hx, hb⟩ := Finset.exists_pos_lt_bounds (upper i) (bound i v) (hupper i hm v)
      exact ⟨x, fun _ => ⟨hx, hb⟩, by simp [hm], by simp [hm]⟩
    · obtain ⟨x, hx⟩ := Finset.exists_gt_bounds (lower i) (bound i v)
      exact ⟨x, by simp [hm], fun _ => hx, by simp [hm]⟩
    · have hh := hmixed i hm v
      refine ⟨(lo i v + hi i v) / 2, by simp [hm], by simp [hm], ?_⟩
      intro _
      constructor <;> linarith
  obtain ⟨f, _, hf⟩ := (Relation.wellFounded_of_finite_acyclic hacyclic).exists_assignment
    (A := fun _ => ℝ) (fun _ => univ) P (by
      intro i v _
      obtain ⟨x, hx⟩ := hnode i v
      exact ⟨x, mem_univ x, hx⟩)
  exact ⟨f, hf⟩

end DifferentialGeometry.Geometry.Fibration
