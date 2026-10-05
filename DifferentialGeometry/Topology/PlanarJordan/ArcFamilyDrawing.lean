import DifferentialGeometry.External.Schoenflies.Graph.Drawing

open Set
open scoped Graph

namespace Graph

def curveGraph {α β : Type*} (f : β → ℝ → α) (W : Set α) : Graph α β where
  vertexSet := W ∪ range (fun d => f d 0) ∪ range (fun d => f d 1)
  edgeSet := univ
  IsLink d x y := (x = f d 0 ∧ y = f d 1) ∨ (x = f d 1 ∧ y = f d 0)
  isLink_symm := by
    intro d _
    exact ⟨fun _ _ h => h.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro d x y v w (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals simp
  edge_mem_iff_exists_isLink := fun d => ⟨fun _ => ⟨f d 0, f d 1, Or.inl ⟨rfl, rfl⟩⟩,
    fun _ => mem_univ _⟩
  left_mem_of_isLink := by
    rintro d x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl (Or.inr (mem_range_self d))
    · exact Or.inr (mem_range_self d)

theorem finite_curveGraph {α β : Type*} [_root_.Finite β]
    (f : β → ℝ → α) {W : Set α} (hW : W.Finite) : (curveGraph f W).Finite :=
  ⟨(hW.union (finite_range _)).union (finite_range _), finite_univ⟩

open Schoenflies in
theorem isDrawing_curveGraph {β : Type*} {f : β → ℝ → Plane} {W : Set Plane}
    (hf : ∀ d, ContinuousOn (f d) unitInterval) (hi : ∀ d, InjOn (f d) unitInterval)
    (hW : ∀ d, edgeArc f d ∩ W ⊆ {f d 0, f d 1})
    (hmeet : Pairwise fun d j => edgeArc f d ∩ edgeArc f j ⊆ {f d 0, f d 1}) :
    IsDrawing (curveGraph f W) f := by
  have hlink (d : β) : (curveGraph f W).IsLink d (f d 0) (f d 1) := Or.inl ⟨rfl, rfl⟩
  have hvertex (d : β) {v : Plane} (hv : v ∈ V(curveGraph f W))
      (hvd : v ∈ edgeArc f d) : v = f d 0 ∨ v = f d 1 := by
    rcases hv with (hv | ⟨j, rfl⟩) | ⟨j, rfl⟩
    · exact hW d ⟨hvd, hv⟩
    · by_cases hj : d = j
      · subst j
        exact Or.inl rfl
      exact hmeet hj ⟨hvd, mem_image_of_mem (f j) zero_mem_I⟩
    · by_cases hj : d = j
      · subst j
        exact Or.inr rfl
      exact hmeet hj ⟨hvd, mem_image_of_mem (f j) one_mem_I⟩
  refine ⟨fun {d} _ => ⟨hf d, hi d, hlink d⟩, ?_, ?_⟩
  · intro d x y v hxy hv hvd
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hvertex d hv hvd
    · exact (hvertex d hv hvd).symm
  · intro d j _ _ hdj p hpd hpj
    have hpdends := hmeet hdj ⟨hpd, hpj⟩
    have hpjends := hmeet (Ne.symm hdj) ⟨hpj, hpd⟩
    refine ⟨?_, ?_, ?_⟩
    · rcases hpdends with rfl | rfl
      · exact (hlink d).left_mem
      · exact (hlink d).right_mem
    · exact hpdends.elim (fun heq => heq ▸ (hlink d).inc_left)
        (fun heq => heq ▸ (hlink d).inc_right)
    · exact hpjends.elim (fun heq => heq ▸ (hlink j).inc_left)
        (fun heq => heq ▸ (hlink j).inc_right)

end Graph
