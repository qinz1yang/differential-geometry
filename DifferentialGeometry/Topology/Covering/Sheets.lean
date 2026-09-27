import Mathlib.Topology.Covering.Basic

noncomputable section
open Set Bundle
namespace DifferentialGeometry.Topology.Covering

variable {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
  [DiscreteTopology F] {p : E → B}

def sheet (t : Trivialization F p) (o : F) : OpenPartialHomeomorph E B where
  toFun := p
  invFun x := t.toOpenPartialHomeomorph.symm (x, o)
  source := t.source ∩ {z | (t z).2 = o}
  target := t.baseSet
  map_source' z hz := t.mem_source.mp hz.1
  map_target' x hx := by
    exact ⟨t.map_target (t.mem_target.mpr hx), congrArg Prod.snd (t.apply_symm_apply (t.mem_target.mpr hx))⟩
  left_inv' z hz := by
    have ht : t z = (p z, o) := Prod.ext (t.proj_toFun z hz.1) hz.2
    rw [← ht]
    exact t.toOpenPartialHomeomorph.left_inv hz.1
  right_inv' x hx := t.proj_symm_apply' hx
  open_source := t.toOpenPartialHomeomorph.continuousOn.snd.isOpen_inter_preimage t.open_source (isOpen_discrete {o})
  open_target := t.open_baseSet
  continuousOn_toFun := (t.toOpenPartialHomeomorph.continuousOn.fst.congr (fun z hz => (t.proj_toFun z hz).symm)).mono
    inter_subset_left
  continuousOn_invFun := t.toOpenPartialHomeomorph.continuousOn_symm.comp (Continuous.prodMk_left o).continuousOn
    (fun x hx => t.mem_target.mpr hx)

theorem sheet_disjoint (t : Trivialization F p) {o o' : F} (h : o ≠ o') :
    Disjoint (sheet t o).source (sheet t o').source := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact h (hz.2.symm.trans hz'.2)

theorem sheet_union (t : Trivialization F p) (o o' : F) (h : ∀ q : F, q = o ∨ q = o') :
    (sheet t o).source ∪ (sheet t o').source = p ⁻¹' t.baseSet := by
  ext z
  constructor
  · rintro (hz | hz) <;> exact t.mem_source.mp hz.1
  · intro hz
    rcases h (t z).2 with ho | ho'
    · exact Or.inl ⟨t.mem_source.mpr hz, ho⟩
    · exact Or.inr ⟨t.mem_source.mpr hz, ho'⟩

end DifferentialGeometry.Topology.Covering
