import DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation

noncomputable section
open Set
open scoped Topology

namespace DifferentialGeometry.Topology.SphereSeparation

variable {A N : Type*} [TopologicalSpace A] [TopologicalSpace N]

private theorem prod_level_frontier_below (h : ℝ) :
    frontier (univ ×ˢ Iio h : Set (A × ℝ)) = univ ×ˢ {h} := by
  have heq : (univ ×ˢ Iio h : Set (A × ℝ))ᶜ = univ ×ˢ Ici h := by
    ext x
    simp
  rw [frontier_eq_closure_inter_closure, heq, closure_prod_eq, closure_prod_eq,
    closure_univ, closure_Iio, closure_Ici, prod_inter_prod, univ_inter]
  congr 1
  ext z
  simp only [mem_inter_iff, mem_Iic, mem_Ici, mem_singleton_iff]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

private theorem prod_level_frontier_above (h : ℝ) :
    frontier (univ ×ˢ Ioi h : Set (A × ℝ)) = univ ×ˢ {h} := by
  have heq : (univ ×ˢ Ioi h : Set (A × ℝ))ᶜ = univ ×ˢ Iic h := by
    ext x
    simp
  rw [frontier_eq_closure_inter_closure, heq, closure_prod_eq, closure_prod_eq,
    closure_univ, closure_Ioi, closure_Iic, prod_inter_prod, univ_inter]
  congr 1
  ext z
  simp only [mem_inter_iff, mem_Iic, mem_Ici, mem_singleton_iff]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

def TwoSidedSeparation.prodLevel [Nonempty A] (e : (A × ℝ) ≃ₜ N) (h : ℝ) :
    TwoSidedSeparation (e '' (univ ×ˢ ({h} : Set ℝ))) where
  negativeSide := {y | (e.symm y).2 < h}
  positiveSide := {y | h < (e.symm y).2}
  isOpen_negativeSide := isOpen_lt (continuous_snd.comp e.symm.continuous) continuous_const
  isOpen_positiveSide := isOpen_lt continuous_const (continuous_snd.comp e.symm.continuous)
  nonempty_negativeSide := by
    let p : A := Classical.choice ‹Nonempty A›
    exact ⟨e (p, h - 1), by simp⟩
  nonempty_positiveSide := by
    let p : A := Classical.choice ‹Nonempty A›
    exact ⟨e (p, h + 1), by simp⟩
  disjoint := by
    rw [disjoint_left]
    intro y hy hz
    change h < (e.symm y).2 at hy
    change (e.symm y).2 < h at hz
    exact (lt_asymm hy hz).elim
  union_eq_compl := by
    ext y
    have hmem : y ∈ e '' (univ ×ˢ ({h} : Set ℝ)) ↔ (e.symm y).2 = h := by
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [e.symm_apply_apply, mem_singleton_iff] using hz.2
      · intro hy
        exact ⟨e.symm y, ⟨mem_univ _, hy⟩, e.apply_symm_apply y⟩
    simp only [mem_union, mem_ofPred_eq, mem_compl_iff, hmem, ← ne_iff_lt_or_gt]
    exact ne_comm
  frontier_negativeSide := by
    have heq : {y : N | (e.symm y).2 < h} = e '' (univ ×ˢ Iio h : Set (A × ℝ)) := by
      ext y
      constructor
      · intro hy
        exact ⟨e.symm y, ⟨mem_univ _, hy⟩, e.apply_symm_apply y⟩
      · rintro ⟨z, hz, rfl⟩
        simpa only [mem_ofPred_eq, e.symm_apply_apply, mem_Iio, mem_Ioi] using hz.2
    rw [heq]
    change frontier (e '' (univ ×ˢ Iio h)) = e '' (univ ×ˢ {h})
    rw [← e.image_frontier, prod_level_frontier_below (A := A)]
  frontier_positiveSide := by
    have heq : {y : N | h < (e.symm y).2} = e '' (univ ×ˢ Ioi h : Set (A × ℝ)) := by
      ext y
      constructor
      · intro hy
        exact ⟨e.symm y, ⟨mem_univ _, hy⟩, e.apply_symm_apply y⟩
      · rintro ⟨z, hz, rfl⟩
        simpa only [mem_ofPred_eq, e.symm_apply_apply, mem_Iio, mem_Ioi] using hz.2
    rw [heq]
    change frontier (e '' (univ ×ˢ Ioi h)) = e '' (univ ×ˢ {h})
    rw [← e.image_frontier, prod_level_frontier_above (A := A)]

def TwoSidedSeparation.symm {S : Set N} (d : TwoSidedSeparation S) : TwoSidedSeparation S where
  positiveSide := d.negativeSide
  negativeSide := d.positiveSide
  isOpen_positiveSide := d.isOpen_negativeSide
  isOpen_negativeSide := d.isOpen_positiveSide
  nonempty_positiveSide := d.nonempty_negativeSide
  nonempty_negativeSide := d.nonempty_positiveSide
  disjoint := d.disjoint.symm
  union_eq_compl := (union_comm _ _).trans d.union_eq_compl
  frontier_positiveSide := d.frontier_negativeSide
  frontier_negativeSide := d.frontier_positiveSide

end DifferentialGeometry.Topology.SphereSeparation
