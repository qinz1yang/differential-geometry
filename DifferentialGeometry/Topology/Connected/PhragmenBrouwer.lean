import DifferentialGeometry.Topology.Connected.Separation
import DifferentialGeometry.Topology.VanKampen.CoverCycle
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Tactic.NormNum

open Set

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

theorem separates_or_separates_of_union [SimplyConnectedSpace X] [LocallyConnectedSpace X]
    (hpath : ∀ U : Set X, IsOpen U → IsConnected U → IsPathConnected U)
    {C D H K : Set X} (hC : IsClosed C) (hD : IsClosed D) (hCD : Disjoint C D)
    (hH : IsPreconnected H) (hK : IsPreconnected K) (h : Separates (C ∪ D) H K) :
    Separates C H K ∨ Separates D H K := by
  classical
  have hHC : H ⊆ Cᶜ := h.left_subset_compl.trans (compl_subset_compl.mpr subset_union_left)
  have hHD : H ⊆ Dᶜ := h.left_subset_compl.trans (compl_subset_compl.mpr subset_union_right)
  have hKC : K ⊆ Cᶜ := h.right_subset_compl.trans (compl_subset_compl.mpr subset_union_left)
  have hKD : K ⊆ Dᶜ := h.right_subset_compl.trans (compl_subset_compl.mpr subset_union_right)
  rcases H.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact Or.inl (separates_empty_left hC hKC)
  rcases K.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · exact Or.inl (separates_empty_left hC hHC).symm
  by_contra! hn
  obtain ⟨p⟩ := (joinedIn_compl_of_not_separates hpath hC hH hK hHC hKC hn.1 hx hy).joined_subtype
  obtain ⟨q⟩ := (joinedIn_compl_of_not_separates hpath hD hH hK hHD hKD hn.2 hx hy).joined_subtype
  obtain ⟨A, B, hA, hB, hd, heq, hHA, hKB⟩ := h
  let label : ↥(Dᶜ) → ℤˣ := fun z => if z.val ∈ A then -1 else 1
  have hlabel : ∀ (a b : ↑(Cᶜ ∩ Dᶜ)) (_ : Path a b),
      label ⟨a.val, a.property.2⟩ = label ⟨b.val, b.property.2⟩ := by
    intro a b r
    let f := fun t => (r t).val
    have hR : IsPreconnected (range f) :=
      (isConnected_range (continuous_subtype_val.comp r.continuous)).isPreconnected
    have hRA : range f ⊆ A ∪ B := by
      rintro z ⟨t, rfl⟩
      exact heq.symm ▸ show f t ∈ (C ∪ D)ᶜ from
        fun hz => hz.elim (r t).property.1 (r t).property.2
    have ha : a.val ∈ range f := ⟨0, congrArg Subtype.val r.source⟩
    have hb : b.val ∈ range f := ⟨1, congrArg Subtype.val r.target⟩
    rcases hR.subset_or_subset hA hB hd hRA with hs | hs
    · simp only [label, hs ha, hs hb, if_true]
    · have hna : a.val ∉ A := fun haA => disjoint_left.mp hd haA (hs ha)
      have hnb : b.val ∉ A := fun hbA => disjoint_left.mp hd hbA (hs hb)
      simp only [label, hna, hnb, if_false]
  have hcover : Cᶜ ∪ Dᶜ = (univ : Set X) := by
    rw [← compl_inter, disjoint_iff_inter_eq_empty.mp hCD, compl_empty]
  have hyA : y ∉ A := fun hyA => disjoint_left.mp hd hyA (hKB hy)
  have hne : label ⟨y, hKD hy⟩ * (label ⟨x, hHD hx⟩)⁻¹ ≠ 1 := by
    norm_num [label, hyA, hHA hx]
  exact VanKampen.not_simplyConnectedSpace_of_cover_cycle Cᶜ Dᶜ
    hC.isOpen_compl hD.isOpen_compl hcover x y (hHC hx) (hKC hy) (hHD hx) (hKD hy)
    p q label hlabel hne inferInstance

theorem phragmen_brouwer [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {C D H K : Set X} (hC : IsClosed C) (hD : IsClosed D) (hCD : Disjoint C D)
    (hH : IsPreconnected H) (hK : IsPreconnected K) (h : Separates (C ∪ D) H K) :
    Separates C H K ∨ Separates D H K := by
  apply separates_or_separates_of_union (fun U hU hconn => ?_) hC hD hCD hH hK h
  exact hU.isConnected_iff_isPathConnected.mp hconn

end DifferentialGeometry.Topology
