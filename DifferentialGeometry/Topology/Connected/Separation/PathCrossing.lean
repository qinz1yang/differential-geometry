import DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path


open Set

namespace DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation

variable {X : Type*} [TopologicalSpace X] {S : Set X}

theorem exists_mem_Ioo_of_continuousOn (d : TwoSidedSeparation S)
    {a b : ℝ} {gamma : ℝ → X} (hab : a ≤ b)
    (hgamma : ContinuousOn gamma (Icc a b))
    (ha : gamma a ∈ d.negativeSide) (hb : gamma b ∈ d.positiveSide) :
    ∃ t ∈ Ioo a b, gamma t ∈ S := by
  have hhit : ∃ t ∈ Icc a b, gamma t ∈ S := by
    by_contra! havoid
    have hsub : gamma '' Icc a b ⊆ Sᶜ := by
      rintro _ ⟨t, ht, rfl⟩
      exact havoid t ht
    rcases d.subset_positiveSide_or_subset_negativeSide
        (isPreconnected_Icc.image gamma hgamma) hsub with hpos | hneg
    · exact Set.disjoint_left.mp d.disjoint
        (hpos ⟨a, ⟨le_rfl, hab⟩, rfl⟩) ha
    · exact Set.disjoint_left.mp d.disjoint hb
        (hneg ⟨b, ⟨hab, le_rfl⟩, rfl⟩)
  obtain ⟨t, ht, hS⟩ := hhit
  have hta : t ≠ a := by
    intro heq
    exact d.negativeSide_subset_compl ha (heq ▸ hS)
  have htb : t ≠ b := by
    intro heq
    exact d.positiveSide_subset_compl hb (heq ▸ hS)
  exact ⟨t, ⟨lt_of_le_of_ne ht.1 hta.symm, lt_of_le_of_ne ht.2 htb⟩, hS⟩

theorem exists_mem_Ioo_of_path (d : TwoSidedSeparation S) {x y : X}
    (gamma : Path x y) (hx : x ∈ d.negativeSide) (hy : y ∈ d.positiveSide) :
    ∃ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Ioo 0 1 ∧ gamma t ∈ S := by
  obtain ⟨t, ht, hS⟩ := d.exists_mem_Ioo_of_continuousOn (gamma := gamma.extend)
    zero_le_one gamma.continuous_extend.continuousOn
    (by simpa only [gamma.extend_zero] using hx)
    (by simpa only [gamma.extend_one] using hy)
  refine ⟨⟨t, ht.1.le, ht.2.le⟩, ht, ?_⟩
  exact (gamma.extend_extends' ⟨t, ht.1.le, ht.2.le⟩) ▸ hS

end DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation
