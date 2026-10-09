import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Separation.Basic

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Topology.SphereSeparation

theorem pairwise_disjoint_closure_of_isOpen_side
    {X ι : Type*} [TopologicalSpace X] {C : Set X} {sphere side : ι → Set X}
    (hopen : ∀ b, IsOpen (side b)) (hconn : ∀ b, IsConnected (side b))
    (hsphere_subset : ∀ b, sphere b ⊆ C) (hregion : ∀ b, Disjoint (side b) C)
    (hclosure : ∀ b, closure (side b) = side b ∪ sphere b)
    (hsphere_disjoint : Pairwise fun b d => Disjoint (sphere b) (sphere d))
    (hsphere_nonempty : ∀ b, (sphere b).Nonempty) :
    Pairwise fun b d => Disjoint (closure (side b)) (closure (side d)) := by
  intro b d hbd
  rw [Set.disjoint_left]
  intro x hxb hxd
  rw [hclosure b] at hxb
  rw [hclosure d] at hxd
  rcases hxb with hxb | hxb
  · rcases hxd with hxd | hxd
    · have hsubset : side d ⊆ side b ∪ (closure (side b))ᶜ := by
        intro y hy
        by_cases hyb : y ∈ side b
        · exact Or.inl hyb
        · refine Or.inr ?_
          rw [Set.mem_compl_iff, hclosure b, Set.mem_union]
          simp only [not_or]
          exact ⟨hyb, fun hyS => Set.disjoint_left.mp (hregion d) hy (hsphere_subset b hyS)⟩
      rcases (hconn d).isPreconnected.subset_or_subset (hopen b)
        (isClosed_closure.isOpen_compl)
        (Set.disjoint_left.mpr fun y hy hyc => hyc (subset_closure hy)) hsubset with hsd | hsd
      · obtain ⟨y, hy⟩ := hsphere_nonempty d
        have hy' : y ∈ closure (side d) := by
          rw [hclosure d]
          exact Or.inr hy
        have hyb : y ∈ side b ∪ sphere b := by
          rw [← hclosure b]
          exact closure_mono hsd hy'
        rcases hyb with hyb | hyb
        · exact Set.disjoint_left.mp (hregion b) hyb (hsphere_subset d hy)
        · exact Set.disjoint_left.mp (hsphere_disjoint hbd) hyb hy
      · exact hsd hxd (subset_closure hxb)
    · exact Set.disjoint_left.mp (hregion b) hxb (hsphere_subset d hxd)
  · rcases hxd with hxd | hxd
    · exact Set.disjoint_left.mp (hregion d) hxd (hsphere_subset b hxb)
    · exact Set.disjoint_left.mp (hsphere_disjoint hbd) hxb hxd

end DifferentialGeometry.Topology.SphereSeparation
