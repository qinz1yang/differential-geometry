import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

open Set Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

theorem compact_sides_nested_of_disjoint_slices
    {X : Type*} [TopologicalSpace X]
    (B1 U1 S1 B2 U2 S2 : Set X)
    (hB1 : IsPreconnected B1) (hU1 : IsPreconnected U1) (hS2 : IsPreconnected S2)
    (hB1op : IsOpen B1) (hU1op : IsOpen U1) (hB2op : IsOpen B2) (hU2op : IsOpen U2)
    (hdis1 : Disjoint B1 U1) (hdis2 : Disjoint B2 U2)
    (hcover1 : B1 ∪ U1 = S1ᶜ) (hcover2 : B2 ∪ U2 = S2ᶜ)
    (hK1 : closure B1 = U1ᶜ) (hK2 : closure B2 = U2ᶜ)
    (hfront1 : frontier U1 = S1) (hfront2 : frontier U2 = S2)
    (hcompact2 : IsCompact (closure B2)) (hnoncompact1 : ¬ IsCompact (closure U1))
    (hslices : Disjoint S1 S2) (hcommon : (B1 ∩ B2).Nonempty) :
    closure B1 ⊆ B2 ∨ closure B2 ⊆ B1 := by
  classical
  have hsplitSub : S2 ⊆ B1 ∪ U1 := by
    rw [hcover1]
    intro x hx hx1
    exact Set.disjoint_left.mp hslices hx1 hx
  rcases hS2.subset_or_subset hB1op hU1op hdis1 hsplitSub with hS2B1 | hS2U1
  · have hU1cover : U1 ⊆ B2 ∪ U2 := by
      rw [hcover2]
      intro x hx hxS2
      exact Set.disjoint_left.mp hdis1 (hS2B1 hxS2) hx
    have hU1U2 : U1 ⊆ U2 := by
      rcases hU1.subset_or_subset hB2op hU2op hdis2 hU1cover with hU1B2 | hU1U2
      · exact False.elim (hnoncompact1
          (hcompact2.of_isClosed_subset isClosed_closure (closure_mono hU1B2)))
      · exact hU1U2
    have hS1U2 : S1 ⊆ U2 := by
      intro x hx
      by_contra hnot
      have hxcl : x ∈ closure U2 := (closure_mono hU1U2)
        (frontier_subset_closure (hfront1.symm ▸ hx))
      have hxfront : x ∈ frontier U2 := by
        rw [frontier, hU2op.interior_eq]
        exact ⟨hxcl, hnot⟩
      exact Set.disjoint_left.mp hslices hx (hfront2 ▸ hxfront)
    right
    intro x hx
    have hnotU2 : x ∉ U2 := by simpa only [hK2, mem_compl_iff] using hx
    by_cases hxS1 : x ∈ S1
    · exact False.elim (hnotU2 (hS1U2 hxS1))
    · have hcases : x ∈ B1 ∪ U1 := by rw [hcover1]; exact hxS1
      rcases hcases with hxB1 | hxU1
      · exact hxB1
      · exact False.elim (hnotU2 (hU1U2 hxU1))
  · have hB1cover : B1 ⊆ B2 ∪ U2 := by
      rw [hcover2]
      intro x hx hxS2
      exact Set.disjoint_left.mp hdis1 hx (hS2U1 hxS2)
    have hB1B2 : B1 ⊆ B2 := hB1.subset_left_of_subset_union hB2op hU2op hdis2 hB1cover hcommon
    left
    intro x hx
    have hnotU1 : x ∉ U1 := by simpa only [hK1, mem_compl_iff] using hx
    have hnotU2 : x ∉ U2 := by
      simpa only [hK2, mem_compl_iff] using closure_mono hB1B2 hx
    by_cases hxS2 : x ∈ S2
    · exact False.elim (hnotU1 (hS2U1 hxS2))
    · have hcases : x ∈ B2 ∪ U2 := by rw [hcover2]; exact hxS2
      exact hcases.resolve_right hnotU2

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
