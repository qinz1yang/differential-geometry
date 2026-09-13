import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Maps.Basic

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Topology

namespace DifferentialGeometry.Topology

theorem isPreconnected_subset_interior_of_meets_of_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {R H : Set X} (hH : IsPreconnected H)
    (hne : (H ∩ R).Nonempty) (hdisj : Disjoint H (frontier R)) :
    H ⊆ interior R := by
  have hsub : H ⊆ interior R ∪ (closure R)ᶜ := by
    intro z hz
    by_cases hzi : z ∈ interior R
    · exact Or.inl hzi
    · refine Or.inr fun hzcl => ?_
      exact hdisj.le_bot ⟨hz, hzcl, hzi⟩
  have h1 : IsOpen (interior R) := isOpen_interior
  have h2 : IsOpen ((closure R)ᶜ) := isClosed_closure.isOpen_compl
  have h3 : Disjoint (interior R) ((closure R)ᶜ) :=
    Set.disjoint_left.mpr fun z hz1 hz2 =>
      hz2 (subset_closure (interior_subset hz1))
  rcases hH.subset_or_subset h1 h2 h3 hsub with h | h
  · exact h
  · obtain ⟨w, hwH, hwR⟩ := hne
    exact absurd (h hwH) fun hwc => hwc (subset_closure hwR)

theorem union_iUnion_closure_eq_univ_of_local_side
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [LocallyConnectedSpace X]
    {ι : Type*} (sphereRange side : ι → Set X) (R : Set X)
    (hRclosed : IsClosed R) (hRne : R.Nonempty)
    (hfront : frontier R ⊆ ⋃ b, sphereRange b)
    (hside_open : ∀ b, IsOpen (side b))
    (hside_closed : ∀ b, closure (side b) ∩ Rᶜ ⊆ side b)
    (hlocal : ∀ b, ∀ p ∈ sphereRange b, ∃ U ∈ 𝓝 p, U ∩ Rᶜ ⊆ side b) :
    R ∪ ⋃ b, closure (side b) = univ := by
  classical
  rw [Set.eq_univ_iff_forall]
  intro x
  by_cases hxR : x ∈ R
  · exact Or.inl hxR
  · refine Or.inr ?_
    have hx : x ∈ Rᶜ := hxR
    let y : ↥(Rᶜ) := ⟨x, hx⟩
    set E : Set X := connectedComponentIn Rᶜ x with hE
    have hEim : E = Subtype.val '' connectedComponent y :=
      hE.trans (connectedComponentIn_eq_image hx)
    have hEsub : E ⊆ Rᶜ := by
      rw [hEim]
      rintro z ⟨w, -, rfl⟩
      exact w.2
    have hxE : x ∈ E := by
      rw [hEim]
      exact ⟨y, mem_connectedComponent, rfl⟩
    have hRp : IsPreconnected E := by
      rw [hEim]
      exact isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
    have hRcopen : IsOpen (Rᶜ : Set X) := hRclosed.isOpen_compl
    have hEopen : IsOpen E := by
      rw [hE]
      exact hRcopen.connectedComponentIn
    have hEcl : closure E ∩ Rᶜ = E := by
      rw [hEim]
      apply Subset.antisymm
      · rintro z ⟨hzcl, hzR⟩
        have hmem2 : (⟨z, hzR⟩ : ↥(Rᶜ)) ∈
            Subtype.val ⁻¹' closure (Subtype.val '' connectedComponent y) := hzcl
        rw [← Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image] at hmem2
        rw [isClosed_connectedComponent.closure_eq] at hmem2
        exact ⟨⟨z, hzR⟩, hmem2, rfl⟩
      · rintro z ⟨w, hw, rfl⟩
        exact ⟨subset_closure ⟨w, hw, rfl⟩, w.2⟩
    have hfrontE_sub : frontier E ⊆ R := by
      intro p hp
      have hpcl : p ∈ closure E := hp.1
      have hpin : p ∉ interior E := hp.2
      by_contra hpR
      have h1 : p ∈ closure E ∩ Rᶜ := ⟨hpcl, hpR⟩
      rw [hEcl] at h1
      have h2 : p ∈ interior E := by
        rw [hEopen.interior_eq]
        exact h1
      exact hpin h2
    have hfrontE : frontier E ⊆ ⋃ b, sphereRange b := by
      refine Subset.trans ?_ hfront
      intro p hp
      have hpR : p ∈ R := hfrontE_sub hp
      have hsub : closure E ⊆ (interior R)ᶜ := by
        rw [← closure_compl]
        exact closure_mono hEsub
      have hmem : p ∈ (interior R)ᶜ := hsub (frontier_subset_closure hp)
      refine ⟨?_, hmem⟩
      rw [hRclosed.closure_eq]
      exact hpR
    have hfrontE_ne : (frontier E).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have hclE : closure E = E := by
        refine Set.Subset.antisymm ?_ subset_closure
        intro p hp
        by_contra hpE
        have hpf : p ∈ frontier E := ⟨hp, fun hpi => hpE (interior_subset hpi)⟩
        simp [hne] at hpf
      have hclopen : IsClopen E := ⟨closure_eq_iff_isClosed.mp hclE, hEopen⟩
      rcases isClopen_iff.mp hclopen with h | h
      · exact absurd (h ▸ hxE) (by simp)
      · obtain ⟨r, hr⟩ := hRne
        exact (hEsub (by rw [h]; trivial) : r ∈ Rᶜ) hr
    obtain ⟨p, hp⟩ := hfrontE_ne
    obtain ⟨b, hpb⟩ := Set.mem_iUnion.mp (hfrontE hp)
    obtain ⟨U, hU, hUsub⟩ := hlocal b p hpb
    obtain ⟨V, hVU, hVopen, hpV⟩ := mem_nhds_iff.mp hU
    obtain ⟨z, hzV, hzE⟩ := mem_closure_iff.mp (frontier_subset_closure hp) V hVopen hpV
    have hzside : z ∈ side b := hUsub ⟨hVU hzV, hEsub hzE⟩
    have hE_side : E ⊆ side b := by
      rcases hRp.subset_or_subset (hside_open b) isClosed_closure.isOpen_compl
        (Set.disjoint_left.mpr fun w hw1 hw2 => hw2 (subset_closure hw1))
        (fun w hw => by
          by_cases hwcl : w ∈ closure (side b)
          · exact Or.inl (hside_closed b ⟨hwcl, hEsub hw⟩)
          · exact Or.inr hwcl) with h | h
      · exact h
      · exact absurd (h hzE) (by simp [subset_closure hzside])
    exact Set.mem_iUnion.mpr ⟨b, subset_closure (hE_side hxE)⟩

end DifferentialGeometry.Topology
