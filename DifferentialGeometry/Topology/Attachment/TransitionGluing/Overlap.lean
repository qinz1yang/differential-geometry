import DifferentialGeometry.Topology.Attachment.TransitionGluing
import DifferentialGeometry.Topology.Embedding.SubtypePreimage

section

noncomputable section
open Set Topology
universe u
namespace TopCat.GlueData
variable {ι E : Type u} [TopologicalSpace E]
    (U : Set E) (hU : IsOpen U) (near : ι → ι → Bool)
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hJ : ∀ a, ContinuousOn (J a) U)
    (hrefl : ∀ i, near i i = true)
    (hsymm : ∀ i j, near i j = true → near j i = true)
    (hself : ∀ i x, x ∈ U → J ⟨(i, i), hrefl i⟩ x = x)
    (hinv : ∀ i j (h : near i j = true) x, x ∈ U → J ⟨(i, j), h⟩ x ∈ U →
      J ⟨(j, i), hsymm i j h⟩ (J ⟨(i, j), h⟩ x) = x)
    (htrans : ∀ i j k (hij : near i j = true) (hjk : near j k = true) x,
      x ∈ U → J ⟨(i, j), hij⟩ x ∈ U → J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x) ∈ U →
      ∃ hik : near i k = true,
        J ⟨(i, k), hik⟩ x = J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x))


theorem ofTransitionMaps_ι_eq_iff_graph (i j : ι) (z w : U) :
    (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι i z =
      (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι j w ↔
      ∃ h : near i j = true, J ⟨(i, j), h⟩ z = w :=
  ((ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).ι_eq_iff_rel i j z w).trans
    (rel_iff_graph U hU near J hJ hrefl hsymm hself hinv htrans i j z w)


theorem ofTransitionMaps_near_of_nonempty_inter_range (i j : ι)
    (h : (range ((ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι i) ∩
      range ((ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι j)).Nonempty) :
    near i j = true := by
  obtain ⟨p, ⟨z, rfl⟩, w, hw⟩ := h
  exact ((ofTransitionMaps_ι_eq_iff_graph U hU near J hJ hrefl hsymm hself hinv htrans
    i j z w).mp hw.symm).choose

theorem ofTransitionMaps_mapsTo_of_subset_image (i j : ι) (h : near i j = true)
    {L : Set (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.glued}
    {W : Set E}
    (hL : L ⊆ (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι j ''
      {z : U | (z : E) ∈ W}) :
    MapsTo (J ⟨(i, j), h⟩)
      (Subtype.val '' ((ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι i ⁻¹' L)) W := by
  rintro z ⟨u, hu, rfl⟩
  obtain ⟨v, hv, huv⟩ := hL hu
  obtain ⟨h', heq⟩ := (ofTransitionMaps_ι_eq_iff_graph U hU near J hJ hrefl hsymm hself hinv htrans
    i j u v).mp huv.symm
  exact heq ▸ hv

end TopCat.GlueData

end

end

section

noncomputable section
open Set Topology
universe u
namespace TopCat.GlueData
variable {ι E : Type u} [TopologicalSpace E]
    (U : Set E) (hU : IsOpen U) (near : ι → ι → Bool)
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hJ : ∀ a, ContinuousOn (J a) U)
    (hrefl : ∀ i, near i i = true)
    (hsymm : ∀ i j, near i j = true → near j i = true)
    (hself : ∀ i x, x ∈ U → J ⟨(i, i), hrefl i⟩ x = x)
    (hinv : ∀ i j (h : near i j = true) x, x ∈ U → J ⟨(i, j), h⟩ x ∈ U →
      J ⟨(j, i), hsymm i j h⟩ (J ⟨(i, j), h⟩ x) = x)
    (htrans : ∀ i j k (hij : near i j = true) (hjk : near j k = true) x,
      x ∈ U → J ⟨(i, j), hij⟩ x ∈ U → J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x) ∈ U →
      ∃ hik : near i k = true,
        J ⟨(i, k), hik⟩ x = J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x))


theorem ofTransitionMaps_compact_overlap (i j : ι)
    {L : Set (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.glued}
    {Wi Wj : Set E} (hL : IsCompact L) (hLn : L.Nonempty)
    (hLi : L ⊆ (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι i ''
      {z : U | (z : E) ∈ Wi})
    (hLj : L ⊆ (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι j ''
      {z : U | (z : E) ∈ Wj}) :
    let K := Subtype.val '' ((ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.ι i ⁻¹' L)
    IsCompact K ∧ K ⊆ Wi ∧
      ∃ h : near i j = true, MapsTo (J ⟨(i, j), h⟩) K Wj := by
  dsimp only
  let D := ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans
  have hLi' : L ⊆ range (D.toGlueData.ι i) := hLi.trans (image_subset_range _ _)
  have hLj' : L ⊆ range (D.toGlueData.ι j) := hLj.trans (image_subset_range _ _)
  have hij : near i j = true :=
    ofTransitionMaps_near_of_nonempty_inter_range U hU near J hJ hrefl hsymm hself hinv htrans
      i j (hLn.mono (subset_inter hLi' hLj'))
  exact ⟨(D.ι_isOpenEmbedding i).isInducing.isCompact_image_subtype_preimage hL hLi',
    (D.ι_isOpenEmbedding i).injective.image_subtype_preimage_subset hLi,
    hij, ofTransitionMaps_mapsTo_of_subset_image U hU near J hJ hrefl hsymm hself hinv htrans i j hij hLj⟩

end TopCat.GlueData

end

end
