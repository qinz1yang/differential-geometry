/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceTorusCycle

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] {U : Set M₁}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}

omit [FiniteDimensional ℝ Ea] in
theorem eq_or_eq_of_section34VertexIndex_subset (e : Section34EdgeIndex 𝒦 𝒦')
    {a b w : Section34VertexIndex 𝒦 𝒦'} (hab : (e.1 : Set Ea) = (a.1 : Set Ea) ∪ (b.1 : Set Ea))
    (hwe : w.1 ⊆ e.1) : w = a ∨ w = b := by
  have h : ((w.1 : Finset Ea) : Set Ea) ⊆ (a.1 : Set Ea) ∪ (b.1 : Set Ea) := by
    rw [← hab]
    exact Finset.coe_subset.mpr hwe
  rcases eq_or_eq_of_card_eq_one_of_subset_union w.2.2.1 a.2.2.1 b.2.2.1 h with h' | h'
  · exact Or.inl (Subtype.ext h')
  · exact Or.inr (Subtype.ext h')

theorem exists_section34EdgeIndex_pair_of_incident (hsub : IsSubdivision 𝒦'.complex 𝒦.complex)
    (hmap : 𝒦'.map = 𝒦.map) (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (hw : Section34Incident w.1 s.1) :
    ∃ e₁ e₂ : Section34EdgeIndex 𝒦 𝒦', e₁ ≠ e₂ ∧ Section34Incident e₁.1 s.1 ∧
      Section34Incident e₂.1 s.1 ∧ w.1 ⊆ e₁.1 ∧ w.1 ⊆ e₂.1 ∧
      ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 → w.1 ⊆ e.1 →
        e = e₁ ∨ e = e₂ := by
  classical
  set R : Set Ea := ⋃ u ∈ s.1, convexHull ℝ ((s.1.erase u : Finset Ea) : Set Ea)
  have hRs : R ⊆ convexHull ℝ (s.1 : Set Ea) :=
    iUnion₂_subset fun u _ => convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset u s.1))
  have hs𝒦 : convexHull ℝ (s.1 : Set Ea) ⊆ 𝒦.complex.space :=
    𝒦.complex.convexHull_subset_space s.2.1
  have hsp' : 𝒦'.complex.space = 𝒦.complex.space := hsub.1
  have hRsph : IsPLSphere 1 R := isPLSphere_biUnion_erase s.1 (𝒦.complex.indep s.2.1) s.2.2
  have hL₀ : (restrict 𝒦.complex R).space = R := by
    refine Subset.antisymm (restrict_space_subset _ _) fun x hx => ?_
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
    have hcard : (s.1.erase u).card = 2 := by rw [Finset.card_erase_of_mem hu, s.2.2]
    exact (restrict 𝒦.complex R).convexHull_subset_space
      ⟨𝒦.complex.down_closed s.2.1 (Finset.erase_subset u s.1) (Finset.card_pos.mp (by omega)),
        subset_iUnion₂ (s := fun u (_ : u ∈ s.1) =>
          convexHull ℝ ((s.1.erase u : Finset Ea) : Set Ea)) u hu⟩ hxu
  set L := restrict 𝒦'.complex R
  have hLsub : IsSubdivision L (restrict 𝒦.complex R) := by
    have := hsub.restrict (restrict 𝒦.complex R) (restrict_faces_subset _ _)
    rwa [hL₀] at this
  have hLsp : L.space = R := hLsub.1.trans hL₀
  have hRc : IsCompact R := hRsph.isPolyhedron.isCompact
  have hLfin : L.faces.Finite := by
    refine (𝒦'.finite_faces_inter_of_isCompact hRc ((hRs.trans hs𝒦).trans hsp'.ge)).subset ?_
    rintro σ ⟨hσ, hσR⟩
    obtain ⟨q, hq⟩ := 𝒦'.complex.nonempty_of_mem_faces hσ
    exact ⟨hσ, q, subset_convexHull ℝ _ (Finset.mem_coe.mpr hq),
      hσR (subset_convexHull ℝ _ (Finset.mem_coe.mpr hq))⟩
  have _ : Finite L.faces := hLfin.to_subtype
  have hLman : IsCombinatorialManifold 1 L :=
    IsPLSphere.isCombinatorialManifold (n := 0) (by rw [hLsp]; exact hRsph)
  obtain ⟨-, hnbr⟩ := (isCombinatorialManifold_one_iff L).mp hLman
  have hgraphR : ∀ x ∈ R, 𝒦'.map x ∈ graphSkeletonSpace 𝒦 := fun x hx => by
    rw [hmap]
    exact map_mem_graphSkeletonSpace_of_mem_biUnion_convexHull_erase s hx
  have hRof : ∀ σ : Finset Ea, σ ∈ 𝒦'.complex.faces →
      simplexBody 𝒦' σ ⊆ graphSkeletonSpace 𝒦 → (σ : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea) →
        convexHull ℝ (σ : Set Ea) ⊆ R := by
    intro σ hσ hσg hσs y hy
    have hy𝒦 : y ∈ 𝒦.complex.space := hsp'.le (𝒦'.complex.convexHull_subset_space hσ hy)
    have hys : y ∈ convexHull ℝ (s.1 : Set Ea) := convexHull_min hσs (convex_convexHull ℝ _) hy
    have hyg : 𝒦.map y ∈ graphSkeletonSpace 𝒦 := by
      rw [← hmap]
      exact hσg ⟨y, hy, rfl⟩
    exact mem_biUnion_convexHull_erase_of_map_mem_graphSkeletonSpace s hy𝒦 hys hyg
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp w.2.2.1
  have hvL : ({v} : Finset Ea) ∈ L.faces := by
    refine ⟨hv ▸ w.2.1, ?_⟩
    rw [← hv]
    exact hRof w.1 w.2.1 w.2.2.2 hw
  obtain ⟨a, b, hab, hnb⟩ := hnbr v hvL
  have hmem : ∀ x, x ∈ ({a, b} : Set Ea) → x ≠ v ∧ ({v, x} : Finset Ea) ∈ L.faces := by
    intro x hx
    rw [← hnb] at hx
    exact ⟨hx.1, by convert hx.2⟩
  have hedge : ∀ x, x ≠ v → ({v, x} : Finset Ea) ∈ L.faces →
      ∃ e : Section34EdgeIndex 𝒦 𝒦', e.1 = {v, x} ∧ Section34Incident e.1 s.1 := by
    intro x hxv hx
    refine ⟨⟨{v, x}, hx.1, Finset.card_pair (Ne.symm hxv), ?_⟩, rfl, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hgraphR y (hx.2 hy)
    · exact (subset_convexHull ℝ _).trans (hx.2.trans hRs)
  obtain ⟨ha, haL⟩ := hmem a (mem_insert a {b})
  obtain ⟨hb, hbL⟩ := hmem b (mem_insert_of_mem a (mem_singleton b))
  obtain ⟨e₁, he₁, hi₁⟩ := hedge a ha haL
  obtain ⟨e₂, he₂, hi₂⟩ := hedge b hb hbL
  have hwe : ∀ x, w.1 ⊆ ({v, x} : Finset Ea) := by
    intro x
    rw [hv]
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self v {x})
  refine ⟨e₁, e₂, fun h => hab ?_, hi₁, hi₂, he₁ ▸ hwe a, he₂ ▸ hwe b, fun e he hwe' => ?_⟩
  · have hvab : ({v, a} : Finset Ea) = {v, b} := by rw [← he₁, ← he₂, h]
    have ha' : a ∈ ({v, b} : Finset Ea) := by
      rw [← hvab]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self a)
    rcases Finset.mem_insert.mp ha' with h' | h'
    · exact absurd h' ha
    · exact Finset.mem_singleton.mp h'
  · obtain ⟨x, y, hxy, hexy⟩ := Finset.card_eq_two.mp e.2.2.1
    have hve : v ∈ e.1 := hwe' (by rw [hv]; exact Finset.mem_singleton_self v)
    obtain ⟨z, hzv, hez⟩ : ∃ z, z ≠ v ∧ e.1 = {v, z} := by
      rw [hexy] at hve
      rcases Finset.mem_insert.mp hve with h | h
      · refine ⟨y, fun h' => hxy ?_, ?_⟩
        · rw [← h, ← h']
        · rw [hexy, ← h]
      · have h := Finset.mem_singleton.mp h
        refine ⟨x, fun h' => hxy ?_, ?_⟩
        · rw [h', h]
        · rw [hexy, h, Finset.pair_comm]
    have hzL : ({v, z} : Finset Ea) ∈ L.faces := by
      rw [← hez]
      exact ⟨e.2.1, hRof e.1 e.2.1 e.2.2.2 he⟩
    have hz : z ∈ ({a, b} : Set Ea) := by
      rw [← hnb]
      exact ⟨hzv, by convert hzL⟩
    rcases hz with hz | hz
    · left
      apply Subtype.ext
      rw [hez, he₁, hz]
    · right
      apply Subtype.ext
      rw [hez, he₂, mem_singleton_iff.mp hz]

theorem exists_section34EdgeIndex_incident_not_subset
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (hw : Section34Incident w.1 s.1) :
    ∃ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 ∧ ¬ w.1 ⊆ e.1 := by
  classical
  obtain ⟨e₁, -, -, hi₁, -, hw₁, -, -⟩ :=
    exists_section34EdgeIndex_pair_of_incident hsub hmap s w hw
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp w.2.2.1
  have hve₁ : v ∈ e₁.1 := hw₁ (by rw [hv]; exact Finset.mem_singleton_self v)
  obtain ⟨a, hav, hae₁, he₁eq⟩ : ∃ a, a ≠ v ∧ a ∈ e₁.1 ∧ e₁.1 = {v, a} := by
    obtain ⟨x, y, hxy, hexy⟩ := Finset.card_eq_two.mp e₁.2.2.1
    rw [hexy] at hve₁
    rcases Finset.mem_insert.mp hve₁ with h | h
    · refine ⟨y, fun h' => hxy (h.symm.trans h'.symm), ?_, ?_⟩
      · rw [hexy]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
      · rw [hexy, h]
    · have h := Finset.mem_singleton.mp h
      refine ⟨x, fun h' => hxy (h'.trans h), ?_, ?_⟩
      · rw [hexy]
        exact Finset.mem_insert_self x {y}
      · rw [hexy, h, Finset.pair_comm]
  have hae : ({a} : Finset Ea) ⊆ e₁.1 := Finset.singleton_subset_iff.mpr hae₁
  let wa : Section34VertexIndex 𝒦 𝒦' :=
    ⟨{a}, 𝒦'.complex.down_closed e₁.2.1 hae (Finset.singleton_nonempty a),
      Finset.card_singleton a,
      (image_mono (convexHull_mono (Finset.coe_subset.mpr hae))).trans e₁.2.2.2⟩
  have hwa : Section34Incident wa.1 s.1 :=
    (Finset.coe_subset.mpr hae).trans hi₁
  obtain ⟨f₁, f₂, hf, hfi₁, hfi₂, hfa₁, hfa₂, -⟩ :=
    exists_section34EdgeIndex_pair_of_incident hsub hmap s wa hwa
  obtain ⟨f, hfi, hfa, hfe⟩ : ∃ f : Section34EdgeIndex 𝒦 𝒦', Section34Incident f.1 s.1 ∧
      wa.1 ⊆ f.1 ∧ f ≠ e₁ := by
    by_cases h : f₁ = e₁
    · exact ⟨f₂, hfi₂, hfa₂, fun h' => hf (h.trans h'.symm)⟩
    · exact ⟨f₁, hfi₁, hfa₁, h⟩
  refine ⟨f, hfi, fun hwf => ?_⟩
  have haf : a ∈ f.1 := hfa (Finset.mem_singleton_self a)
  have hvf : v ∈ f.1 := hwf (by rw [hv]; exact Finset.mem_singleton_self v)
  have hfeq : f.1 = {v, a} := by
    symm
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro z hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · rw [hz]
        exact hvf
      · rw [Finset.mem_singleton.mp hz]
        exact haf
    · rw [f.2.2.1, Finset.card_pair (Ne.symm hav)]
  exact hfe (Subtype.ext (hfeq.trans he₁eq.symm))

end DifferentialGeometry.Topology.PiecewiseLinear
