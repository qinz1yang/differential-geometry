/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.SeparatingComponent
import DifferentialGeometry.Topology.PiecewiseLinear.CoveringLift
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isPreconnected_compl_iUnion_of_isPreconnected_compl {X ι : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X] [Finite ι] {F : ι → Set X}
    (hF : ∀ i, IsClosed (F i)) (hd : Pairwise fun i j => Disjoint (F i) (F j))
    (hc : ∀ i, IsPreconnected (F i)ᶜ) : IsPreconnected (⋃ i, F i)ᶜ := by
  intro U V hU hV hsub ⟨a, haS, haU⟩ ⟨b, hbS, hbV⟩
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hFcl : IsClosed (⋃ i, F i) := isClosed_iUnion_of_finite hF
  have hsep : Separates (⋃ i, F i) {a} {b} := by
    refine ⟨(⋃ i, F i)ᶜ ∩ U, (⋃ i, F i)ᶜ ∩ V, hFcl.isOpen_compl.inter hU,
      hFcl.isOpen_compl.inter hV, ?_, ?_, singleton_subset_iff.mpr ⟨haS, haU⟩,
      singleton_subset_iff.mpr ⟨hbS, hbV⟩⟩
    · rw [disjoint_iff_inter_eq_empty, ← hne]
      ext y
      constructor
      · rintro ⟨⟨hy, hyU⟩, -, hyV⟩
        exact ⟨hy, hyU, hyV⟩
      · rintro ⟨hy, hyU, hyV⟩
        exact ⟨⟨hy, hyU⟩, hy, hyV⟩
    · apply Subset.antisymm
      · rintro y (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
      · intro y hy
        rcases hsub hy with h1 | h1
        · exact Or.inl ⟨hy, h1⟩
        · exact Or.inr ⟨hy, h1⟩
  obtain ⟨i, U', V', hU', hV', hd', heq', ha', hb'⟩ :=
    exists_separates_of_finite_iUnion
      (fun O hO hconn => hO.isConnected_iff_isPathConnected.mp hconn)
      F hF hd isConnected_singleton isConnected_singleton hsep
  have haF : a ∈ (F i)ᶜ := fun h' => haS (mem_iUnion.mpr ⟨i, h'⟩)
  have hbF : b ∈ (F i)ᶜ := fun h' => hbS (mem_iUnion.mpr ⟨i, h'⟩)
  obtain ⟨y, -, hyU', hyV'⟩ := hc i U' V' hU' hV' heq'.symm.subset
    ⟨a, haF, ha' (mem_singleton a)⟩ ⟨b, hbF, hb' (mem_singleton b)⟩
  exact disjoint_left.mp hd' hyU' hyV'

theorem isPreconnected_union_of_subset_union_of_disjoint_closed {X : Type*}
    [TopologicalSpace X] {S A B F Z : Set X} (hS : IsPreconnected S) (hA : IsPreconnected A)
    (hAne : A.Nonempty) (hAS : A ⊆ S) (hBS : B ⊆ S) (hSF : S ⊆ A ∪ B ∪ F) (hBZ : B ⊆ Z)
    (hZ : IsClosed Z) (hF : IsClosed F) (hZF : Disjoint Z F) : IsPreconnected (A ∪ B) := by
  rw [isPreconnected_iff_subset_of_disjoint] at hS hA ⊢
  have key : ∀ U V : Set X, IsOpen U → IsOpen V → A ∪ B ⊆ U ∪ V →
      (A ∪ B) ∩ (U ∩ V) = ∅ → A ⊆ U → A ∪ B ⊆ U := by
    intro U V hU hV hsub hdis hAU
    have hcov : S ⊆ (U ∪ Zᶜ) ∪ (V ∩ Fᶜ) := by
      intro y hy
      rcases hSF hy with (hyA | hyB) | hyF
      · exact Or.inl (Or.inl (hAU hyA))
      · rcases hsub (Or.inr hyB) with h1 | h1
        · exact Or.inl (Or.inl h1)
        · exact Or.inr ⟨h1, fun hyF => disjoint_left.mp hZF (hBZ hyB) hyF⟩
      · exact Or.inl (Or.inr fun hyZ => disjoint_left.mp hZF hyZ hyF)
    have hdis' : S ∩ ((U ∪ Zᶜ) ∩ (V ∩ Fᶜ)) = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun y ⟨hyS, hyUZ, hyV, hyF⟩ => ?_
      have hyAB : y ∈ A ∪ B := by
        rcases hSF hyS with h1 | h1
        · exact h1
        · exact absurd h1 hyF
      have hyU : y ∈ U := by
        rcases hyUZ with h1 | h1
        · exact h1
        · rcases hyAB with h2 | h2
          · exact hAU h2
          · exact absurd (hBZ h2) h1
      have hmem : y ∈ (A ∪ B) ∩ (U ∩ V) := ⟨hyAB, hyU, hyV⟩
      rw [hdis] at hmem
      exact hmem
    rcases hS (U ∪ Zᶜ) (V ∩ Fᶜ) (hU.union hZ.isOpen_compl) (hV.inter hF.isOpen_compl) hcov
      hdis' with hSU | hSV
    · rintro y (hyA | hyB)
      · exact hAU hyA
      · rcases hSU (hBS hyB) with h1 | h1
        · exact h1
        · exact absurd (hBZ hyB) h1
    · obtain ⟨a, ha⟩ := hAne
      have haV := (hSV (hAS ha)).1
      have hmem : a ∈ (A ∪ B) ∩ (U ∩ V) := ⟨Or.inl ha, hAU ha, haV⟩
      rw [hdis] at hmem
      exact hmem.elim
  intro U V hU hV hsub hdis
  have hAdis : A ∩ (U ∩ V) = ∅ := subset_empty_iff.mp fun y hy => by
    rw [← hdis]
    exact ⟨Or.inl hy.1, hy.2⟩
  rcases hA U V hU hV (subset_union_left.trans hsub) hAdis with hAU | hAV
  · exact Or.inl (key U V hU hV hsub hdis hAU)
  · refine Or.inr (key V U hV hU ?_ ?_ hAV)
    · rwa [union_comm V U]
    · rwa [inter_comm V U]

theorem vertex_ne_centroid_of_card_eq_two {K : Geometry.SimplicialComplex ℝ E3} {f : Finset E3}
    (hf : f ∈ K.faces) (hfc : f.card = 2) {a : E3} (ha : a ∈ K.vertices) :
    a ≠ f.centroid ℝ id := by
  intro hac
  have hx : f.centroid ℝ id ∈ convexHull ℝ (({a} : Finset E3) : Set E3) := by
    rw [← hac]
    exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self a))
  have hsub := face_subset_of_mem_openSimplex_of_mem_convexHull K hf ha
    (centroid_mem_openSimplex (K.nonempty_of_mem_faces hf)) hx
  have hle := Finset.card_le_card hsub
  rw [hfc, Finset.card_singleton] at hle
  omega

section CollarFacts

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {V : E3 → Set E3} {W : Finset E3 → Set E3}

theorem IsEdgeCollarFamily.eq_of_mem_of_mem (hW : IsEdgeCollarFamily K C D Dbd h V W)
    {e f : Finset E3} (he : e ∈ K.faces) (hec : e.card = 2) (hf : f ∈ K.faces)
    (hfc : f.card = 2) {x : E3} (hxe : x ∈ W e) (hxf : x ∈ W f) : e = f := by
  by_contra hne
  exact disjoint_left.mp ((hW e he hec).2.2.2.2.2 f hf hfc hne) hxe hxf

theorem IsEdgeCollarFamily.image_vertex_notMem (hW : IsEdgeCollarFamily K C D Dbd h V W)
    (ht : IsTube K N C D Dbd h N') {f : Finset E3} (hf : f ∈ K.faces) (hfc : f.card = 2)
    {a : E3} (ha : a ∈ K.vertices) : h a ∉ W f := by
  intro haW
  have hmem : h a ∈ W f ∩ h '' K.space :=
    ⟨haW, a, Geometry.SimplicialComplex.vertices_subset_space ha, rfl⟩
  rw [(hW f hf hfc).2.2.1] at hmem
  have hspaceN : K.space ⊆ N := subset_of_mem_nhdsSet ht.isNeighborhood
  have hc : f.centroid ℝ id ∈ K.space :=
    K.convexHull_subset_space hf (f.centroid_mem_convexHull (K.nonempty_of_mem_faces hf))
  exact vertex_ne_centroid_of_card_eq_two hf hfc ha
    (ht.injOn (hspaceN (Geometry.SimplicialComplex.vertices_subset_space ha)) (hspaceN hc) hmem)

theorem IsEdgeCollarFamily.image_splitDisk_subset (hW : IsEdgeCollarFamily K C D Dbd h V W)
    {f : Finset E3} (hf : f ∈ K.faces) (hfc : f.card = 2) : h '' D f ⊆ W f := by
  obtain ⟨-, hint, hK, hpair, -, -⟩ := hW f hf hfc
  obtain ⟨a, haf⟩ := K.nonempty_of_mem_faces hf
  obtain ⟨b, hbf, hba⟩ := Finset.exists_mem_ne (by omega : 1 < f.card) a
  have hbd : h '' Dbd f ⊆ W f := by
    rw [← (hpair a haf b hbf hba.symm).2]
    exact inter_subset_left
  have hc : h (f.centroid ℝ id) ∈ W f := by
    have hcm : h (f.centroid ℝ id) ∈ W f ∩ h '' K.space := by
      rw [hK]
      exact mem_singleton _
    exact hcm.1
  rintro _ ⟨x, hx, rfl⟩
  by_cases hxb : x ∈ Dbd f
  · exact hbd ⟨x, hxb, rfl⟩
  · by_cases hxc : h x = h (f.centroid ℝ id)
    · rw [hxc]
      exact hc
    · exact interior_subset (hint ⟨⟨x, ⟨hx, hxb⟩, rfl⟩, hxc⟩)

theorem IsEdgeCollarFamily.exists_mem_of_mem_image_inter
    (hW : IsEdgeCollarFamily K C D Dbd h V W) (ht : IsTube K N C D Dbd h N') {a b : E3}
    (ha : a ∈ K.vertices) (hb : b ∈ K.vertices) (hab : a ≠ b) {x : E3} (hxa : x ∈ h '' C a)
    (hxb : x ∈ h '' C b) : ∃ f ∈ K.faces, f.card = 2 ∧ a ∈ f ∧ b ∈ f ∧ x ∈ W f := by
  have hx : x ∈ h '' (C a ∩ C b) := by
    rw [ht.injOn.image_inter (ht.dualCell_subset ha) (ht.dualCell_subset hb)]
    exact ⟨hxa, hxb⟩
  by_cases hadj : ∃ f ∈ K.faces, a ∈ f ∧ b ∈ f
  · obtain ⟨f, hf, haf, hbf⟩ := hadj
    have hfc := ht.card_eq_two_of_mem hf haf hbf hab
    rw [ht.inter_eq_of_mem_faces ha hb hab hf haf hbf] at hx
    exact ⟨f, hf, hfc, haf, hbf, hW.image_splitDisk_subset hf hfc hx⟩
  · rw [ht.inter_eq_empty_of_forall_notMem_faces ha hb hab
      fun f hf haf hbf => hadj ⟨f, hf, haf, hbf⟩, image_empty] at hx
    exact hx.elim

theorem IsEdgeCollarFamily.disjoint_image_dualCell (hW : IsEdgeCollarFamily K C D Dbd h V W)
    (ht : IsTube K N C D Dbd h N') {f : Finset E3} (hf : f ∈ K.faces) (hfc : f.card = 2)
    {w : E3} (hw : w ∈ K.vertices) (hwf : w ∉ f) : Disjoint (W f) (h '' C w) := by
  obtain ⟨a, haf⟩ := K.nonempty_of_mem_faces hf
  obtain ⟨b, hbf, hba⟩ := Finset.exists_mem_ne (by omega : 1 < f.card) a
  have hvert : ∀ c ∈ f, c ∈ K.vertices := fun c hc =>
    K.down_closed hf (Finset.singleton_subset_iff.mpr hc) (Finset.singleton_nonempty c)
  have hsub := ((hW f hf hfc).2.2.2.1 a haf b hbf hba.symm).1
  rw [disjoint_left]
  intro x hxW hxw
  have key : ∀ c ∈ f, x ∈ h '' C c → False := by
    intro c hcf hxc
    have hcw : c ≠ w := fun hcw => hwf (hcw ▸ hcf)
    obtain ⟨g, hg, hgc, -, hwg, hxg⟩ :=
      hW.exists_mem_of_mem_image_inter ht (hvert c hcf) hw hcw hxc hxw
    exact hwf ((hW.eq_of_mem_of_mem hg hgc hf hfc hxg hxW) ▸ hwg)
  rcases hsub hxW with hxa | hxb
  · exact key a haf hxa
  · exact key b hbf hxb

theorem IsEdgeCollarFamily.isPreconnected_image_dualCell_sdiff
    (hW : IsEdgeCollarFamily K C D Dbd h V W) (ht : IsTube K N C D Dbd h N') {w : E3}
    (hw : w ∈ K.vertices) :
    IsPreconnected (h '' C w \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ w ∈ e}, W e) := by
  have hball := ht.dualBall w hw
  let _ : SimplyConnectedSpace (C w) := hball.simplyConnectedSpace
  let _ : LocallyPathConnectedSpace (C w) := hball.locallyPathConnectedSpace
  have hfin : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ w ∈ e}.Finite :=
    ht.facesFinite.subset fun e he => he.1
  let _ : Finite {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ w ∈ e} := hfin.to_subtype
  have hCc : IsCompact (C w) := hball.isPolyhedron.isCompact
  have hcont : ContinuousOn h (C w) := ht.continuousOn.mono (ht.dualCell_subset hw)
  have hinj : InjOn h (C w) := ht.injOn.mono (ht.dualCell_subset hw)
  have _ : CompactSpace (C w) := isCompact_iff_compactSpace.mp hCc
  have hemb : IsInducing ((C w).domRestrict h) :=
    (hcont.domRestrict.isClosedEmbedding hinj.injective).isEmbedding.isInducing
  have hF : ∀ i : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ w ∈ e},
      IsClosed ((C w).domRestrict h ⁻¹' W i) := fun i =>
    (hW i i.2.1 i.2.2.1).1.preimage hcont.domRestrict
  have hd : Pairwise fun i j : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ w ∈ e} =>
      Disjoint ((C w).domRestrict h ⁻¹' W i) ((C w).domRestrict h ⁻¹' W j) := by
    intro i j hij
    exact ((hW i i.2.1 i.2.2.1).2.2.2.2.2 j j.2.1 j.2.2.1
      fun h' => hij (Subtype.ext h')).preimage _
  have himg : ∀ T : Set E3,
      (C w).domRestrict h '' ((C w).domRestrict h ⁻¹' T)ᶜ = h '' C w \ T := by
    intro T
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, z.2, rfl⟩, hz⟩
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      exact ⟨⟨z, hz⟩, hy, rfl⟩
  have hc : ∀ i : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ w ∈ e},
      IsPreconnected ((C w).domRestrict h ⁻¹' W i)ᶜ := by
    intro i
    rw [← hemb.isPreconnected_image, himg]
    exact ((hW i i.2.1 i.2.2.1).2.2.2.2.1 w i.2.2.2).1.isPreconnected
  have hmain := isPreconnected_compl_iUnion_of_isPreconnected_compl hF hd hc
  have heq : (C w).domRestrict h '' (⋃ i : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ w ∈ e},
      (C w).domRestrict h ⁻¹' W i)ᶜ =
      h '' C w \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ w ∈ e}, W e := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, z.2, rfl⟩, fun hy => hz ?_⟩
      obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion.mpr ⟨⟨e, he⟩, hye⟩
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨⟨z, hz⟩, fun hz' => hy ?_, rfl⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz'
      exact mem_iUnion₂.mpr ⟨i, i.2, hi⟩
  rw [← heq]
  exact hmain.image _ hcont.domRestrict.continuousOn

end CollarFacts

section Leaves

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}

open Classical in
theorem isHandleDecomposition_of_edgeCollars (ht : IsTube K N C D Dbd h N')
    {V : E3 → Set E3} {W : Finset E3 → Set E3} (hW : IsEdgeCollarFamily K C D Dbd h V W)
    {Ec Eint Ebd : Finset E3 → Set E3}
    (hE : ∀ e ∈ K.faces, e.card = 2 → ∃ u v : E3, u ∈ K.vertices ∧ v ∈ K.vertices ∧ u ≠ v ∧
      e = {u, v} ∧ SplitsDualCellsAlong K N C Dbd h (W e) (Ec e) (Eint e) (Ebd e) u v) :
    (∀ v ∈ K.vertices, handlePiece K N' Ec h v ∩ h '' K.vertices = {h v}) ∧
    N' = ⋃ v ∈ K.vertices, handlePiece K N' Ec h v ∧
    (∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v → ({u, v} : Finset E3) ∈ K.faces →
      handlePiece K N' Ec h u ∩ handlePiece K N' Ec h v = Ec {u, v}) ∧
    ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v → ({u, v} : Finset E3) ∉ K.faces →
      handlePiece K N' Ec h u ∩ handlePiece K N' Ec h v = ∅ := by
  have hinj := ht.injOn
  have hcont := ht.continuousOn
  have hCN : ∀ a ∈ K.vertices, C a ⊆ N := fun a ha => ht.dualCell_subset ha
  have hclosedP : ∀ a ∈ K.vertices, IsClosed (h '' C a) := fun a ha =>
    ((ht.dualBall a ha).isPolyhedron.isCompact.image_of_continuousOn
      (hcont.mono (hCN a ha))).isClosed
  have hmemC : ∀ a ∈ K.vertices, a ∈ C a := fun a ha => ht.mem_dualCell ha
  have hVfin := ht.finite_vertices
  have hEfin : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}.Finite :=
    ht.facesFinite.subset fun e he => he.1
  have hCN' : ∀ a ∈ K.vertices, h '' C a ⊆ N' := fun a ha => by
    rw [ht.imageEq]
    exact image_mono (hCN a ha)
  have hN'cl : IsClosed N' := by
    have hNc : IsCompact N := by
      rw [ht.unionEq]
      exact hVfin.isCompact_biUnion fun v hv => (ht.dualBall v hv).isPolyhedron.isCompact
    rw [ht.imageEq]
    exact (hNc.image_of_continuousOn hcont).isClosed
  have hpiece : ∀ y ∈ N', ∃ z ∈ K.vertices, y ∈ h '' C z := by
    intro y hy
    rw [ht.imageEq] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rw [ht.unionEq] at hp
    obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
    exact ⟨z, hz, p, hpz, rfl⟩
  have hvW : ∀ f ∈ K.faces, f.card = 2 → ∀ a ∈ K.vertices, h a ∉ W f :=
    fun f hf hfc a ha => hW.image_vertex_notMem ht hf hfc ha
  have hEcW : ∀ f ∈ K.faces, f.card = 2 → Ec f ⊆ W f := by
    intro f hf hfc
    obtain ⟨_, _, -, -, -, -, hS⟩ := hE f hf hfc
    exact hS.2.2.1
  have hside : ∀ e : Finset E3, ∃ a b : E3, ∃ U₁ U₂ : Set E3, e ∈ K.faces → e.card = 2 →
      a ∈ K.vertices ∧ b ∈ K.vertices ∧ a ≠ b ∧ a ∈ e ∧ b ∈ e ∧ h a ∈ U₁ ∧ h b ∈ U₂ ∧
      IsConnected U₁ ∧ IsConnected U₂ ∧ Disjoint U₁ U₂ ∧
      U₁ ∪ U₂ = (h '' C a ∪ h '' C b) \ Ec e ∧
      (∀ V' : Set E3, IsPreconnected V' → V' ⊆ (h '' C a ∪ h '' C b) \ Ec e →
        V' ⊆ U₁ ∨ V' ⊆ U₂) ∧ Ec e ⊆ closure U₁ ∧ Ec e ⊆ closure U₂ := by
    intro e
    by_cases he : e ∈ K.faces ∧ e.card = 2
    · obtain ⟨a, b, ha, hb, hab, heq, hS⟩ := hE e he.1 he.2
      obtain ⟨-, -, -, -, -, U₁, U₂, hU₁, hU₂, hc₁, hc₂, hd, hun, hpre, hf₁, hf₂, -, -⟩ := hS
      refine ⟨a, b, U₁, U₂, fun _ _ => ⟨ha, hb, hab, ?_, ?_, hU₁, hU₂, hc₁, hc₂, hd, hun, hpre,
        hf₁.trans frontier_subset_closure, hf₂.trans frontier_subset_closure⟩⟩
      · rw [heq]
        exact Finset.mem_insert_self a {b}
      · rw [heq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    · exact ⟨0, 0, ∅, ∅, fun h1 h2 => absurd ⟨h1, h2⟩ he⟩
  choose ea eb U₁ U₂ hU using hside
  obtain ⟨sd, hsd_def⟩ : ∃ sd : E3 → Finset E3 → Set E3,
      sd = fun w e => if w = ea e then U₁ e else U₂ e := ⟨_, rfl⟩
  obtain ⟨pt, hpt_def⟩ : ∃ pt : E3 → Finset E3 → E3,
      pt = fun w e => if w = ea e then eb e else ea e := ⟨_, rfl⟩
  have hsda : ∀ e, sd (ea e) e = U₁ e := fun e => by
    rw [hsd_def]
    exact ite_eq_left rfl
  have hsdb : ∀ e ∈ K.faces, e.card = 2 → sd (eb e) e = U₂ e := fun e he hc => by
    rw [hsd_def]
    exact ite_eq_right fun h' => (hU e he hc).2.2.1 h'.symm
  have hpta : ∀ e, pt (ea e) e = eb e := fun e => by
    rw [hpt_def]
    exact ite_eq_left rfl
  have hptb : ∀ e ∈ K.faces, e.card = 2 → pt (eb e) e = ea e := fun e he hc => by
    rw [hpt_def]
    exact ite_eq_right fun h' => (hU e he hc).2.2.1 h'.symm
  have hsd : ∀ e ∈ K.faces, e.card = 2 → ∀ w ∈ e, pt w e ∈ K.vertices ∧ pt w e ∈ e ∧
      pt w e ≠ w ∧ w ∈ K.vertices ∧ h w ∈ sd w e ∧ IsConnected (sd w e) ∧
      Disjoint (sd w e) (sd (pt w e) e) ∧
      sd w e ∪ sd (pt w e) e = (h '' C w ∪ h '' C (pt w e)) \ Ec e ∧
      (∀ V' : Set E3, IsPreconnected V' → V' ⊆ (h '' C w ∪ h '' C (pt w e)) \ Ec e →
        V' ⊆ sd w e ∨ V' ⊆ sd (pt w e) e) ∧ Ec e ⊆ closure (sd w e) := by
    intro e he hc w hwe
    obtain ⟨ha, hb, hab, hae, hbe, hua, hub, hc₁, hc₂, hd, hun, hpre, hcl₁, hcl₂⟩ := hU e he hc
    rcases eq_or_eq_of_mem_of_card_eq_two hc hae hbe hab hwe with rfl | rfl
    · rw [hpta, hsda, hsdb e he hc]
      exact ⟨hb, hbe, Ne.symm hab, ha, hua, hc₁, hd, hun, hpre, hcl₁⟩
    · rw [hptb e he hc, hsda, hsdb e he hc]
      refine ⟨ha, hae, hab, hb, hub, hc₂, hd.symm, ?_,
        fun V' hV' hsub => (hpre V' hV' ?_).symm, hcl₂⟩
      · rw [union_comm (U₂ e), hun, union_comm (h '' C (eb e))]
      · rwa [union_comm] at hsub
  have hE1 : ∀ e ∈ K.faces, e.card = 2 → ∀ w ∈ e, h '' C w \ W e ⊆ sd w e := by
    intro e he hc w hwe
    obtain ⟨-, -, -, hwv, hws, -, hd, -, hpre, -⟩ := hsd e he hc w hwe
    have hconn := ((hW e he hc).2.2.2.2.1 w hwe).1
    have hsub : h '' C w \ W e ⊆ (h '' C w ∪ h '' C (pt w e)) \ Ec e :=
      fun x hx => ⟨Or.inl hx.1, fun hxE => hx.2 (hEcW e he hc hxE)⟩
    rcases hpre _ hconn.isPreconnected hsub with h1 | h1
    · exact h1
    · have hwmem : h w ∈ h '' C w \ W e := ⟨⟨w, hmemC w hwv, rfl⟩, hvW e he hc w hwv⟩
      exact absurd (h1 hwmem) (disjoint_left.mp hd hws)
  have hE2 : ∀ e ∈ K.faces, e.card = 2 → ∀ w ∈ e, sd w e ∩ h '' C (pt w e) ⊆ W e := by
    intro e he hc w hwe x ⟨hxs, hxo⟩
    by_contra hxW
    obtain ⟨-, hpe, -, -, -, -, hd, -⟩ := hsd e he hc w hwe
    exact disjoint_left.mp hd hxs (hE1 e he hc (pt w e) hpe ⟨hxo, hxW⟩)
  obtain ⟨X, hX⟩ : ∃ X : Set E3,
      X = N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e := ⟨_, rfl⟩
  have hXmem : ∀ z, z ∈ X ↔ z ∈ N' ∧ ∀ f ∈ K.faces, f.card = 2 → z ∉ Ec f := by
    intro z
    rw [hX]
    constructor
    · rintro ⟨hzN, hzE⟩
      exact ⟨hzN, fun f hf hfc hzf => hzE (mem_iUnion₂.mpr ⟨f, ⟨hf, hfc⟩, hzf⟩)⟩
    · rintro ⟨hzN, hzE⟩
      refine ⟨hzN, fun hz => ?_⟩
      obtain ⟨f, ⟨hf, hfc⟩, hzf⟩ := mem_iUnion₂.mp hz
      exact hzE f hf hfc hzf
  obtain ⟨P, hP⟩ : ∃ P : E3 → Set E3, P = fun w => {x | x ∈ X ∧
      (x ∈ h '' C w ∨ ∃ e ∈ K.faces, e.card = 2 ∧ w ∈ e ∧ x ∈ W e) ∧
      ∀ e ∈ K.faces, e.card = 2 → w ∈ e → x ∈ W e → x ∈ sd w e} := ⟨_, rfl⟩
  have hPmem : ∀ w x, x ∈ P w ↔ x ∈ X ∧
      (x ∈ h '' C w ∨ ∃ e ∈ K.faces, e.card = 2 ∧ w ∈ e ∧ x ∈ W e) ∧
      ∀ e ∈ K.faces, e.card = 2 → w ∈ e → x ∈ W e → x ∈ sd w e := by
    intro w x
    rw [hP]
    exact Iff.rfl
  have hQP : ∀ w ∈ K.vertices,
      h '' C w \ ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ w ∈ f}, W f ⊆ P w := by
    intro w hw y ⟨hyC, hyW⟩
    have hnot : ∀ e ∈ K.faces, e.card = 2 → w ∈ e → y ∉ W e := fun e he hc hwe hye =>
      hyW (mem_iUnion₂.mpr ⟨e, ⟨he, hc, hwe⟩, hye⟩)
    refine (hPmem w y).mpr ⟨(hXmem y).mpr ⟨hCN' w hw hyC, fun f hf hfc hyf => ?_⟩, Or.inl hyC,
      fun e he hc hwe hye => absurd hye (hnot e he hc hwe)⟩
    by_cases hwf : w ∈ f
    · exact hnot f hf hfc hwf (hEcW f hf hfc hyf)
    · exact disjoint_left.mp (hW.disjoint_image_dualCell ht hf hfc hw hwf) (hEcW f hf hfc hyf) hyC
  have hwP : ∀ w ∈ K.vertices, h w ∈ P w := fun w hw => hQP w hw ⟨⟨w, hmemC w hw, rfl⟩,
    fun hx => by
      obtain ⟨e, ⟨he, hc, -⟩, hxe⟩ := mem_iUnion₂.mp hx
      exact hvW e he hc w hw hxe⟩
  have hWsdP : ∀ e ∈ K.faces, e.card = 2 → ∀ w ∈ e, W e ∩ sd w e ⊆ P w := by
    intro e he hc w hwe y ⟨hye, hys⟩
    obtain ⟨hpv, -, -, hwv, -, -, -, hun, -, -⟩ := hsd e he hc w hwe
    have hyS : y ∈ (h '' C w ∪ h '' C (pt w e)) \ Ec e := by
      rw [← hun]
      exact Or.inl hys
    refine (hPmem w y).mpr ⟨(hXmem y).mpr ⟨?_, fun f hf hfc hyf => ?_⟩,
      Or.inr ⟨e, he, hc, hwe, hye⟩, fun e' he' hc' _ hye' => ?_⟩
    · rcases hyS.1 with h1 | h1
      · exact hCN' w hwv h1
      · exact hCN' _ hpv h1
    · by_cases hfe : f = e
      · rw [hfe] at hyf
        exact hyS.2 hyf
      · exact disjoint_left.mp ((hW e he hc).2.2.2.2.2 f hf hfc (Ne.symm hfe)) hye
          (hEcW f hf hfc hyf)
    · rw [hW.eq_of_mem_of_mem he' hc' he hc hye' hye]
      exact hys
  have hsdP : ∀ e ∈ K.faces, e.card = 2 → ∀ w ∈ e, ∀ y : E3,
      (∀ f ∈ K.faces, f.card = 2 → y ∈ W f → f = e) → y ∈ sd w e → y ∈ P w := by
    intro e he hc w hwe y hyW hys
    obtain ⟨-, -, -, hwv, -, -, -, hun, -, -⟩ := hsd e he hc w hwe
    by_cases hye : y ∈ W e
    · exact hWsdP e he hc w hwe ⟨hye, hys⟩
    · have hyS : y ∈ (h '' C w ∪ h '' C (pt w e)) \ Ec e := by
        rw [← hun]
        exact Or.inl hys
      have hyC : y ∈ h '' C w :=
        hyS.1.resolve_right fun hyo => hye (hE2 e he hc w hwe ⟨hys, hyo⟩)
      refine hQP w hwv ⟨hyC, fun hy => ?_⟩
      obtain ⟨f, ⟨hf, hfc, -⟩, hyf⟩ := mem_iUnion₂.mp hy
      exact hye ((hyW f hf hfc hyf) ▸ hyf)
  have hnbhd : ∀ e ∈ K.faces, e.card = 2 → ∀ x ∈ W e, ∃ O ∈ 𝓝 x, ∀ y ∈ O,
      (∀ f ∈ K.faces, f.card = 2 → y ∈ W f → f = e) ∧
      (∀ z ∈ K.vertices, y ∈ h '' C z → z ∈ e) := by
    intro e he hc x hxe
    have hF1 : IsClosed (⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ f ≠ e}, W f) :=
      (hEfin.subset fun f hf => ⟨hf.1, hf.2.1⟩).isClosed_biUnion fun f hf => (hW f hf.1 hf.2.1).1
    have hF2 : IsClosed (⋃ z ∈ {z : E3 | z ∈ K.vertices ∧ z ∉ e}, h '' C z) :=
      (hVfin.subset fun z hz => hz.1).isClosed_biUnion fun z hz => hclosedP z hz.1
    refine ⟨((⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ f ≠ e}, W f) ∪
      ⋃ z ∈ {z : E3 | z ∈ K.vertices ∧ z ∉ e}, h '' C z)ᶜ,
      (hF1.union hF2).isOpen_compl.mem_nhds ?_, ?_⟩
    · rintro (hx | hx)
      · obtain ⟨f, ⟨hf, hfc, hfe⟩, hxf⟩ := mem_iUnion₂.mp hx
        exact hfe (hW.eq_of_mem_of_mem hf hfc he hc hxf hxe)
      · obtain ⟨z, ⟨hz, hze⟩, hxz⟩ := mem_iUnion₂.mp hx
        exact disjoint_left.mp (hW.disjoint_image_dualCell ht he hc hz hze) hxe hxz
    · intro y hy
      refine ⟨fun f hf hfc hyf => ?_, fun z hz hyz => ?_⟩
      · by_contra hfe
        exact hy (Or.inl (mem_iUnion₂.mpr ⟨f, ⟨hf, hfc, hfe⟩, hyf⟩))
      · by_contra hze
        exact hy (Or.inr (mem_iUnion₂.mpr ⟨z, ⟨hz, hze⟩, hyz⟩))
  have hcleq : ∀ e ∈ K.faces, e.card = 2 → ∀ w ∈ e, ∀ x ∈ W e,
      (x ∈ closure (P w) ↔ x ∈ closure (sd w e)) := by
    intro e he hc w hwe x hxe
    obtain ⟨O, hO, hOy⟩ := hnbhd e he hc x hxe
    have hOeq : ∀ y ∈ O, (y ∈ P w ↔ y ∈ sd w e) := by
      intro y hyO
      constructor
      · intro hyP
        obtain ⟨-, hy1, hy2⟩ := (hPmem w y).mp hyP
        by_cases hyW : y ∈ W e
        · exact hy2 e he hc hwe hyW
        · rcases hy1 with hyC | ⟨f, hf, hfc, -, hyf⟩
          · exact hE1 e he hc w hwe ⟨hyC, hyW⟩
          · exact absurd (((hOy y hyO).1 f hf hfc hyf) ▸ hyf) hyW
      · exact hsdP e he hc w hwe y (fun f hf hfc hyf => (hOy y hyO).1 f hf hfc hyf)
    have key : ∀ s t : Set E3, (∀ y ∈ O, y ∈ s → y ∈ t) → x ∈ closure s → x ∈ closure t := by
      intro s t hst hx
      rw [mem_closure_iff_nhds] at hx ⊢
      intro U hU
      obtain ⟨y, ⟨hyU, hyO⟩, hys⟩ := hx (U ∩ O) (Filter.inter_mem hU hO)
      exact ⟨y, hyU, hst y hyO hys⟩
    exact ⟨key _ _ fun y hy h1 => (hOeq y hy).mp h1, key _ _ fun y hy h1 => (hOeq y hy).mpr h1⟩
  have hcommon : ∀ w ∈ K.vertices, ∀ z ∈ K.vertices, w ≠ z → ∀ x : E3,
      (x ∈ h '' C w ∨ ∃ f ∈ K.faces, f.card = 2 ∧ w ∈ f ∧ x ∈ W f) →
      (x ∈ h '' C z ∨ ∃ f ∈ K.faces, f.card = 2 ∧ z ∈ f ∧ x ∈ W f) →
      ∃ e ∈ K.faces, e.card = 2 ∧ w ∈ e ∧ z ∈ e ∧ x ∈ W e := by
    intro w hw z hz hwz x hxw hxz
    rcases hxw with hxw | ⟨f, hf, hfc, hwf, hxf⟩
    · rcases hxz with hxz | ⟨f, hf, hfc, hzf, hxf⟩
      · exact hW.exists_mem_of_mem_image_inter ht hw hz hwz hxw hxz
      · by_cases hwf : w ∈ f
        · exact ⟨f, hf, hfc, hwf, hzf, hxf⟩
        · exact absurd hxw (disjoint_left.mp (hW.disjoint_image_dualCell ht hf hfc hw hwf) hxf)
    · rcases hxz with hxz | ⟨f', hf', hfc', hzf', hxf'⟩
      · by_cases hzf : z ∈ f
        · exact ⟨f, hf, hfc, hwf, hzf, hxf⟩
        · exact absurd hxz (disjoint_left.mp (hW.disjoint_image_dualCell ht hf hfc hz hzf) hxf)
      · have hff := hW.eq_of_mem_of_mem hf hfc hf' hfc' hxf hxf'
        subst hff
        exact ⟨f, hf, hfc, hwf, hzf', hxf⟩
  have hcover : ∀ x ∈ X, ∃ w ∈ K.vertices, x ∈ P w := by
    intro x hxX
    have hxN := (hXmem x).mp hxX
    by_cases hxW : ∃ e ∈ K.faces, e.card = 2 ∧ x ∈ W e
    · obtain ⟨e, he, hc, hxe⟩ := hxW
      obtain ⟨ha, hb, hab, hae, hbe, -, -, -, -, -, hun, -⟩ := hU e he hc
      have hxS : x ∈ (h '' C (ea e) ∪ h '' C (eb e)) \ Ec e :=
        ⟨((hW e he hc).2.2.2.1 (ea e) hae (eb e) hbe hab).1 hxe, hxN.2 e he hc⟩
      rw [← hun] at hxS
      have hothers : ∀ f ∈ K.faces, f.card = 2 → x ∈ W f → f = e :=
        fun f hf hfc hxf => hW.eq_of_mem_of_mem hf hfc he hc hxf hxe
      rcases hxS with h1 | h1
      · refine ⟨ea e, ha, hsdP e he hc (ea e) hae x hothers ?_⟩
        rw [hsda]
        exact h1
      · refine ⟨eb e, hb, hsdP e he hc (eb e) hbe x hothers ?_⟩
        rw [hsdb e he hc]
        exact h1
    · obtain ⟨a, ha, hxa⟩ := hpiece x hxN.1
      exact ⟨a, ha, (hPmem a x).mpr ⟨hxX, Or.inl hxa,
        fun e he hc _ hxe => absurd ⟨e, he, hc, hxe⟩ hxW⟩⟩
  have hdisjP : ∀ w ∈ K.vertices, ∀ z ∈ K.vertices, w ≠ z → Disjoint (P w) (P z) := by
    intro w hw z hz hwz
    rw [disjoint_left]
    intro x hxw hxz
    obtain ⟨-, hxw1, hxw2⟩ := (hPmem w x).mp hxw
    obtain ⟨-, hxz1, hxz2⟩ := (hPmem z x).mp hxz
    obtain ⟨e, he, hc, hwe, hze, hxe⟩ := hcommon w hw z hz hwz x hxw1 hxz1
    obtain ⟨-, hpe, hpw, -, -, -, hd, -⟩ := hsd e he hc w hwe
    have hzp : z = pt w e :=
      (eq_or_eq_of_mem_of_card_eq_two hc hwe hpe hpw.symm hze).resolve_left (Ne.symm hwz)
    have hxs := hxz2 e he hc hze hxe
    rw [hzp] at hxs
    exact disjoint_left.mp hd (hxw2 e he hc hwe hxe) hxs
  have hopen : ∀ w ∈ K.vertices, ∀ x ∈ P w, ∃ O ∈ 𝓝 x, ∀ y ∈ O, y ∈ X → y ∈ P w := by
    intro w hw x hx
    obtain ⟨-, hx1, hx2⟩ := (hPmem w x).mp hx
    by_cases hxW : ∃ e ∈ K.faces, e.card = 2 ∧ w ∈ e ∧ x ∈ W e
    · obtain ⟨e, he, hc, hwe, hxe⟩ := hxW
      obtain ⟨-, hpe, hpw, -, -, hconn, hd, hun, hpre, -⟩ := hsd e he hc w hwe
      obtain ⟨-, -, -, -, -, hconn', -⟩ := hsd e he hc (pt w e) hpe
      have hxs : x ∈ sd w e := hx2 e he hc hwe hxe
      have hxS : x ∈ (h '' C w ∪ h '' C (pt w e)) \ Ec e := by
        rw [← hun]
        exact Or.inl hxs
      obtain ⟨O₁, hO₁, hO₁S⟩ :=
        exists_mem_nhds_forall_mem_iff_of_forall_subset_or_subset hconn hconn' hd hun hpre hxS
      obtain ⟨O₂, hO₂, hO₂y⟩ := hnbhd e he hc x hxe
      refine ⟨O₁ ∩ O₂, Filter.inter_mem hO₁ hO₂, fun y hy hyX => ?_⟩
      have hyN := (hXmem y).mp hyX
      obtain ⟨z, hz, hyz⟩ := hpiece y hyN.1
      have hze : z ∈ e := (hO₂y y hy.2).2 z hz hyz
      have hyS : y ∈ (h '' C w ∪ h '' C (pt w e)) \ Ec e := by
        refine ⟨?_, hyN.2 e he hc⟩
        rcases eq_or_eq_of_mem_of_card_eq_two hc hwe hpe hpw.symm hze with rfl | rfl
        · exact Or.inl hyz
        · exact Or.inr hyz
      exact hsdP e he hc w hwe y (hO₂y y hy.2).1 ((hO₁S y hy.1 hyS).mpr hxs)
    · have hxC : x ∈ h '' C w :=
        hx1.resolve_right fun ⟨e, he, hc, hwe, hxe⟩ => hxW ⟨e, he, hc, hwe, hxe⟩
      have hF1 : IsClosed (⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2}, W f) :=
        hEfin.isClosed_biUnion fun f hf => (hW f hf.1 hf.2).1
      have hF2 : IsClosed (⋃ z ∈ {z : E3 | z ∈ K.vertices ∧ z ≠ w}, h '' C z) :=
        (hVfin.subset fun z hz => hz.1).isClosed_biUnion fun z hz => hclosedP z hz.1
      refine ⟨((⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2}, W f) ∪
        ⋃ z ∈ {z : E3 | z ∈ K.vertices ∧ z ≠ w}, h '' C z)ᶜ,
        (hF1.union hF2).isOpen_compl.mem_nhds ?_, fun y hy hyX => ?_⟩
      · rintro (hx' | hx')
        · obtain ⟨f, ⟨hf, hfc⟩, hxf⟩ := mem_iUnion₂.mp hx'
          by_cases hwf : w ∈ f
          · exact hxW ⟨f, hf, hfc, hwf, hxf⟩
          · exact disjoint_left.mp (hW.disjoint_image_dualCell ht hf hfc hw hwf) hxf hxC
        · obtain ⟨z, ⟨hz, hzw⟩, hxz⟩ := mem_iUnion₂.mp hx'
          obtain ⟨f, hf, hfc, hwf, -, hxf⟩ :=
            hW.exists_mem_of_mem_image_inter ht hw hz (Ne.symm hzw) hxC hxz
          exact hxW ⟨f, hf, hfc, hwf, hxf⟩
      · have hyN := (hXmem y).mp hyX
        obtain ⟨z, hz, hyz⟩ := hpiece y hyN.1
        have hzw : z = w := by
          by_contra hzw
          exact hy (Or.inr (mem_iUnion₂.mpr ⟨z, ⟨hz, hzw⟩, hyz⟩))
        rw [hzw] at hyz
        refine hQP w hw ⟨hyz, fun hy' => ?_⟩
        obtain ⟨f, ⟨hf, hfc, -⟩, hyf⟩ := mem_iUnion₂.mp hy'
        exact hy (Or.inl (mem_iUnion₂.mpr ⟨f, ⟨hf, hfc⟩, hyf⟩))
  have hPconn : ∀ w ∈ K.vertices, IsPreconnected (P w) := by
    intro w hw
    have hQ := hW.isPreconnected_image_dualCell_sdiff ht hw
    have hwQ : h w ∈ h '' C w \ ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ w ∈ f}, W f :=
      ⟨⟨w, hmemC w hw, rfl⟩, fun hx => by
        obtain ⟨e, ⟨he, hc, -⟩, hxe⟩ := mem_iUnion₂.mp hx
        exact hvW e he hc w hw hxe⟩
    have hPeq : P w = ⋃ e : Finset E3,
        ((h '' C w \ ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ w ∈ f}, W f) ∪
          {y | e ∈ K.faces ∧ e.card = 2 ∧ w ∈ e ∧ y ∈ W e ∧ y ∈ sd w e}) := by
      apply Subset.antisymm
      · intro y hy
        obtain ⟨-, hy1, hy2⟩ := (hPmem w y).mp hy
        by_cases hyW : ∃ e ∈ K.faces, e.card = 2 ∧ w ∈ e ∧ y ∈ W e
        · obtain ⟨e, he, hc, hwe, hye⟩ := hyW
          exact mem_iUnion.mpr ⟨e, Or.inr ⟨he, hc, hwe, hye, hy2 e he hc hwe hye⟩⟩
        · refine mem_iUnion.mpr ⟨∅, Or.inl ⟨hy1.resolve_right hyW, fun hy' => hyW ?_⟩⟩
          obtain ⟨e, ⟨he, hc, hwe⟩, hye⟩ := mem_iUnion₂.mp hy'
          exact ⟨e, he, hc, hwe, hye⟩
      · refine iUnion_subset fun e => union_subset (hQP w hw) ?_
        rintro y ⟨he, hc, hwe, hye, hys⟩
        exact hWsdP e he hc w hwe ⟨hye, hys⟩
    rw [hPeq]
    refine isPreconnected_iUnion ⟨h w, mem_iInter.mpr fun e => Or.inl hwQ⟩ fun e => ?_
    by_cases he : e ∈ K.faces ∧ e.card = 2 ∧ w ∈ e
    · obtain ⟨he₁, he₂, hwe⟩ := he
      obtain ⟨-, -, -, -, -, hconn, -, hun, -, -⟩ := hsd e he₁ he₂ w hwe
      have hReq : {y | e ∈ K.faces ∧ e.card = 2 ∧ w ∈ e ∧ y ∈ W e ∧ y ∈ sd w e} =
          W e ∩ sd w e := by
        ext y
        exact ⟨fun hy => ⟨hy.2.2.2.1, hy.2.2.2.2⟩, fun hy => ⟨he₁, he₂, hwe, hy.1, hy.2⟩⟩
      rw [hReq]
      have hFcl : IsClosed
          (⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ w ∈ f ∧ f ≠ e}, W f) :=
        (ht.facesFinite.subset fun f hf => hf.1).isClosed_biUnion fun f hf => (hW f hf.1 hf.2.1).1
      refine isPreconnected_union_of_subset_union_of_disjoint_closed hconn.isPreconnected hQ
        ⟨h w, hwQ⟩ ?_ inter_subset_right ?_ inter_subset_left (hW e he₁ he₂).1 hFcl ?_
      · rintro y ⟨hyC, hyW⟩
        exact hE1 e he₁ he₂ w hwe
          ⟨hyC, fun hye => hyW (mem_iUnion₂.mpr ⟨e, ⟨he₁, he₂, hwe⟩, hye⟩)⟩
      · intro y hys
        by_cases hye : y ∈ W e
        · exact Or.inl (Or.inr ⟨hye, hys⟩)
        · have hyS : y ∈ (h '' C w ∪ h '' C (pt w e)) \ Ec e := by
            rw [← hun]
            exact Or.inl hys
          have hyC : y ∈ h '' C w :=
            hyS.1.resolve_right fun hyo => hye (hE2 e he₁ he₂ w hwe ⟨hys, hyo⟩)
          by_cases hyF : ∃ f ∈ K.faces, f.card = 2 ∧ w ∈ f ∧ f ≠ e ∧ y ∈ W f
          · obtain ⟨f, hf, hfc, hwf, hfe, hyf⟩ := hyF
            exact Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfc, hwf, hfe⟩, hyf⟩)
          · refine Or.inl (Or.inl ⟨hyC, fun hy => ?_⟩)
            obtain ⟨f, ⟨hf, hfc, hwf⟩, hyf⟩ := mem_iUnion₂.mp hy
            by_cases hfe : f = e
            · rw [hfe] at hyf
              exact hye hyf
            · exact hyF ⟨f, hf, hfc, hwf, hfe, hyf⟩
      · rw [disjoint_left]
        intro y hye hyF
        obtain ⟨f, ⟨hf, hfc, -, hfe⟩, hyf⟩ := mem_iUnion₂.mp hyF
        exact hfe (hW.eq_of_mem_of_mem hf hfc he₁ he₂ hyf hye)
    · have hRe : {y | e ∈ K.faces ∧ e.card = 2 ∧ w ∈ e ∧ y ∈ W e ∧ y ∈ sd w e} = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun y hy => he ⟨hy.1, hy.2.1, hy.2.2.1⟩
      rw [hRe, union_empty]
      exact hQ
  have hwX : ∀ w ∈ K.vertices, h w ∈ X := fun w hw => ((hPmem w (h w)).mp (hwP w hw)).1
  have hcomp : ∀ w ∈ K.vertices, connectedComponentIn X (h w) = P w := by
    intro w hw
    apply Subset.antisymm
    · intro y hy
      have hloc' : ∀ x ∈ X, ∃ O ∈ 𝓝 x, ∀ y ∈ O, y ∈ X → (y ∈ P w ↔ x ∈ P w) := by
        intro x hxX
        by_cases hxP : x ∈ P w
        · obtain ⟨O, hO, hOP⟩ := hopen w hw x hxP
          exact ⟨O, hO, fun y hy hyX => ⟨fun _ => hxP, fun _ => hOP y hy hyX⟩⟩
        · obtain ⟨z, hz, hxz⟩ := hcover x hxX
          have hzw : z ≠ w := fun h' => hxP (h' ▸ hxz)
          obtain ⟨O, hO, hOP⟩ := hopen z hz x hxz
          exact ⟨O, hO, fun y hy hyX => ⟨fun hyP => absurd (hOP y hy hyX)
            (disjoint_left.mp (hdisjP w hw z hz hzw.symm) hyP), fun h' => absurd h' hxP⟩⟩
      have hcont' : ContinuousOn (fun z => decide (z ∈ P w)) (connectedComponentIn X (h w)) := by
        intro z hz
        obtain ⟨O, hO, hOR⟩ := hloc' z (connectedComponentIn_subset X (h w) hz)
        rw [ContinuousWithinAt, nhds_discrete Bool, Filter.tendsto_pure]
        filter_upwards [mem_nhdsWithin_of_mem_nhds hO, self_mem_nhdsWithin] with y' hy'O hy'C
        exact decide_eq_decide.mpr (hOR y' hy'O (connectedComponentIn_subset X (h w) hy'C))
      have hconst := isPreconnected_connectedComponentIn.constant hcont'
        (mem_connectedComponentIn (hwX w hw)) hy
      exact (decide_eq_decide.mp hconst).mp (hwP w hw)
    · exact (hPconn w hw).subset_connectedComponentIn (hwP w hw)
        fun y hy => ((hPmem w y).mp hy).1
  have hhp : ∀ w ∈ K.vertices, handlePiece K N' Ec h w = closure (P w) := by
    intro w hw
    rw [← hcomp w hw, hX]
    rfl
  have hT : ∀ w ∈ K.vertices, ∀ x ∈ closure (P w),
      x ∈ h '' C w ∨ ∃ f ∈ K.faces, f.card = 2 ∧ w ∈ f ∧ x ∈ W f := by
    intro w hw x hx
    rw [← hhp w hw] at hx
    rcases handlePiece_subset_of_edgeCollars ht hW hE w hw hx with h1 | h1
    · exact Or.inl h1
    · obtain ⟨f, ⟨hf, hfc, hwf⟩, hxf⟩ := mem_iUnion₂.mp h1
      exact Or.inr ⟨f, hf, hfc, hwf, hxf⟩
  refine ⟨fun v hv => ?_, ?_, fun u hu v hv huv he => ?_, fun u hu v hv huv he => ?_⟩
  · rw [hhp v hv]
    apply Subset.antisymm
    · rintro y ⟨hyH, a, ha, rfl⟩
      by_cases hav : a = v
      · rw [hav]
        exact mem_singleton _
      · exfalso
        rcases hT v hv (h a) hyH with h1 | ⟨f, hf, hfc, -, hxf⟩
        · obtain ⟨z, hz, hza⟩ := h1
          have hza' : z = a := hinj (hCN v hv hz) (hCN a ha (hmemC a ha)) hza
          have hmem : a ∈ C v ∩ K.vertices := ⟨hza' ▸ hz, ha⟩
          rw [ht.dualVertex hv] at hmem
          exact hav hmem
        · exact hvW f hf hfc a ha hxf
    · rintro y rfl
      exact ⟨subset_closure (hwP v hv), v, hv, rfl⟩
  · apply Subset.antisymm
    · intro y hy
      by_cases hyX : y ∈ X
      · obtain ⟨w, hw, hyw⟩ := hcover y hyX
        refine mem_iUnion₂.mpr ⟨w, hw, ?_⟩
        rw [hhp w hw]
        exact subset_closure hyw
      · obtain ⟨f, hf, hfc, hyf⟩ : ∃ f ∈ K.faces, f.card = 2 ∧ y ∈ Ec f := by
          by_contra hno
          push Not at hno
          exact hyX ((hXmem y).mpr ⟨hy, hno⟩)
        obtain ⟨ha, -, -, hae, -⟩ := hU f hf hfc
        obtain ⟨-, -, -, -, -, -, -, -, -, hcl⟩ := hsd f hf hfc (ea f) hae
        refine mem_iUnion₂.mpr ⟨ea f, ha, ?_⟩
        rw [hhp _ ha]
        exact (hcleq f hf hfc (ea f) hae y (hEcW f hf hfc hyf)).mpr (hcl hyf)
    · refine iUnion₂_subset fun w hw => ?_
      rw [hhp w hw]
      exact closure_minimal (fun y hy => ((hXmem y).mp ((hPmem w y).mp hy).1).1) hN'cl
  · have hue : u ∈ ({u, v} : Finset E3) := Finset.mem_insert_self u {v}
    have hve : v ∈ ({u, v} : Finset E3) := Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
    have hc₀ : ({u, v} : Finset E3).card = 2 := ht.card_eq_two_of_mem he hue hve huv
    rw [hhp u hu, hhp v hv]
    obtain ⟨hpu, hpue, hpuw, -, -, hconnu, hdu, hunu, hpreu, hclu⟩ := hsd _ he hc₀ u hue
    obtain ⟨hpv, hpve, hpvw, -, -, hconnv, hdv, hunv, hprev, hclv⟩ := hsd _ he hc₀ v hve
    have hptu : pt u {u, v} = v :=
      ((eq_or_eq_of_mem_of_card_eq_two hc₀ hue hpue hpuw.symm hve).resolve_left
        (Ne.symm huv)).symm
    have hptv : pt v {u, v} = u :=
      ((eq_or_eq_of_mem_of_card_eq_two hc₀ hve hpve hpvw.symm hue).resolve_left huv).symm
    apply Subset.antisymm
    · rintro x ⟨hxu, hxv⟩
      obtain ⟨e, he', hc, hue', hve', hxe⟩ :=
        hcommon u hu v hv huv x (hT u hu x hxu) (hT v hv x hxv)
      have hee : ({u, v} : Finset E3) = e :=
        Finset.eq_of_subset_of_card_le
          (Finset.insert_subset hue' (Finset.singleton_subset_iff.mpr hve')) (hc.trans hc₀.symm).le
      rw [← hee] at hxe
      by_contra hxE
      have hxS : x ∈ (h '' C u ∪ h '' C v) \ Ec {u, v} :=
        ⟨((hW _ he hc₀).2.2.2.1 u hue v hve huv).1 hxe, hxE⟩
      have hxu' : x ∈ sd u {u, v} := by
        rw [hptu] at hdu hunu hpreu
        have hAS : sd u {u, v} ⊆ (h '' C u ∪ h '' C v) \ Ec {u, v} := by
          rw [← hunu]
          exact subset_union_left
        exact mem_of_mem_closure_of_forall_subset_or_subset hconnu hdu hAS hpreu
          ((hcleq _ he hc₀ u hue x hxe).mp hxu) hxS
      have hxv' : x ∈ sd v {u, v} := by
        rw [hptv] at hdv hunv hprev
        rw [union_comm] at hxS
        have hAS : sd v {u, v} ⊆ (h '' C v ∪ h '' C u) \ Ec {u, v} := by
          rw [← hunv]
          exact subset_union_left
        exact mem_of_mem_closure_of_forall_subset_or_subset hconnv hdv hAS hprev
          ((hcleq _ he hc₀ v hve x hxe).mp hxv) hxS
      rw [hptu] at hdu
      exact disjoint_left.mp hdu hxu' hxv'
    · intro x hx
      exact ⟨(hcleq _ he hc₀ u hue x (hEcW _ he hc₀ hx)).mpr (hclu hx),
        (hcleq _ he hc₀ v hve x (hEcW _ he hc₀ hx)).mpr (hclv hx)⟩
  · rw [hhp u hu, hhp v hv]
    refine eq_empty_iff_forall_notMem.mpr fun x ⟨hxu, hxv⟩ => ?_
    obtain ⟨e, he', hc, hue', hve', -⟩ := hcommon u hu v hv huv x (hT u hu x hxu) (hT v hv x hxv)
    apply he
    have hee : ({u, v} : Finset E3) = e :=
      Finset.eq_of_subset_of_card_le
        (Finset.insert_subset hue' (Finset.singleton_subset_iff.mpr hve'))
        (by
          rw [hc]
          exact Finset.one_lt_card.mpr ⟨u, Finset.mem_insert_self u {v}, v,
            Finset.mem_insert_of_mem (Finset.mem_singleton_self v), huv⟩)
    rw [hee]
    exact he'

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
