/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeComplement
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexBallStar
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexComplex
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isConnected_closedStar_sdiff_convexHull (K : Geometry.SimplicialComplex ℝ E) {v : E}
    {t : Finset E} (ht : t ∈ K.faces) (hvt : v ∈ t) (hcard : t.card = 4)
    (hlk : IsPLSphere 2 (SimplicialComplex.geometricLink K {v}).space) :
    IsConnected (closedStar K v \ convexHull ℝ (t : Set E)) := by
  classical
  have hv : ({v} : Finset E) ∈ K.faces :=
    K.down_closed ht (Finset.singleton_subset_iff.mpr hvt) (Finset.singleton_nonempty v)
  have hf : AffineIndependent ℝ ((↑) : ↥(t.erase v) → E) :=
    affineIndependent_of_subset (K.indep ht) (Finset.erase_subset v t)
  have hfcard : (t.erase v).card = 2 + 1 := by rw [Finset.card_erase_of_mem hvt, hcard]
  have hfne : (t.erase v).Nonempty := Finset.card_pos.mp (by omega)
  have hLK : (simplexComplex (t.erase v) hf).faces ⊆
      (SimplicialComplex.geometricLink K {v}).faces := by
    rintro ρ ⟨hρne, hρf⟩
    exact (SimplicialComplex.mem_geometricLink_singleton K v ρ).mpr
      ⟨hρne, fun h => Finset.notMem_erase v t (hρf h),
        K.down_closed ht (Finset.insert_subset hvt (hρf.trans (Finset.erase_subset v t)))
          (Finset.insert_nonempty v ρ)⟩
  have hp := isConeBase_geometricLink K (p := v)
  have hcone : (coneComplex (hp.of_faces_subset hLK)).space = convexHull ℝ (t : Set E) := by
    ext x
    rw [mem_coneComplex_space_iff, simplexComplex_space _ hf hfne]
    constructor
    · rintro (hx | ⟨z, hz, s, hs, hs1, hx⟩)
      · rw [hx]
        exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hvt)
      · have h := mem_convexHull_insert_of_combo (p := v) hz hs.le hs1
        rw [Finset.insert_erase hvt] at h
        rw [hx]
        exact h
    · intro hx
      rw [← Finset.insert_erase hvt] at hx
      exact exists_combo_of_mem_convexHull_insert (Finset.notMem_erase v t) hx
  rw [closedStar_eq_coneComplex_space K hv, ← hcone]
  apply hp.isConnected_sdiff_coneComplex hLK
  rw [simplexComplex_space _ hf hfne]
  exact hlk.isConnected_sdiff_of_isPLBall_two
    (isPLBall_convexHull_of_affineIndependent _ hf hfcard)
    ((SimplicialComplex.geometricLink K {v}).convexHull_subset_space (hLK ⟨hfne, subset_rfl⟩))

section LocallyFinite

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  {U : Set X}

open Classical in
theorem LocallyFinitePLPieceIn.exists_insert_mem_faces_ne (𝒦 : LocallyFinitePLPieceIn E 3 X U)
    (hK : IsCombinatorialManifold 3 𝒦.complex) {s : Finset E} (hs : s ∈ 𝒦.complex.faces)
    (hs3 : s.card = 3) {d : E} (hds : d ∉ s) (hins : insert d s ∈ 𝒦.complex.faces) :
    ∃ z, z ∉ s ∧ z ≠ d ∧ insert z s ∈ 𝒦.complex.faces := by
  classical
  have hsph := 𝒦.isPLSphere_geometricLink (n := 2) hK hs (k := 2) (by omega) le_rfl
  rw [Nat.sub_self] at hsph
  have : Finite (SimplicialComplex.geometricLink 𝒦.complex s).faces :=
    (𝒦.geometricLink_faces_finite hs).to_subtype
  have hmem : ∀ z, ({z} : Finset E) ∈ (SimplicialComplex.geometricLink 𝒦.complex s).faces ↔
      z ∉ s ∧ insert z s ∈ 𝒦.complex.faces := by
    intro z
    change ({z} : Finset E).Nonempty ∧ Disjoint s {z} ∧ s ∪ {z} ∈ 𝒦.complex.faces ↔ _
    rw [Finset.disjoint_singleton_right, Finset.union_comm, ← Finset.insert_eq]
    exact ⟨fun h => h.2, fun h => ⟨Finset.singleton_nonempty z, h⟩⟩
  have hd : d ∈ (SimplicialComplex.geometricLink 𝒦.complex s).space :=
    (SimplicialComplex.geometricLink 𝒦.complex s).convexHull_subset_space ((hmem d).mpr ⟨hds, hins⟩)
      (by simp)
  obtain ⟨x, y, hxy, hxyS⟩ := isPLSphere_zero_iff.mp hsph
  obtain ⟨z, hzS, hzd⟩ : ∃ z ∈ (SimplicialComplex.geometricLink 𝒦.complex s).space, z ≠ d := by
    rw [hxyS] at hd ⊢
    rcases hd with hdx | hdy
    · exact ⟨y, Or.inr rfl, fun h => hxy (hdx.symm.trans h.symm)⟩
    · exact ⟨x, Or.inl rfl, fun h => hxy (h.trans (mem_singleton_iff.mp hdy))⟩
  obtain ⟨ρ, hρ, hzρ⟩ := (SimplicialComplex.geometricLink 𝒦.complex s).mem_space_iff.mp hzS
  have hρcard : ρ.card ≤ 0 + 1 := card_le_of_isPLSphere (m := 0) _ hsph hρ
  have hρpos := Finset.card_pos.mpr
    ((SimplicialComplex.geometricLink 𝒦.complex s).nonempty_of_mem_faces hρ)
  obtain ⟨z', rfl⟩ := Finset.card_eq_one.mp (show ρ.card = 1 by omega)
  rw [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at hzρ
  subst hzρ
  exact ⟨z, ((hmem z).mp hρ).1, hzd, ((hmem z).mp hρ).2⟩

theorem LocallyFinitePLPieceIn.isPreconnected_iUnion_closedStar_sdiff_convexHull
    (𝒦 : LocallyFinitePLPieceIn E 3 X U) (hK : IsCombinatorialManifold 3 𝒦.complex)
    {t : Finset E} (ht : t ∈ 𝒦.complex.faces) (hcard : t.card = 4) :
    IsPreconnected (⋃ v ∈ t, closedStar 𝒦.complex v \ convexHull ℝ (t : Set E)) := by
  classical
  have hW : ∀ v ∈ t, IsConnected (closedStar 𝒦.complex v \ convexHull ℝ (t : Set E)) :=
    fun v hv => isConnected_closedStar_sdiff_convexHull _ ht hv hcard
      (hK v (𝒦.complex.down_closed ht (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)))
  have hmeet : ∀ a ∈ t, ∀ b ∈ t, ((closedStar 𝒦.complex a \ convexHull ℝ (t : Set E)) ∩
      (closedStar 𝒦.complex b \ convexHull ℝ (t : Set E))).Nonempty := by
    intro a ha b hb
    obtain ⟨d, hdt, hda, hdb⟩ : ∃ d ∈ t, d ≠ a ∧ d ≠ b := by
      by_contra hcon
      have hsub : t ⊆ {a, b} := by
        intro d hd
        by_cases hda : d = a
        · rw [hda]
          exact Finset.mem_insert_self a {b}
        · by_cases hdb : d = b
          · rw [hdb]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
          · exact absurd ⟨d, hd, hda, hdb⟩ hcon
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_insert_le a ({b} : Finset E)
      rw [Finset.card_singleton] at h2
      omega
    have hs : t.erase d ∈ 𝒦.complex.faces :=
      𝒦.complex.down_closed ht (Finset.erase_subset d t)
        (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hdt]; omega))
    have hs3 : (t.erase d).card = 3 := by rw [Finset.card_erase_of_mem hdt, hcard]
    have hins : insert d (t.erase d) ∈ 𝒦.complex.faces := by
      rw [Finset.insert_erase hdt]
      exact ht
    obtain ⟨z, hzs, hzd, hzins⟩ :=
      𝒦.exists_insert_mem_faces_ne hK hs hs3 (Finset.notMem_erase d t) hins
    have hzt : z ∉ convexHull ℝ (t : Set E) := by
      intro hz
      have hzv : ({z} : Finset E) ∈ 𝒦.complex.faces :=
        𝒦.complex.down_closed hzins (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self z _))
          (Finset.singleton_nonempty z)
      have hzt' := mem_of_mem_convexHull_of_singleton_mem _ hzv ht hz
      exact hzs (Finset.mem_erase.mpr ⟨hzd, hzt'⟩)
    have hzhull : z ∈ convexHull ℝ ((insert z (t.erase d) : Finset E) : Set E) :=
      subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_self z _))
    have hmemStar : ∀ c ∈ t, c ≠ d → z ∈ closedStar 𝒦.complex c := by
      intro c hc hcd
      have hc' : c ∈ insert z (t.erase d) :=
        Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hcd, hc⟩)
      exact mem_iUnion₂.mpr ⟨insert z (t.erase d),
        ⟨hzins, subset_convexHull ℝ _ (Finset.mem_coe.mpr hc')⟩, hzhull⟩
    exact ⟨z, ⟨hmemStar a ha hda.symm, hzt⟩, hmemStar b hb hdb.symm, hzt⟩
  obtain ⟨a₀, ha₀⟩ : t.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x₀, hx₀⟩ := (hW a₀ ha₀).nonempty
  have heq : (⋃ v ∈ t, closedStar 𝒦.complex v \ convexHull ℝ (t : Set E)) =
      ⋃₀ ((fun v => (closedStar 𝒦.complex v \ convexHull ℝ (t : Set E)) ∪
        (closedStar 𝒦.complex a₀ \ convexHull ℝ (t : Set E))) '' (t : Set E)) := by
    rw [sUnion_image]
    apply Subset.antisymm
    · exact iUnion₂_mono fun v _ => subset_union_left
    · refine iUnion₂_subset fun v hv => union_subset ?_ ?_
      · exact subset_biUnion_of_mem (u := fun v => closedStar 𝒦.complex v \
          convexHull ℝ (t : Set E)) hv
      · exact subset_biUnion_of_mem (u := fun v => closedStar 𝒦.complex v \
          convexHull ℝ (t : Set E)) (Finset.mem_coe.mpr ha₀)
  rw [heq]
  refine isPreconnected_sUnion x₀ _ ?_ ?_
  · rintro _ ⟨v, -, rfl⟩
    exact Or.inr hx₀
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨y, hyv, hya⟩ := hmeet v hv a₀ ha₀
    exact IsPreconnected.union y hyv hya (hW v hv).isPreconnected (hW a₀ ha₀).isPreconnected

theorem LocallyFinitePLPieceIn.exists_isClopen_of_isClopen_sdiff_convexHull
    (𝒦 : LocallyFinitePLPieceIn E 3 X U) (hK : IsCombinatorialManifold 3 𝒦.complex)
    {t : Finset E} (ht : t ∈ 𝒦.complex.faces) (hcard : t.card = 4) {R : Set E}
    (hR : Disjoint R (convexHull ℝ (t : Set E)))
    (hRo : IsOpen ((Subtype.val : 𝒦.complex.space → E) ⁻¹' R))
    (hRc : IsOpen ((Subtype.val : 𝒦.complex.space → E) ⁻¹' (R ∪ convexHull ℝ (t : Set E))ᶜ)) :
    ∃ C : Set E, R ⊆ C ∧ C ⊆ R ∪ convexHull ℝ (t : Set E) ∧
      IsClopen ((Subtype.val : 𝒦.complex.space → E) ⁻¹' C) := by
  classical
  obtain ⟨W, hWdef⟩ : ∃ W : Set E,
      W = ⋃ v ∈ t, closedStar 𝒦.complex v \ convexHull ℝ (t : Set E) := ⟨_, rfl⟩
  have hWc : IsPreconnected W := by
    rw [hWdef]
    exact 𝒦.isPreconnected_iUnion_closedStar_sdiff_convexHull hK ht hcard
  have hWK : W ⊆ 𝒦.complex.space := by
    rw [hWdef]
    refine iUnion₂_subset fun v _ => sdiff_subset.trans ?_
    exact iUnion₂_subset fun τ hτ => 𝒦.complex.convexHull_subset_space hτ.1
  have hWt : Disjoint W (convexHull ℝ (t : Set E)) := by
    rw [hWdef, Set.disjoint_left]
    intro z hz hzt
    obtain ⟨v, -, -, hzt'⟩ := mem_iUnion₂.mp hz
    exact hzt' hzt
  have hW' : IsPreconnected ((Subtype.val : 𝒦.complex.space → E) ⁻¹' W) := by
    rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.mpr hWK]
    exact hWc
  have hcover : (Subtype.val ⁻¹' W : Set 𝒦.complex.space) ⊆
      Subtype.val ⁻¹' R ∪ Subtype.val ⁻¹' (R ∪ convexHull ℝ (t : Set E))ᶜ := by
    intro z hz
    by_cases hzR : (z : E) ∈ R
    · exact Or.inl hzR
    · refine Or.inr ?_
      rintro (h | h)
      · exact hzR h
      · exact disjoint_left.mp hWt hz h
  have hdisj : Disjoint (Subtype.val ⁻¹' R : Set 𝒦.complex.space)
      (Subtype.val ⁻¹' (R ∪ convexHull ℝ (t : Set E))ᶜ) :=
    disjoint_left.mpr fun z h1 h2 => h2 (Or.inl h1)
  have hstarOpen : ∀ v, IsOpen ((Subtype.val : 𝒦.complex.space → E) ⁻¹' openStar 𝒦.complex v) := by
    intro v
    have h := (𝒦.isClosed_preimage_avoidingUnion v).isOpen_compl
    have heq : (Subtype.val : 𝒦.complex.space → E) ⁻¹' openStar 𝒦.complex v =
        (Subtype.val ⁻¹' avoidingUnion 𝒦.complex v)ᶜ := by
      ext z
      exact ⟨fun hz => hz.2, fun hz => ⟨z.2, hz⟩⟩
    rw [heq]
    exact h
  have hstarHull : ∀ z : 𝒦.complex.space, (z : E) ∈ convexHull ℝ (t : Set E) →
      ∃ v ∈ t, (z : E) ∈ openStar 𝒦.complex v := by
    intro z hzt
    obtain ⟨ρ, hρ, hzρ⟩ := exists_face_mem_openSimplex 𝒦.complex z.2
    have hρt := face_subset_of_mem_openSimplex_of_mem_convexHull _ hρ ht hzρ hzt
    obtain ⟨v, hv⟩ := 𝒦.complex.nonempty_of_mem_faces hρ
    exact ⟨v, hρt hv, z.2, notMem_avoidingUnion_of_mem_openSimplex _ hρ hzρ hv⟩
  have hstarSub : ∀ v ∈ t, openStar 𝒦.complex v ⊆ W ∪ convexHull ℝ (t : Set E) := by
    intro v hv z hz
    by_cases hzt : z ∈ convexHull ℝ (t : Set E)
    · exact Or.inr hzt
    · have hv1 : ({v} : Finset E) ∈ 𝒦.complex.faces :=
        𝒦.complex.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      refine Or.inl ?_
      rw [hWdef]
      exact mem_iUnion₂.mpr ⟨v, hv, openStar_subset_closedStar _ hv1 hz, hzt⟩
  rcases hW'.subset_or_subset hRo hRc hdisj hcover with hWR | hWRc
  · refine ⟨R ∪ convexHull ℝ (t : Set E), subset_union_left, subset_rfl, ?_, ?_⟩
    · rw [← isOpen_compl_iff]
      exact hRc
    · rw [isOpen_iff_forall_mem_open]
      intro z hz
      rcases hz with hzR | hzt
      · exact ⟨Subtype.val ⁻¹' R, fun y hy => Or.inl hy, hRo, hzR⟩
      · obtain ⟨v, hv, hzv⟩ := hstarHull z hzt
        refine ⟨Subtype.val ⁻¹' openStar 𝒦.complex v, fun y hy => ?_, hstarOpen v, hzv⟩
        rcases hstarSub v hv hy with hyW | hyt
        · exact Or.inl (hWR hyW)
        · exact Or.inr hyt
  · refine ⟨R, subset_rfl, subset_union_left, ?_, hRo⟩
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    by_cases hzt : (z : E) ∈ convexHull ℝ (t : Set E)
    · obtain ⟨v, hv, hzv⟩ := hstarHull z hzt
      refine ⟨Subtype.val ⁻¹' openStar 𝒦.complex v, fun y hy hyR => ?_, hstarOpen v, hzv⟩
      rcases hstarSub v hv hy with hyW | hyt
      · exact hWRc hyW (Or.inl hyR)
      · exact disjoint_left.mp hR hyR hyt
    · refine ⟨Subtype.val ⁻¹' (R ∪ convexHull ℝ (t : Set E))ᶜ, fun y hy hyR => hy (Or.inl hyR),
        hRc, ?_⟩
      rintro (h | h)
      · exact hz h
      · exact hzt h

omit [FiniteDimensional ℝ E] in
theorem LocallyFinitePLPieceIn.isOpen_preimage_of_carrier_class
    (𝒦 : LocallyFinitePLPieceIn E 3 X U) {t : Finset E} (ht : t ∈ 𝒦.complex.faces)
    {G R : Set E}
    (hG : ∀ τ ∈ 𝒦.complex.faces, ∀ u ∈ τ, ∀ u' ∈ τ, u ∉ t → u' ∉ t → u ∈ G → u' ∈ G)
    (hR : ∀ z, z ∈ R ↔ z ∈ 𝒦.complex.space ∧
      ∃ τ ∈ 𝒦.complex.faces, z ∈ openSimplex τ ∧ ∃ u ∈ τ, u ∉ t ∧ u ∈ G) :
    Disjoint R (convexHull ℝ (t : Set E)) ∧
      IsOpen ((Subtype.val : 𝒦.complex.space → E) ⁻¹' R) ∧
      IsOpen ((Subtype.val : 𝒦.complex.space → E) ⁻¹' (R ∪ convexHull ℝ (t : Set E))ᶜ) := by
  have hstarOpen : ∀ v, IsOpen ((Subtype.val : 𝒦.complex.space → E) ⁻¹' openStar 𝒦.complex v) := by
    intro v
    have heq : (Subtype.val : 𝒦.complex.space → E) ⁻¹' openStar 𝒦.complex v =
        (Subtype.val ⁻¹' avoidingUnion 𝒦.complex v)ᶜ := by
      ext z
      exact ⟨fun hz => hz.2, fun hz => ⟨z.2, hz⟩⟩
    rw [heq]
    exact (𝒦.isClosed_preimage_avoidingUnion v).isOpen_compl
  have hnbhd : ∀ τ : Finset E,
      IsOpen (⋂ v ∈ τ, (Subtype.val : 𝒦.complex.space → E) ⁻¹' openStar 𝒦.complex v) :=
    fun τ => isOpen_biInter_finset fun v _ => hstarOpen v
  have hmem : ∀ (z : 𝒦.complex.space) (τ : Finset E), τ ∈ 𝒦.complex.faces →
      (z : E) ∈ openSimplex τ →
      z ∈ ⋂ v ∈ τ, (Subtype.val : 𝒦.complex.space → E) ⁻¹' openStar 𝒦.complex v :=
    fun z τ hτ hz => mem_iInter₂.mpr fun v hv =>
      ⟨z.2, notMem_avoidingUnion_of_mem_openSimplex _ hτ hz hv⟩
  have hsup : ∀ (z : 𝒦.complex.space) (τ τ' : Finset E), τ' ∈ 𝒦.complex.faces →
      z ∈ (⋂ v ∈ τ, (Subtype.val : 𝒦.complex.space → E) ⁻¹' openStar 𝒦.complex v) →
      (z : E) ∈ openSimplex τ' → τ ⊆ τ' := by
    intro z τ τ' hτ' hz hzτ' v hv
    by_contra hvτ'
    exact (mem_iInter₂.mp hz v hv).2
      (mem_iUnion₂.mpr ⟨τ', ⟨hτ', hvτ'⟩, openSimplex_subset_convexHull τ' hzτ'⟩)
  have hdisj : Disjoint R (convexHull ℝ (t : Set E)) := by
    rw [Set.disjoint_left]
    intro z hz hzt
    obtain ⟨-, τ, hτ, hzτ, u, huτ, hut, -⟩ := (hR z).mp hz
    exact hut (face_subset_of_mem_openSimplex_of_mem_convexHull _ hτ ht hzτ hzt huτ)
  refine ⟨hdisj, ?_, ?_⟩
  · rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨-, τ, hτ, hzτ, u, huτ, hut, huG⟩ := (hR z).mp hz
    refine ⟨⋂ v ∈ τ, (Subtype.val : 𝒦.complex.space → E) ⁻¹' openStar 𝒦.complex v,
      fun z' hz' => ?_, hnbhd τ, hmem z τ hτ hzτ⟩
    obtain ⟨τ', hτ', hz'τ'⟩ := exists_face_mem_openSimplex 𝒦.complex z'.2
    exact (hR z').mpr ⟨z'.2, τ', hτ', hz'τ', u, hsup z' τ τ' hτ' hz' hz'τ' huτ, hut, huG⟩
  · rw [isOpen_iff_forall_mem_open]
    intro z hz
    have hzR : (z : E) ∉ R := fun h => hz (Or.inl h)
    have hzt : (z : E) ∉ convexHull ℝ (t : Set E) := fun h => hz (Or.inr h)
    obtain ⟨τ, hτ, hzτ⟩ := exists_face_mem_openSimplex 𝒦.complex z.2
    obtain ⟨u, huτ, hut⟩ : ∃ u ∈ τ, u ∉ t := by
      by_contra hcon
      apply hzt
      refine convexHull_mono (Finset.coe_subset.mpr fun u hu => ?_)
        (openSimplex_subset_convexHull τ hzτ)
      by_contra h
      exact hcon ⟨u, hu, h⟩
    have huG : u ∉ G := fun h => hzR ((hR z).mpr ⟨z.2, τ, hτ, hzτ, u, huτ, hut, h⟩)
    refine ⟨⋂ v ∈ τ, (Subtype.val : 𝒦.complex.space → E) ⁻¹' openStar 𝒦.complex v,
      fun z' hz' => ?_, hnbhd τ, hmem z τ hτ hzτ⟩
    obtain ⟨τ', hτ', hz'τ'⟩ := exists_face_mem_openSimplex 𝒦.complex z'.2
    have hττ' := hsup z' τ τ' hτ' hz' hz'τ'
    rintro (h | h)
    · obtain ⟨-, τ'', hτ'', hz'τ'', u'', hu''τ'', hu''t, hu''G⟩ := (hR z').mp h
      have h1 := face_subset_of_mem_openSimplex_of_mem_convexHull _ hτ'' hτ' hz'τ''
        (openSimplex_subset_convexHull τ' hz'τ')
      exact huG (hG τ' hτ' u'' (h1 hu''τ'') u (hττ' huτ) hu''t hut hu''G)
    · exact hut (face_subset_of_mem_openSimplex_of_mem_convexHull _ hτ' ht hz'τ' h (hττ' huτ))

end LocallyFinite

end DifferentialGeometry.Topology.PiecewiseLinear
