import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def avoidingUnion (K : Geometry.SimplicialComplex ℝ E) (p : E) : Set E :=
  ⋃ t ∈ {t ∈ K.faces | p ∉ t}, convexHull ℝ (t : Set E)

def openStar (K : Geometry.SimplicialComplex ℝ E) (p : E) : Set E :=
  K.space \ avoidingUnion K p

theorem isClosed_avoidingUnion (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (p : E) :
    IsClosed (avoidingUnion K p) :=
  ((Set.toFinite K.faces).subset (Set.sep_subset _ _)).isClosed_biUnion fun t _ =>
    (t.finite_toSet.isCompact_convexHull ℝ).isClosed

theorem openStar_subset_space (K : Geometry.SimplicialComplex ℝ E) (p : E) :
    openStar K p ⊆ K.space := sdiff_subset

theorem openStar_eq_inter (K : Geometry.SimplicialComplex ℝ E) (p : E) :
    openStar K p = K.space ∩ (avoidingUnion K p)ᶜ := rfl

theorem isOpen_preimage_openStar (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (p : E) :
    IsOpen ((Subtype.val : K.space → E) ⁻¹' openStar K p) := by
  have h : (Subtype.val : K.space → E) ⁻¹' openStar K p =
      (Subtype.val : K.space → E) ⁻¹' (avoidingUnion K p)ᶜ := by
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩
  rw [h]
  exact (isClosed_avoidingUnion K p).isOpen_compl.preimage continuous_subtype_val

theorem notMem_avoidingUnion_of_mem_openSimplex (K : Geometry.SimplicialComplex ℝ E) {p x : E}
    {u : Finset E} (hu : u ∈ K.faces) (hxu : x ∈ openSimplex u) (hpu : p ∈ u) :
    x ∉ avoidingUnion K p := by
  intro hx
  obtain ⟨t, ⟨ht, hpt⟩, hxt⟩ := mem_iUnion₂.mp hx
  exact hpt (face_subset_of_mem_openSimplex_of_mem_convexHull K hu ht hxu hxt hpu)

theorem exists_vertex_mem_openStar (K : Geometry.SimplicialComplex ℝ E) {x : E}
    (hx : x ∈ K.space) : ∃ p, {p} ∈ K.faces ∧ x ∈ openStar K p := by
  obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex K hx
  obtain ⟨p, hp⟩ := K.nonempty_of_mem_faces hu
  refine ⟨p, K.down_closed hu (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_nonempty p),
    hx, notMem_avoidingUnion_of_mem_openSimplex K hu hxu hp⟩

section Cone

open Classical in
theorem mem_openStar_iff (K : Geometry.SimplicialComplex ℝ E) {p : E} (hp : {p} ∈ K.faces)
    {x : E} :
    x ∈ openStar K p ↔ x = p ∨ ∃ z ∈ (SimplicialComplex.geometricLink K {p}).space,
      ∃ s : ℝ, 0 < s ∧ s < 1 ∧ x = p + s • (z - p) := by
  constructor
  · rintro ⟨hxK, hxA⟩
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex K hxK
    have hpu : p ∈ u := by
      by_contra hpu
      exact hxA (mem_iUnion₂.mpr ⟨u, ⟨hu, hpu⟩, openSimplex_subset_convexHull u hxu⟩)
    have hxins : x ∈ convexHull ℝ ((insert p (u.erase p) : Finset E) : Set E) := by
      rw [Finset.insert_erase hpu]
      exact openSimplex_subset_convexHull u hxu
    rcases exists_combo_of_mem_convexHull_insert (Finset.notMem_erase p u) hxins with
      hxp | ⟨z, hz, s, hs, hs', hxz⟩
    · exact Or.inl hxp
    have hne : (u.erase p).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.coe_empty, convexHull_empty] at hz
      exact hz
    have hlk : u.erase p ∈ (SimplicialComplex.geometricLink K {p}).faces :=
      (SimplicialComplex.mem_geometricLink_singleton K p _).mpr
        ⟨hne, Finset.notMem_erase p u, by rwa [Finset.insert_erase hpu]⟩
    refine Or.inr ⟨z, Geometry.SimplicialComplex.mem_space_iff.mpr ⟨_, hlk, hz⟩, s, hs, ?_, hxz⟩
    rcases lt_or_eq_of_le hs' with h | h
    · exact h
    · exfalso
      rw [h, one_smul, add_sub_cancel] at hxz
      refine hxA (mem_iUnion₂.mpr ⟨u.erase p, ⟨SimplicialComplex.geometricLink_le K {p} hlk,
        Finset.notMem_erase p u⟩, ?_⟩)
      rw [hxz]
      exact hz
  · rintro (hxp | ⟨z, hz, s, hs, hs', hxz⟩)
    · refine ⟨hxp ▸ K.convexHull_subset_space hp (subset_convexHull ℝ _ (by simp)), ?_⟩
      rw [hxp]
      intro h
      obtain ⟨t, ⟨ht, hpt⟩, hpt'⟩ := mem_iUnion₂.mp h
      exact hpt (mem_of_mem_convexHull_of_singleton_mem K hp ht hpt')
    · obtain ⟨σ, hσ, hzσ⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hz
      obtain ⟨-, hpσ, hins⟩ := (SimplicialComplex.mem_geometricLink_singleton K p σ).mp hσ
      have hxins : x ∈ convexHull ℝ ((insert p σ : Finset E) : Set E) := by
        rw [hxz]
        exact mem_convexHull_insert_of_combo hzσ hs.le hs'.le
      refine ⟨K.convexHull_subset_space hins hxins, ?_⟩
      obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex K (K.convexHull_subset_space hins hxins)
      have hu' : u ⊆ insert p σ :=
        face_subset_of_mem_openSimplex_of_mem_convexHull K hu hins hxu hxins
      have hpos : 0 < weights (insert p σ) x p := by
        have hw : ∀ v ∈ insert p σ, weights (insert p σ) x v =
            if v = p then 1 - s else s * weights σ z v := by
          refine weights_eq (K.indep hins) hxins ?_ ?_
          · rw [Finset.sum_insert hpσ, if_pos rfl,
              Finset.sum_congr rfl fun v hv => if_neg (ne_of_mem_of_not_mem hv hpσ),
              ← Finset.mul_sum, sum_weights hzσ]
            ring
          · rw [Finset.sum_insert hpσ, if_pos rfl,
              Finset.sum_congr rfl fun v hv => by rw [if_neg (ne_of_mem_of_not_mem hv hpσ)]]
            simp_rw [mul_smul]
            rw [← Finset.smul_sum, sum_weights_smul hzσ, hxz, add_smul_sub_eq_combo]
        rw [hw p (Finset.mem_insert_self p σ), if_pos rfl]
        linarith
      have hpu : p ∈ u :=
        ((mem_openSimplex_iff_weights_pos (K.indep hins) hu' hxins).mp hxu p
          (Finset.mem_insert_self p σ)).mp hpos
      exact notMem_avoidingUnion_of_mem_openSimplex K hu hxu hpu

open Classical in
theorem openStar_subset_closedStar (K : Geometry.SimplicialComplex ℝ E) {p : E}
    (hp : {p} ∈ K.faces) : openStar K p ⊆ closedStar K p := by
  intro x hx
  rw [closedStar_eq_coneComplex_space K hp, mem_coneComplex_space_iff]
  rcases (mem_openStar_iff K hp).mp hx with hxp | ⟨z, hz, s, hs, hs', hxz⟩
  · exact Or.inl hxp
  · exact Or.inr ⟨z, hz, s, hs, hs'.le, hxz⟩

theorem openSimplex_eq_openCone {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : 2 ≤ T.card) {p : E} (hp : p ∈ openSimplex T) :
    openSimplex T = {p} ∪ {x | ∃ z ∈ (simplexBoundary T hT).space,
      ∃ s : ℝ, 0 < s ∧ s < 1 ∧ x = p + s • (z - p)} := by
  classical
  have hpT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hp
  have hpos := (mem_openSimplex_self_iff hT hpT).mp hp
  ext x
  rw [simplexBoundary_space T hT hcard]
  constructor
  · intro hx
    have hxT : x ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hx
    obtain ⟨v, hv, hxv⟩ := exists_mem_convexHull_insert_erase hT hp hxT
    rcases exists_combo_of_mem_convexHull_insert (notMem_erase_of_mem_openSimplex hT hp hv) hxv
      with hxp | ⟨z, hz, s, hs, hs', hxz⟩
    · exact Or.inl hxp
    · refine Or.inr ⟨z, mem_iUnion₂.mpr ⟨v, hv, hz⟩, s, hs, ?_, hxz⟩
      rcases lt_or_eq_of_le hs' with h | h
      · exact h
      · exfalso
        rw [h, one_smul, add_sub_cancel] at hxz
        have h0 := weights_eq_zero_of_subset_of_notMem hT (Finset.erase_subset v T) hz hv
          (Finset.notMem_erase v T)
        have h1 := (mem_openSimplex_self_iff hT hxT).mp hx v hv
        rw [hxz, h0] at h1
        exact lt_irrefl _ h1
  · rintro (hxp | ⟨z, hz, s, hs, hs', hxz⟩)
    · rw [mem_singleton_iff.mp hxp]
      exact hp
    · obtain ⟨v, -, hzv⟩ := mem_iUnion₂.mp hz
      have hzT : z ∈ convexHull ℝ (T : Set E) :=
        convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset v T)) hzv
      have hxT : x ∈ convexHull ℝ (T : Set E) := by
        rw [hxz, add_smul_sub_eq_combo]
        exact (convex_convexHull ℝ _) hpT hzT (by linarith) hs.le (by ring)
      rw [mem_openSimplex_self_iff hT hxT]
      intro u hu
      rw [hxz, add_smul_sub_eq_combo, weights_combo hT hpT hzT (by linarith) hs.le (by ring) u hu]
      have h1 := hpos u hu
      have h2 := weights_nonneg hzT hu
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - s) h1, mul_nonneg hs.le h2]

end Cone

open Classical in
theorem exists_starHomeo [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] {p : E} (hp : {p} ∈ K.faces) {n : ℕ}
    (hsph : IsPLSphere n (SimplicialComplex.geometricLink K {p}).space) :
    ∃ g : (Fin (n + 2) → ℝ) → E, IsPLHomeomorphOn g (stdSimplex ℝ (Fin (n + 2))) (closedStar K p) ∧
      g '' openSimplex (stdVertices n) = openStar K p ∧ g (stdCenter n) = p := by
  obtain ⟨f, hf⟩ := hsph
  obtain ⟨f₀, hf₀⟩ := isPLSphere_simplexBoundary_std n
  have hfin : Finite (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hhomeo := hf₀.symm.trans hf
  obtain ⟨g, hg, -, hgc, hray⟩ :=
    exists_isPLHomeomorphOn_coneComplex (isConeBase_std n) (isConeBase_geometricLink K) hhomeo
  rw [coneComplex_std_space, ← closedStar_eq_coneComplex_space K hp] at hg
  refine ⟨g, hg, ?_, hgc⟩
  rw [openSimplex_eq_openCone (stdVertices_affineIndependent n) (two_le_card_stdVertices n)
    (stdCenter_mem_openSimplex n)]
  ext x
  rw [mem_openStar_iff K hp]
  constructor
  · rintro ⟨w, hw | ⟨z, hz, s, hs, hs', rfl⟩, rfl⟩
    · rw [mem_singleton_iff.mp hw, hgc]
      exact Or.inl rfl
    · rw [hray z hz s hs.le hs'.le]
      exact Or.inr ⟨_, hhomeo.bijOn.mapsTo hz, s, hs, hs', rfl⟩
  · rintro (rfl | ⟨z, hz, s, hs, hs', rfl⟩)
    · exact ⟨stdCenter n, Or.inl rfl, hgc⟩
    · obtain ⟨w, hw, rfl⟩ := hhomeo.bijOn.surjOn hz
      exact ⟨stdCenter n + s • (w - stdCenter n), Or.inr ⟨w, hw, s, hs, hs', rfl⟩,
        hray w hw s hs.le hs'.le⟩

end DifferentialGeometry.Topology.PiecewiseLinear
