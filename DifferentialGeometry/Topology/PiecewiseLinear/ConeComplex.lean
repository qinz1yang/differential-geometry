import DifferentialGeometry.Topology.PiecewiseLinear.Cone

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Combo

variable [DecidableEq E]

theorem exists_combo_of_mem_convexHull_insert {p : E} {σ : Finset E} (hpσ : p ∉ σ) {x : E}
    (hx : x ∈ convexHull ℝ ((insert p σ : Finset E) : Set E)) :
    x = p ∨ ∃ z ∈ convexHull ℝ (σ : Set E), ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ x = p + s • (z - p) := by
  obtain ⟨μ, hμ₀, hμ₁, hμx⟩ := mem_convexHull_iff_exists_weights.mp hx
  rw [Finset.sum_insert hpσ] at hμ₁ hμx
  have hτ₀ : 0 ≤ ∑ v ∈ σ, μ v :=
    Finset.sum_nonneg fun v hv => hμ₀ v (Finset.mem_insert_of_mem hv)
  by_cases h1 : μ p = 1
  · left
    have hzero : ∀ v ∈ σ, μ v = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg fun v hv =>
        hμ₀ v (Finset.mem_insert_of_mem hv)).mp ?_
      linarith
    rw [← hμx, h1, one_smul, Finset.sum_eq_zero fun v hv => by rw [hzero v hv, zero_smul],
      add_zero]
  right
  have hlt : μ p < 1 := lt_of_le_of_ne (by linarith) h1
  have hs : 0 < 1 - μ p := by linarith
  refine ⟨∑ v ∈ σ, ((1 - μ p)⁻¹ * μ v) • v, ?_, 1 - μ p, hs, by linarith [hμ₀ p (Finset.mem_insert_self p σ)], ?_⟩
  · refine (convex_convexHull ℝ _).sum_mem
      (fun v hv => mul_nonneg (inv_pos.mpr hs).le (hμ₀ v (Finset.mem_insert_of_mem hv))) ?_
      fun v hv => subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)
    rw [← Finset.mul_sum]
    have : ∑ v ∈ σ, μ v = 1 - μ p := by linarith
    rw [this, inv_mul_cancel₀ hs.ne']
  · rw [smul_sub, Finset.smul_sum]
    simp_rw [smul_smul, mul_inv_cancel_left₀ hs.ne']
    rw [← hμx]
    simp only [sub_smul, one_smul]
    abel

theorem mem_convexHull_insert_of_combo {p : E} {σ : Finset E} {z : E}
    (hz : z ∈ convexHull ℝ (σ : Set E)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    p + s • (z - p) ∈ convexHull ℝ ((insert p σ : Finset E) : Set E) := by
  rw [add_smul_sub_eq_combo]
  refine (convex_convexHull ℝ _) (subset_convexHull ℝ _ ?_)
    (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert p σ)) hz) (by linarith) hs0
    (by ring)
  exact Finset.mem_coe.mpr (Finset.mem_insert_self p σ)

end Combo

section ConeComplex

variable [DecidableEq E] (p : E) (L : Geometry.SimplicialComplex ℝ E)

def coneFaces : Set (Finset E) :=
  {t | t ∈ L.faces ∨ t = {p} ∨ ∃ σ ∈ L.faces, t = insert p σ}

theorem mem_coneFaces_iff {t : Finset E} :
    t ∈ coneFaces p L ↔ t ∈ L.faces ∨ t = {p} ∨ ∃ σ ∈ L.faces, t = insert p σ := Iff.rfl

theorem coneFaces_isRelLowerSet : IsRelLowerSet (coneFaces p L) Finset.Nonempty := by
  rintro t ht
  rcases ht with ht | rfl | ⟨σ, hσ, rfl⟩
  · exact ⟨L.nonempty_of_mem_faces ht, fun u hut hu => Or.inl (L.down_closed ht hut hu)⟩
  · refine ⟨Finset.singleton_nonempty p, fun u hut hu => Or.inr (Or.inl ?_)⟩
    rcases Finset.subset_singleton_iff.mp hut with h | h
    · exact absurd h hu.ne_empty
    · exact h
  · refine ⟨Finset.insert_nonempty p σ, fun u hut hu => ?_⟩
    by_cases hpu : p ∈ u
    · have hsub : u.erase p ⊆ σ := fun v hv => by
        rcases Finset.mem_insert.mp (hut (Finset.mem_of_mem_erase hv)) with h | h
        · exact absurd h (Finset.ne_of_mem_erase hv)
        · exact h
      by_cases hne : (u.erase p).Nonempty
      · exact Or.inr (Or.inr ⟨u.erase p, L.down_closed hσ hsub hne, (Finset.insert_erase hpu).symm⟩)
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        refine Or.inr (Or.inl ?_)
        rw [← Finset.insert_erase hpu, hne, Finset.insert_empty]
    · have hsub : u ⊆ σ := fun v hv => by
        rcases Finset.mem_insert.mp (hut hv) with h | h
        · exact absurd (h ▸ hv) hpu
        · exact h
      exact Or.inl (L.down_closed hσ hsub hu)

variable {p L}

theorem coneFaces_indep (h : IsConeBase p L) {t : Finset E} (ht : t ∈ coneFaces p L) :
    AffineIndependent ℝ ((↑) : t → E) := by
  rcases ht with ht | rfl | ⟨σ, hσ, rfl⟩
  · exact L.indep ht
  · have : Subsingleton {x // x ∈ ({p} : Finset E)} :=
      ⟨fun a b => Subtype.ext ((Finset.mem_singleton.mp a.2).trans
        (Finset.mem_singleton.mp b.2).symm)⟩
    exact affineIndependent_of_subsingleton ℝ _
  · have h' := h.indep σ hσ
    rwa [← Finset.coe_insert] at h'

omit [DecidableEq E] in
theorem IsConeBase.notMem_face (h : IsConeBase p L) {σ : Finset E} (hσ : σ ∈ L.faces) : p ∉ σ :=
  fun hp => h.notMem_space (L.convexHull_subset_space hσ (subset_convexHull ℝ _ (Finset.mem_coe.mpr hp)))

theorem coneFaces_inter_base_cone (h : IsConeBase p L) {σ₁ σ₂ : Finset E} (h₁ : σ₁ ∈ L.faces)
    (h₂ : σ₂ ∈ L.faces) :
    convexHull ℝ (σ₁ : Set E) ∩ convexHull ℝ ((insert p σ₂ : Finset E) : Set E) ⊆
      convexHull ℝ ((σ₁ : Set E) ∩ ((insert p σ₂ : Finset E) : Set E)) := by
  rintro x ⟨hx₁, hx₂⟩
  have hxL : x ∈ L.space := L.convexHull_subset_space h₁ hx₁
  rcases exists_combo_of_mem_convexHull_insert (h.notMem_face h₂) hx₂ with rfl | ⟨z, hz, s, hs, -, hxz⟩
  · exact absurd hxL h.notMem_space
  · have hzL : z ∈ L.space := L.convexHull_subset_space h₂ hz
    have hxz' : x = z := h.radial z hzL x hxL s hs hxz
    rw [hxz'] at hx₁ ⊢
    exact convexHull_mono (inter_subset_inter_right _ (Finset.coe_subset.mpr (Finset.subset_insert p σ₂)))
      (L.inter_subset_convexHull h₁ h₂ ⟨hx₁, hz⟩)

theorem coneFaces_inter_cone_cone (h : IsConeBase p L) {σ₁ σ₂ : Finset E} (h₁ : σ₁ ∈ L.faces)
    (h₂ : σ₂ ∈ L.faces) :
    convexHull ℝ ((insert p σ₁ : Finset E) : Set E) ∩
        convexHull ℝ ((insert p σ₂ : Finset E) : Set E) ⊆
      convexHull ℝ (((insert p σ₁ : Finset E) : Set E) ∩ ((insert p σ₂ : Finset E) : Set E)) := by
  rintro x ⟨hx₁, hx₂⟩
  have hp₁ : p ∈ ((insert p σ₁ : Finset E) : Set E) ∩ ((insert p σ₂ : Finset E) : Set E) :=
    ⟨Finset.mem_coe.mpr (Finset.mem_insert_self p σ₁), Finset.mem_coe.mpr (Finset.mem_insert_self p σ₂)⟩
  rcases exists_combo_of_mem_convexHull_insert (h.notMem_face h₁) hx₁ with rfl | ⟨z₁, hz₁, s₁, hs₁, hs₁', hxz₁⟩
  · exact subset_convexHull ℝ _ hp₁
  rcases exists_combo_of_mem_convexHull_insert (h.notMem_face h₂) hx₂ with hxp | ⟨z₂, hz₂, s₂, hs₂, -, hxz₂⟩
  · rw [hxp]
    exact subset_convexHull ℝ _ hp₁
  have hz₁L : z₁ ∈ L.space := L.convexHull_subset_space h₁ hz₁
  have hz₂L : z₂ ∈ L.space := L.convexHull_subset_space h₂ hz₂
  have hzz : z₂ = z₁ := by
    refine h.radial z₁ hz₁L z₂ hz₂L (s₁ / s₂) (div_pos hs₁ hs₂) ?_
    have hx : s₁ • (z₁ - p) = s₂ • (z₂ - p) := by
      have := hxz₁.symm.trans hxz₂
      rwa [add_right_inj] at this
    rw [div_eq_inv_mul, mul_smul, hx, smul_smul, inv_mul_cancel₀ hs₂.ne', one_smul, add_sub_cancel]
  rw [hzz] at hz₂
  have hzν : z₁ ∈ convexHull ℝ ((σ₁ : Set E) ∩ (σ₂ : Set E)) :=
    L.inter_subset_convexHull h₁ h₂ ⟨hz₁, hz₂⟩
  have hsub : (σ₁ : Set E) ∩ (σ₂ : Set E) ⊆
      ((insert p σ₁ : Finset E) : Set E) ∩ ((insert p σ₂ : Finset E) : Set E) :=
    inter_subset_inter (Finset.coe_subset.mpr (Finset.subset_insert p σ₁))
      (Finset.coe_subset.mpr (Finset.subset_insert p σ₂))
  rw [hxz₁, add_smul_sub_eq_combo]
  exact (convex_convexHull ℝ _) (subset_convexHull ℝ _ hp₁) (convexHull_mono hsub hzν)
    (by linarith) hs₁.le (by ring)

theorem coneFaces_inter (h : IsConeBase p L) {t₁ t₂ : Finset E} (h₁ : t₁ ∈ coneFaces p L)
    (h₂ : t₂ ∈ coneFaces p L) :
    convexHull ℝ (t₁ : Set E) ∩ convexHull ℝ (t₂ : Set E) ⊆
      convexHull ℝ ((t₁ : Set E) ∩ (t₂ : Set E)) := by
  have hsing : ∀ t ∈ coneFaces p L, convexHull ℝ (({p} : Finset E) : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((({p} : Finset E) : Set E) ∩ (t : Set E)) := by
    intro t ht
    rintro x ⟨hx₁, hx₂⟩
    rw [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at hx₁
    rw [hx₁] at hx₂ ⊢
    rcases ht with ht | rfl | ⟨σ, hσ, rfl⟩
    · exact absurd (L.convexHull_subset_space ht hx₂) h.notMem_space
    · exact subset_convexHull ℝ _ ⟨by simp, by simp⟩
    · exact subset_convexHull ℝ _ ⟨by simp, Finset.mem_coe.mpr (Finset.mem_insert_self p σ)⟩
  rcases h₁ with h₁ | rfl | ⟨σ₁, hσ₁, rfl⟩
  · rcases h₂ with h₂ | rfl | ⟨σ₂, hσ₂, rfl⟩
    · exact L.inter_subset_convexHull h₁ h₂
    · rw [Set.inter_comm, Set.inter_comm (t₁ : Set E)]
      exact hsing t₁ (Or.inl h₁)
    · exact coneFaces_inter_base_cone h h₁ hσ₂
  · exact hsing t₂ h₂
  · rcases h₂ with h₂ | rfl | ⟨σ₂, hσ₂, rfl⟩
    · rw [Set.inter_comm, Set.inter_comm ((insert p σ₁ : Finset E) : Set E)]
      exact coneFaces_inter_base_cone h h₂ hσ₁
    · rw [Set.inter_comm, Set.inter_comm ((insert p σ₁ : Finset E) : Set E)]
      exact hsing _ (Or.inr (Or.inr ⟨σ₁, hσ₁, rfl⟩))
    · exact coneFaces_inter_cone_cone h hσ₁ hσ₂

def coneComplex (h : IsConeBase p L) : Geometry.SimplicialComplex ℝ E where
  faces := coneFaces p L
  isRelLowerSet_faces := coneFaces_isRelLowerSet p L
  indep ht := coneFaces_indep h ht
  inter_subset_convexHull h₁ h₂ := coneFaces_inter h h₁ h₂

theorem mem_coneComplex_faces_iff (h : IsConeBase p L) {t : Finset E} :
    t ∈ (coneComplex h).faces ↔ t ∈ L.faces ∨ t = {p} ∨ ∃ σ ∈ L.faces, t = insert p σ := Iff.rfl

theorem coneComplex_faces_finite (h : IsConeBase p L) (hL : L.faces.Finite) :
    (coneComplex h).faces.Finite := by
  refine ((hL.union (Set.finite_singleton ({p} : Finset E))).union
    (hL.image fun σ => insert p σ)).subset ?_
  rintro t (ht | rfl | ⟨σ, hσ, rfl⟩)
  · exact Or.inl (Or.inl ht)
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr ⟨σ, hσ, rfl⟩

theorem mem_coneComplex_space_iff (h : IsConeBase p L) {x : E} :
    x ∈ (coneComplex h).space ↔
      x = p ∨ ∃ z ∈ L.space, ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ x = p + s • (z - p) := by
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    rcases ht with ht | rfl | ⟨σ, hσ, rfl⟩
    · exact Or.inr ⟨x, L.convexHull_subset_space ht hxt, 1, one_pos, le_rfl, by
        rw [one_smul, add_sub_cancel]⟩
    · rw [Finset.coe_singleton, convexHull_singleton] at hxt
      exact Or.inl hxt
    · rcases exists_combo_of_mem_convexHull_insert (h.notMem_face hσ) hxt with hxp | ⟨z, hz, s, hs, hs', hxz⟩
      · exact Or.inl hxp
      · exact Or.inr ⟨z, L.convexHull_subset_space hσ hz, s, hs, hs', hxz⟩
  · rintro (hxp | ⟨z, hz, s, hs, hs', rfl⟩)
    · rw [hxp]
      exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨{p}, Or.inr (Or.inl rfl), by simp⟩
    · obtain ⟨σ, hσ, hzσ⟩ := L.mem_space_iff.mp hz
      exact Geometry.SimplicialComplex.mem_space_iff.mpr
        ⟨insert p σ, Or.inr (Or.inr ⟨σ, hσ, rfl⟩), mem_convexHull_insert_of_combo hzσ hs.le hs'⟩

theorem space_subset_coneComplex_space (h : IsConeBase p L) : L.space ⊆ (coneComplex h).space :=
  fun x hx => (mem_coneComplex_space_iff h).mpr
    (Or.inr ⟨x, hx, 1, one_pos, le_rfl, by rw [one_smul, add_sub_cancel]⟩)

theorem apex_mem_coneComplex_space (h : IsConeBase p L) : p ∈ (coneComplex h).space :=
  (mem_coneComplex_space_iff h).mpr (Or.inl rfl)

theorem geometricLink_coneComplex_faces (h : IsConeBase p L) :
    (SimplicialComplex.geometricLink (coneComplex h) {p}).faces = L.faces := by
  ext t
  rw [SimplicialComplex.mem_geometricLink_singleton]
  constructor
  · rintro ⟨hne, hpt, hins⟩
    rcases hins with hins | hins | ⟨σ, hσ, hins⟩
    · exact absurd (L.convexHull_subset_space hins
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_self p t)))) h.notMem_space
    · exfalso
      obtain ⟨v, hv⟩ := hne
      have : v ∈ ({p} : Finset E) := hins ▸ Finset.mem_insert_of_mem hv
      exact hpt ((Finset.mem_singleton.mp this) ▸ hv)
    · have : t = σ := by
        rw [← Finset.erase_insert hpt, hins, Finset.erase_insert (h.notMem_face hσ)]
      rw [this]
      exact hσ
  · intro ht
    exact ⟨L.nonempty_of_mem_faces ht, h.notMem_face ht, Or.inr (Or.inr ⟨t, ht, rfl⟩)⟩

end ConeComplex

section Star

variable [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) {p : E}

theorem coneFaces_geometricLink_subset (hp : {p} ∈ K.faces) :
    coneFaces p (SimplicialComplex.geometricLink K {p}) ⊆ K.faces := by
  rintro t (ht | rfl | ⟨σ, hσ, rfl⟩)
  · exact SimplicialComplex.geometricLink_le K {p} ht
  · exact hp
  · exact ((SimplicialComplex.mem_geometricLink_singleton K p σ).mp hσ).2.2

theorem closedStar_eq_coneComplex_space (hp : {p} ∈ K.faces) :
    closedStar K p = (coneComplex (isConeBase_geometricLink K (p := p))).space := by
  ext x
  rw [mem_coneComplex_space_iff]
  constructor
  · intro hx
    obtain ⟨t, ⟨ht, hpt⟩, hxt⟩ := mem_iUnion₂.mp hx
    have hpt' : p ∈ t := mem_of_mem_convexHull_of_singleton_mem K hp ht hpt
    rw [← Finset.insert_erase hpt'] at hxt
    rcases exists_combo_of_mem_convexHull_insert (Finset.notMem_erase p t) hxt with hxp | ⟨z, hz, s, hs, hs', hxz⟩
    · exact Or.inl hxp
    · refine Or.inr ⟨z, ?_, s, hs, hs', hxz⟩
      refine Geometry.SimplicialComplex.mem_space_iff.mpr ⟨t.erase p, ?_, hz⟩
      refine (SimplicialComplex.mem_geometricLink_singleton K p _).mpr
        ⟨?_, Finset.notMem_erase p t, by rwa [Finset.insert_erase hpt']⟩
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.coe_empty, convexHull_empty] at hz
      exact hz
  · rintro (hxp | ⟨z, hz, s, hs, hs', rfl⟩)
    · rw [hxp]
      exact mem_biUnion (s := {s ∈ K.faces | p ∈ convexHull ℝ (s : Set E)})
        (t := fun s => convexHull ℝ (s : Set E)) ⟨hp, by simp⟩ (by simp)
    · obtain ⟨σ, hσ, hzσ⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hz
      obtain ⟨-, -, hins⟩ := (SimplicialComplex.mem_geometricLink_singleton K p σ).mp hσ
      exact mem_biUnion (s := {s ∈ K.faces | p ∈ convexHull ℝ (s : Set E)})
        (t := fun s => convexHull ℝ (s : Set E))
        ⟨hins, subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_self p σ))⟩
        (mem_convexHull_insert_of_combo hzσ hs.le hs')

end Star

end DifferentialGeometry.Topology.PiecewiseLinear
