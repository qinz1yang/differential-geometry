import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAvoiding
import DifferentialGeometry.Topology.PiecewiseLinear.StarComplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section UnionComplex

variable (K₁ K₂ : Geometry.SimplicialComplex ℝ E)
  (h : ∀ s ∈ K₁.faces, ∀ t ∈ K₂.faces,
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆ convexHull ℝ ((s : Set E) ∩ (t : Set E)))

def unionComplex : Geometry.SimplicialComplex ℝ E where
  faces := K₁.faces ∪ K₂.faces
  isRelLowerSet_faces := K₁.isRelLowerSet_faces.union K₂.isRelLowerSet_faces
  indep := by
    rintro s (hs | hs)
    · exact K₁.indep hs
    · exact K₂.indep hs
  inter_subset_convexHull := by
    rintro s t (hs | hs) (ht | ht)
    · exact K₁.inter_subset_convexHull hs ht
    · exact h s hs t ht
    · rw [Set.inter_comm (convexHull ℝ (s : Set E)), Set.inter_comm (s : Set E)]
      exact h t ht s hs
    · exact K₂.inter_subset_convexHull hs ht

theorem mem_unionComplex_faces_iff {t : Finset E} :
    t ∈ (unionComplex K₁ K₂ h).faces ↔ t ∈ K₁.faces ∨ t ∈ K₂.faces := Iff.rfl

theorem unionComplex_faces_finite (h₁ : K₁.faces.Finite) (h₂ : K₂.faces.Finite) :
    (unionComplex K₁ K₂ h).faces.Finite := h₁.union h₂

theorem unionComplex_space : (unionComplex K₁ K₂ h).space = K₁.space ∪ K₂.space := by
  ext x
  simp only [Geometry.SimplicialComplex.mem_space_iff, mem_unionComplex_faces_iff, Set.mem_union]
  constructor
  · rintro ⟨s, hs | hs, hxs⟩
    · exact Or.inl ⟨s, hs, hxs⟩
    · exact Or.inr ⟨s, hs, hxs⟩
  · rintro (⟨s, hs, hxs⟩ | ⟨s, hs, hxs⟩)
    · exact ⟨s, Or.inl hs, hxs⟩
    · exact ⟨s, Or.inr hs, hxs⟩

end UnionComplex

section Swap

variable {α : Type*} [DecidableEq α]

def swapVertex (a c v : α) : α := if v = a then c else v

theorem swapVertex_self (a c : α) : swapVertex a c a = c := by simp [swapVertex]

theorem swapVertex_of_ne {a c v : α} (h : v ≠ a) : swapVertex a c v = v := if_neg h

theorem swapVertex_swapVertex {a c v : α} (h : v ≠ c) :
    swapVertex c a (swapVertex a c v) = v := by
  by_cases hva : v = a
  · subst hva
    rw [swapVertex_self, swapVertex_self]
  · rw [swapVertex_of_ne hva, swapVertex_of_ne h]

theorem image_swapVertex_of_notMem {a c : α} {s : Finset α} (h : a ∉ s) :
    s.image (swapVertex a c) = s := by
  conv_rhs => rw [← Finset.image_id (s := s)]
  exact Finset.image_congr fun v hv => swapVertex_of_ne (ne_of_mem_of_not_mem hv h)

theorem image_swapVertex_of_mem {a c : α} {s : Finset α} (h : a ∈ s) :
    s.image (swapVertex a c) = insert c (s.erase a) := by
  conv_lhs => rw [← Finset.insert_erase h]
  rw [Finset.image_insert, swapVertex_self, image_swapVertex_of_notMem (Finset.notMem_erase a s)]

end Swap

section Stellar

variable [DecidableEq E] {T σ₀ : Finset E} {a c : E} (hT : AffineIndependent ℝ ((↑) : T → E))
  (hT' : AffineIndependent ℝ ((↑) : T.erase a → E)) (hσ₀T : σ₀ ⊆ T) (ha : a ∈ σ₀)
  (hc : c ∈ openSimplex (T \ σ₀))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
include ha in
theorem sdiff_subset_erase_of_mem : T \ σ₀ ⊆ T.erase a := fun v hv => by
  obtain ⟨hvT, hvσ⟩ := Finset.mem_sdiff.mp hv
  exact Finset.mem_erase.mpr ⟨fun h => hvσ (h ▸ ha), hvT⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
include hσ₀T ha in
theorem erase_eq_union_sdiff_of_mem : T.erase a = σ₀.erase a ∪ T \ σ₀ := by
  ext v
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨hva, hvT⟩
    by_cases hvσ : v ∈ σ₀
    · exact Or.inl ⟨hva, hvσ⟩
    · exact Or.inr ⟨hvT, hvσ⟩
  · rintro (⟨hva, hvσ⟩ | ⟨hvT, hvσ⟩)
    · exact ⟨hva, hσ₀T hvσ⟩
    · exact ⟨fun h => hvσ (h ▸ ha), hvT⟩

include hT' ha hc

theorem isConeBase_stellar :
    IsConeBase c (simplexAvoiding (T.erase a) hT' {σ₀.erase a, T \ σ₀}) :=
  isConeBase_simplexAvoiding hT' (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    (sdiff_subset_erase_of_mem ha) hc

theorem stellar_cross {s : Finset E} (hs : s ∈ (simplexAvoiding (T.erase a) hT' {T \ σ₀}).faces)
    {t : Finset E} (ht : t ∈ (coneComplex (isConeBase_stellar hT' ha hc)).faces) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
  have hτ₀ : T \ σ₀ ∈ ({T \ σ₀} : Finset (Finset E)) := Finset.mem_singleton_self _
  have hτ₀T' : T \ σ₀ ⊆ T.erase a := sdiff_subset_erase_of_mem ha
  have hcB : c ∉ (simplexAvoiding (T.erase a) hT' {T \ σ₀}).space :=
    notMem_simplexAvoiding_space hT' hτ₀ hτ₀T' hc
  rcases (mem_coneComplex_faces_iff _).mp ht with ht | rfl | ⟨σ, hσ, rfl⟩
  · exact convexHull_inter_subset_of_affineIndependent hT' hs.2.1 ht.2.1
  · rintro x ⟨hxs, hxc⟩
    rw [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] at hxc
    subst hxc
    exact absurd ((simplexAvoiding _ hT' _).convexHull_subset_space hs hxs) hcB
  · rintro x ⟨hxs, hxt⟩
    have hcσ : c ∉ σ := (isConeBase_stellar hT' ha hc).notMem_face hσ
    have hxσ : x ∈ convexHull ℝ (σ : Set E) := by
      rcases exists_combo_of_mem_convexHull_insert hcσ hxt with rfl | ⟨z, hz, r, hr0, hr1, rfl⟩
      · exact absurd ((simplexAvoiding _ hT' _).convexHull_subset_space hs hxs) hcB
      · rcases hr1.lt_or_eq with hr1 | rfl
        · exfalso
          have hzB : z ∈ (simplexAvoiding (T.erase a) hT' {T \ σ₀}).space :=
            (simplexAvoiding _ hT' _).convexHull_subset_space
              (simplexAvoiding_faces_mono _ hT' _ (Finset.subset_insert _ _) hσ) hz
          exact not_radial_lt_one_simplexAvoiding hT' hτ₀ hτ₀T' hc hzB
            ((simplexAvoiding _ hT' _).convexHull_subset_space hs hxs) hr0 hr1 rfl
        · rwa [one_smul, add_sub_cancel]
    refine convexHull_mono (Set.inter_subset_inter_right _ ?_)
      (convexHull_inter_subset_of_affineIndependent hT' hs.2.1 hσ.2.1 ⟨hxs, hxσ⟩)
    rw [Finset.coe_insert]
    exact Set.subset_insert c _

def stellarComplex : Geometry.SimplicialComplex ℝ E :=
  unionComplex (simplexAvoiding (T.erase a) hT' {T \ σ₀})
    (coneComplex (isConeBase_stellar hT' ha hc)) fun _ hs _ ht =>
      stellar_cross hT' ha hc hs ht

theorem mem_stellarComplex_faces_iff {t : Finset E} :
    t ∈ (stellarComplex hT' ha hc).faces ↔
      t ∈ (simplexAvoiding (T.erase a) hT' {T \ σ₀}).faces ∨
        t ∈ (coneComplex (isConeBase_stellar hT' ha hc)).faces := Iff.rfl

theorem stellarComplex_faces_finite : (stellarComplex hT' ha hc).faces.Finite :=
  unionComplex_faces_finite _ _ _ (simplexAvoiding_faces_finite _ _ _)
    (coneComplex_faces_finite _ (simplexAvoiding_faces_finite _ _ _))

include hσ₀T in
theorem stellarComplex_space (hσ' : (σ₀.erase a).Nonempty) :
    (stellarComplex hT' ha hc).space = (simplexBoundary (T.erase a) hT').space := by
  have hτ₀T' : T \ σ₀ ⊆ T.erase a := sdiff_subset_erase_of_mem ha
  have hτ₀ne : (T \ σ₀).Nonempty := nonempty_of_mem_openSimplex hc
  have hσ'T' : σ₀.erase a ⊆ T.erase a := Finset.erase_subset_erase a hσ₀T
  have hdisj : ∀ v ∈ σ₀.erase a, v ∉ T \ σ₀ := fun v hv h =>
    (Finset.mem_sdiff.mp h).2 (Finset.mem_of_mem_erase hv)
  rw [stellarComplex, unionComplex_space]
  apply Subset.antisymm
  · rintro x (hx | hx)
    · obtain ⟨s, ⟨hsne, hsT, hA⟩, hxs⟩ := (simplexAvoiding _ hT' _).mem_space_iff.mp hx
      refine (simplexBoundary _ hT').convexHull_subset_space ?_ hxs
      refine mem_simplexBoundary_faces_iff.mpr ⟨hsT, hsne, fun h => ?_⟩
      exact hA _ (Finset.mem_singleton_self _) (h ▸ hτ₀T')
    · rcases (mem_coneComplex_space_iff _).mp hx with rfl | ⟨z, hz, r, hr0, hr1, rfl⟩
      · refine (simplexBoundary _ hT').convexHull_subset_space
          (mem_simplexBoundary_faces_iff.mpr ⟨hτ₀T', hτ₀ne, fun h => ?_⟩)
          (openSimplex_subset_convexHull _ hc)
        obtain ⟨v, hv⟩ := hσ'
        exact hdisj v hv (h ▸ hσ'T' hv)
      · obtain ⟨σ, ⟨hσne, hσT, hA⟩, hzσ⟩ := (simplexAvoiding _ hT' _).mem_space_iff.mp hz
        refine (simplexBoundary _ hT').convexHull_subset_space (s := T \ σ₀ ∪ σ)
          (mem_simplexBoundary_faces_iff.mpr
            ⟨Finset.union_subset hτ₀T' hσT, hτ₀ne.mono Finset.subset_union_left, fun h => ?_⟩) ?_
        · apply hA (σ₀.erase a) (Finset.mem_insert_self _ _)
          intro v hv
          have hv' : v ∈ T \ σ₀ ∪ σ := by
            rw [h]
            exact hσ'T' hv
          rcases Finset.mem_union.mp hv' with h' | h'
          · exact absurd h' (hdisj v hv)
          · exact h'
        · rw [add_smul_sub_eq_combo]
          exact (convex_convexHull ℝ _)
            (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left)
              (openSimplex_subset_convexHull _ hc))
            (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right) hzσ)
            (by linarith) hr0.le (by ring)
  · intro x hx
    obtain ⟨F, hF, hxF⟩ := (simplexBoundary _ hT').mem_space_iff.mp hx
    obtain ⟨hFT, hFne, hFne'⟩ := mem_simplexBoundary_faces_iff.mp hF
    by_cases hτ₀F : T \ σ₀ ⊆ F
    · have hF' : AffineIndependent ℝ ((↑) : F → E) := affineIndependent_of_subset hT' hFT
      obtain ⟨w, hw, hxw⟩ :=
        exists_mem_convexHull_insert_erase_of_mem_openSimplex hF' hτ₀F hc hxF
      refine Or.inr ((coneComplex _).convexHull_subset_space ?_ hxw)
      rw [mem_coneComplex_faces_iff]
      rcases (F.erase w).eq_empty_or_nonempty with h | hne
      · rw [h, Finset.insert_empty]
        exact Or.inr (Or.inl rfl)
      · refine Or.inr (Or.inr ⟨F.erase w, ⟨hne, (Finset.erase_subset w F).trans hFT, ?_⟩, rfl⟩)
        intro σ hσ hσsub
        rcases Finset.mem_insert.mp hσ with h | hσ
        · rw [h] at hσsub
          apply hFne'
          refine Finset.Subset.antisymm hFT ?_
          rw [erase_eq_union_sdiff_of_mem hσ₀T ha]
          exact Finset.union_subset (hσsub.trans (Finset.erase_subset w F)) hτ₀F
        · rw [Finset.mem_singleton] at hσ
          subst hσ
          exact Finset.notMem_erase w F (hσsub hw)
    · refine Or.inl ((simplexAvoiding _ hT' _).convexHull_subset_space ⟨hFne, hFT, ?_⟩ hxF)
      intro σ hσ
      rw [Finset.mem_singleton] at hσ
      subst hσ
      exact hτ₀F

include hσ₀T in
theorem isGlueIso_stellar (hσ' : (σ₀.erase a).Nonempty) :
    IsGlueIso (simplexAvoiding T hT {σ₀, T \ σ₀}) (stellarComplex hT' ha hc) (swapVertex a c)
      (swapVertex c a) := by
  have hτ₀T : T \ σ₀ ⊆ T := Finset.sdiff_subset
  have haτ₀ : a ∉ T \ σ₀ := fun h => (Finset.mem_sdiff.mp h).2 ha
  have haT : a ∈ T := hσ₀T ha
  have hτ₀ne : (T \ σ₀).Nonempty := nonempty_of_mem_openSimplex hc
  have hcT : ∀ s : Finset E, s ⊆ T → c ∈ s → T \ σ₀ ⊆ s := by
    intro s hsT hcs
    have heq : T \ σ₀ = {c} :=
      eq_of_mem_openSimplex_of_mem_openSimplex hT hτ₀T
        (Finset.singleton_subset_iff.mpr (hsT hcs)) hc (mem_openSimplex_singleton c)
    rw [heq]
    exact Finset.singleton_subset_iff.mpr hcs
  have hca : c ≠ a := by
    intro h
    obtain ⟨v, hv⟩ := hτ₀ne
    have hsub := hcT {a} (Finset.singleton_subset_iff.mpr haT) (h ▸ Finset.mem_singleton_self a)
    have hva := Finset.mem_singleton.mp (hsub hv)
    exact haτ₀ (hva ▸ hv)
  have hcJ : ∀ s ∈ (simplexAvoiding T hT {σ₀, T \ σ₀}).faces, c ∉ s := fun s hs hcs =>
    hs.2.2 (T \ σ₀) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (hcT s hs.2.1 hcs)
  have hcB : ∀ s ∈ (simplexAvoiding (T.erase a) hT' {T \ σ₀}).faces, c ∉ s := fun s hs hcs =>
    hs.2.2 (T \ σ₀) (Finset.mem_singleton_self _)
      (hcT s (hs.2.1.trans (Finset.erase_subset a T)) hcs)
  have hcJ' : ∀ s ∈ (simplexAvoiding (T.erase a) hT' {σ₀.erase a, T \ σ₀}).faces, c ∉ s :=
    fun s hs hcs => hs.2.2 (T \ σ₀) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      (hcT s (hs.2.1.trans (Finset.erase_subset a T)) hcs)
  have haS : ∀ t ∈ (stellarComplex hT' ha hc).faces, a ∉ t := by
    intro t ht
    rcases (mem_stellarComplex_faces_iff hT' ha hc).mp ht with ht | ht
    · exact fun h => Finset.notMem_erase a T (ht.2.1 h)
    · rcases (mem_coneComplex_faces_iff _).mp ht with ht | rfl | ⟨σ, hσ, rfl⟩
      · exact fun h => Finset.notMem_erase a T (ht.2.1 h)
      · exact fun h => hca (Finset.mem_singleton.mp h).symm
      · intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact hca h.symm
        · exact Finset.notMem_erase a T (hσ.2.1 h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨hsne, hsT, hA⟩ := hs
    have hσ₀s : ¬ σ₀ ⊆ s := hA σ₀ (Finset.mem_insert_self _ _)
    have hτ₀s : ¬ T \ σ₀ ⊆ s := hA _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [mem_stellarComplex_faces_iff]
    by_cases has : a ∈ s
    · rw [image_swapVertex_of_mem has]
      refine Or.inr ?_
      rw [mem_coneComplex_faces_iff]
      rcases (s.erase a).eq_empty_or_nonempty with h | hne
      · rw [h, Finset.insert_empty]
        exact Or.inr (Or.inl rfl)
      · refine Or.inr (Or.inr ⟨s.erase a, ⟨hne, Finset.erase_subset_erase a hsT, ?_⟩, rfl⟩)
        intro σ hσ hσsub
        rcases Finset.mem_insert.mp hσ with h | hσ
        · rw [h] at hσsub
          apply hσ₀s
          intro v hv
          by_cases hva : v = a
          · exact hva ▸ has
          · exact Finset.mem_of_mem_erase (hσsub (Finset.mem_erase.mpr ⟨hva, hv⟩))
        · rw [Finset.mem_singleton] at hσ
          subst hσ
          exact hτ₀s (hσsub.trans (Finset.erase_subset a s))
    · rw [image_swapVertex_of_notMem has]
      refine Or.inl ⟨hsne, fun v hv => Finset.mem_erase.mpr ⟨fun h => has (h ▸ hv), hsT hv⟩, ?_⟩
      intro σ hσ
      rw [Finset.mem_singleton] at hσ
      subst hσ
      exact hτ₀s
  · intro t ht
    rcases (mem_stellarComplex_faces_iff hT' ha hc).mp ht with ht | ht
    · obtain ⟨htne, htT, hA⟩ := ht
      rw [image_swapVertex_of_notMem (hcB t ⟨htne, htT, hA⟩)]
      refine ⟨htne, htT.trans (Finset.erase_subset a T), ?_⟩
      intro σ hσ hσsub
      rcases Finset.mem_insert.mp hσ with h | hσ
      · rw [h] at hσsub
        exact Finset.notMem_erase a T (htT (hσsub ha))
      · rw [Finset.mem_singleton] at hσ
        subst hσ
        exact hA _ (Finset.mem_singleton_self _) hσsub
    · rcases (mem_coneComplex_faces_iff _).mp ht with ht | rfl | ⟨σ, hσ, rfl⟩
      · obtain ⟨htne, htT, hA⟩ := ht
        rw [image_swapVertex_of_notMem (hcJ' t ⟨htne, htT, hA⟩)]
        refine ⟨htne, htT.trans (Finset.erase_subset a T), ?_⟩
        intro σ hσ hσsub
        rcases Finset.mem_insert.mp hσ with h | hσ
        · rw [h] at hσsub
          exact Finset.notMem_erase a T (htT (hσsub ha))
        · rw [Finset.mem_singleton] at hσ
          subst hσ
          exact hA _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hσsub
      · rw [Finset.image_singleton, swapVertex_self]
        refine ⟨Finset.singleton_nonempty a, Finset.singleton_subset_iff.mpr haT, ?_⟩
        intro σ hσ hσsub
        rcases Finset.mem_insert.mp hσ with h | hσ
        · rw [h] at hσsub
          obtain ⟨v, hv⟩ := hσ'
          have hva := Finset.mem_singleton.mp (hσsub (Finset.mem_of_mem_erase hv))
          exact (Finset.mem_erase.mp hv).1 hva
        · rw [Finset.mem_singleton] at hσ
          subst hσ
          obtain ⟨v, hv⟩ := hτ₀ne
          have hva := Finset.mem_singleton.mp (hσsub hv)
          exact haτ₀ (hva ▸ hv)
      · obtain ⟨hσne, hσT, hA⟩ := hσ
        rw [Finset.image_insert, swapVertex_self,
          image_swapVertex_of_notMem (hcJ' σ ⟨hσne, hσT, hA⟩)]
        refine ⟨Finset.insert_nonempty a σ,
          Finset.insert_subset haT (hσT.trans (Finset.erase_subset a T)), ?_⟩
        intro ρ hρ hρsub
        rcases Finset.mem_insert.mp hρ with h | hρ
        · rw [h] at hρsub
          apply hA (σ₀.erase a) (Finset.mem_insert_self _ _)
          intro v hv
          rcases Finset.mem_insert.mp (hρsub (Finset.mem_of_mem_erase hv)) with h | h
          · exact absurd h (Finset.mem_erase.mp hv).1
          · exact h
        · rw [Finset.mem_singleton] at hρ
          subst hρ
          apply hA (T \ σ₀) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
          intro v hv
          rcases Finset.mem_insert.mp (hρsub hv) with h | h
          · exact absurd (h ▸ hv) haτ₀
          · exact h
  · intro s hs v hv
    exact swapVertex_swapVertex (ne_of_mem_of_not_mem hv (hcJ s hs))
  · intro t ht v hv
    exact swapVertex_swapVertex (ne_of_mem_of_not_mem hv (haS t ht))

end Stellar

theorem isPLSphere_simplexAvoiding_pair [FiniteDimensional ℝ E] [DecidableEq E] {n : ℕ}
    {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = n + 3)
    {σ₀ : Finset E} (hσ₀T : σ₀ ⊆ T) (hne : σ₀.Nonempty) (hσ₀ : σ₀ ≠ T) :
    IsPLSphere n (simplexAvoiding T hT {σ₀, T \ σ₀}).space := by
  obtain ⟨a, ha⟩ := hne
  have hT' : AffineIndependent ℝ ((↑) : T.erase a → E) :=
    affineIndependent_of_subset hT (Finset.erase_subset a T)
  have haT : a ∈ T := hσ₀T ha
  have hcard' : (T.erase a).card = n + 2 := by
    have := Finset.card_erase_of_mem haT
    omega
  have hτ₀ne : (T \ σ₀).Nonempty := by
    obtain ⟨v, hvT, hvσ⟩ :=
      Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hσ₀T, hσ₀⟩)
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hvT, hvσ⟩⟩
  rcases (σ₀.erase a).eq_empty_or_nonempty with hσ' | hσ'
  · have hσ₀a : σ₀ = {a} :=
      ((Finset.erase_eq_empty_iff σ₀ a).mp hσ').resolve_left (Finset.Nonempty.ne_empty ⟨a, ha⟩)
    have heq : simplexAvoiding T hT {σ₀, T \ σ₀} = simplexBoundary (T.erase a) hT' := by
      ext s
      rw [mem_simplexAvoiding_faces_iff, mem_simplexBoundary_faces_iff, hσ₀a,
        Finset.sdiff_singleton_eq_erase]
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
        Finset.singleton_subset_iff]
      constructor
      · rintro ⟨hsne, hsT, has, hTs⟩
        refine ⟨fun v hv => Finset.mem_erase.mpr ⟨fun h => has (h ▸ hv), hsT hv⟩, hsne, fun h => ?_⟩
        subst h
        exact hTs (Finset.Subset.refl _)
      · rintro ⟨hsT, hsne, hsT'⟩
        exact ⟨hsne, hsT.trans (Finset.erase_subset a T), fun h => Finset.notMem_erase a T (hsT h),
          fun h => hsT' (Finset.Subset.antisymm hsT h)⟩
    rw [heq, simplexBoundary_space _ hT' (by omega)]
    exact isPLSphere_biUnion_erase _ hT' hcard'
  · have hc : (T \ σ₀).centroid ℝ id ∈ openSimplex (T \ σ₀) := centroid_mem_openSimplex hτ₀ne
    have hiso := isGlueIso_stellar hT hT' hσ₀T ha hc hσ'
    have hfinJ := (simplexAvoiding_faces_finite T hT {σ₀, T \ σ₀}).to_subtype
    have hfinS := (stellarComplex_faces_finite hT' ha hc).to_subtype
    have hS : IsPLSphere n (stellarComplex hT' ha hc).space := by
      rw [stellarComplex_space hT' hσ₀T ha hc hσ', simplexBoundary_space _ hT' (by omega)]
      exact isPLSphere_biUnion_erase _ hT' hcard'
    exact hS.of_isPLHomeomorphOn hiso.isPLHomeomorphOn.symm

end DifferentialGeometry.Topology.PiecewiseLinear
