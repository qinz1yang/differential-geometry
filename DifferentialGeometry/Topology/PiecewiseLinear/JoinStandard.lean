import DifferentialGeometry.Topology.PiecewiseLinear.Join
import DifferentialGeometry.Topology.PiecewiseLinear.StellarSphere

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [DecidableEq E] [DecidableEq F] {σ : Finset E}
  (hσ : AffineIndependent ℝ ((↑) : σ → E)) {τ : Finset F}
  (hτ : AffineIndependent ℝ ((↑) : τ → F))

include hσ hτ in
theorem affineIndependent_image_joinFst_union_image_joinSnd :
    AffineIndependent ℝ
      ((↑) : (σ.image (joinFst E F) ∪ τ.image (joinSnd E F) : Finset (E × F × ℝ)) →
        E × F × ℝ) := by
  rcases τ.eq_empty_or_nonempty with hτe | hτne
  · rcases σ.eq_empty_or_nonempty with hσe | hσne
    · rw [hσe, hτe, Finset.image_empty, Finset.image_empty, Finset.union_empty]
      have : IsEmpty {x // x ∈ (∅ : Finset (E × F × ℝ))} := Finset.isEmpty_coe_sort.mpr rfl
      exact affineIndependent_of_subsingleton ℝ _
    · exact joinFaces_indep (simplexComplex σ hσ) (simplexComplex τ hτ)
        ⟨σ, τ, Or.inr ⟨hσne, subset_rfl⟩, Or.inl hτe, Or.inl hσne, rfl⟩
  · rcases σ.eq_empty_or_nonempty with hσe | hσne
    · exact joinFaces_indep (simplexComplex σ hσ) (simplexComplex τ hτ)
        ⟨σ, τ, Or.inl hσe, Or.inr ⟨hτne, subset_rfl⟩, Or.inr hτne, rfl⟩
    · exact joinFaces_indep (simplexComplex σ hσ) (simplexComplex τ hτ)
        ⟨σ, τ, Or.inr ⟨hσne, subset_rfl⟩, Or.inr ⟨hτne, subset_rfl⟩, Or.inl hσne, rfl⟩

theorem image_joinFst_subset_of_subset_union {σ₁ σ₂ : Finset E} {t : Finset (E × F × ℝ)}
    {τ' : Finset F} (h : σ₁.image (joinFst E F) ⊆ t) (ht : t ⊆ σ₂.image (joinFst E F) ∪
      τ'.image (joinSnd E F)) : σ₁ ⊆ σ₂ := by
  intro v hv
  have hmem := ht (h (Finset.mem_image_of_mem _ hv))
  rcases Finset.mem_union.mp hmem with h' | h'
  · obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp h'
    rw [joinFst_injective huv] at hu
    exact hu
  · obtain ⟨w, -, hw⟩ := Finset.mem_image.mp h'
    exact absurd hw (joinFst_ne_joinSnd v w).symm

theorem image_joinSnd_subset_of_subset_union {τ₁ τ₂ : Finset F} {t : Finset (E × F × ℝ)}
    {σ' : Finset E} (h : τ₁.image (joinSnd E F) ⊆ t) (ht : t ⊆ σ'.image (joinFst E F) ∪
      τ₂.image (joinSnd E F)) : τ₁ ⊆ τ₂ := by
  intro w hw
  have hmem := ht (h (Finset.mem_image_of_mem _ hw))
  rcases Finset.mem_union.mp hmem with h' | h'
  · obtain ⟨v, -, hv⟩ := Finset.mem_image.mp h'
    exact absurd hv (joinFst_ne_joinSnd v w)
  · obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp h'
    rw [joinSnd_injective huw] at hu
    exact hu

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem eq_image_filter_union_image_filter {t : Finset (E × F × ℝ)}
    (ht : t ⊆ σ.image (joinFst E F) ∪ τ.image (joinSnd E F)) :
    t = (σ.filter fun v => joinFst E F v ∈ t).image (joinFst E F) ∪
      (τ.filter fun w => joinSnd E F w ∈ t).image (joinSnd E F) := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_union.mp (ht hz) with h | h
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hv, hz⟩))
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw, hz⟩))
  · intro hz
    rcases Finset.mem_union.mp hz with h | h
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hv).2
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hw).2

include hσ hτ in
theorem joinComplex_simplexBoundary_simplexBoundary (hσne : σ.Nonempty) (hτne : τ.Nonempty) :
    joinComplex (simplexBoundary σ hσ) (simplexBoundary τ hτ) =
      simplexAvoiding (σ.image (joinFst E F) ∪ τ.image (joinSnd E F))
        (affineIndependent_image_joinFst_union_image_joinSnd hσ hτ)
        {σ.image (joinFst E F), τ.image (joinSnd E F)} := by
  ext t
  rw [mem_joinComplex_faces_iff, mem_simplexAvoiding_faces_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨σ', τ', hσ', hτ', hne, rfl⟩
    have hσ'σ : σ' ⊆ σ := by
      rcases hσ' with rfl | h
      · exact Finset.empty_subset σ
      · exact h.1
    have hτ'τ : τ' ⊆ τ := by
      rcases hτ' with rfl | h
      · exact Finset.empty_subset τ
      · exact h.1
    refine ⟨?_, Finset.union_subset_union (Finset.image_subset_image hσ'σ)
      (Finset.image_subset_image hτ'τ), ?_, ?_⟩
    · rcases hne with h | h
      · exact (h.image _).mono Finset.subset_union_left
      · exact (h.image _).mono Finset.subset_union_right
    · intro h
      have hσσ' : σ ⊆ σ' := image_joinFst_subset_of_subset_union h subset_rfl
      rcases hσ' with rfl | h'
      · exact hσne.ne_empty (Finset.subset_empty.mp hσσ')
      · exact h'.2.2 (Finset.Subset.antisymm h'.1 hσσ')
    · intro h
      have hττ' : τ ⊆ τ' := image_joinSnd_subset_of_subset_union h subset_rfl
      rcases hτ' with rfl | h'
      · exact hτne.ne_empty (Finset.subset_empty.mp hττ')
      · exact h'.2.2 (Finset.Subset.antisymm h'.1 hττ')
  · rintro ⟨htne, ht, hσt, hτt⟩
    refine ⟨σ.filter fun v => joinFst E F v ∈ t, τ.filter fun w => joinSnd E F w ∈ t, ?_, ?_, ?_,
      eq_image_filter_union_image_filter ht⟩
    · rcases (σ.filter fun v => joinFst E F v ∈ t).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · refine Or.inr ⟨Finset.filter_subset _ _, h, fun heq => hσt ?_⟩
        intro z hz
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
        have hv' : v ∈ σ.filter fun v => joinFst E F v ∈ t := by
          rw [heq]
          exact hv
        exact (Finset.mem_filter.mp hv').2
    · rcases (τ.filter fun w => joinSnd E F w ∈ t).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · refine Or.inr ⟨Finset.filter_subset _ _, h, fun heq => hτt ?_⟩
        intro z hz
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
        have hw' : w ∈ τ.filter fun w => joinSnd E F w ∈ t := by
          rw [heq]
          exact hw
        exact (Finset.mem_filter.mp hw').2
    · obtain ⟨z, hz⟩ := htne
      rcases Finset.mem_union.mp (ht hz) with h | h
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
        exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨hv, hz⟩⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
        exact Or.inr ⟨w, Finset.mem_filter.mpr ⟨hw, hz⟩⟩

include hσ hτ in
theorem joinComplex_simplexBoundary_simplexComplex (hσne : σ.Nonempty) :
    joinComplex (simplexBoundary σ hσ) (simplexComplex τ hτ) =
      simplexAvoiding (σ.image (joinFst E F) ∪ τ.image (joinSnd E F))
        (affineIndependent_image_joinFst_union_image_joinSnd hσ hτ) {σ.image (joinFst E F)} := by
  ext t
  rw [mem_joinComplex_faces_iff, mem_simplexAvoiding_faces_iff]
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · rintro ⟨σ', τ', hσ', hτ', hne, rfl⟩
    have hσ'σ : σ' ⊆ σ := by
      rcases hσ' with rfl | h
      · exact Finset.empty_subset σ
      · exact h.1
    have hτ'τ : τ' ⊆ τ := by
      rcases hτ' with rfl | h
      · exact Finset.empty_subset τ
      · exact h.2
    refine ⟨?_, Finset.union_subset_union (Finset.image_subset_image hσ'σ)
      (Finset.image_subset_image hτ'τ), ?_⟩
    · rcases hne with h | h
      · exact (h.image _).mono Finset.subset_union_left
      · exact (h.image _).mono Finset.subset_union_right
    · intro h
      have hσσ' : σ ⊆ σ' := image_joinFst_subset_of_subset_union h subset_rfl
      rcases hσ' with rfl | h'
      · exact hσne.ne_empty (Finset.subset_empty.mp hσσ')
      · exact h'.2.2 (Finset.Subset.antisymm h'.1 hσσ')
  · rintro ⟨htne, ht, hσt⟩
    refine ⟨σ.filter fun v => joinFst E F v ∈ t, τ.filter fun w => joinSnd E F w ∈ t, ?_, ?_, ?_,
      eq_image_filter_union_image_filter ht⟩
    · rcases (σ.filter fun v => joinFst E F v ∈ t).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · refine Or.inr ⟨Finset.filter_subset _ _, h, fun heq => hσt ?_⟩
        intro z hz
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
        have hv' : v ∈ σ.filter fun v => joinFst E F v ∈ t := by
          rw [heq]
          exact hv
        exact (Finset.mem_filter.mp hv').2
    · rcases (τ.filter fun w => joinSnd E F w ∈ t).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, Finset.filter_subset _ _⟩
    · obtain ⟨z, hz⟩ := htne
      rcases Finset.mem_union.mp (ht hz) with h | h
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
        exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨hv, hz⟩⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
        exact Or.inr ⟨w, Finset.mem_filter.mpr ⟨hw, hz⟩⟩

theorem card_image_joinFst_union_image_joinSnd (σ : Finset E) (τ : Finset F) :
    (σ.image (joinFst E F) ∪ τ.image (joinSnd E F)).card = σ.card + τ.card := by
  rw [Finset.card_union_of_disjoint (disjoint_image_joinFst_joinSnd σ τ),
    Finset.card_image_of_injective _ joinFst_injective,
    Finset.card_image_of_injective _ joinSnd_injective]

theorem union_sdiff_image_joinFst (σ : Finset E) (τ : Finset F) :
    (σ.image (joinFst E F) ∪ τ.image (joinSnd E F)) \ σ.image (joinFst E F) =
      τ.image (joinSnd E F) :=
  Finset.union_sdiff_cancel_left (disjoint_image_joinFst_joinSnd σ τ)

include hσ hτ in
theorem isPLSphere_joinComplex_simplexBoundary_simplexBoundary [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {a b : ℕ} (hσcard : σ.card = a + 2) (hτcard : τ.card = b + 2) :
    IsPLSphere (a + b + 1) (joinComplex (simplexBoundary σ hσ) (simplexBoundary τ hτ)).space := by
  have hσne : σ.Nonempty := Finset.card_pos.mp (by omega)
  have hτne : τ.Nonempty := Finset.card_pos.mp (by omega)
  rw [joinComplex_simplexBoundary_simplexBoundary hσ hτ hσne hτne]
  have hcard : (σ.image (joinFst E F) ∪ τ.image (joinSnd E F)).card = a + b + 1 + 3 := by
    rw [card_image_joinFst_union_image_joinSnd]
    omega
  have hne : σ.image (joinFst E F) ≠ σ.image (joinFst E F) ∪ τ.image (joinSnd E F) := by
    intro h
    obtain ⟨w, hw⟩ := hτne
    have hmem : joinSnd E F w ∈ σ.image (joinFst E F) ∪ τ.image (joinSnd E F) :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw)
    rw [← h] at hmem
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hmem
    exact joinFst_ne_joinSnd v w hv
  have h := isPLSphere_simplexAvoiding_pair (affineIndependent_image_joinFst_union_image_joinSnd hσ hτ)
    hcard Finset.subset_union_left (hσne.image _) hne
  rwa [union_sdiff_image_joinFst] at h

include hσ hτ in
theorem isPLBall_joinComplex_simplexBoundary_simplexComplex [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {a b : ℕ} (hσcard : σ.card = a + 2) (hτcard : τ.card = b + 1) :
    IsPLBall (a + b + 1) (joinComplex (simplexBoundary σ hσ) (simplexComplex τ hτ)).space := by
  have hσne : σ.Nonempty := Finset.card_pos.mp (by omega)
  have hτne : τ.Nonempty := Finset.card_pos.mp (by omega)
  rw [joinComplex_simplexBoundary_simplexComplex hσ hτ hσne]
  refine isPLBall_simplexAvoiding_singleton _ ?_ Finset.subset_union_left (hσne.image _) ?_
  · rw [card_image_joinFst_union_image_joinSnd]
    omega
  · intro h
    obtain ⟨w, hw⟩ := hτne
    have hmem : joinSnd E F w ∈ σ.image (joinFst E F) ∪ τ.image (joinSnd E F) :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw)
    rw [← h] at hmem
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hmem
    exact joinFst_ne_joinSnd v w hv

end DifferentialGeometry.Topology.PiecewiseLinear
