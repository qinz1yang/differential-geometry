import DifferentialGeometry.Topology.PiecewiseLinear.JoinInvariance

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

variable (E F) in
def joinSwap : E × F × ℝ → F × E × ℝ := fun z => (z.2.1, z.1, 1 - z.2.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem joinSwap_joinFst (v : E) : joinSwap E F (joinFst E F v) = joinSnd F E v := by
  change ((0 : F), v, (1 : ℝ) - 0) = ((0 : F), v, (1 : ℝ))
  rw [sub_zero]

omit [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem joinSwap_joinSnd (w : F) : joinSwap E F (joinSnd E F w) = joinFst F E w := by
  change (w, (0 : E), (1 : ℝ) - 1) = (w, (0 : E), (0 : ℝ))
  rw [sub_self]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem joinSwap_joinSwap (z : E × F × ℝ) : joinSwap F E (joinSwap E F z) = z := by
  change (z.1, z.2.1, (1 : ℝ) - (1 - z.2.2)) = z
  rw [sub_sub_cancel]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem image_joinSwap_image_joinFst [DecidableEq E] [DecidableEq F] (σ : Finset E) :
    (σ.image (joinFst E F)).image (joinSwap E F) = σ.image (joinSnd F E) := by
  rw [Finset.image_image]
  exact Finset.image_congr fun v _ => joinSwap_joinFst v

omit [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem image_joinSwap_image_joinSnd [DecidableEq E] [DecidableEq F] (τ : Finset F) :
    (τ.image (joinSnd E F)).image (joinSwap E F) = τ.image (joinFst F E) := by
  rw [Finset.image_image]
  exact Finset.image_congr fun w _ => joinSwap_joinSnd w

theorem isGlueIso_joinComplex_swap [DecidableEq E] [DecidableEq F]
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F) :
    IsGlueIso (joinComplex K L) (joinComplex L K) (joinSwap E F) (joinSwap F E) where
  image₁ := by
    rintro s ⟨σ, τ, hσ, hτ, hne, rfl⟩
    rw [Finset.image_union, image_joinSwap_image_joinFst, image_joinSwap_image_joinSnd,
      Finset.union_comm]
    exact union_image_mem_joinComplex L K hτ hσ hne.symm
  image₂ := by
    rintro t ⟨τ, σ, hτ, hσ, hne, rfl⟩
    rw [Finset.image_union, image_joinSwap_image_joinFst, image_joinSwap_image_joinSnd,
      Finset.union_comm]
    exact union_image_mem_joinComplex K L hσ hτ hne.symm
  left _ _ _ _ := joinSwap_joinSwap _
  right _ _ _ _ := joinSwap_joinSwap _

theorem exists_isPLHomeomorphOn_joinComplex_swap [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [DecidableEq E] [DecidableEq F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces] :
    ∃ f, IsPLHomeomorphOn f (joinComplex K L).space (joinComplex L K).space := by
  have hKL : Finite (joinComplex K L).faces := (joinComplex_faces_finite K L).to_subtype
  have hLK : Finite (joinComplex L K).faces := (joinComplex_faces_finite L K).to_subtype
  exact ⟨_, (isGlueIso_joinComplex_swap K L).isPLHomeomorphOn⟩

theorem joinComplex_simplexComplex_simplexComplex [DecidableEq E] [DecidableEq F] {σ : Finset E}
    (hσ : AffineIndependent ℝ ((↑) : σ → E)) {τ : Finset F}
    (hτ : AffineIndependent ℝ ((↑) : τ → F)) :
    joinComplex (simplexComplex σ hσ) (simplexComplex τ hτ) =
      simplexComplex (σ.image (joinFst E F) ∪ τ.image (joinSnd E F))
        (affineIndependent_image_joinFst_union_image_joinSnd hσ hτ) := by
  ext t
  constructor
  · rintro ⟨σ', τ', hσ', hτ', hne, rfl⟩
    have hσ'σ : σ' ⊆ σ := by
      rcases hσ' with rfl | h
      · exact Finset.empty_subset σ
      · exact h.2
    have hτ'τ : τ' ⊆ τ := by
      rcases hτ' with rfl | h
      · exact Finset.empty_subset τ
      · exact h.2
    refine ⟨?_, Finset.union_subset_union (Finset.image_subset_image hσ'σ)
      (Finset.image_subset_image hτ'τ)⟩
    rcases hne with h | h
    · exact (h.image _).mono Finset.subset_union_left
    · exact (h.image _).mono Finset.subset_union_right
  · rintro ⟨htne, ht⟩
    refine ⟨σ.filter fun v => joinFst E F v ∈ t, τ.filter fun w => joinSnd E F w ∈ t, ?_, ?_, ?_,
      eq_image_filter_union_image_filter ht⟩
    · rcases (σ.filter fun v => joinFst E F v ∈ t).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, Finset.filter_subset _ _⟩
    · rcases (τ.filter fun w => joinSnd E F w ∈ t).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, Finset.filter_subset _ _⟩
    · obtain ⟨z, hz⟩ := htne
      rcases Finset.mem_union.mp (ht hz) with h | h
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
        exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨hv, hz⟩⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
        exact Or.inr ⟨w, Finset.mem_filter.mpr ⟨hw, hz⟩⟩

theorem isPLBall_joinComplex_simplexComplex_simplexComplex [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [DecidableEq E] [DecidableEq F] {σ : Finset E}
    (hσ : AffineIndependent ℝ ((↑) : σ → E)) {τ : Finset F}
    (hτ : AffineIndependent ℝ ((↑) : τ → F)) {a b : ℕ} (hσcard : σ.card = a + 1)
    (hτcard : τ.card = b + 1) :
    IsPLBall (a + b + 1) (joinComplex (simplexComplex σ hσ) (simplexComplex τ hτ)).space := by
  have hσne : σ.Nonempty := Finset.card_pos.mp (by omega)
  have hne : (σ.image (joinFst E F) ∪ τ.image (joinSnd E F)).Nonempty :=
    (hσne.image _).mono Finset.subset_union_left
  rw [joinComplex_simplexComplex_simplexComplex hσ hτ, simplexComplex_space _ _ hne]
  refine isPLBall_convexHull_of_affineIndependent _
    (affineIndependent_image_joinFst_union_image_joinSnd hσ hτ) ?_
  rw [card_image_joinFst_union_image_joinSnd]
  omega

theorem isPLBall_joinComplex_of_isPLBall_of_isPLBall [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [DecidableEq E] [DecidableEq F]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} [Finite L.faces] {a b : ℕ} (hK : IsPLBall a K.space)
    (hL : IsPLBall b L.space) : IsPLBall (a + b + 1) (joinComplex K L).space := by
  obtain ⟨T, hT, f, hTcard, hf⟩ := exists_isPLHomeomorphOn_simplexComplex hK
  obtain ⟨S, hS, g, hScard, hg⟩ := exists_isPLHomeomorphOn_simplexComplex hL
  have hfinT : Finite (simplexComplex T hT).faces := (simplexComplex_faces_finite T hT).to_subtype
  have hfinS : Finite (simplexComplex S hS).faces := (simplexComplex_faces_finite S hS).to_subtype
  obtain ⟨h, hh⟩ := exists_isPLHomeomorphOn_joinComplex hf hg
  exact (isPLBall_joinComplex_simplexComplex_simplexComplex hT hS hTcard
    hScard).of_isPLHomeomorphOn hh

theorem isPLBall_joinComplex_of_isPLBall_of_isPLSphere [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [DecidableEq E] [DecidableEq F]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} [Finite L.faces] {a b : ℕ} (hK : IsPLBall a K.space)
    (hL : IsPLSphere b L.space) : IsPLBall (a + b + 1) (joinComplex K L).space := by
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_joinComplex_swap L K
  have h := (isPLBall_joinComplex_of_isPLSphere_of_isPLBall hL hK).of_isPLHomeomorphOn hf
  have hab : b + a + 1 = a + b + 1 := by omega
  rwa [hab] at h

end DifferentialGeometry.Topology.PiecewiseLinear
