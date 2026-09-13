import DifferentialGeometry.Topology.PiecewiseLinear.Join

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E E' F F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

noncomputable def joinVertexMap (φ : E → E') (ψ : F → F') (z : E × F × ℝ) : E' × F' × ℝ :=
  if glueHeight E F z = 0 then joinFst E' F' (φ (glueFst E F z))
  else joinSnd E' F' (ψ (glueSnd E F z))

omit [NormedSpace ℝ E'] [NormedSpace ℝ F'] in
theorem joinVertexMap_joinFst (φ : E → E') (ψ : F → F') (v : E) :
    joinVertexMap φ ψ (joinFst E F v) = joinFst E' F' (φ v) := by
  rw [joinVertexMap, if_pos (glueHeight_joinFst v), glueFst_joinFst]

omit [NormedSpace ℝ E'] [NormedSpace ℝ F'] in
theorem joinVertexMap_joinSnd (φ : E → E') (ψ : F → F') (w : F) :
    joinVertexMap φ ψ (joinSnd E F w) = joinSnd E' F' (ψ w) := by
  rw [joinVertexMap, if_neg (by rw [glueHeight_joinSnd]; exact one_ne_zero), glueSnd_joinSnd]

omit [NormedSpace ℝ E'] [NormedSpace ℝ F'] in
theorem image_joinVertexMap [DecidableEq E] [DecidableEq E'] [DecidableEq F] [DecidableEq F']
    (φ : E → E') (ψ : F → F') (σ : Finset E) (τ : Finset F) :
    (σ.image (joinFst E F) ∪ τ.image (joinSnd E F)).image (joinVertexMap φ ψ) =
      (σ.image φ).image (joinFst E' F') ∪ (τ.image ψ).image (joinSnd E' F') := by
  have hfst : (σ.image (joinFst E F)).image (joinVertexMap φ ψ) =
      (σ.image φ).image (joinFst E' F') := by
    rw [Finset.image_image, Finset.image_image]
    exact Finset.image_congr fun v _ => joinVertexMap_joinFst φ ψ v
  have hsnd : (τ.image (joinSnd E F)).image (joinVertexMap φ ψ) =
      (τ.image ψ).image (joinSnd E' F') := by
    rw [Finset.image_image, Finset.image_image]
    exact Finset.image_congr fun w _ => joinVertexMap_joinSnd φ ψ w
  rw [Finset.image_union, hfst, hsnd]

theorem image_joinVertexMap_mem_joinComplex [DecidableEq E] [DecidableEq E'] [DecidableEq F]
    [DecidableEq F'] {K₁ : Geometry.SimplicialComplex ℝ E} {K₂ : Geometry.SimplicialComplex ℝ E'}
    {L₁ : Geometry.SimplicialComplex ℝ F} {L₂ : Geometry.SimplicialComplex ℝ F'} {φ : E → E'}
    {ψ : F → F'} (hφ : ∀ s ∈ K₁.faces, s.image φ ∈ K₂.faces)
    (hψ : ∀ t ∈ L₁.faces, t.image ψ ∈ L₂.faces) {s : Finset (E × F × ℝ)}
    (hs : s ∈ (joinComplex K₁ L₁).faces) :
    s.image (joinVertexMap φ ψ) ∈ (joinComplex K₂ L₂).faces := by
  obtain ⟨σ, τ, hσ, hτ, hne, rfl⟩ := hs
  rw [image_joinVertexMap]
  refine union_image_mem_joinComplex K₂ L₂ ?_ ?_ ?_
  · rcases hσ with rfl | hσ
    · exact Or.inl (Finset.image_empty φ)
    · exact Or.inr (hφ σ hσ)
  · rcases hτ with rfl | hτ
    · exact Or.inl (Finset.image_empty ψ)
    · exact Or.inr (hψ τ hτ)
  · rcases hne with hne | hne
    · exact Or.inl (hne.image φ)
    · exact Or.inr (hne.image ψ)

theorem joinVertexMap_joinVertexMap [DecidableEq E] [DecidableEq F]
    {K₁ : Geometry.SimplicialComplex ℝ E} {L₁ : Geometry.SimplicialComplex ℝ F} {φ : E → E'}
    {φ' : E' → E} {ψ : F → F'} {ψ' : F' → F} (hφ : ∀ s ∈ K₁.faces, ∀ v ∈ s, φ' (φ v) = v)
    (hψ : ∀ t ∈ L₁.faces, ∀ w ∈ t, ψ' (ψ w) = w) {s : Finset (E × F × ℝ)}
    (hs : s ∈ (joinComplex K₁ L₁).faces) {z : E × F × ℝ} (hz : z ∈ s) :
    joinVertexMap φ' ψ' (joinVertexMap φ ψ z) = z := by
  obtain ⟨σ, τ, hσ, hτ, -, rfl⟩ := hs
  rcases Finset.mem_union.mp hz with h | h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    have hσK : σ ∈ K₁.faces := by
      rcases hσ with rfl | hσ
      · exact absurd hv (Finset.notMem_empty v)
      · exact hσ
    rw [joinVertexMap_joinFst, joinVertexMap_joinFst, hφ σ hσK v hv]
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
    have hτL : τ ∈ L₁.faces := by
      rcases hτ with rfl | hτ
      · exact absurd hw (Finset.notMem_empty w)
      · exact hτ
    rw [joinVertexMap_joinSnd, joinVertexMap_joinSnd, hψ τ hτL w hw]

theorem IsGlueIso.joinComplex [DecidableEq E] [DecidableEq E'] [DecidableEq F] [DecidableEq F']
    {K₁ : Geometry.SimplicialComplex ℝ E} {K₂ : Geometry.SimplicialComplex ℝ E'}
    {L₁ : Geometry.SimplicialComplex ℝ F} {L₂ : Geometry.SimplicialComplex ℝ F'} {φ : E → E'}
    {φ' : E' → E} {ψ : F → F'} {ψ' : F' → F} (h₁ : IsGlueIso K₁ K₂ φ φ')
    (h₂ : IsGlueIso L₁ L₂ ψ ψ') :
    IsGlueIso (joinComplex K₁ L₁) (joinComplex K₂ L₂) (joinVertexMap φ ψ)
      (joinVertexMap φ' ψ') where
  image₁ _ hs := image_joinVertexMap_mem_joinComplex h₁.image₁ h₂.image₁ hs
  image₂ _ ht := image_joinVertexMap_mem_joinComplex h₁.image₂ h₂.image₂ ht
  left _ hs _ hz := joinVertexMap_joinVertexMap h₁.left h₂.left hs hz
  right _ ht _ hu := joinVertexMap_joinVertexMap h₁.right h₂.right ht hu

theorem isGlueIso_id [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) :
    IsGlueIso K K id id where
  image₁ _ hs := by rwa [Finset.image_id]
  image₂ _ hs := by rwa [Finset.image_id]
  left _ _ _ _ := rfl
  right _ _ _ _ := rfl

theorem IsSubdivision.joinComplex_right [DecidableEq E] [DecidableEq F]
    {K : Geometry.SimplicialComplex ℝ E} {L' L : Geometry.SimplicialComplex ℝ F}
    (h : IsSubdivision L' L) : IsSubdivision (joinComplex K L') (joinComplex K L) := by
  refine ⟨by rw [joinComplex_space, joinComplex_space, h.space_eq], ?_⟩
  rintro t ⟨σ, τ', hσ, hτ', hne, rfl⟩
  rcases hτ' with rfl | hτ'
  · exact ⟨_, union_image_mem_joinComplex K L hσ (Or.inl rfl) hne, subset_rfl⟩
  obtain ⟨τ, hτ, hsub⟩ := h.exists_face_subset hτ'
  refine ⟨σ.image (joinFst E F) ∪ τ.image (joinSnd E F),
    union_image_mem_joinComplex K L hσ (Or.inr hτ) (Or.inr (L.nonempty_of_mem_faces hτ)), ?_⟩
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro u hu
  rcases Finset.mem_union.mp (Finset.mem_coe.mp hu) with h' | h'
  · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_union_left _ h'))
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h'
    exact convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right)
      (joinSnd_mem_convexHull_image (hsub (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw))))

theorem IsSubdivision.joinComplex [DecidableEq E] [DecidableEq F]
    {K' K : Geometry.SimplicialComplex ℝ E} {L' L : Geometry.SimplicialComplex ℝ F}
    (hK : IsSubdivision K' K) (hL : IsSubdivision L' L) :
    IsSubdivision (joinComplex K' L') (joinComplex K L) :=
  (IsSubdivision.joinComplex_left K L' hK).trans (IsSubdivision.joinComplex_right hL)

end DifferentialGeometry.Topology.PiecewiseLinear
