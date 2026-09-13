import DifferentialGeometry.Topology.PiecewiseLinear.Gluing
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section Inverse

variable [DecidableEq E] [DecidableEq F] (K : Geometry.SimplicialComplex ℝ E) (φ : E → F)
  (hind : ∀ σ ∈ K.faces, AffineIndependent ℝ ((↑) : {u // u ∈ σ.image φ} → F))
  (hinj : InjOn (simplicialMap K φ) K.space)

theorem exists_isGlueIso_simplicialImage :
    ∃ φ' : F → E, IsGlueIso K (simplicialImage K φ hind hinj) φ φ' := by
  let V : Set E := {v | {v} ∈ K.faces}
  have hV : ∀ v ∈ V, v ∈ K.space := fun v hv =>
    K.convexHull_subset_space hv (subset_convexHull ℝ _ (by simp))
  have hφV : InjOn φ V := by
    intro v hv w hw hvw
    refine hinj (hV v hv) (hV w hw) ?_
    rw [simplicialMap_vertex K φ hv, simplicialMap_vertex K φ hw, hvw]
  have hmemV : ∀ σ ∈ K.faces, ∀ v ∈ σ, v ∈ V := fun σ hσ v hv =>
    K.down_closed hσ (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hψφ : ∀ σ ∈ K.faces, ∀ v ∈ σ, Function.invFunOn φ V (φ v) = v := fun σ hσ v hv =>
    hφV.leftInvOn_invFunOn (hmemV σ hσ v hv)
  refine ⟨Function.invFunOn φ V, fun σ hσ => ⟨σ, hσ, rfl⟩, ?_, hψφ, ?_⟩
  · rintro t ⟨σ, hσ, rfl⟩
    rw [Finset.image_image]
    have : σ.image (Function.invFunOn φ V ∘ φ) = σ.image id :=
      Finset.image_congr fun v hv => hψφ σ hσ v hv
    rw [this, Finset.image_id]
    exact hσ
  · rintro t ⟨σ, hσ, rfl⟩ u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    rw [hψφ σ hσ v hv]

end Inverse

section Transport

variable [DecidableEq E] [DecidableEq F] {A : Geometry.SimplicialComplex ℝ E}
  {B : Geometry.SimplicialComplex ℝ F} {φ : E → F} {φ' : F → E}

theorem IsGlueIso.simplicialMap_simplicialMap_left (h : IsGlueIso A B φ φ') {x : E}
    (hx : x ∈ A.space) : simplicialMap B φ' (simplicialMap A φ x) = x :=
  simplicialMap_simplicialMap A B φ φ' h.image₁ h.left hx

theorem IsGlueIso.simplicialMap_simplicialMap_right (h : IsGlueIso A B φ φ') {y : F}
    (hy : y ∈ B.space) : simplicialMap A φ (simplicialMap B φ' y) = y :=
  simplicialMap_simplicialMap B A φ' φ h.image₂ h.right hy

theorem IsGlueIso.mapsTo_left (h : IsGlueIso A B φ φ') :
    MapsTo (simplicialMap A φ) A.space B.space :=
  simplicialMap_mapsTo A B φ h.image₁

theorem IsGlueIso.mapsTo_right (h : IsGlueIso A B φ φ') :
    MapsTo (simplicialMap B φ') B.space A.space :=
  simplicialMap_mapsTo B A φ' h.image₂

theorem IsGlueIso.bijOn_left (h : IsGlueIso A B φ φ') :
    BijOn (simplicialMap A φ) A.space B.space :=
  InvOn.bijOn ⟨fun _ hx => h.simplicialMap_simplicialMap_left hx,
    fun _ hy => h.simplicialMap_simplicialMap_right hy⟩ h.mapsTo_left h.mapsTo_right

theorem IsGlueIso.bijOn_right (h : IsGlueIso A B φ φ') :
    BijOn (simplicialMap B φ') B.space A.space :=
  InvOn.bijOn ⟨fun _ hy => h.simplicialMap_simplicialMap_right hy,
    fun _ hx => h.simplicialMap_simplicialMap_left hx⟩ h.mapsTo_right h.mapsTo_left

theorem IsGlueIso.image_left (h : IsGlueIso A B φ φ') :
    simplicialMap A φ '' A.space = B.space :=
  h.bijOn_left.image_eq

theorem IsGlueIso.image_right (h : IsGlueIso A B φ φ') :
    simplicialMap B φ' '' B.space = A.space :=
  h.bijOn_right.image_eq

theorem IsGlueIso.injOn_right (h : IsGlueIso A B φ φ') : InjOn (simplicialMap B φ') B.space :=
  h.bijOn_right.injOn

theorem IsGlueIso.exists_isSubdivision [FiniteDimensional ℝ F] (h : IsGlueIso A B φ φ')
    (B₂ : Geometry.SimplicialComplex ℝ F) (hB₂ : IsSubdivision B₂ B) [Finite B₂.faces] :
    ∃ A₂ : Geometry.SimplicialComplex ℝ E, IsSubdivision A₂ A ∧ A₂.faces.Finite ∧
      IsGlueIso A₂ B₂ (simplicialMap A φ) (simplicialMap B φ') := by
  have haff : ∀ t ∈ B₂.faces, ∃ Af : F →ᵃ[ℝ] E,
      EqOn (simplicialMap B φ') Af (convexHull ℝ (t : Set F)) := fun t ht => by
    obtain ⟨t', ht', htt'⟩ := hB₂.exists_face_subset ht
    obtain ⟨Af, hAf⟩ := exists_affineMap_eqOn_simplicialMap B φ' ht'
    exact ⟨Af, hAf.mono htt'⟩
  have hsimp : EqOn (simplicialMap B₂ (simplicialMap B φ')) (simplicialMap B φ') B₂.space :=
    simplicialMap_eq_of_forall_affineOn B₂ _ haff
  have hinjB : InjOn (simplicialMap B φ') B₂.space := by
    rw [hB₂.space_eq]
    exact h.injOn_right
  have hinj : InjOn (simplicialMap B₂ (simplicialMap B φ')) B₂.space :=
    fun y hy y' hy' hyy' => hinjB hy hy' (by rw [← hsimp hy, ← hsimp hy']; exact hyy')
  have hind : ∀ t ∈ B₂.faces,
      AffineIndependent ℝ ((↑) : {u // u ∈ t.image (simplicialMap B φ')} → E) := fun t ht => by
    obtain ⟨Af, hAf⟩ := haff t ht
    have himg : t.image (simplicialMap B φ') = t.image Af :=
      Finset.image_congr fun u hu => hAf (subset_convexHull ℝ _ hu)
    rw [himg]
    refine affineIndependent_image_of_injOn_convexHull Af (B₂.indep ht) fun y hy y' hy' hyy' =>
      hinjB (B₂.convexHull_subset_space ht hy) (B₂.convexHull_subset_space ht hy') ?_
    rw [hAf hy, hAf hy']
    exact hyy'
  have hmemB : ∀ t ∈ B₂.faces, ∀ u ∈ t, u ∈ B.space := fun t ht u hu =>
    hB₂.space_eq ▸ B₂.convexHull_subset_space ht (subset_convexHull ℝ _ (Finset.mem_coe.mpr hu))
  refine ⟨simplicialImage B₂ (simplicialMap B φ') hind hinj, ⟨?_, ?_⟩,
    simplicialImage_faces_finite _ _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [simplicialImage_space, hsimp.image_eq, hB₂.space_eq, h.image_right]
  · rintro s ⟨t, ht, rfl⟩
    obtain ⟨t', ht', htt'⟩ := hB₂.exists_face_subset ht
    refine ⟨t'.image φ', h.image₂ t' ht', ?_⟩
    rw [← image_convexHull_simplicialMap B₂ _ ht (injOn_of_injOn_simplicialMap B₂ _ hinj ht),
      ← image_convexHull_simplicialMap B φ' ht'
        (injOn_of_injOn_simplicialMap B φ' h.injOn_right ht')]
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, htt' hy, (hsimp (B₂.convexHull_subset_space ht hy)).symm⟩
  · rintro s ⟨t, ht, rfl⟩
    rw [Finset.image_image]
    have himg : t.image (simplicialMap A φ ∘ simplicialMap B φ') = t.image id :=
      Finset.image_congr fun u hu => h.simplicialMap_simplicialMap_right (hmemB t ht u hu)
    rw [himg, Finset.image_id]
    exact ht
  · intro t ht
    exact ⟨t, ht, rfl⟩
  · rintro s ⟨t, ht, rfl⟩ v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    rw [h.simplicialMap_simplicialMap_right (hmemB t ht u hu)]
  · intro t ht u hu
    exact h.simplicialMap_simplicialMap_right (hmemB t ht u hu)

end Transport

end DifferentialGeometry.Topology.PiecewiseLinear
