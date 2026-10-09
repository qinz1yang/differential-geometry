/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Gluing
import DifferentialGeometry.Topology.PiecewiseLinear.RegularNeighborhood
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

theorem IsGlueIso.trans {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [DecidableEq G]
    {C : Geometry.SimplicialComplex ℝ G} {ψ : F → G} {ψ' : G → F}
    (h : IsGlueIso A B φ φ') (h' : IsGlueIso B C ψ ψ') :
    IsGlueIso A C (ψ ∘ φ) (φ' ∘ ψ') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [← Finset.image_image]
    exact h'.image₁ _ (h.image₁ s hs)
  · intro s hs
    rw [← Finset.image_image]
    exact h.image₂ _ (h'.image₂ s hs)
  · intro s hs v hv
    simp only [Function.comp_apply]
    rw [h'.left _ (h.image₁ s hs) (φ v) (Finset.mem_image_of_mem φ hv), h.left s hs v hv]
  · intro s hs v hv
    simp only [Function.comp_apply]
    rw [h.right _ (h'.image₂ s hs) (ψ' v) (Finset.mem_image_of_mem ψ' hv), h'.right s hs v hv]

theorem IsGlueIso.simplicialMap_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (h : IsGlueIso A B φ φ') (ψ : F → G) {x : E} (hx : x ∈ A.space) :
    simplicialMap B ψ (simplicialMap A φ x) = simplicialMap A (ψ ∘ φ) x := by
  obtain ⟨s, hs, hxs⟩ := A.mem_space_iff.mp hx
  have hinj : ∀ v ∈ s, ∀ w ∈ s, φ v = φ w → v = w := by
    intro v hv w hw hvw
    rw [← h.left s hs v hv, ← h.left s hs w hw, hvw]
  let μ : F → ℝ := weights s x ∘ φ'
  have hμ (v : E) (hv : v ∈ s) : μ (φ v) = weights s x v :=
    congrArg (weights s x) (h.left s hs v hv)
  have hsum : ∑ v ∈ s.image φ, μ v = 1 := by
    rw [Finset.sum_image hinj]
    exact (Finset.sum_congr rfl fun v hv => hμ v hv).trans (sum_weights hxs)
  have hvec : ∑ v ∈ s.image φ, μ v • v = simplicialMap A φ x := by
    rw [Finset.sum_image hinj, simplicialMap_eq_of_mem A φ hs hxs]
    exact Finset.sum_congr rfl fun v hv => by rw [hμ v hv]
  have hmem := simplicialMap_mem_convexHull_image A φ hs hxs
  rw [simplicialMap_eq_of_mem B ψ (h.image₁ s hs) hmem,
    simplicialMap_eq_of_mem A (ψ ∘ φ) hs hxs, Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun v hv => by
    rw [weights_eq (B.indep (h.image₁ s hs)) hmem hsum hvec _ (Finset.mem_image_of_mem φ hv), hμ v
        hv]
    rfl

theorem IsGlueIso.faces_eq_simplicialImageFaces (h : IsGlueIso A B φ φ') :
    B.faces = simplicialImageFaces A φ := by
  ext t
  constructor
  · intro ht
    refine ⟨t.image φ', h.image₂ t ht, ?_⟩
    rw [Finset.image_image]
    have heq : t.image (φ ∘ φ') = t.image id :=
      Finset.image_congr fun v hv => h.right t ht v hv
    rw [heq, Finset.image_id]
  · rintro ⟨s, hs, rfl⟩
    exact h.image₁ s hs

theorem IsGlueIso.exists_subcomplex (h : IsGlueIso A B φ φ')
    (C : Geometry.SimplicialComplex ℝ E) (hC : C.faces ⊆ A.faces) :
    ∃ D : Geometry.SimplicialComplex ℝ F, D.faces ⊆ B.faces ∧ IsGlueIso C D φ φ' := by
  have hCB : simplicialImageFaces C φ ⊆ B.faces := by
    rintro t ⟨s, hs, rfl⟩
    exact h.image₁ s (hC hs)
  let D : Geometry.SimplicialComplex ℝ F :=
    { faces := simplicialImageFaces C φ
      isRelLowerSet_faces := simplicialImageFaces_isRelLowerSet C φ
      indep := fun hs => B.indep (hCB hs)
      inter_subset_convexHull := fun hs ht => B.inter_subset_convexHull (hCB hs) (hCB ht) }
  refine ⟨D, hCB, fun s hs => ⟨s, hs, rfl⟩, ?_,
    fun s hs v hv => h.left s (hC hs) v hv, fun s hs v hv => h.right s (hCB hs) v hv⟩
  rintro t ⟨s, hs, rfl⟩
  rw [Finset.image_image]
  have heq : s.image (φ' ∘ φ) = s.image id :=
    Finset.image_congr fun v hv => h.left s (hC hs) v hv
  rwa [heq, Finset.image_id]

theorem IsGlueIso.image_regularNeighborhoodIn (h : IsGlueIso A B φ φ') {C : Set E}
    (hCA : C ⊆ A.space) :
    simplicialMap A φ '' (regularNeighborhoodIn A C).space =
      (regularNeighborhoodIn B (simplicialMap A φ '' C)).space := by
  apply Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    obtain ⟨s, ⟨_, t, ht, hst, y, hyt, hyC⟩, hxs⟩ := (regularNeighborhoodIn A C).mem_space_iff.mp hx
    have hxt := convexHull_mono (Finset.coe_subset.mpr hst) hxs
    exact (regularNeighborhoodIn B (simplicialMap A φ '' C)).convexHull_subset_space
      ⟨h.image₁ t ht, t.image φ, h.image₁ t ht, Finset.Subset.refl _,
        simplicialMap A φ y, simplicialMap_mem_convexHull_image A φ ht hyt, y, hyC, rfl⟩
      (simplicialMap_mem_convexHull_image A φ ht hxt)
  · intro z hz
    obtain ⟨s, ⟨_, t, ht, hst, y, hyt, hyC⟩, hzs⟩ :=
      (regularNeighborhoodIn B (simplicialMap A φ '' C)).mem_space_iff.mp hz
    have hzt := convexHull_mono (Finset.coe_subset.mpr hst) hzs
    obtain ⟨u, hu, rfl⟩ := h.faces_eq_simplicialImageFaces.subset ht
    have himage := image_convexHull_simplicialMap A φ hu
      (injOn_of_injOn_simplicialMap A φ h.bijOn_left.injOn hu)
    obtain ⟨x, hxu, hfx⟩ := himage.symm.subset hzt
    obtain ⟨w, hwu, hfw⟩ := himage.symm.subset hyt
    obtain ⟨a, ha, hfa⟩ := hyC
    have haw : a = w := h.bijOn_left.injOn (hCA ha) (A.convexHull_subset_space hu hwu)
      (hfa.trans hfw.symm)
    exact ⟨x, (regularNeighborhoodIn A C).convexHull_subset_space
      ⟨hu, u, hu, Finset.Subset.refl u, w, hwu, haw ▸ ha⟩ hxu, hfx⟩

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
