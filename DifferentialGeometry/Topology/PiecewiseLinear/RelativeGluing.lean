import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionTransport

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section Neighborhood

variable [DecidableEq E] [DecidableEq F]

theorem glueHeight_eq_one_of_mem_glued₁ {B A : Geometry.SimplicialComplex ℝ E}
    (hdis : Disjoint B.space A.space) (ψ : E → F) {z : E × F × ℝ}
    (hz : z ∈ (glued₁ B A ψ).space) : glueHeight E F z = 1 := by
  obtain ⟨s, ⟨t, ht, rfl⟩, hz⟩ := (glued₁ B A ψ).mem_space_iff.mp hz
  have hvert : ∀ v ∈ t.image (glueEmbed₁ A ψ), glueHeight E F v = 1 := by
    rintro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    have hxA : {x} ∉ A.faces := fun hh => Set.disjoint_left.mp hdis
      (B.convexHull_subset_space ht (subset_convexHull ℝ _ hx))
      (A.convexHull_subset_space hh (subset_convexHull ℝ _ (by simp)))
    simp only [glueEmbed₁, glueHeight, LinearMap.comp_apply, LinearMap.snd_apply, if_neg hxA]
  obtain ⟨w, _, hw, rfl⟩ := mem_convexHull_iff_exists_weights.mp hz
  rw [map_sum]
  calc
    _ = ∑ v ∈ t.image (glueEmbed₁ A ψ), w v := Finset.sum_congr rfl fun v hv => by
      rw [map_smul, hvert v hv, smul_eq_mul, mul_one]
    _ = 1 := hw

theorem regularNeighborhoodIn_gluedComplex_subset
    (K₁ A₁ B : Geometry.SimplicialComplex ℝ E) (K₂ A₂ : Geometry.SimplicialComplex ℝ F)
    {ψ : E → F} {ψ' : F → E} (h : IsGlueIso A₁ A₂ ψ ψ')
    (hA₂ : A₂.faces ⊆ K₂.faces)
    (hfull : ∀ s ∈ K₁.faces, (∀ v ∈ s, {v} ∈ A₁.faces) → s ∈ A₁.faces)
    (hdis : Disjoint B.space A₁.space) :
    (regularNeighborhoodIn (gluedComplex K₁ K₂ h hA₂ hfull) (glued₁ B A₁ ψ).space).space ⊆
      (glued₁ K₁ A₁ ψ).space ∩ (glueFst E F) ⁻¹' (regularNeighborhoodIn K₁ B.space).space := by
  intro z hz
  obtain ⟨s, ⟨_, t, ht, hst, y, hyt, hyB⟩, hzs⟩ :=
    (regularNeighborhoodIn (gluedComplex K₁ K₂ h hA₂ hfull) (glued₁ B A₁ ψ).space).mem_space_iff.mp hz
  have hzt := convexHull_mono (Finset.coe_subset.mpr hst) hzs
  rcases ht with ht | ht
  · have hzG := (glued₁ K₁ A₁ ψ).convexHull_subset_space ht hzt
    refine ⟨hzG, ?_⟩
    obtain ⟨u, hu, rfl⟩ := ht
    have hpre (x : E × F × ℝ)
        (hx : x ∈ convexHull ℝ ((u.image (glueEmbed₁ A₁ ψ) : Finset (E × F × ℝ)) : Set (E × F × ℝ))) :
        glueFst E F x ∈ convexHull ℝ (u : Set E) := by
      rw [← image_convexHull_simplicialMap K₁ _ hu (glueEmbed₁_injective A₁ ψ).injOn] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      rwa [glueFst_simplicialMap K₁ A₁ ψ (K₁.convexHull_subset_space hu ha)]
    exact (regularNeighborhoodIn K₁ B.space).convexHull_subset_space
      ⟨hu, u, hu, Finset.Subset.refl u, glueFst E F y, hpre y hyt,
        glueFst_mem_of_mem_glued₁ B A₁ ψ hyB⟩ (hpre z hzt)
  · have hnonpos := glueHeight_nonpos_of_mem_glued₂ K₂ A₂ ψ'
      ((glued₂ K₂ A₂ ψ').convexHull_subset_space ht hyt)
    rw [glueHeight_eq_one_of_mem_glued₁ hdis ψ hyB] at hnonpos
    exact (not_le_of_gt zero_lt_one hnonpos).elim

end Neighborhood

theorem PLPieceIn.exists_glue_with_regularNeighborhood {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [DecidableEq E] [DecidableEq F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space X]
    {Y₁ Y₂ : Set X} (T₁ : PLPieceIn E n X Y₁) (T₂ : PLPieceIn F n X Y₂)
    {A₁ : Geometry.SimplicialComplex ℝ E} {A₂ : Geometry.SimplicialComplex ℝ F}
    {ψ : E → F} {ψ' : F → E} (h : IsGlueIso A₁ A₂ ψ ψ')
    (hA₁ : A₁.faces ⊆ T₁.complex.faces) (hA₂ : A₂.faces ⊆ T₂.complex.faces)
    (hcompat : ∀ x ∈ A₁.space, T₂.map (simplicialMap A₁ ψ x) = T₁.map x)
    (hoverlap : Y₁ ∩ Y₂ = T₁.map '' A₁.space)
    (B : Geometry.SimplicialComplex ℝ E) (hB : B.faces ⊆ T₁.complex.faces)
    (hdis : Disjoint B.space A₁.space) :
    ∃ T : PLPieceIn (E × F × ℝ) n X (Y₁ ∪ Y₂),
      ∃ B' : Geometry.SimplicialComplex ℝ (E × F × ℝ),
        ∃ φ : E → E × F × ℝ, ∃ φ' : E × F × ℝ → E,
          B'.faces ⊆ T.complex.faces ∧ IsGlueIso B B' φ φ' ∧
            (∀ x ∈ B.space, T.map (simplicialMap B φ x) = T₁.map x) ∧
              T.map '' (regularNeighborhoodIn T.complex B'.space).space ⊆
                T₁.map '' (regularNeighborhoodIn T₁.complex B.space).space := by
  classical
  have := T₁.finite_faces.to_subtype
  have := (T₁.finite_faces.subset hA₁).to_subtype
  obtain ⟨R, hR, hfinR, hBR, hA₁R, hfull⟩ :=
    exists_isSubdivision_extension_of_disjoint hB hA₁ hdis (IsSubdivision.refl A₁)
  let T₁' := T₁.subdivide R hR hfinR
  obtain ⟨T, hTcomplex, hTmap⟩ := T₁'.exists_glue_of_full T₂ h hA₁R hA₂ hfull hcompat hoverlap
  let φ := glueEmbed₁ A₁ ψ
  have hπ : ∀ s ∈ B.faces, ∀ v ∈ s, glueFst E F (φ v) = v := fun _ _ _ _ => rfl
  let B' := embedComplex B φ (glueFst E F) hπ
  obtain ⟨φ', hiso⟩ := exists_isGlueIso_simplicialImage B φ
    (fun _ hs => affineIndependent_image_of_leftInverse B φ (glueFst E F) hπ hs)
    (injOn_simplicialMap_of_leftInverse B φ (glueFst E F) hπ)
  refine ⟨T, B', φ, φ', ?_, hiso, ?_, ?_⟩
  · intro s hs
    rw [hTcomplex]
    obtain ⟨t, ht, rfl⟩ := hs
    exact Or.inl ⟨t, hBR ht, rfl⟩
  · intro x hx
    have hxR := space_mono_of_faces_subset hBR hx
    have heq : simplicialMap B φ x = simplicialMap R φ x := by
      obtain ⟨s, hs, hxs⟩ := B.mem_space_iff.mp hx
      rw [simplicialMap_eq_of_mem B φ hs hxs, simplicialMap_eq_of_mem R φ (hBR hs) hxs]
    rw [hTmap, heq]
    change gluedMap R A₁ ψ T₁.map T₂.map (simplicialMap R (glueEmbed₁ A₁ ψ) x) = T₁.map x
    rw [gluedMap_of_mem _ _ _ _ _ (simplicialMap_mem_glued₁ R A₁ ψ hxR),
      glueFst_simplicialMap R A₁ ψ hxR]
  · rintro y ⟨z, hz, rfl⟩
    rw [hTcomplex] at hz
    have hbound := regularNeighborhoodIn_gluedComplex_subset R A₁ B T₂.complex A₂ h hA₂ hfull hdis hz
    refine ⟨glueFst E F z, regularNeighborhoodIn_space_subset_of_isSubdivision hR B.space hbound.2, ?_⟩
    rw [hTmap]
    exact (gluedMap_of_mem R A₁ ψ T₁.map T₂.map hbound.1).symm

theorem PLPieceIn.exists_glue_preserving_subcomplex {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [DecidableEq E] [DecidableEq F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space X]
    {Y₁ Y₂ : Set X} (T₁ : PLPieceIn E n X Y₁) (T₂ : PLPieceIn F n X Y₂)
    {A₁ : Geometry.SimplicialComplex ℝ E} {A₂ : Geometry.SimplicialComplex ℝ F}
    {ψ : E → F} {ψ' : F → E} (h : IsGlueIso A₁ A₂ ψ ψ')
    (hA₁ : A₁.faces ⊆ T₁.complex.faces) (hA₂ : A₂.faces ⊆ T₂.complex.faces)
    (hcompat : ∀ x ∈ A₁.space, T₂.map (simplicialMap A₁ ψ x) = T₁.map x)
    (hoverlap : Y₁ ∩ Y₂ = T₁.map '' A₁.space)
    (B : Geometry.SimplicialComplex ℝ E) (hB : B.faces ⊆ T₁.complex.faces)
    (hdis : Disjoint B.space A₁.space) :
    ∃ T : PLPieceIn (E × F × ℝ) n X (Y₁ ∪ Y₂),
      ∃ B' : Geometry.SimplicialComplex ℝ (E × F × ℝ),
        ∃ φ : E → E × F × ℝ, ∃ φ' : E × F × ℝ → E,
          B'.faces ⊆ T.complex.faces ∧ IsGlueIso B B' φ φ' ∧
            ∀ x ∈ B.space, T.map (simplicialMap B φ x) = T₁.map x := by
  obtain ⟨T, B', φ, φ', hB', hiso, hmap, -⟩ :=
    T₁.exists_glue_with_regularNeighborhood T₂ h hA₁ hA₂ hcompat hoverlap B hB hdis
  exact ⟨T, B', φ, φ', hB', hiso, hmap⟩

end DifferentialGeometry.Topology.PiecewiseLinear
