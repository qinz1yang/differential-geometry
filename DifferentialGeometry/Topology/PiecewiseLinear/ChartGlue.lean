import DifferentialGeometry.Topology.PiecewiseLinear.RelativeGluing
import DifferentialGeometry.Topology.PiecewiseLinear.ChartPiece

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem PLPieceIn.image_inter_preimage {Y : Set X} (T : PLPieceIn E n X Y) (V : Set X) :
    T.map '' (T.complex.space ∩ T.map ⁻¹' V) = Y ∩ V := by
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨hx, hxV⟩, rfl⟩
    exact ⟨T.bijOn.mapsTo hx, hxV⟩
  · rintro y ⟨hy, hyV⟩
    obtain ⟨x, hx, rfl⟩ := T.bijOn.surjOn hy
    exact ⟨x, ⟨hx, hyV⟩, rfl⟩

theorem PLPieceIn.isPolyhedron_inter_preimage_chart [FiniteDimensional ℝ E] [T2Space X]
    {Y : Set X} (T : PLPieceIn E n X Y) (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsHPolytope C) (hCe : C ⊆ e.target) :
    IsPolyhedron (T.complex.space ∩ T.map ⁻¹' (e.symm '' C)) := by
  have hfin := T.finite_faces.to_subtype
  have himg : e.symm '' C = e.source ∩ e ⁻¹' C := e.symm_image_eq_source_inter_preimage hCe
  have heq : T.complex.space ∩ T.map ⁻¹' e.source ∩ (e ∘ T.map) ⁻¹' C =
      T.complex.space ∩ T.map ⁻¹' (e.symm '' C) := by
    rw [himg]
    ext x
    simp only [mem_inter_iff, mem_preimage, Function.comp_apply]
    tauto
  have hclosed : IsClosed (e.symm '' C) :=
    (hC.isPolyhedron.isCompact.image_of_continuousOn (e.continuousOn_symm.mono hCe)).isClosed
  have hcomp : IsCompact (T.complex.space ∩ T.map ⁻¹' (e.symm '' C)) :=
    (PiecewiseLinear.isPolyhedron_space T.complex).isCompact.of_isClosed_subset
      (T.continuousOn.preimage_isClosed_of_isClosed
        (PiecewiseLinear.isPolyhedron_space T.complex).isClosed hclosed) inter_subset_left
  rw [← heq] at hcomp ⊢
  exact isPolyhedron_inter_preimage_of_isCompact (T.isPiecewiseAffineOn_chart e he) hC hcomp

open Classical in
theorem PLPieceIn.exists_glue_chart_with_regularNeighborhood [FiniteDimensional ℝ E] [DecidableEq E]
    [T2Space X]
    [HasGroupoid X (plGroupoid n)] {Y : Set X} (T : PLPieceIn E n X Y)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsHPolytope C) (hCe : C ⊆ e.target)
    (B : Geometry.SimplicialComplex ℝ E) (hB : B.faces ⊆ T.complex.faces)
    (hdis : Disjoint (regularNeighborhoodIn T.complex B.space).space
      (T.complex.space ∩ T.map ⁻¹' (e.symm '' C))) :
    ∃ T' : PLPieceIn (E × EuclideanSpace ℝ (Fin n) × ℝ) n X (Y ∪ e.symm '' C),
      ∃ B' : Geometry.SimplicialComplex ℝ (E × EuclideanSpace ℝ (Fin n) × ℝ),
        ∃ φ : E → E × EuclideanSpace ℝ (Fin n) × ℝ,
          ∃ φ' : E × EuclideanSpace ℝ (Fin n) × ℝ → E,
            B'.faces ⊆ T'.complex.faces ∧ IsGlueIso B B' φ φ' ∧
              (∀ x ∈ B.space, T'.map (simplicialMap B φ x) = T.map x) ∧
                T'.map '' (regularNeighborhoodIn T'.complex B'.space).space ⊆
                  T.map '' (regularNeighborhoodIn T.complex B.space).space := by
  have hfinK := T.finite_faces.to_subtype
  have himg : e.symm '' C = e.source ∩ e ⁻¹' C := e.symm_image_eq_source_inter_preimage hCe
  have hApoly := T.isPolyhedron_inter_preimage_chart e he hC hCe
  obtain ⟨K₁, hK₁, hfin₁, hBK₁, hA₁space⟩ :=
    exists_isSubdivision_restrict_space_preserving_subcomplex T.complex B hB hApoly
      inter_subset_left hdis
  have hBQ : Disjoint B.space (T.complex.space ∩ T.map ⁻¹' (e.symm '' C)) :=
    hdis.mono_left fun x hx => mem_of_mem_nhdsWithin (space_mono_of_faces_subset hB hx)
      (regularNeighborhoodIn_mem_nhdsWithin T.complex B.space hx)
  have hfinK₁ := hfin₁.to_subtype
  have hfinA₁ :=
    (restrict_faces_finite K₁ (T.complex.space ∩ T.map ⁻¹' (e.symm '' C))).to_subtype
  have hplA : IsPiecewiseAffineOn (e ∘ T.map)
      (restrict K₁ (T.complex.space ∩ T.map ⁻¹' (e.symm '' C))).space := by
    rw [hA₁space]
    refine (T.isPiecewiseAffineOn_chart e he).mono_of_isPolyhedron hApoly ?_
    rintro x ⟨hx, hxV⟩
    rw [mem_preimage, himg] at hxV
    exact ⟨hx, hxV.1⟩
  obtain ⟨A₂, hA₂, hfinA₂, hAff⟩ := hplA.exists_isSubdivision_affineOn_faces _
  have hfinA₂' := hfinA₂.to_subtype
  have hA₂space : A₂.space = T.complex.space ∩ T.map ⁻¹' (e.symm '' C) :=
    hA₂.space_eq.trans hA₁space
  have hBA₁ : Disjoint B.space
      (restrict K₁ (T.complex.space ∩ T.map ⁻¹' (e.symm '' C))).space := hA₁space.symm ▸ hBQ
  obtain ⟨K₂, hK₂, hfinK₂, hBK₂, hA₂K₂, -⟩ :=
    exists_isSubdivision_extension_of_disjoint hBK₁ (restrict_faces_subset K₁ _) hBA₁ hA₂
  have hfinK₂' := hfinK₂.to_subtype
  have hinjA : InjOn (e ∘ T.map) A₂.space := by
    rw [hA₂space]
    refine e.injOn.comp (T.bijOn.injOn.mono inter_subset_left) ?_
    rintro x ⟨hx, hxV⟩
    rw [mem_preimage, himg] at hxV
    exact hxV.1
  have hsimpA : EqOn (simplicialMap A₂ (e ∘ T.map)) (e ∘ T.map) A₂.space :=
    simplicialMap_eq_of_forall_affineOn A₂ _ hAff
  have hinjB : InjOn (simplicialMap A₂ (e ∘ T.map)) A₂.space := fun x hx y hy hxy =>
    hinjA hx hy (by rw [← hsimpA hx, ← hsimpA hy]; exact hxy)
  have hindB : ∀ s ∈ A₂.faces,
      AffineIndependent ℝ ((↑) : {u // u ∈ s.image (e ∘ T.map)} → EuclideanSpace ℝ (Fin n)) :=
    fun s hs => by
      obtain ⟨Af, hAf⟩ := hAff s hs
      have himgs : s.image (e ∘ T.map) = s.image Af :=
        Finset.image_congr fun v hv => hAf (subset_convexHull ℝ _ hv)
      rw [himgs]
      refine affineIndependent_image_of_injOn_convexHull Af (A₂.indep hs) fun x hx y hy hxy =>
        hinjA (A₂.convexHull_subset_space hs hx) (A₂.convexHull_subset_space hs hy) ?_
      rw [hAf hx, hAf hy]
      exact hxy
  obtain ⟨φ', hφ'⟩ := exists_isGlueIso_simplicialImage A₂ (e ∘ T.map) hindB hinjB
  have hfinB := (simplicialImage_faces_finite A₂ (e ∘ T.map) hindB hinjB).to_subtype
  have hBspace : (simplicialImage A₂ (e ∘ T.map) hindB hinjB).space =
      e '' (T.map '' (T.complex.space ∩ T.map ⁻¹' (e.symm '' C))) := by
    rw [simplicialImage_space, hsimpA.image_eq, hA₂space, image_comp]
  have hBC : (simplicialImage A₂ (e ∘ T.map) hindB hinjB).space ⊆
      (chartPiece e he hC hCe).complex.space := by
    rw [hBspace, chartPiece_space, T.image_inter_preimage, himg]
    rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
    exact hy.2
  have hfinKc := (chartPiece e he hC hCe).finite_faces.to_subtype
  obtain ⟨Kc₁, hKc₁, hfinc₁, hB₂⟩ := exists_isSubdivision_restrict_isSubdivision
    (chartPiece e he hC hCe).complex (simplicialImage A₂ (e ∘ T.map) hindB hinjB) hBC
  have hfinKc₁ := hfinc₁.to_subtype
  have hfinB₂ :=
    (restrict_faces_finite Kc₁ (simplicialImage A₂ (e ∘ T.map) hindB hinjB).space).to_subtype
  obtain ⟨A₃, hA₃, hfinA₃, hiso⟩ := hφ'.exists_isSubdivision _ hB₂
  have hfinA₃' := hfinA₃.to_subtype
  have hBA₂ : Disjoint B.space A₂.space := hA₂space.symm ▸ hBQ
  obtain ⟨K₃, hK₃, hfinK₃, hBK₃, hA₃K₃, -⟩ :=
    exists_isSubdivision_extension_of_disjoint hBK₂ hA₂K₂ hBA₂ hA₃
  have hcompat : ∀ x ∈ A₃.space,
      ((chartPiece e he hC hCe).subdivide Kc₁ hKc₁ hfinc₁).map
        (simplicialMap A₃ (simplicialMap A₂ (e ∘ T.map)) x) =
      (T.subdivide _ (hK₃.trans (hK₂.trans hK₁)) hfinK₃).map x := by
    intro x hx
    change e.symm (simplicialMap A₃ (simplicialMap A₂ (e ∘ T.map)) x) = T.map x
    have hxA₂ : x ∈ A₂.space := hA₃.space_eq ▸ hx
    have haff₃ : ∀ s ∈ A₃.faces, ∃ Af : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
        EqOn (simplicialMap A₂ (e ∘ T.map)) Af (convexHull ℝ (s : Set E)) := fun s hs => by
      obtain ⟨s', hs', hss'⟩ := hA₃.exists_face_subset hs
      obtain ⟨Af, hAf⟩ := exists_affineMap_eqOn_simplicialMap A₂ (e ∘ T.map) hs'
      exact ⟨Af, hAf.mono hss'⟩
    rw [simplicialMap_eq_of_forall_affineOn A₃ _ haff₃ hx, hsimpA hxA₂]
    have hxV : T.map x ∈ e.symm '' C :=
      (hA₂space ▸ hxA₂ : x ∈ T.complex.space ∩ T.map ⁻¹' (e.symm '' C)).2
    rw [himg] at hxV
    exact e.left_inv hxV.1
  have hoverlap : Y ∩ e.symm '' C =
      (T.subdivide _ (hK₃.trans (hK₂.trans hK₁)) hfinK₃).map '' A₃.space := by
    change Y ∩ e.symm '' C = T.map '' A₃.space
    rw [hA₃.space_eq, hA₂space, T.image_inter_preimage]
  obtain ⟨T', B', φ, φ', hB', hiso', hmap, hneigh⟩ :=
    (T.subdivide K₃ (hK₃.trans (hK₂.trans hK₁)) hfinK₃).exists_glue_with_regularNeighborhood
    ((chartPiece e he hC hCe).subdivide Kc₁ hKc₁ hfinc₁) hiso hA₃K₃
    (restrict_faces_subset Kc₁ _) hcompat hoverlap B hBK₃ (hA₃.space_eq.symm ▸ hBA₂)
  exact ⟨T', B', φ, φ', hB', hiso', hmap, hneigh.trans
    (image_mono (regularNeighborhoodIn_space_subset_of_isSubdivision (hK₃.trans (hK₂.trans hK₁)) B.space))⟩

open Classical in
theorem PLPieceIn.exists_glue_chart_preserving_subcomplex [FiniteDimensional ℝ E] [T2Space X]
    [HasGroupoid X (plGroupoid n)] {Y : Set X} (T : PLPieceIn E n X Y)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsHPolytope C) (hCe : C ⊆ e.target)
    (B : Geometry.SimplicialComplex ℝ E) (hB : B.faces ⊆ T.complex.faces)
    (hdis : Disjoint (regularNeighborhoodIn T.complex B.space).space
      (T.complex.space ∩ T.map ⁻¹' (e.symm '' C))) :
    ∃ T' : PLPieceIn (E × EuclideanSpace ℝ (Fin n) × ℝ) n X (Y ∪ e.symm '' C),
      ∃ B' : Geometry.SimplicialComplex ℝ (E × EuclideanSpace ℝ (Fin n) × ℝ),
        ∃ φ : E → E × EuclideanSpace ℝ (Fin n) × ℝ,
          ∃ φ' : E × EuclideanSpace ℝ (Fin n) × ℝ → E,
            B'.faces ⊆ T'.complex.faces ∧ IsGlueIso B B' φ φ' ∧
              ∀ x ∈ B.space, T'.map (simplicialMap B φ x) = T.map x := by
  obtain ⟨T', B', φ, φ', hB', hiso, hmap, -⟩ :=
    T.exists_glue_chart_with_regularNeighborhood e he hC hCe B hB hdis
  exact ⟨T', B', φ, φ', hB', hiso, hmap⟩

theorem PLPieceIn.exists_glue_chart [FiniteDimensional ℝ E] [T2Space X]
    [HasGroupoid X (plGroupoid n)] {Y : Set X} (T : PLPieceIn E n X Y)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsHPolytope C) (hCe : C ⊆ e.target) :
    Nonempty (PLPieceIn (E × EuclideanSpace ℝ (Fin n) × ℝ) n X (Y ∪ e.symm '' C)) := by
  classical
  have hdis : Disjoint (regularNeighborhoodIn T.complex
      (⊥ : Geometry.SimplicialComplex ℝ E).space).space
      (T.complex.space ∩ T.map ⁻¹' (e.symm '' C)) := by
    rw [Set.disjoint_left]
    intro x hx _
    obtain ⟨s, ⟨_, t, _, _, y, _, hy⟩, _⟩ :=
      (regularNeighborhoodIn T.complex (⊥ : Geometry.SimplicialComplex ℝ E).space).mem_space_iff.mp hx
    simp only [space_bot, Set.mem_empty_iff_false] at hy
  obtain ⟨T', -⟩ := T.exists_glue_chart_preserving_subcomplex e he hC hCe ⊥
    (fun _ hs => hs.elim) hdis
  exact ⟨T'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
