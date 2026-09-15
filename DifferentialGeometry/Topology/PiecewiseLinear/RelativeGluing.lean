import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionTransport

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem PLPieceIn.exists_glue_preserving_subcomplex {n : ℕ} {X : Type*} [TopologicalSpace X]
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
            ∀ x ∈ B.space, T.map (simplicialMap B φ x) = T₁.map x := by
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
  refine ⟨T, B', φ, φ', ?_, hiso, ?_⟩
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

end DifferentialGeometry.Topology.PiecewiseLinear
