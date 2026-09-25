import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCollarExtensionPrism
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_complement_of_surface_collar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L) {a b : ℝ} (hab : a < b)
    {ρ : E × ℝ → E} {W : Set E} (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc a b) W)
    (hWK : W ⊆ K.space) (htrace : W ∩ (boundaryComplex 3 K).space = L.space) :
    ∃ A R : Geometry.SimplicialComplex ℝ E,
      A.faces.Finite ∧ R.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 A ∧
      IsCombinatorialManifoldWithBoundary 3 R ∧ A.space = W ∧
      R.space = closure (K.space \ W) ∧
      (boundaryComplex 3 A).space =
        ρ '' (L.space ×ˢ {a, b} ∪ (boundaryComplex 2 L).space ×ˢ Icc a b) ∧
      W ∩ R.space ⊆ (boundaryComplex 3 R).space ∧
      (boundaryComplex 3 K).space ∩ R.space ⊆ (boundaryComplex 3 R).space := by
  have hprod := (isPolyhedron_space L).prod (isHPolytope_Icc (a := a) (b := b)).isPolyhedron
  have hW : IsPolyhedron W := by
    rw [← hρ.image_eq]
    exact hprod.image_of_isPiecewiseAffineOn hρ.isPiecewiseAffineOn hρ.bijOn.injOn
  obtain ⟨T, hTfin, hTspace⟩ := hprod.exists_simplicialComplex
  let _ : Finite T.faces := hTfin.to_subtype
  have hT := isCombinatorialManifoldWithBoundary_surface_prism hL hab T hTspace
  obtain ⟨K', hK', hK'fin, hK'W⟩ := exists_isSubdivision_restrict_space K hW hWK
  let _ : Finite K'.faces := hK'fin.to_subtype
  let A := PiecewiseLinear.restrict K' W
  let _ : Finite A.faces := (restrict_faces_finite K' W).to_subtype
  have hAspace : A.space = W := hK'W
  have hρT : IsPLHomeomorphOn ρ T.space A.space := by
    rw [hTspace, hAspace]
    exact hρ
  have hA : IsCombinatorialManifoldWithBoundary 3 A := hT.of_isPLHomeomorphOn hρT
  let D := PiecewiseLinear.restrict A (boundaryComplex 3 K').space
  let _ : Finite D.faces := (restrict_faces_finite A _).to_subtype
  have hDspace : D.space = L.space := by
    rw [show D.space = (PiecewiseLinear.restrict A (boundaryComplex 3 K').space).space from rfl,
      restrict_space_eq_inter_of_faces_subset K' A (boundaryComplex 3 K')
        (restrict_faces_subset K' W) (boundaryComplex_faces_subset 3 K'), hAspace,
      boundaryComplex_space_of_isSubdivision K K' hK hK', htrace]
  have hD : IsCombinatorialManifoldWithBoundary 2 D := by
    apply hL.of_isPLHomeomorphOn (f := id)
    rw [hDspace]
    exact (isPolyhedron_space L).isPLHomeomorphOn_id
  let R := subcomplexGeneratedBy K' A.facesᶜ
  let _ : Finite R.faces := (subcomplexGeneratedBy_faces_finite K' A.facesᶜ).to_subtype
  have hR : IsCombinatorialManifoldWithBoundary 3 R :=
    (hK.of_isSubdivision hK').complement K' A hA (restrict_faces_subset K' W) hD
  have hRspace : R.space = closure (K.space \ W) := by
    have h := closure_space_sdiff_space_eq_subcomplexGeneratedBy K' K' A Subset.rfl
      (restrict_faces_subset K' W)
    rw [hK'.space_eq, hAspace] at h
    exact h.symm
  have hAK : A.space ⊆ K.space := hAspace ▸ hWK
  have hRK : R.space ⊆ K.space := by
    rw [hRspace]
    exact closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  refine ⟨A, R, Set.toFinite A.faces, Set.toFinite R.faces, hA, hR, hAspace, hRspace,
    ?_, ?_, ?_⟩
  · exact (boundaryComplex_space_of_isPLHomeomorphOn T A hT hρT).trans
      (congrArg (fun S => ρ '' S) (boundaryComplex_space_surface_prism
        (d := fun x y => Classical.propDecidable (x = y)) hL hab T hTspace))
  · have h := inter_space_complement_subset_boundaryComplex K A R hK hA hAK hR
      (by rw [hAspace]; exact hRspace)
    simpa only [hAspace] using h
  · intro x hx
    exact inter_boundaryComplex_space_subset_of_subset K R hK hR hRK ⟨hx.2, hx.1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
