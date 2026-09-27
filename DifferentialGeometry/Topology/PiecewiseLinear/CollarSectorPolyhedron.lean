import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffineSimplicial
import DifferentialGeometry.Topology.PiecewiseLinear.BallComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsPiecewiseAffineOn.isPolyhedron_inter_preimage_of_isPolyhedron {f : E → F} {P : Set E}
    (hf : IsPiecewiseAffineOn f P) (hP : IsPolyhedron P) {Q : Set F} (hQ : IsPolyhedron Q) :
    IsPolyhedron (P ∩ f ⁻¹' Q) := by
  classical
  obtain ⟨K, hKfin, hKspace⟩ := hP.exists_simplicialComplex
  have _ : Finite K.faces := hKfin.to_subtype
  have hfK : IsPiecewiseAffineOn f K.space := by rw [hKspace]; exact hf
  obtain ⟨K', hsub, hK'fin, hAff⟩ := hfK.exists_isSubdivision_affineOn_faces K
  have _ : Finite K'.faces := hK'fin.to_subtype
  have hK'space : K'.space = P := by rw [hsub.space_eq, hKspace]
  have hcover : P ∩ f ⁻¹' Q =
      ⋃ s : K'.faces, (convexHull ℝ ((s : Finset E) : Set E) ∩ f ⁻¹' Q) := by
    rw [← iUnion_inter, ← hK'space, Geometry.SimplicialComplex.space, biUnion_eq_iUnion]
  rw [hcover]
  refine IsPolyhedron.iUnion fun s => ?_
  obtain ⟨A, hA⟩ := hAff s s.2
  have heq : convexHull ℝ ((s : Finset E) : Set E) ∩ f ⁻¹' Q
      = convexHull ℝ ((s : Finset E) : Set E) ∩ A ⁻¹' Q := by
    ext x
    constructor
    · rintro ⟨hx, hxQ⟩
      exact ⟨hx, by rw [mem_preimage, ← hA hx]; exact hxQ⟩
    · rintro ⟨hx, hxQ⟩
      exact ⟨hx, by rw [mem_preimage, hA hx]; exact hxQ⟩
  rw [heq]
  obtain ⟨κ, hκ, Dcell, hDcell, rfl⟩ := hQ
  have := hκ
  rw [preimage_iUnion, inter_iUnion]
  exact IsPolyhedron.iUnion fun j =>
    ((isHPolytope_convexHull_of_affineIndependent _ (K'.indep s.2)).inter_preimage
      (hDcell j) A).isPolyhedron

theorem exists_polyhedral_sectors_of_isPiecewiseAffineOn
    {Δ' D J Jc : Set (EuclideanSpace ℝ (Fin 2))}
    (hΔ' : IsPLBall 2 Δ') (hD : IsPLBall 2 D)
    {ρ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hρ : IsPiecewiseAffineOn ρ (Δ' \ interior D))
    (hJ : IsPolyhedron J) (hJc : IsPolyhedron Jc)
    (hmaps : MapsTo ρ (Δ' \ interior D) (J ∪ Jc)) :
    ∃ A B : Set (EuclideanSpace ℝ (Fin 2)), IsPolyhedron A ∧ IsPolyhedron B ∧
      A ∪ B = Δ' \ interior D ∧ MapsTo ρ A J ∧ MapsTo ρ B Jc ∧
      IsPiecewiseAffineOn ρ A ∧ IsPiecewiseAffineOn ρ B := by
  have hann : IsPolyhedron (Δ' \ interior D) :=
    hΔ'.isPolyhedron.sdiff_interior_of_isPLBall hD
  refine ⟨(Δ' \ interior D) ∩ ρ ⁻¹' J, (Δ' \ interior D) ∩ ρ ⁻¹' Jc,
    hρ.isPolyhedron_inter_preimage_of_isPolyhedron hann hJ,
    hρ.isPolyhedron_inter_preimage_of_isPolyhedron hann hJc, ?_,
    fun _ hx => hx.2, fun _ hx => hx.2, ?_, ?_⟩
  · apply Subset.antisymm
    · exact union_subset inter_subset_left inter_subset_left
    · intro x hx
      rcases hmaps hx with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  · exact hρ.mono_of_isPolyhedron
      (hρ.isPolyhedron_inter_preimage_of_isPolyhedron hann hJ) inter_subset_left
  · exact hρ.mono_of_isPolyhedron
      (hρ.isPolyhedron_inter_preimage_of_isPolyhedron hann hJc) inter_subset_left

end DifferentialGeometry.Topology.PiecewiseLinear
