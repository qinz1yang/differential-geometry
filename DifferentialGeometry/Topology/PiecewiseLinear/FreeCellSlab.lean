import DifferentialGeometry.Topology.PiecewiseLinear.SlabFaceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.PrismArcPatch
import DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMonotonicity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isPLBall_slab_patch_of_isFreeDiskCell
    (K A : Geometry.SimplicialComplex ℝ E) (hAK : A.faces ⊆ K.faces)
    {T : Finset E} (hT : T ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    {a b r : ℝ} (hab : a < b) (hr : r ∈ Icc a b)
    (hvertices : ∀ v ∈ T, ℓ v < a ∨ b < ℓ v)
    {L : Geometry.SimplicialComplex ℝ E} {cells : Finset (Set E)}
    (hL : IsPLDiskDecomposition L cells)
    (hboundary : (convexHull ℝ (T : Set E) ∩ {x | ℓ x = r}) ∩ (boundaryComplex 2 L).space =
      (convexHull ℝ (T : Set E) ∩ {x | ℓ x = r}) ∩ A.space)
    (hC : convexHull ℝ (T : Set E) ∩ {x | ℓ x = r} ∈ cells)
    (hfree : IsFreeDiskCell L (convexHull ℝ (T : Set E) ∩ {x | ℓ x = r})) :
    IsPLBall 2 ((convexHull ℝ (T : Set E) ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b}) ∩
      ((A.space ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b}) ∪ (K.space ∩ {x | ℓ x = a ∨ ℓ x = b}))) := by
  classical
  let _ : Finite L.faces := hL.finite_faces.to_subtype
  let C := convexHull ℝ (T : Set E) ∩ {x | ℓ x = r}
  let J := restrict L C
  let _ : Finite J.faces := (restrict_faces_finite L C).to_subtype
  have hJspace : J.space = C := hL.cell_space C hC
  have hJ : IsPLBall 2 J.space := hJspace.symm ▸ hL.cell_isPLBall C hC
  have hboundarySub := inter_boundaryComplex_space_subset L J
    hL.isPLBall.isCombinatorialManifoldWithBoundary hJ.isCombinatorialManifoldWithBoundary
    (restrict_faces_subset L C)
  have hbandBoundary : C ∩ A.space ⊆ (boundaryComplex 2 J).space := by
    intro x hx
    apply hboundarySub
    exact ⟨hJspace.symm ▸ hx.1, (hboundary.symm.subset hx).2⟩
  have hfreeEq : (boundaryComplex 2 J).space ∩ (boundaryComplex 2 L).space = C ∩ A.space := by
    apply Subset.antisymm
    · intro x hx
      exact hboundary.subset ⟨hJspace.subset (boundaryComplex_space_subset 2 J hx.1), hx.2⟩
    · intro x hx
      exact ⟨hbandBoundary hx, (hboundary.symm.subset hx).2⟩
  have harc : IsPLBall 1 (C ∩ A.space) := by
    change IsPLBall 1 ((boundaryComplex 2 J).space ∩ (boundaryComplex 2 L).space) at hfree
    rwa [hfreeEq] at hfree
  let P := convexHull ℝ (T : Set E) ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b}
  let B := C ×ˢ {a, b} ∪ (C ∩ A.space) ×ˢ Icc a b
  have hB : IsPLBall 2 B := by
    simpa only [hJspace] using isPLBall_prism_ends_union_arc J hJ harc hbandBoundary hab
  have hBQ : B ⊆ C ×ˢ Icc a b := by
    rintro x (hx | hx)
    · rcases hx.2 with hxa | hxb
      · exact ⟨hx.1, hxa.symm ▸ ⟨le_rfl, hab.le⟩⟩
      · exact ⟨hx.1, hxb.symm ▸ ⟨hab.le, le_rfl⟩⟩
    · exact ⟨hx.1.1, hx.2⟩
  obtain ⟨f, hf, hcontrol⟩ := exists_isPLHomeomorphOn_face_slab_prism K hT ℓ hr hvertices
  have hpreimage : P ∩ f ⁻¹' B = P ∩
      ((A.space ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b}) ∪ (K.space ∩ {x | ℓ x = a ∨ ℓ x = b})) := by
    ext x
    constructor
    · rintro ⟨hx, hfx⟩
      obtain ⟨hsub, hlow, hhigh⟩ := hcontrol x hx
      refine ⟨hx, ?_⟩
      rcases hfx with hends | hband
      · exact Or.inr ⟨K.convexHull_subset_space hT hx.1,
          hends.2.elim (fun h => Or.inl (hlow.mp h)) (fun h => Or.inr (hhigh.mp h))⟩
      · exact Or.inl ⟨(hsub A hAK).mp hband.1.2, hx.2⟩
    · rintro ⟨hx, hside | hends⟩
      · obtain ⟨hsub, -, -⟩ := hcontrol x hx
        have hy := hf.bijOn.mapsTo hx
        exact ⟨hx, Or.inr ⟨⟨hy.1, (hsub A hAK).mpr hside.1⟩, hy.2⟩⟩
      · obtain ⟨-, hlow, hhigh⟩ := hcontrol x hx
        have hy := hf.bijOn.mapsTo hx
        exact ⟨hx, Or.inl ⟨hy.1,
          hends.2.elim (fun h => Or.inl (hlow.mpr h)) (fun h => Or.inr (hhigh.mpr h))⟩⟩
  have hpoly : IsPolyhedron (P ∩ f ⁻¹' B) := hf.isPolyhedron_preimage hB.isPolyhedron hBQ
  have hrestrict := hf.restrict hpoly inter_subset_left
  have himage : f '' (P ∩ f ⁻¹' B) = B := by
    rw [image_inter_preimage, hf.image_eq, inter_eq_right.mpr hBQ]
  rw [himage] at hrestrict
  have hball := hB.of_isPLHomeomorphOn hrestrict.symm
  rwa [hpreimage] at hball

end DifferentialGeometry.Topology.PiecewiseLinear
