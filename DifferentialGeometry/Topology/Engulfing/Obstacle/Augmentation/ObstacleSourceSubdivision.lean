import DifferentialGeometry.Topology.Engulfing.Obstacle.Approximation.ObstacleApproximation
import DifferentialGeometry.Topology.SimplicialComplex.Refinement.InverseSubdivision

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n d p : ℕ} {K L : SimplicialComplex ℝ E}
  {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
  {f : C(K.space, EuclideanSpace ℝ (Fin n))}

def ObstacleAugmentation.sourceHomeomorph (a : ObstacleAugmentation K L T f d p) :
    K.space ≃ₜ a.sourceImage.space :=
  (IsEmbedding.subtypeVal.comp a.sourceMap_embedding.isEmbedding).toHomeomorph.trans
    (Homeomorph.setCongr a.sourceImage_space.symm)

omit [DecidableEq E] in
@[simp] theorem ObstacleAugmentation.sourceHomeomorph_apply
    (a : ObstacleAugmentation K L T f d p) (x : K.space) :
    (a.sourceHomeomorph x).val = (a.sourceMap x).val := by
  classical
  exact rfl

omit [DecidableEq E] in
theorem ObstacleAugmentation.sourceHomeomorph_affine_inverse
    (a : ObstacleAugmentation K L T f d p) :
    hasAffineInverseFaceParents K a.sourceImage a.sourceHomeomorph := by
  classical
  intro s hs
  obtain ⟨t, ht, B, hB⟩ := a.sourceImage_sections s hs
  refine ⟨t, ht, B, ?_⟩
  intro x hx
  obtain ⟨z, hzB, hzt, hqz⟩ := hB x.val hx
  have he : a.sourceHomeomorph z = x := Subtype.ext hqz
  have hei : a.sourceHomeomorph.symm x = z := by
    rw [← he, a.sourceHomeomorph.symm_apply_apply]
  exact ⟨(congrArg Subtype.val hei).trans hzB, hzB ▸ hzt⟩

theorem ObstacleAugmentation.exists_source_subdivision
    (a : ObstacleAugmentation K L T f d p) (N : ℕ) :
    ∃ r : EuclideanSpace ℝ (Fin a.ambientDimension) → E,
      ∃ R : SimplicialComplex ℝ E,
      let P := barycentricSubdivisionIter a.sourceImage N
      R.faces.Finite ∧ R.space = K.space ∧ simplicialRefines R K ∧
      (∀ s ∈ R.faces, s.card ≤ d + 1) ∧
      (∀ y : a.sourceImage.space, r y.val = (a.sourceHomeomorph.symm y).val) ∧
      (∀ s ∈ P.faces, ∃ B : EuclideanSpace ℝ (Fin a.ambientDimension) →ᵃ[ℝ] E,
        EqOn r B (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))))) ∧
      InjOn r P.space ∧
      R.faces = {s | ∃ t ∈ P.faces, t.image r = s} ∧
      (∀ s ∈ P.faces,
        (fun x : K.space => (a.sourceMap x).val) ''
          {x | x.val ∈ convexHull ℝ (s.image r : Set E)} =
            convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension)))) := by
  let P := barycentricSubdivisionIter a.sourceImage N
  have hsource : a.sourceImage.faces.Finite := a.joint_finite.subset a.sourceImage_faces
  have hP : P.faces.Finite := barycentricSubdivisionIter_finite_faces a.sourceImage hsource N
  have hspace : P.space = a.sourceImage.space := barycentricSubdivisionIter_space a.sourceImage N
  obtain ⟨r, R, hR, hRs, href, hr, hraff, hri, hRf, hfaces⟩ :=
    exists_inverse_geometric_subdivision K a.sourceImage P a.sourceHomeomorph
      a.sourceHomeomorph_affine_inverse hP (barycentricSubdivisionIter_refines a.sourceImage N) hspace
  refine ⟨r, R, hR, hRs, href, ?_, hr, hraff, hri, hRf, ?_⟩
  · intro s hs
    rw [hRf] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact Finset.card_image_le.trans
      (barycentricSubdivisionIter_face_card_le a.sourceImage a.sourceImage_dimension N t ht)
  · intro s hs
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hfaces s hs x).mp hx
    · intro y hy
      have hyS : y ∈ a.sourceImage.space := hspace.subset (P.convexHull_subset_space hs hy)
      let y' : a.sourceImage.space := ⟨y, hyS⟩
      refine ⟨a.sourceHomeomorph.symm y', ?_, ?_⟩
      · apply (hfaces s hs _).mpr
        simpa only [a.sourceHomeomorph.apply_symm_apply] using hy
      · exact congrArg Subtype.val (a.sourceHomeomorph.apply_symm_apply y')

end

end DifferentialGeometry.Topology.Engulfing
