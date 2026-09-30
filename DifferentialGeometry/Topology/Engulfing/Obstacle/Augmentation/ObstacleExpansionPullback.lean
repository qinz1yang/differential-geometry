import DifferentialGeometry.Topology.Engulfing.Obstacle.Augmentation.ObstacleExpansionCompatibility

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n d p : ℕ} {K L : SimplicialComplex ℝ E}
  {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
  {f : C(K.space, EuclideanSpace ℝ (Fin n))}

theorem ObstacleAugmentation.exists_source_subdivision_preserving_expansions
    (a : ObstacleAugmentation K L T f d p) (ha : a.preservesSourceExpansions) :
    ∃ r : EuclideanSpace ℝ (Fin a.ambientDimension) → E,
      ∃ R : SimplicialComplex ℝ E,
      R.faces.Finite ∧ R.space = K.space ∧ simplicialRefines R K ∧
      (∀ s ∈ R.faces, s.card ≤ d + 1) ∧
      (∀ y : a.sourceImage.space, r y.val = (a.sourceHomeomorph.symm y).val) ∧
      (∀ s ∈ a.sourceImage.faces, ∃ B : EuclideanSpace ℝ (Fin a.ambientDimension) →ᵃ[ℝ] E,
        EqOn r B (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))))) ∧
      InjOn r a.sourceImage.space ∧
      R.faces = {s | ∃ t ∈ a.sourceImage.faces, t.image r = s} ∧
      (∀ s ∈ a.sourceImage.faces,
        (fun x : K.space => (a.sourceMap x).val) ''
          {x | x.val ∈ convexHull ℝ (s.image r : Set E)} =
            convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension)))) ∧
      ∀ A C, C ⊆ K.space → FiniteSimplexExpansionIn K A C →
        FiniteSimplexExpansionIn R A C := by
  obtain ⟨r, R, hR, hRs, href, hdim, hr, hra, hri, hRf, hfaces⟩ := a.exists_source_subdivision 0
  change (∀ s ∈ a.sourceImage.faces, ∃ B : EuclideanSpace ℝ (Fin a.ambientDimension) →ᵃ[ℝ] E,
    EqOn r B (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))))) at hra
  change InjOn r a.sourceImage.space at hri
  change R.faces = {s | ∃ t ∈ a.sourceImage.faces, t.image r = s} at hRf
  have hrsource (x : K.space) : r (a.sourceMap x).val = x.val := by
    have h := hr (a.sourceHomeomorph x)
    simpa only [a.sourceHomeomorph.symm_apply_apply, ObstacleAugmentation.sourceHomeomorph_apply] using h
  have himage (A : Set E) (hA : A ⊆ K.space) :
      r '' ((fun x : K.space => (a.sourceMap x).val) '' (Subtype.val ⁻¹' A)) = A := by
    rw [image_image]
    ext y
    constructor
    · rintro ⟨x, hx, he⟩
      change r (a.sourceMap x).val = y at he
      rw [hrsource x] at he
      exact he ▸ hx
    · intro hy
      exact ⟨⟨y, hA hy⟩, hy, hrsource ⟨y, hA hy⟩⟩
  refine ⟨r, R, hR, hRs, href, hdim, hr, hra, hri, hRf, hfaces, ?_⟩
  intro A C hC he
  have hS : (fun x : K.space => (a.sourceMap x).val) '' (Subtype.val ⁻¹' C) ⊆
      a.sourceImage.space := by
    rintro _ ⟨x, hx, rfl⟩
    exact a.sourceImage_space.symm.subset (mem_range_self x)
  have h := ((ha A C hC he).restrict a.sourceImage_faces hS).image (Q := R) hS r hri hra
    (fun s hs => by rw [hRf]; exact ⟨s, hs, rfl⟩)
  rwa [himage A (he.subset.trans hC), himage C hC] at h

end

end DifferentialGeometry.Topology.Engulfing
