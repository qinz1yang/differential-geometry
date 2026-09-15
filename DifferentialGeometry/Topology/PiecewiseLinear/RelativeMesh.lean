import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSubdivision

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_isSubdivision_diam_lt_preserving_subcomplex
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hA : A.faces ⊆ K.faces)
    {N : ℕ} (hcard : ∀ s ∈ K.faces, s.card ≤ N + 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      A.faces ⊆ R.faces ∧ ∀ s ∈ R.faces,
        convexHull ℝ (s : Set E) ⊆ (regularNeighborhoodIn K A.space).space ∨
          diam (convexHull ℝ (s : Set E)) < ε := by
  classical
  let B := restrict K A.spaceᶜ
  have := (restrict_faces_finite K A.spaceᶜ).to_subtype
  obtain ⟨B', hB', hfinB', -, hdiam⟩ :=
    exists_isSubdivision_diam_lt B (fun s hs => hcard s hs.1) hε
  have := hfinB'.to_subtype
  have hAB : Disjoint A.space B.space := by
    rw [Set.disjoint_left]
    exact fun x hx hxb => restrict_space_subset K A.spaceᶜ hxb hx
  obtain ⟨R, hR, hfin, hAR, -, -, hfaces⟩ :=
    exists_isSubdivision_extension_of_disjoint_with_face_control hA
      (restrict_faces_subset K A.spaceᶜ) hAB hB'
  refine ⟨R, hR, hfin, hAR, fun s hs => ?_⟩
  rcases hfaces s hs with hsB | ⟨t, ht, htB, hst⟩
  · exact Or.inr (hdiam s hsB)
  · left
    have hmeet : (convexHull ℝ (t : Set E) ∩ A.space).Nonempty := by
      by_contra h
      apply htB
      refine ⟨ht, fun x hx hxA => h ⟨x, hx, hxA⟩⟩
    exact hst.trans ((regularNeighborhoodIn K A.space).convexHull_subset_space
      ⟨ht, t, ht, Finset.Subset.refl t, hmeet⟩)

theorem regularNeighborhoodIn_space_subset_cthickening
    (K : Geometry.SimplicialComplex ℝ E) {A D S : Set E} {ε r : ℝ}
    (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hfaces : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ D ∨
      diam (convexHull ℝ (s : Set E)) < ε)
    (hDS : D ⊆ S) (hAS : A ⊆ cthickening r S) :
    (regularNeighborhoodIn K A).space ⊆ cthickening (ε + r) S := by
  intro x hx
  obtain ⟨s, ⟨_, t, ht, hst, y, hyt, hyA⟩, hxs⟩ :=
    (regularNeighborhoodIn K A).mem_space_iff.mp hx
  have hxt := convexHull_mono (Finset.coe_subset.mpr hst) hxs
  rcases hfaces t ht with htD | hdiam
  · exact self_subset_cthickening S (hDS (htD hxt))
  · apply cthickening_cthickening_subset hε hr S
    exact mem_cthickening_of_dist_le x y ε (cthickening r S) (hAS hyA)
      ((dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull ℝ).isBounded hxt hyt).trans
        hdiam.le)

end DifferentialGeometry.Topology.PiecewiseLinear
