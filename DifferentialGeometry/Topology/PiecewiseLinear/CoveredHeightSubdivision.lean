/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HeightSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.LinkUnionSection

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_triangulation_union_with_face_cover_and_halfSpace_faces
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {D : Set E} (hD : IsPolyhedron D)
    (a : E →ᵃ[ℝ] ℝ) (r : ℝ) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧ R.space = K.space ∪ D ∧
      IsSubdivision (restrict R K.space) K ∧ (restrict R D).space = D ∧
      (∀ s ∈ R.faces, s ∈ (restrict R K.space).faces ∨ s ∈ (restrict R D).faces) ∧
      ∀ s ∈ R.faces, convexHull ℝ (s : Set E) ⊆ {x | a x ≤ r} ∨
        convexHull ℝ (s : Set E) ⊆ {x | r ≤ a x} := by
  classical
  obtain ⟨ι, hι, B, hB, hDB⟩ := hD
  let _ : Finite ι := hι
  let A : K.faces ⊕ ι → Set E :=
    Sum.elim (fun s => convexHull ℝ ((s : Finset E) : Set E)) B
  have hA : ∀ j, IsHPolytope (A j) := by
    rintro (s | i)
    · exact isHPolytope_convexHull_of_affineIndependent _ (K.indep s.2)
    · exact hB i
  let C : (K.faces ⊕ ι) × Bool → Set E := fun j =>
    if j.2 then A j.1 ∩ {x | r ≤ a x} else A j.1 ∩ {x | a x ≤ r}
  have hC : ∀ j, IsHPolytope (C j) := by
    rintro ⟨j, b⟩
    cases b
    · exact (hA j).inter_affine_le a r
    · simpa only [C, Bool.true_eq, ↓reduceIte, AffineMap.coe_neg, Pi.neg_apply,
        neg_le_neg_iff] using (hA j).inter_affine_le (-a) (-r)
  have hCA : ∀ j, C j ⊆ A j.1 := by
    rintro ⟨j, b⟩
    cases b <;> exact inter_subset_left
  have hcoverA : ∀ j, ∀ x ∈ A j, ∃ b, x ∈ C (j, b) := by
    intro j x hx
    rcases le_total (a x) r with h | h
    · exact ⟨false, hx, h⟩
    · exact ⟨true, hx, h⟩
  obtain ⟨R, hRfin, hRspace, hcover⟩ :=
    exists_simplicialComplex_of_forall_isHPolytope C hC
  have hAR : ∀ j, A j = ⋃ s ∈ {s ∈ R.faces | convexHull ℝ (s : Set E) ⊆ A j},
      convexHull ℝ (s : Set E) := by
    intro j
    apply Subset.antisymm
    · intro x hx
      obtain ⟨b, hxb⟩ := hcoverA j x hx
      rw [hcover (j, b)] at hxb
      obtain ⟨s, ⟨hs, hsC⟩, hxs⟩ := mem_iUnion₂.mp hxb
      exact mem_iUnion₂.mpr ⟨s, ⟨hs, hsC.trans (hCA (j, b))⟩, hxs⟩
    · exact iUnion₂_subset fun s hs => hs.2
  have hARsub : ∀ j, A j ⊆ R.space := by
    intro j
    rw [hAR j]
    exact iUnion₂_subset fun s hs => R.convexHull_subset_space hs.1
  have hspace : R.space = K.space ∪ D := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨⟨j, b⟩, hxC⟩ := mem_iUnion.mp (hRspace.subset hx)
      have hxA := hCA (j, b) hxC
      rcases j with s | i
      · exact Or.inl (K.convexHull_subset_space s.2 hxA)
      · exact Or.inr (hDB.symm.subset (mem_iUnion.mpr ⟨i, hxA⟩))
    · rintro x (hx | hx)
      · obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
        exact hARsub (Sum.inl ⟨s, hs⟩) hxs
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp (hDB.subset hx)
        exact hARsub (Sum.inr i) hxi
  have hrestrictD : (restrict R D).space = D := by
    apply restrict_space_of_eq_biUnion
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp (hDB.subset hx)
      change x ∈ A (Sum.inr i) at hxi
      rw [hAR (Sum.inr i)] at hxi
      obtain ⟨s, ⟨hs, hsA⟩, hxs⟩ := mem_iUnion₂.mp hxi
      have hAD : A (Sum.inr i) ⊆ D := (subset_iUnion B i).trans hDB.symm.subset
      exact mem_iUnion₂.mpr ⟨s, ⟨hs, hsA.trans hAD⟩, hxs⟩
    · exact iUnion₂_subset fun s hs => hs.2
  have hcarrier (s : Finset E) (hs : s ∈ R.faces) :
      ∃ j b, convexHull ℝ (s : Set E) ⊆ C (j, b) := by
    have hx := centroid_mem_openSimplex (R.nonempty_of_mem_faces hs)
    have hxR := R.convexHull_subset_space hs (openSimplex_subset_convexHull s hx)
    obtain ⟨⟨j, b⟩, hxC⟩ := mem_iUnion.mp (hRspace.subset hxR)
    rw [hcover (j, b)] at hxC
    obtain ⟨t, ⟨ht, htC⟩, hxt⟩ := mem_iUnion₂.mp hxC
    exact ⟨j, b, (convexHull_mono (Finset.coe_subset.mpr
      (face_subset_of_mem_openSimplex_of_mem_convexHull R hs ht hx hxt))).trans htC⟩
  have hface : ∀ s ∈ R.faces,
      s ∈ (restrict R K.space).faces ∨ s ∈ (restrict R D).faces := by
    intro s hs
    obtain ⟨j, b, hsC⟩ := hcarrier s hs
    have hsA := hsC.trans (hCA (j, b))
    rcases j with t | i
    · exact Or.inl ⟨hs, hsA.trans (K.convexHull_subset_space t.2)⟩
    · exact Or.inr ⟨hs, hsA.trans
        ((subset_iUnion B i).trans hDB.symm.subset)⟩
  refine ⟨R, hRfin, hspace,
    restrict_isSubdivision K (fun s hs => hAR (Sum.inl ⟨s, hs⟩)),
    hrestrictD, hface, ?_⟩
  intro s hs
  obtain ⟨j, b, hsC⟩ := hcarrier s hs
  cases b
  · exact Or.inl (hsC.trans inter_subset_right)
  · exact Or.inr (hsC.trans inter_subset_right)

end DifferentialGeometry.Topology.PiecewiseLinear
