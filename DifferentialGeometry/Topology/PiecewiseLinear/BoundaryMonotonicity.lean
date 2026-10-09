/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphereBallInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem inter_boundaryComplex_faces_subset {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.faces ⊆ K.faces) :
    A.faces ∩ (boundaryComplex (n + 1) K).faces ⊆ (boundaryComplex (n + 1) A).faces := by
  classical
  rintro s ⟨hsA, hsK⟩
  have hbd := (hK.mem_boundaryComplex_faces_iff K).mp hsK
  obtain ⟨k, hk⟩ : ∃ k, s.card = k + 1 :=
    ⟨s.card - 1, by have := Finset.card_pos.mpr (A.nonempty_of_mem_faces hsA); omega⟩
  have hkn : k ≤ n := by omega
  have hdim : n + 1 - s.card = n - k := by omega
  have hlinkK : IsPLBall (n - k) (SimplicialComplex.geometricLink K s).space := by
    simpa only [hdim] using hbd.2.2
  have hlinkSub : (SimplicialComplex.geometricLink A s).space ⊆
      (SimplicialComplex.geometricLink K s).space := by
    apply space_mono_of_faces_subset
    intro t ht
    exact ⟨ht.1, ht.2.1, hAK ht.2.2⟩
  rcases hA.isPLSphere_or_isPLBall_geometricLink A hsA hk hkn with hS | hB
  · exact (hS.not_subset_of_isPLBall hlinkK hlinkSub).elim
  · apply (hA.mem_boundaryComplex_faces_iff A).mpr
    exact ⟨hsA, hbd.2.1, hdim ▸ hB⟩

open Classical in
theorem inter_boundaryComplex_space_subset {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.faces ⊆ K.faces) :
    A.space ∩ (boundaryComplex (n + 1) K).space ⊆ (boundaryComplex (n + 1) A).space := by
  classical
  rintro x ⟨hxA, hxK⟩
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex A hxA
  have hsK := mem_faces_of_mem_openSimplex_of_mem_space
    (boundaryComplex_faces_subset (n + 1) K) (hAK hs) hxs hxK
  exact (boundaryComplex (n + 1) A).convexHull_subset_space
    (inter_boundaryComplex_faces_subset K A hK hA hAK ⟨hs, hsK⟩)
    (openSimplex_subset_convexHull _ hxs)

open Classical in
theorem inter_boundaryComplex_space_subset_of_subset {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.space ⊆ K.space) :
    A.space ∩ (boundaryComplex (n + 1) K).space ⊆ (boundaryComplex (n + 1) A).space := by
  classical
  obtain ⟨R, hR, hfin, hA'⟩ := exists_isSubdivision_restrict_isSubdivision K A hAK
  let _ : Finite R.faces := hfin.to_subtype
  let _ : Finite (restrict R A.space).faces := (restrict_faces_finite R A.space).to_subtype
  have hi := inter_boundaryComplex_space_subset R (restrict R A.space)
    (hK.of_isSubdivision hR) (hA.of_isSubdivision hA') (restrict_faces_subset R A.space)
  rw [hA'.space_eq, boundaryComplex_space_of_isSubdivision K R hK hR,
    boundaryComplex_space_of_isSubdivision A (restrict R A.space) hA hA'] at hi
  exact hi

end DifferentialGeometry.Topology.PiecewiseLinear
