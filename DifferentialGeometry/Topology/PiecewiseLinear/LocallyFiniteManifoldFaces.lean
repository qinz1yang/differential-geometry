/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteGraphDualCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} {d n : ℕ} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) X] {Y : Set X}

theorem LocallyFinitePLPieceIn.exists_face_superset_card_eq
    (T : LocallyFinitePLPieceIn E d X Y)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) T.complex)
    {s : Finset E} (hs : s ∈ T.complex.faces) :
    ∃ t ∈ T.complex.faces, s ⊆ t ∧ t.card = n + 2 := by
  classical
  obtain ⟨v, hv⟩ := T.complex.nonempty_of_mem_faces hs
  have hvK : {v} ∈ T.complex.faces := T.complex.down_closed hs
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  let S := starComplex T.complex v
  let _ : Finite S.faces := (T.starComplex_faces_finite hvK).to_subtype
  have hball : IsPLBall (n + 1) S.space := by
    rw [starComplex_space T.complex v hvK]
    exact T.isPLBall_closedStar hK hvK
  have hsS : s ∈ S.faces := ⟨hs, by rwa [Finset.insert_eq_of_mem hv]⟩
  obtain ⟨t, ht, hst, hcard⟩ := exists_face_superset_card_eq_of_isPLBall S hball hsS
  exact ⟨t, (starComplex_faces_subset T.complex v) ht, hst, hcard⟩

theorem LocallyFinitePLPieceIn.space_eq_union_topFace_residuals
    (T : LocallyFinitePLPieceIn E d X Y)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) T.complex)
    {N : Set E} (hN : N ⊆ T.complex.space) :
    T.complex.space = N ∪ ⋃ t ∈ {t : Finset E | t ∈ T.complex.faces ∧ t.card = n + 2},
      closure (convexHull ℝ (t : Set E) \ N) := by
  apply Subset.antisymm
  · intro x hx
    by_cases hxN : x ∈ N
    · exact Or.inl hxN
    · obtain ⟨s, hs, hxs⟩ := T.complex.mem_space_iff.mp hx
      obtain ⟨t, ht, hst, hcard⟩ := T.exists_face_superset_card_eq hK hs
      exact Or.inr (mem_iUnion₂.mpr ⟨t, ⟨ht, hcard⟩, subset_closure
        ⟨convexHull_mono (Finset.coe_subset.mpr hst) hxs, hxN⟩⟩)
  · refine union_subset hN (iUnion₂_subset fun t ht => ?_)
    exact (closure_minimal sdiff_subset
      (t.finite_toSet.isCompact_convexHull ℝ).isClosed).trans
      (T.complex.convexHull_subset_space ht.1)

end DifferentialGeometry.Topology.PiecewiseLinear
