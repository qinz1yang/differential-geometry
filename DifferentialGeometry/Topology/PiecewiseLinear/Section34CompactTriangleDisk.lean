/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_triangle_subcomplex_with_rim
    (K : Geometry.SimplicialComplex ℝ E3)
    (s : Section34CompactSimplexIndex K 3) :
    ∃ F : Geometry.SimplicialComplex ℝ E3,
      F.faces.Finite ∧ F.faces ⊆ K.faces ∧
      IsPLBall 2 F.space ∧
      F.space = convexHull ℝ (s.1 : Set E3) ∧
      (boundaryComplex 2 F).space = section34CompactSimplexRim s.1 ∧
      (boundaryComplex 2 F).faces ⊆
        (restrict K (section34CompactGraphSkeleton K)).faces := by
  classical
  let F := simplexComplex s.1 (K.indep s.2.1)
  have hspace : F.space = convexHull ℝ (s.1 : Set E3) :=
    simplexComplex_space s.1 (K.indep s.2.1) (K.nonempty_of_mem_faces s.2.1)
  have hboundary : boundaryComplex 2 F = simplexBoundary s.1 (K.indep s.2.1) :=
    boundaryComplex_simplexComplex (K.indep s.2.1) s.2.2
  refine ⟨F, simplexComplex_faces_finite _ _, ?_, ?_, hspace, ?_, ?_⟩
  · intro t ht
    exact K.down_closed s.2.1 ht.2 ht.1
  · rw [hspace]
    exact isPLBall_convexHull_of_affineIndependent s.1 (K.indep s.2.1) s.2.2
  · rw [hboundary]
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, hxt⟩ := (simplexBoundary _ _).mem_space_iff.mp hx
      exact mem_iUnion₂.mpr ⟨t, Finset.ssubset_iff_subset_ne.mpr ⟨ht.1, ht.2.2⟩, hxt⟩
    · intro hx
      obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
      have hne : t.Nonempty := by
        by_contra hn
        have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
        simp only [ht0, Finset.coe_empty, convexHull_empty, mem_empty_iff_false] at hxt
      exact (simplexBoundary _ _).convexHull_subset_space
        ⟨ht.subset, hne, ht.ne⟩ hxt
  · rw [hboundary]
    intro t ht
    have htK := K.down_closed s.2.1 ht.1 ht.2.1
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨ht.1, ht.2.2⟩)
    have hcard : t.card ≤ 2 := by have := s.2.2; omega
    exact ⟨htK, fun x hx => mem_iUnion₂.mpr ⟨t, ⟨htK, hcard⟩, hx⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
