/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComplexUnion
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldWithBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem not_mem_faces_of_disjoint_space
    {K L : Geometry.SimplicialComplex ℝ E} (hdis : Disjoint K.space L.space)
    {s : Finset E} (hs : s ∈ K.faces) : s ∉ L.faces := by
  intro ht
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  exact disjoint_left.mp hdis (K.subset_space hs hv) (L.subset_space ht hv)

theorem IsCombinatorialManifoldWithBoundary.unionComplex_of_disjoint {n : ℕ}
    (K L : Geometry.SimplicialComplex ℝ E)
    (h : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)))
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L) (hdis : Disjoint K.space L.space) :
    IsCombinatorialManifoldWithBoundary n (unionComplex K L h) := by
  classical
  cases n with
  | zero =>
    intro v hv
    rcases hv with hv | hv
    · rw [geometricLink_unionComplex_of_notMem_right K L h (Finset.singleton_nonempty v)
        (not_mem_faces_of_disjoint_space hdis hv)]
      exact hK v hv
    · rw [geometricLink_unionComplex_of_notMem_left K L h (Finset.singleton_nonempty v)
        (not_mem_faces_of_disjoint_space hdis.symm hv)]
      exact hL v hv
  | succ n =>
    intro v hv
    rcases hv with hv | hv
    · rw [geometricLink_unionComplex_of_notMem_right K L h (Finset.singleton_nonempty v)
        (not_mem_faces_of_disjoint_space hdis hv)]
      exact hK v hv
    · rw [geometricLink_unionComplex_of_notMem_left K L h (Finset.singleton_nonempty v)
        (not_mem_faces_of_disjoint_space hdis.symm hv)]
      exact hL v hv

theorem boundaryComplex_faces_unionComplex_of_disjoint [DecidableEq E]
    (n : ℕ) (K L : Geometry.SimplicialComplex ℝ E)
    (h : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E))) (hdis : Disjoint K.space L.space) :
    (boundaryComplex n (unionComplex K L h)).faces =
      (boundaryComplex n K).faces ∪ (boundaryComplex n L).faces := by
  ext s
  constructor
  · rintro ⟨hs, t, ht | ht, hst, hcard, hball⟩
    · have hsK := K.down_closed ht hst ((unionComplex K L h).nonempty_of_mem_faces hs)
      rw [geometricLink_unionComplex_of_notMem_right K L h (K.nonempty_of_mem_faces ht)
        (not_mem_faces_of_disjoint_space hdis ht)] at hball
      exact Or.inl ⟨hsK, t, ht, hst, hcard, hball⟩
    · have hsL := L.down_closed ht hst ((unionComplex K L h).nonempty_of_mem_faces hs)
      rw [geometricLink_unionComplex_of_notMem_left K L h (L.nonempty_of_mem_faces ht)
        (not_mem_faces_of_disjoint_space hdis.symm ht)] at hball
      exact Or.inr ⟨hsL, t, ht, hst, hcard, hball⟩
  · rintro (⟨hs, t, ht, hst, hcard, hball⟩ | ⟨hs, t, ht, hst, hcard, hball⟩)
    · refine ⟨Or.inl hs, t, Or.inl ht, hst, hcard, ?_⟩
      rwa [geometricLink_unionComplex_of_notMem_right K L h (K.nonempty_of_mem_faces ht)
        (not_mem_faces_of_disjoint_space hdis ht)]
    · refine ⟨Or.inr hs, t, Or.inr ht, hst, hcard, ?_⟩
      rwa [geometricLink_unionComplex_of_notMem_left K L h (L.nonempty_of_mem_faces ht)
        (not_mem_faces_of_disjoint_space hdis.symm ht)]

theorem boundaryComplex_space_unionComplex_of_disjoint [DecidableEq E]
    (n : ℕ) (K L : Geometry.SimplicialComplex ℝ E)
    (h : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E))) (hdis : Disjoint K.space L.space) :
    (boundaryComplex n (unionComplex K L h)).space =
      (boundaryComplex n K).space ∪ (boundaryComplex n L).space := by
  ext x
  simp only [Geometry.SimplicialComplex.mem_space_iff,
    boundaryComplex_faces_unionComplex_of_disjoint n K L h hdis, mem_union]
  constructor
  · rintro ⟨s, hs | hs, hxs⟩
    · exact Or.inl ⟨s, hs, hxs⟩
    · exact Or.inr ⟨s, hs, hxs⟩
  · rintro (⟨s, hs, hxs⟩ | ⟨s, hs, hxs⟩)
    · exact ⟨s, Or.inl hs, hxs⟩
    · exact ⟨s, Or.inr hs, hxs⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_space_disjoint_union {n : ℕ}
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L) (hdis : Disjoint K.space L.space) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary n R ∧ R.space = K.space ∪ L.space ∧
      (boundaryComplex n R).space = (boundaryComplex n K).space ∪ (boundaryComplex n L).space := by
  have h : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
    intro s hs t ht x hx
    exact (disjoint_left.mp hdis (K.convexHull_subset_space hs hx.1)
      (L.convexHull_subset_space ht hx.2)).elim
  exact ⟨unionComplex K L h, Set.toFinite _, hK.unionComplex_of_disjoint K L h hL hdis,
    unionComplex_space K L h, boundaryComplex_space_unionComplex_of_disjoint n K L h hdis⟩

end DifferentialGeometry.Topology.PiecewiseLinear
