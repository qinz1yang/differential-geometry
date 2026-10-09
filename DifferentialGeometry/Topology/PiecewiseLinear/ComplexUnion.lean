/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.EulerPolyhedra
import DifferentialGeometry.Topology.PiecewiseLinear.FaceLink
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem intersectionComplex_space (K L : Geometry.SimplicialComplex ℝ E)
    (h : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E))) :
    (intersectionComplex K L).space = K.space ∩ L.space := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := (intersectionComplex K L).mem_space_iff.mp hx
    exact ⟨K.convexHull_subset_space hs.1 hxs, L.convexHull_subset_space hs.2 hxs⟩
  · rintro x ⟨hxK, hxL⟩
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hxK
    obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hxL
    have hx : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
      simpa only [Finset.coe_inter] using h s hs t ht ⟨hxs, hxt⟩
    have hne : (s ∩ t).Nonempty := by
      by_contra hnot
      simp [Finset.not_nonempty_iff_eq_empty.mp hnot] at hx
    exact (intersectionComplex K L).convexHull_subset_space
      ⟨K.down_closed hs Finset.inter_subset_left hne,
        L.down_closed ht Finset.inter_subset_right hne⟩ hx

theorem geometricLink_intersectionComplex [DecidableEq E]
    (K L : Geometry.SimplicialComplex ℝ E) (s : Finset E) :
    SimplicialComplex.geometricLink (intersectionComplex K L) s =
      intersectionComplex (SimplicialComplex.geometricLink K s)
        (SimplicialComplex.geometricLink L s) := by
  ext t
  simp only [mem_geometricLink_faces_iff, mem_intersectionComplex_faces_iff]
  tauto

theorem geometricLink_space_unionComplex [DecidableEq E]
    (K L : Geometry.SimplicialComplex ℝ E)
    (h : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E))) (s : Finset E) :
    (SimplicialComplex.geometricLink (unionComplex K L h) s).space =
      (SimplicialComplex.geometricLink K s).space ∪
        (SimplicialComplex.geometricLink L s).space := by
  ext x
  simp only [Geometry.SimplicialComplex.mem_space_iff, mem_geometricLink_faces_iff,
    mem_unionComplex_faces_iff, mem_union]
  constructor
  · rintro ⟨t, ⟨hne, hdisj, ht | ht⟩, hxt⟩
    · exact Or.inl ⟨t, ⟨hne, hdisj, ht⟩, hxt⟩
    · exact Or.inr ⟨t, ⟨hne, hdisj, ht⟩, hxt⟩
  · rintro (⟨t, ⟨hne, hdisj, ht⟩, hxt⟩ | ⟨t, ⟨hne, hdisj, ht⟩, hxt⟩)
    · exact ⟨t, ⟨hne, hdisj, Or.inl ht⟩, hxt⟩
    · exact ⟨t, ⟨hne, hdisj, Or.inr ht⟩, hxt⟩

theorem geometricLink_unionComplex_of_notMem_right [DecidableEq E]
    (K L : Geometry.SimplicialComplex ℝ E)
    (h : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)))
    {s : Finset E} (hne : s.Nonempty) (hs : s ∉ L.faces) :
    SimplicialComplex.geometricLink (unionComplex K L h) s =
      SimplicialComplex.geometricLink K s := by
  ext t
  simp only [mem_geometricLink_faces_iff, mem_unionComplex_faces_iff]
  constructor
  · rintro ⟨ht, hdis, hmem | hmem⟩
    · exact ⟨ht, hdis, hmem⟩
    · exact (hs (L.down_closed hmem Finset.subset_union_left hne)).elim
  · exact fun ht => ⟨ht.1, ht.2.1, Or.inl ht.2.2⟩

theorem geometricLink_unionComplex_of_notMem_left [DecidableEq E]
    (K L : Geometry.SimplicialComplex ℝ E)
    (h : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)))
    {s : Finset E} (hne : s.Nonempty) (hs : s ∉ K.faces) :
    SimplicialComplex.geometricLink (unionComplex K L h) s =
      SimplicialComplex.geometricLink L s := by
  ext t
  simp only [mem_geometricLink_faces_iff, mem_unionComplex_faces_iff]
  constructor
  · rintro ⟨ht, hdis, hmem | hmem⟩
    · exact (hs (K.down_closed hmem Finset.subset_union_left hne)).elim
    · exact ⟨ht, hdis, hmem⟩
  · exact fun ht => ⟨ht.1, ht.2.1, Or.inr ht.2.2⟩

theorem exists_simplicialComplex_space_union [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      R.space = K.space ∪ L.space ∧
      IsSubdivision (restrict R K.space) K ∧ IsSubdivision (restrict R L.space) L := by
  let C : K.faces ⊕ L.faces → Set E := Sum.elim
    (fun s => convexHull ℝ ((s : Finset E) : Set E))
    (fun t => convexHull ℝ ((t : Finset E) : Set E))
  have hC : ∀ i, IsHPolytope (C i) := by
    rintro (s | t)
    · exact isHPolytope_convexHull_of_affineIndependent _ (K.indep s.2)
    · exact isHPolytope_convexHull_of_affineIndependent _ (L.indep t.2)
  obtain ⟨R, hfin, hspace, hcover⟩ := exists_simplicialComplex_of_forall_isHPolytope C hC
  refine ⟨R, hfin, ?_, restrict_isSubdivision K (fun s hs => hcover (Sum.inl ⟨s, hs⟩)),
    restrict_isSubdivision L (fun t ht => hcover (Sum.inr ⟨t, ht⟩))⟩
  rw [hspace]
  ext x
  constructor
  · intro hx
    obtain ⟨s | t, hx⟩ := mem_iUnion.mp hx
    · exact Or.inl (K.convexHull_subset_space s.2 hx)
    · exact Or.inr (L.convexHull_subset_space t.2 hx)
  · rintro (hx | hx)
    · obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
      exact mem_iUnion.mpr ⟨Sum.inl ⟨s, hs⟩, hxs⟩
    · obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hx
      exact mem_iUnion.mpr ⟨Sum.inr ⟨t, ht⟩, hxt⟩

theorem exists_simplicialComplex_space_iUnion [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] (K : ι → Geometry.SimplicialComplex ℝ E)
    [∀ i, Finite (K i).faces] :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      R.space = ⋃ i, (K i).space ∧
      ∀ i, IsSubdivision (restrict R (K i).space) (K i) := by
  let C : (Σ i, (K i).faces) → Set E := fun s =>
    convexHull ℝ ((s.2 : Finset E) : Set E)
  have hC : ∀ s, IsHPolytope (C s) := fun s =>
    isHPolytope_convexHull_of_affineIndependent _ ((K s.1).indep s.2.2)
  obtain ⟨R, hfin, hspace, hcover⟩ := exists_simplicialComplex_of_forall_isHPolytope C hC
  refine ⟨R, hfin, ?_, fun i =>
    restrict_isSubdivision (K i) (fun s hs => hcover ⟨i, ⟨s, hs⟩⟩)⟩
  rw [hspace]
  ext x
  constructor
  · intro hx
    obtain ⟨⟨i, s⟩, hxs⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, (K i).convexHull_subset_space s.2 hxs⟩
  · intro hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    obtain ⟨s, hs, hxs⟩ := (K i).mem_space_iff.mp hxi
    exact mem_iUnion.mpr ⟨⟨i, ⟨s, hs⟩⟩, hxs⟩

theorem exists_simplicialComplex_space_union_three [FiniteDimensional ℝ E]
    (K L M : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite L.faces] [Finite M.faces] :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      R.space = K.space ∪ L.space ∪ M.space ∧
      IsSubdivision (restrict R K.space) K ∧
      IsSubdivision (restrict R L.space) L ∧
      IsSubdivision (restrict R M.space) M := by
  let C : Fin 3 → Geometry.SimplicialComplex ℝ E := ![K, L, M]
  let _ : ∀ i, Finite (C i).faces := by
    intro i
    fin_cases i <;> dsimp [C] <;> infer_instance
  obtain ⟨R, hfin, hspace, hsub⟩ := exists_simplicialComplex_space_iUnion C
  refine ⟨R, hfin, ?_, hsub 0, hsub 1, hsub 2⟩
  rw [hspace]
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    fin_cases i
    · exact Or.inl (Or.inl hxi)
    · exact Or.inl (Or.inr hxi)
    · exact Or.inr hxi
  · rintro ((hx | hx) | hx)
    · exact mem_iUnion.mpr ⟨0, hx⟩
    · exact mem_iUnion.mpr ⟨1, hx⟩
    · exact mem_iUnion.mpr ⟨2, hx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
