/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.ComplexUnion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem geometricLink_space_inter_of_subcomplex_space_eq
    (T K L R : Geometry.SimplicialComplex ℝ E)
    (hKT : K.faces ⊆ T.faces) (hLT : L.faces ⊆ T.faces) (hRT : R.faces ⊆ T.faces)
    (hR : R.space = K.space ∩ L.space) (x : E) :
    (SimplicialComplex.geometricLink R {x}).space =
      (SimplicialComplex.geometricLink K {x}).space ∩
        (SimplicialComplex.geometricLink L {x}).space := by
  have hcompat := fun s (hs : s ∈ K.faces) t (ht : t ∈ L.faces) =>
    T.inter_subset_convexHull (hKT hs) (hLT ht)
  have heq : R = intersectionComplex K L := eq_of_faces_subset_of_space_eq R _ T hRT
    (fun _ hs => hKT hs.1) (hR.trans (intersectionComplex_space K L hcompat).symm)
  rw [heq, geometricLink_intersectionComplex]
  apply intersectionComplex_space
  intro s hs t ht
  exact (SimplicialComplex.geometricLink T {x}).inter_subset_convexHull
    ⟨hs.1, hs.2.1, hKT hs.2.2⟩ ⟨ht.1, ht.2.1, hLT ht.2.2⟩

open Classical in
theorem geometricLink_space_union_of_subcomplex_space_eq
    (T K L R : Geometry.SimplicialComplex ℝ E)
    (hKT : K.faces ⊆ T.faces) (hLT : L.faces ⊆ T.faces) (hRT : R.faces ⊆ T.faces)
    (hR : R.space = K.space ∪ L.space) (x : E) :
    (SimplicialComplex.geometricLink R {x}).space =
      (SimplicialComplex.geometricLink K {x}).space ∪
        (SimplicialComplex.geometricLink L {x}).space := by
  have hcompat := fun s (hs : s ∈ K.faces) t (ht : t ∈ L.faces) =>
    T.inter_subset_convexHull (hKT hs) (hLT ht)
  have heq : R = unionComplex K L hcompat := eq_of_faces_subset_of_space_eq R _ T hRT
    (fun _ hs => hs.elim (fun hs => hKT hs) (fun hs => hLT hs))
    (hR.trans (unionComplex_space K L hcompat).symm)
  rw [heq]
  exact geometricLink_space_unionComplex K L hcompat {x}

open Classical in
theorem geometricLink_space_eq_empty_of_finite_space
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.space.Finite) (x : E) :
    (SimplicialComplex.geometricLink K {x}).space = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hseg : segment ℝ x y ⊆ K.space := by
    rw [segment_eq_image_lineMap]
    rintro z ⟨t, ht, rfl⟩
    simpa only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm] using
      mem_convexHull_insert_of_mem_geometricLink_space K hy ht.1 ht.2
  have hsingle := (convex_segment x y).isPreconnected.isDiscrete_iff_subsingleton.mp
    (hK.subset hseg).isDiscrete
  have hxy := hsingle (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  exact notMem_geometricLink_space K (hxy ▸ hy)

open Classical in
theorem geometricLink_space_eq_empty_of_notMem_space
    (K : Geometry.SimplicialComplex ℝ E) {x : E} (hx : x ∉ K.space) :
    (SimplicialComplex.geometricLink K {x}).space = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact hx (by simpa only [zero_smul, add_zero] using
    mem_convexHull_insert_of_mem_geometricLink_space K hy (t := 0) le_rfl zero_le_one)

variable [FiniteDimensional ℝ E]

theorem IsBridgeDisk.exists_frontier_parametrization
    {C A B : Set E} {a b : E} (h : IsBridgeDisk C A B a b) :
    ∃ δ : ℝ → E, IsPLHomeomorphOn δ (Icc 0 1) (B ∩ frontier C) ∧ δ 0 = a ∧ δ 1 = b := by
  classical
  have hcopy := h
  obtain ⟨q, hq, _, _, _, _, _⟩ := hcopy
  have hB : IsPLBall 2 B := ⟨q, hq⟩
  obtain ⟨K, hKfin, hKB⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := h.exists_parametrization
  have hbd := h.boundary_eq K hKB
  obtain ⟨R, δ, hδ, hδ0, hδ1, hAR, hmeet⟩ := exists_complementary_arc_of_isPLSphere_one
    (isPLSphere_boundaryComplex_space_of_isPLBall K (hKB.symm ▸ hB)) hγ
    (hbd.symm ▸ subset_union_left)
  have hAB : A ⊆ B := (subset_union_left.trans hbd.symm.subset).trans
    ((boundaryComplex_space_subset 2 K).trans hKB.subset)
  have hR : R = B ∩ frontier C := by
    rw [hγ0, hγ1] at hmeet
    ext x
    have hc := Set.ext_iff.mp (hAR.trans hbd) x
    have hm := Set.ext_iff.mp hmeet x
    have hi := Set.ext_iff.mp h.inter_frontier x
    simp only [mem_union, mem_inter_iff] at hc hm hi ⊢
    constructor
    · intro hx
      by_cases hxA : x ∈ A
      · exact ⟨hAB hxA, (hi.mpr (hm.mp ⟨hxA, hx⟩)).2⟩
      · exact (hc.mp (Or.inr hx)).resolve_left hxA
    · intro hx
      by_cases hxA : x ∈ A
      · exact (hm.mpr (hi.mp ⟨hxA, hx.2⟩)).2
      · exact (hc.mpr (Or.inr hx)).resolve_left hxA
  exact ⟨δ, hR ▸ hδ, hδ0.trans hγ0, hδ1.trans hγ1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
