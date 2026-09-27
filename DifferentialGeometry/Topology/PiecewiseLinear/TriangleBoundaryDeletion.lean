/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleArcTrace
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleBoundaryFold

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLHomeomorphOn_disk_boundary_triangle_deletion
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsPLBall 2 K.space) (hL : IsPLBall 2 L.space)
    {T : Finset E} (hT : T ∈ K.faces) (hcard : T.card = 3)
    (htrace : IsPLBall 1 ((boundaryComplex 2 K).space ∩ convexHull ℝ (T : Set E)))
    (hLspace : L.space = closure (K.space \ convexHull ℝ (T : Set E)))
    {C : Set E} (hC : IsPolyhedron C)
    (htri : convexHull ℝ (T : Set E) \
      closure ((boundaryComplex 2 K).space \ convexHull ℝ (T : Set E)) ⊆ interior C) :
    ∃ e : E ≃ₜ E, IsPLHomeomorphOn e univ univ ∧ EqOn e id Cᶜ ∧
      EqOn e id (frontier C) ∧ e '' C = C ∧
      e '' (boundaryComplex 2 K).space = (boundaryComplex 2 L).space := by
  obtain ⟨a, b, c, hab, hca, hcb, rfl, hshape⟩ :=
    exists_triangle_boundary_arc_normal_form K hK hT hcard htrace
  simp only [Finset.coe_insert, Finset.coe_singleton] at hshape hLspace htri
  have hind := K.indep hT
  have hS := isPLSphere_boundaryComplex_space_of_isPLBall K hK
  have hcondition {F : Set E} {γ : ℝ → E}
      (hγ : IsPLHomeomorphOn γ (Icc 0 1) F) (hγ0 : γ 0 = a) (hγ1 : γ 1 = b)
      (hF : (boundaryComplex 2 K).space ∩ convexHull ℝ ({c, a, b} : Set E) = F) :
      convexHull ℝ ({c, a, b} : Set E) \ {a, b} ⊆ interior C := by
    have hFS : F ⊆ (boundaryComplex 2 K).space := hF.symm.subset.trans inter_subset_left
    have hdiff : (boundaryComplex 2 K).space \ convexHull ℝ ({c, a, b} : Set E) =
        (boundaryComplex 2 K).space \ F := by
      ext x
      have h := Set.ext_iff.mp hF x
      simp only [mem_sdiff, mem_inter_iff] at h ⊢
      tauto
    have hends : F ∩ closure ((boundaryComplex 2 K).space \ F) = {a, b} := by
      simpa only [hγ0, hγ1] using hγ.inter_closure_circle_sdiff hS hFS
    intro x hx
    apply htri ⟨hx.1, ?_⟩
    intro hxR
    have hxS : x ∈ (boundaryComplex 2 K).space :=
      closure_minimal sdiff_subset hS.isPolyhedron.isClosed hxR
    have hxF := hF.subset ⟨hxS, hx.1⟩
    rw [hdiff] at hxR
    exact hx.2 (hends.subset ⟨hxF, hxR⟩)
  rcases hshape with hshape | hshape
  · have hinterior := hcondition (isPLHomeomorphOn_lineMap_Icc_segment hab)
      (AffineMap.lineMap_apply_zero a b) (AffineMap.lineMap_apply_one a b) hshape
    exact exists_isPLHomeomorphOn_disk_boundary_one_edge_deletion K L hK hL
      hab hca hcb hT hshape hLspace hC hinterior
  · have hTpoly : IsPolyhedron (convexHull ℝ ({c, a, b} : Set E)) := by
      simpa only [Finset.coe_insert, Finset.coe_pair, Finset.coe_singleton] using
        isPolyhedron_convexHull_of_affineIndependent ({c, a, b} : Finset E) hind
    obtain ⟨N, hN, hTN, _⟩ :=
      exists_isPolyhedron_neighborhood hTpoly.isCompact isOpen_univ (subset_univ _)
    obtain ⟨u, hu, _, _, _, hua, hub, humove⟩ :=
      exists_isPLHomeomorphOn_segment_triangle_move hab hca hcb hind hN
        (sdiff_subset.trans hTN)
    have huArc : IsPLHomeomorphOn u (segment ℝ a b)
        (segment ℝ a c ∪ segment ℝ c b) := by
      rw [← humove]
      exact hu.restrict (isPLBall_segment hab).isPolyhedron (subset_univ _)
    have hγ := (isPLHomeomorphOn_lineMap_Icc_segment hab).trans huArc
    have hγ0 : (u ∘ AffineMap.lineMap (k := ℝ) a b) 0 = a := by
      rw [Function.comp_apply, AffineMap.lineMap_apply_zero, hua]
    have hγ1 : (u ∘ AffineMap.lineMap (k := ℝ) a b) 1 = b := by
      rw [Function.comp_apply, AffineMap.lineMap_apply_one, hub]
    exact exists_isPLHomeomorphOn_disk_boundary_two_edge_deletion K L hK hL
      hab hca hcb hT hshape hLspace hC (hcondition hγ hγ0 hγ1 hshape)

end DifferentialGeometry.Topology.PiecewiseLinear
