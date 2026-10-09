/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.Schoenflies.ArcSquareChain
import DifferentialGeometry.External.Schoenflies.FaceCyclesLand

open Set Topology

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies
open scoped Graph

open Classical in
theorem exists_polygonal_jordan_neighborhood_of_isArc {A U : Set Plane}
    (hA : IsArc A) (hU : U ∈ 𝓝ˢ A) :
    ∃ J : Set Plane, IsJordanCurve J ∧ IsPolygonal J ∧ A ⊆ inside J ∧ closure (inside J) ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := (Metric.hasBasis_nhdsSet_thickening hA.isCompact).mem_iff.mp hU
  obtain ⟨α, hα, hinj, hαA⟩ := hA
  obtain ⟨n, m, c, r, hm, hr, hchain, hc, hcover, hnear⟩ :=
    exists_square_chain hα hinj (div_pos hε (by norm_num : (0 : ℝ) < 8))
  let G := Graph.chainUnion (familyChain c ((n + 1) * m) m r) 0 n
  let _ : G.Finite := hchain.block_finite (by omega)
  have hdraw : G.IsDrawing segmentDrawing := hchain.block_isDrawing (by omega)
  obtain ⟨b, hb, hbunb⟩ := Graph.exists_unbounded_face hdraw
  obtain ⟨e, u, v, D, hface⟩ := Graph.face_cycles' hdraw
    (hchain.block_polygonal (by omega)) (hchain.block_isTwoConnected (by omega)) b hb
  let J := Graph.edgesCover segmentDrawing (e :: D)
  have hJ : IsJordanCurve J := hdraw.cycle_isJordanCurve hface.isCycle
  have hpoly : IsPolygonal J := hdraw.isPolygonal_edgesCover
    (hchain.block_polygonal (by omega)) hface.isCycle.isWalk_cons (List.cons_ne_nil _ _)
  have hout : Graph.face G segmentDrawing b = outside J :=
    hface.eq_inside_or_outside.resolve_left fun heq => hbunb (heq ▸
        hface.isSeparating.isBounded_inside)
  have hfr (j : ℕ) (hj : j ≤ (n + 1) * m) :
      frontier (Plane.closedSquare (c j) r) ⊆ Graph.pointSet G segmentDrawing :=
    frontier_closedSquare_subset_pointSet_chainUnion hr hj
  refine ⟨J, hJ, hpoly, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, hxj⟩ := hcover x (hαA.symm ▸ hx)
    have hxcl : x ∉ closure (Graph.face G segmentDrawing b) := by
      intro hxcl
      obtain ⟨z, hzj, hzF⟩ := mem_closure_iff_nhds.mp hxcl _
        ((Plane.isOpen_openSquare (c j) r).mem_nhds hxj)
      exact notMem_face_of_mem_openSquare (hfr j hj) hbunb hzj hzF
    have hxJ : x ∉ J := fun h => hxcl
      (frontier_subset_closure (hface.frontier_eq.symm ▸ h))
    have hxIO : x ∈ inside J ∪ outside J := by rw [inside_union_outside]; exact hxJ
    exact hxIO.resolve_right fun h => hxcl (subset_closure (hout.symm ▸ h))
  · intro x hx
    apply hεU
    by_contra hxε
    have hfar : ∀ p, p + 1 ≤ n → 3 * (ε / 8) < Plane.supDist x (c (p * m)) := by
      intro p hp
      have hcm : c (p * m) ∈ A := hαA ▸ hc (p * m) (by nlinarith)
      have hdist : ε ≤ dist x (c (p * m)) := le_of_not_gt fun hlt => hxε
        (Metric.mem_thickening_iff.mpr ⟨c (p * m), hcm, hlt⟩)
      have hlt := lt_supDist_of_le_dist hε hdist
      linarith
    obtain ⟨hxG, hxu⟩ := outer_face_familyChain hchain (outerOnPairs_familyChain hnear hfar)
    have hxout : x ∈ outside J := by
      rw [← hout, ← Graph.unbounded_face_unique hdraw hxu hbunb]
      exact Graph.mem_face hxG
    rw [(IsRegionOf.inside J).closure_eq hface.isSeparating] at hx
    rcases hx with hx | hx
    · exact disjoint_left.mp disjoint_inside_outside hx hxout
    · exact hxout.1 hx

end DifferentialGeometry.Topology.PlanarJordan
