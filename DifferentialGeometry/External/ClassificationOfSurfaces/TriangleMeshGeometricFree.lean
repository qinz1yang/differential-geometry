import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.FreeTriangle
import DifferentialGeometry.External.Schoenflies.JordanSeparates
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Separation.Connected
import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.GeometricFreeTriangle
import DifferentialGeometry.External.ClassificationOfSurfaces.TriangleMeshCrosscut
import DifferentialGeometry.External.ClassificationOfSurfaces.PrePolygonTriangulation

/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
Adapted from PolygonalSchoenflies.lean at e3c7230fe78d7b056a415d9ecae6f77887046b32.
See MODIFICATIONS.md and GEOMETRIC_FREE_EXISTENCE.json for the selected proofs and local changes.
-/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
The finite-exclusion density proof is retained privately from FreshDenseSelection.lean.
See GEOMETRIC_FREE_EXISTENCE.json for the exact native source and provenance.
-/

open LeanEval.Topology.ClassificationOfSurfaces.Moise (TriangleMesh)

namespace LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- In a finite planar mesh with preconnected support interior and more than one maximal
triangle, every maximal triangle has an edge-neighbor. A triangle attached only at vertices
would make its open interior a clopen piece of the support interior. -/
private theorem TriangleMesh.exists_edge_neighbor_of_isPreconnected_interior (M : TriangleMesh)
    (hc : IsPreconnected (interior M.toPlaneComplex.support))
    (T : M.Triangle) (hmore : 1 < M.triangles.card) :
    ∃ U : M.Triangle, T.1 ≠ U.1 ∧ M.AreEdgeNeighbors T.1 U.1 := by
  by_contra hexists
  have hNoNeighbor {u : Finset M.Vertex} (hu : u ∈ M.triangles) (hne : T.1 ≠ u) :
      ¬M.AreEdgeNeighbors T.1 u := by
    intro hneighbor
    exact hexists ⟨⟨u, hu⟩, hne, hneighbor⟩
  have hAllBoundary : ∀ e ∈ M.triangleEdges T.1, M.IsBoundaryEdge e := by
    intro e he
    have heData := Finset.mem_powersetCard.mp he
    have heEdges : e ∈ M.edges := by
      apply Finset.mem_biUnion.mpr
      exact ⟨T.1, T.2, Finset.mem_powersetCard.mpr heData⟩
    have hincident : M.incidentTriangles e = {T.1} := by
      ext u
      constructor
      · intro hu
        have huData := M.mem_incidentTriangles_iff.mp hu
        rw [Finset.mem_singleton]
        by_contra hne
        exact hNoNeighbor huData.1 (fun h => hne h.symm)
          ⟨e, heData.2, heData.1, huData.2⟩
      · intro hu
        rw [Finset.mem_singleton] at hu
        subst u
        exact M.mem_incidentTriangles_iff.mpr ⟨T.2, heData.1⟩
    exact ⟨heEdges, by rw [hincident]; simp⟩
  have hfrontierTriangle : frontier (M.triangleCarrier T.1) ⊆
      frontier M.toPlaneComplex.support := by
    intro p hp
    obtain ⟨e, hecard, heT, hpEdge⟩ := M.exists_edge_of_mem_frontier_triangle T.2 hp
    have heTriangle : e ∈ M.triangleEdges T.1 :=
      Finset.mem_powersetCard.mpr ⟨heT, hecard⟩
    exact M.boundaryEdgeCarrier_subset_frontier (hAllBoundary e heTriangle) hpEdge
  have htriangleSubset : M.triangleCarrier T.1 ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset T.1
      (Set.subset_iUnion_of_subset T.2 (by rfl))
  have hInteriorSubset : interior (M.triangleCarrier T.1) ⊆
      interior M.toPlaneComplex.support := interior_mono htriangleSubset
  have hCarrierClosed : IsClosed (M.triangleCarrier T.1) :=
    (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ
  have hcover : interior M.toPlaneComplex.support ⊆
      interior (M.triangleCarrier T.1) ∪ (M.triangleCarrier T.1)ᶜ := by
    intro p hp
    by_cases hpT : p ∈ M.triangleCarrier T.1
    · left
      exact (mem_interior_iff_notMem_frontier hpT).mpr fun hpFrontier =>
        Set.disjoint_left.mp disjoint_interior_frontier hp (hfrontierTriangle hpFrontier)
    · exact Or.inr hpT
  have hdisjoint : Disjoint (interior (M.triangleCarrier T.1))
      (M.triangleCarrier T.1)ᶜ := by
    rw [Set.disjoint_left]
    intro p hpInterior hpCompl
    exact hpCompl (interior_subset hpInterior)
  obtain ⟨p, hpT⟩ := M.interior_triangleCarrier_nonempty T
  have hpInside := hInteriorSubset hpT
  have hallInside : interior M.toPlaneComplex.support ⊆ interior (M.triangleCarrier T.1) :=
    hc.subset_left_of_subset_union
      isOpen_interior hCarrierClosed.isOpen_compl hdisjoint hcover ⟨p, hpInside, hpT⟩
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hmore
  let u := if haT : a = T.1 then b else a
  have hu : u ∈ M.triangles := by
    dsimp [u]
    split_ifs with haT
    · exact hb
    · exact ha
  have hune : T.1 ≠ u := by
    dsimp [u]
    split_ifs with haT
    · exact fun h => hab (haT.trans h)
    · exact fun h => haT h.symm
  let U : M.Triangle := ⟨u, hu⟩
  obtain ⟨q, hqU⟩ := M.interior_triangleCarrier_nonempty U
  have hUCarrierSubset : M.triangleCarrier U.1 ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset U.1
      (Set.subset_iUnion_of_subset U.2 (by rfl))
  have hqInside : q ∈ interior M.toPlaneComplex.support := interior_mono hUCarrierSubset hqU
  exact Set.disjoint_left.mp (M.disjoint_interior_triangleCarrier hune)
    (hallInside hqInside) hqU

end LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace Schoenflies

/-- Removing finitely many forbidden points from a relatively dense subset of a Jordan curve
leaves it relatively dense.  The proof works in the curve subtype, which is a nontrivial
connected T₁ space and therefore has no isolated points. -/
private theorem IsJordanCurve.subset_closure_sdiff_finite
    {C eligible forbidden : Set Plane} (hC : IsJordanCurve C)
    (heligible : eligible ⊆ C) (hdense : C ⊆ closure eligible)
    (hforbidden : forbidden.Finite) : C ⊆ closure (eligible \ forbidden) := by
  let eligible' : Set C := {x | x.1 ∈ eligible}
  let forbidden' : Set C := {x | x.1 ∈ forbidden}
  have heligibleImage : ((↑) : C → Plane) '' eligible' = eligible := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, heligible hx⟩, hx, rfl⟩
  have heligibleDense : Dense eligible' := by
    rw [Subtype.dense_iff, heligibleImage]
    exact hdense
  have hforbiddenFinite : forbidden'.Finite := by
    apply hforbidden.preimage
    exact Set.injOn_of_injective Subtype.val_injective
  have : ConnectedSpace C := Subtype.connectedSpace hC.isConnected
  have : Nontrivial C := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hC.exists_ne
    exact ⟨⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩⟩
  have hcleanDense : Dense (eligible' \ forbidden') :=
    heligibleDense.sdiff_finite hforbiddenFinite
  rw [Subtype.dense_iff] at hcleanDense
  have hcleanImage : ((↑) : C → Plane) '' (eligible' \ forbidden') =
      eligible \ forbidden := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyEligible, hyForbidden⟩, rfl⟩
      exact ⟨hyEligible, hyForbidden⟩
    · rintro ⟨hxEligible, hxForbidden⟩
      exact ⟨⟨x, heligible hxEligible⟩, ⟨hxEligible, hxForbidden⟩, rfl⟩
  rwa [hcleanImage] at hcleanDense

end Schoenflies

namespace LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- If a finite planar mesh has another triangle, some point of the support frontier lies
outside any prescribed maximal triangle. -/
private theorem TriangleMesh.exists_frontier_not_mem_triangleCarrier
    (M : TriangleMesh) (T : M.Triangle) (hmore : 1 < M.triangles.card) :
    ∃ p ∈ frontier M.toPlaneComplex.support, p ∉ M.triangleCarrier T.1 := by
  obtain ⟨U, hUT⟩ := Fintype.exists_ne_of_one_lt_card
    (show 1 < Fintype.card M.Triangle by simpa only [Fintype.card_coe] using hmore) T
  have hTU : T.1 ≠ U.1 := fun h => hUT (Subtype.ext h.symm)
  have hsupportNotSubset :
      ¬M.toPlaneComplex.support ⊆ M.triangleCarrier T.1 := by
    intro hall
    have hUCarrierSubset : M.triangleCarrier U.1 ⊆ M.toPlaneComplex.support := by
      rw [M.toPlaneComplex_support]
      exact Set.subset_iUnion_of_subset U.1
        (Set.subset_iUnion_of_subset U.2 (by rfl))
    have hUInteriorSubset :
        interior (M.triangleCarrier U.1) ⊆ M.triangleCarrier T.1 :=
      interior_subset.trans (hUCarrierSubset.trans hall)
    have hUInteriorSubsetInterior :
        interior (M.triangleCarrier U.1) ⊆ interior (M.triangleCarrier T.1) :=
      interior_maximal hUInteriorSubset isOpen_interior
    obtain ⟨p, hpU⟩ := M.interior_triangleCarrier_nonempty U
    exact Set.disjoint_left.mp (M.disjoint_interior_triangleCarrier hTU)
      (hUInteriorSubsetInterior hpU) hpU
  obtain ⟨p, hpSupport, hpT⟩ := Set.not_subset.mp hsupportNotSubset
  have hTClosed : IsClosed (M.triangleCarrier T.1) :=
    (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ
  obtain ⟨f, u, hfT, hufp⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (M.position '' (T.1 : Set M.Vertex))) hTClosed hpT
  obtain ⟨q, hqSupport, hqMax⟩ :=
    M.toPlaneComplex.isCompact_support.exists_isMaxOn
      ⟨p, hpSupport⟩ f.continuous.continuousOn
  have hqT : q ∉ M.triangleCarrier T.1 := by
    intro hqT
    have := hfT q hqT
    have hpq := hqMax hpSupport
    change f p ≤ f q at hpq
    linarith
  have hfne : f ≠ 0 := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [M.card_triangle T.1 T.2]; omega)
    have hvT : M.position v ∈ M.triangleCarrier T.1 :=
      subset_convexHull ℝ _ ⟨v, hv, rfl⟩
    intro hfzero
    have hleft := hfT (M.position v) hvT
    rw [hfzero] at hleft hufp
    simp only [zero_apply] at hleft hufp
    linarith
  have hqFrontier : q ∈ frontier M.toPlaneComplex.support := by
    apply (mem_frontier_iff_notMem_interior hqSupport).mpr
    intro hqInterior
    obtain ⟨y, hy⟩ : ∃ y : Plane, f y ≠ 0 := by
      by_contra h
      push Not at h
      apply hfne
      ext y
      simpa using h y
    let d : Plane := if 0 < f y then y else -y
    have hfd : 0 < f d := by
      dsimp [d]
      split_ifs with hypos
      · exact hypos
      · simp only [map_neg, Left.neg_pos_iff]
        exact lt_of_le_of_ne (le_of_not_gt hypos) hy
    have hdne : d ≠ 0 := by
      intro hd
      rw [hd] at hfd
      simp at hfd
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
      (mem_interior_iff_mem_nhds.mp hqInterior)
    let δ : ℝ := ε / (2 * ‖d‖)
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    let z : Plane := q + δ • d
    have hzBall : z ∈ Metric.ball q ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      change ‖q + δ • d - q‖ < ε
      rw [add_sub_cancel_left]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      dsimp [δ]
      have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hdne
      field_simp
      linarith
    have hzSupport : z ∈ M.toPlaneComplex.support := hball hzBall
    have hzGreater : f q < f z := by
      dsimp [z]
      rw [map_add, map_smul]
      change f q < f q + δ * f d
      nlinarith
    exact (not_lt_of_ge (hqMax hzSupport)) hzGreater
  exact ⟨q, hqFrontier, hqT⟩

end LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- A mesh whose support frontier is a Jordan curve and which has more than one maximal
triangle has two distinct triangles containing incidence-one edges. -/
private theorem TriangleMesh.exists_two_free_triangles_of_isJordanCurve_frontier
    (M : TriangleMesh) (hJ : Schoenflies.IsJordanCurve (frontier M.toPlaneComplex.support))
    (hmore : 1 < M.triangles.card) :
    ∃ T U : M.Triangle,
      T.1 ≠ U.1 ∧ M.IsFreeTriangle T.1 ∧ M.IsFreeTriangle U.1 := by
  have hne : M.triangles.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨t, htFree⟩ := M.exists_free_triangle_of_triangles_nonempty hne
  let T : M.Triangle := ⟨t, htFree.1⟩
  obtain ⟨q, hqFrontier, hqT⟩ := M.exists_frontier_not_mem_triangleCarrier T hmore
  have hqClosure : q ∈ closure (frontier M.toPlaneComplex.support \ Set.range M.position) :=
    hJ.subset_closure_sdiff_finite Set.Subset.rfl subset_closure
      (Set.finite_range M.position) hqFrontier
  have hTClosed : IsClosed (M.triangleCarrier T.1) :=
    (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ
  obtain ⟨r, hrT, hrFrontier, hrNotVertex⟩ :=
    (mem_closure_iff.mp hqClosure) (M.triangleCarrier T.1)ᶜ
      hTClosed.isOpen_compl hqT
  have hrv : ∀ v : M.Vertex, r ≠ M.position v := by
    intro v hrv
    apply hrNotVertex
    exact ⟨v, hrv.symm⟩
  obtain ⟨u, hu, e, heBoundary, heu, hre⟩ :=
    M.exists_boundaryEdge_through_frontier_point hrFrontier hrv
  let U : M.Triangle := ⟨u, hu⟩
  have hTU : T.1 ≠ U.1 := by
    intro h
    apply hrT
    apply convexHull_mono (Set.image_mono ?_) hre
    intro v hv
    rw [h]
    exact heu hv
  exact ⟨T, U, hTU, htFree, hu, e, heBoundary, heu⟩

end LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace Schoenflies

private theorem bad_free_crosscut_interior_closure {C : Set Plane}
    (hC : IsSeparating C) : interior (closure (inside C)) = inside C := by
  have hd₀ : Disjoint (closure (inside C)) (outside C) :=
    disjoint_inside_outside.closure_left hC.isOpen_outside
  have hd : Disjoint (interior (closure (inside C))) (closure (outside C)) :=
    (hd₀.mono_left interior_subset).closure_right isOpen_interior
  apply Set.Subset.antisymm ?_ hC.isOpen_inside.subset_interior_closure
  intro x hx
  have hxC : x ∉ C := fun hxc => Set.disjoint_left.mp hd hx
    ((IsRegionOf.outside C).subset_closure hC hxc)
  have hxSplit : x ∈ inside C ∪ outside C := (inside_union_outside C).symm ▸ hxC
  exact hxSplit.resolve_right fun hxo => Set.disjoint_left.mp hd hx (subset_closure hxo)

private theorem exists_mesh_crosscut_of_bad_free_triangle
    (M : TriangleMesh) {C : Set Plane} (hC : IsJordanCurve C)
    (hsupport : M.toPlaneComplex.support = closure (inside C))
    (T U : M.Triangle) (hfree : M.IsFreeTriangle T.1)
    (hne : T.1 ≠ U.1) (hneighbors : M.AreEdgeNeighbors T.1 U.1)
    (hnot : ¬M.HasNoIsolatedFrontierVertex T.1) :
    ∃ a v : M.Vertex, a ≠ v ∧ ({a, v} : Finset M.Vertex) ∈ M.edges ∧
      IsCrosscut C (segment ℝ (M.position a) (M.position v))
        (M.position a) (M.position v) := by
  classical
  obtain ⟨a, b, v, hab, hva, hvb, htriangle, hboundary, hvFrontier⟩ :=
    M.exists_cutting_diagonal_configuration T U hfree hne hneighbors hnot
  have havCard : ({a, v} : Finset M.Vertex).card = 2 := by simp [Ne.symm hva]
  have havT : ({a, v} : Finset M.Vertex) ⊆ T.1 := by rw [htriangle]; simp
  have havNotBoundary : ¬M.IsBoundaryEdge {a, v} := by
    intro havBoundary
    have havMem : ({a, v} : Finset M.Vertex) ∈ M.boundaryEdges T.1 :=
      M.mem_boundaryEdges_iff.mpr ⟨havT, havCard, havBoundary⟩
    rw [hboundary, Finset.mem_singleton] at havMem
    have hs : ({a, v} : Set M.Vertex) = {a, b} := by
      simpa using congrArg (fun e : Finset M.Vertex => (e : Set M.Vertex)) havMem
    rw [Set.pair_eq_pair_iff] at hs
    exact hs.elim (fun h => hvb h.2) (fun h => hab h.1)
  have havInterior := M.edgeCarrier_diff_vertices_subset_interior_support
    T.2 havCard havT havNotBoundary
  rw [hsupport, bad_free_crosscut_interior_closure (jordan_curve_theorem hC)] at havInterior
  have habMem : ({a, b} : Finset M.Vertex) ∈ M.boundaryEdges T.1 := by
    rw [hboundary]; simp
  have habBoundary := (M.mem_boundaryEdges_iff.mp habMem).2.2
  have haFrontier : M.position a ∈ frontier M.toPlaneComplex.support :=
    M.boundaryEdgeCarrier_subset_frontier habBoundary
      (subset_convexHull ℝ _ ⟨a, by simp, rfl⟩)
  have hfrontier : frontier M.toPlaneComplex.support ⊆ C := by
    rw [hsupport]
    exact frontier_closure_subset.trans_eq (jordan_curve_theorem hC).frontier_inside
  have havImage : M.position '' (({a, v} : Finset M.Vertex) : Set M.Vertex) =
      {M.position a, M.position v} := by ext p; simp [eq_comm]
  have hedge : ({a, v} : Finset M.Vertex) ∈ M.edges := by
    apply Finset.mem_biUnion.mpr
    exact ⟨T.1, T.2, Finset.mem_powersetCard.mpr ⟨havT, havCard⟩⟩
  refine ⟨a, v, hva.symm, hedge, hC,
    isArcBetween_segment (M.position_injective.ne hva.symm),
    isPolygonal_segment _ _, hfrontier haFrontier, hfrontier hvFrontier, ?_⟩
  rw [← convexHull_pair, ← havImage]
  exact havInterior

end Schoenflies

namespace Schoenflies

private theorem exists_restricted_triangle_edge_subset
    (M : TriangleMesh) (f : Finset M.Vertex → Prop) [DecidablePred f]
    {e : Finset M.Vertex} (he : e ∈ M.edges)
    (hs : convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
      (M.restrictTriangles f).toPlaneComplex.support) :
    ∃ T : (M.restrictTriangles f).Triangle, e ⊆ T.1 := by
  have hecard := M.card_of_mem_edges he
  obtain ⟨x, hxe, hxv⟩ := M.exists_nonvertex_mem_edgeCarrier hecard
  have hx := hs hxe
  rw [(M.restrictTriangles f).toPlaneComplex_support] at hx
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
  have htM := ((M.mem_restrictTriangles_triangles f).mp ht).1
  obtain ⟨s, hsM, hes⟩ := Finset.mem_biUnion.mp he
  have hesData := Finset.mem_powersetCard.mp hes
  exact ⟨⟨t, ht⟩, M.edge_subset_of_nonvertex_mem_triangleCarrier
    hecard hesData.1 hsM htM hxe hxt hxv⟩

private theorem restricted_triangle_eq_of_opposite_edge_triangle
    (M : TriangleMesh) (f g : Finset M.Vertex → Prop) [DecidablePred f] [DecidablePred g]
    {e : Finset M.Vertex} (he : e ∈ M.edges)
    (hdisjoint : Disjoint (M.restrictTriangles f).triangles (M.restrictTriangles g).triangles)
    (V : (M.restrictTriangles g).Triangle) (hV : e ⊆ V.1)
    (T U : (M.restrictTriangles f).Triangle) (hT : e ⊆ T.1) (hU : e ⊆ U.1) : T = U := by
  have hVM := ((M.mem_restrictTriangles_triangles g).mp V.2).1
  have hTM := ((M.mem_restrictTriangles_triangles f).mp T.2).1
  have hUM := ((M.mem_restrictTriangles_triangles f).mp U.2).1
  have hTV : T.1 ≠ V.1 := by
    intro h
    exact Finset.disjoint_left.mp hdisjoint (h ▸ T.2) V.2
  have hUV : U.1 ≠ V.1 := by
    intro h
    exact Finset.disjoint_left.mp hdisjoint (h ▸ U.2) V.2
  apply Subtype.ext
  exact M.incidentTriangle_eq_of_ne (M.card_of_mem_edges he)
    (M.mem_incidentTriangles_iff.mpr ⟨hVM, hV⟩)
    (M.mem_incidentTriangles_iff.mpr ⟨hTM, hT⟩)
    (M.mem_incidentTriangles_iff.mpr ⟨hUM, hU⟩) hTV hUV

open scoped Classical in
private theorem exists_unique_triangle_on_each_crosscut_side
    (M : TriangleMesh) {C A₁ A₂ : Set Plane} {p q : Plane}
    (hsupport : M.toPlaneComplex.support = closure (inside C))
    {e : Finset M.Vertex} (he : e ∈ M.edges)
    (hcarrier : convexHull ℝ (M.position '' (e : Set M.Vertex)) = segment ℝ p q)
    (h : IsCrosscut C (segment ℝ p q) p q) (hcut : IsCutPair C p q A₁ A₂) :
    let N₁ := M.restrictTriangles (fun t =>
      (interior (M.triangleCarrier t) ∩ inside (A₁ ∪ segment ℝ p q)).Nonempty)
    let N₂ := M.restrictTriangles (fun t =>
      (interior (M.triangleCarrier t) ∩ inside (A₂ ∪ segment ℝ p q)).Nonempty)
    (∃! T : N₁.Triangle, e ⊆ T.1) ∧ (∃! T : N₂.Triangle, e ⊆ T.1) := by
  classical
  let f₁ := fun t : Finset M.Vertex =>
    (interior (M.triangleCarrier t) ∩ inside (A₁ ∪ segment ℝ p q)).Nonempty
  let f₂ := fun t : Finset M.Vertex =>
    (interior (M.triangleCarrier t) ∩ inside (A₂ ∪ segment ℝ p q)).Nonempty
  obtain ⟨hs₁, hs₂, _, hd, _, _, _, _⟩ :=
    restrict_triangles_crosscut_partition M hsupport he hcarrier h hcut
  have hc₁ : convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
      (M.restrictTriangles f₁).toPlaneComplex.support := by
    rw [hs₁, hcarrier]
    exact Set.Subset.trans Set.subset_union_right
      ((IsRegionOf.inside (A₁ ∪ segment ℝ p q)).subset_closure
        (jordan_curve_theorem (h.isJordanCurve_union hcut)))
  have hc₂ : convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
      (M.restrictTriangles f₂).toPlaneComplex.support := by
    rw [hs₂, hcarrier]
    exact Set.Subset.trans Set.subset_union_right
      ((IsRegionOf.inside (A₂ ∪ segment ℝ p q)).subset_closure
        (jordan_curve_theorem (h.isJordanCurve_union hcut.symm)))
  obtain ⟨T, hT⟩ := exists_restricted_triangle_edge_subset M f₁ he hc₁
  obtain ⟨U, hU⟩ := exists_restricted_triangle_edge_subset M f₂ he hc₂
  constructor
  · exact ⟨T, hT, fun V hV =>
      restricted_triangle_eq_of_opposite_edge_triangle M f₁ f₂ he hd U hU V T hV hT⟩
  · exact ⟨U, hU, fun V hV =>
      restricted_triangle_eq_of_opposite_edge_triangle M f₂ f₁ he hd.symm T hT V U hV hU⟩

end Schoenflies

namespace Schoenflies

private theorem frontier_closure_inside_eq_curve {C : Set Plane}
    (hC : IsSeparating C) : frontier (closure (inside C)) = C := by
  apply Set.Subset.antisymm (frontier_closure_subset.trans_eq hC.frontier_inside)
  intro x hx
  apply (mem_frontier_iff_notMem_interior ((IsRegionOf.inside C).subset_closure hC hx)).mpr
  intro hxi
  have hd : Disjoint (interior (closure (inside C))) (closure (outside C)) :=
    ((disjoint_inside_outside.closure_left hC.isOpen_outside).mono_left
      interior_subset).closure_right isOpen_interior
  exact Set.disjoint_left.mp hd hxi ((IsRegionOf.outside C).subset_closure hC hx)

private theorem triangle_inter_crosscut_subset_endpoints
    (M : TriangleMesh) {a b : M.Vertex} (he : ({a, b} : Finset M.Vertex) ∈ M.edges)
    {t : Finset M.Vertex} (ht : t ∈ M.triangles) (hchord : ¬({a, b} : Finset M.Vertex) ⊆ t) :
    M.triangleCarrier t ∩ segment ℝ (M.position a) (M.position b) ⊆
      {M.position a, M.position b} := by
  classical
  let e : Finset M.Vertex := {a, b}
  have hedgeCard : e.card = 2 := M.card_of_mem_edges he
  have htFace : t ∈ M.toPlaneComplex.simplexes :=
    M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by rw [M.card_triangle t ht]; omega),
      t, ht, subset_rfl⟩
  have hedgeFace : e ∈ M.toPlaneComplex.simplexes := by
    obtain ⟨u, hu, heu⟩ := Finset.mem_biUnion.mp he
    have heuData := Finset.mem_powersetCard.mp heu
    exact M.mem_faces_iff.mpr
      ⟨Finset.card_pos.mp (by rw [hedgeCard]; omega), u, hu, heuData.1⟩
  have hface := M.toPlaneComplex.face_inter t htFace e hedgeFace
  change M.triangleCarrier t ∩ convexHull ℝ (M.position '' (e : Set M.Vertex)) =
    convexHull ℝ (M.position '' ((t ∩ e : Finset M.Vertex) : Set M.Vertex)) at hface
  have hinterCard : (t ∩ e).card ≤ 1 := by
    have hle := Finset.card_le_card (Finset.inter_subset_right : t ∩ e ⊆ e)
    rw [hedgeCard] at hle
    by_contra hnot
    have hcard : (t ∩ e).card = 2 := by omega
    have heq : t ∩ e = e :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hcard, hedgeCard])
    apply hchord
    intro v hv
    have : v ∈ t ∩ e := by rw [heq]; exact hv
    exact (Finset.mem_inter.mp this).1
  have hcarrier : convexHull ℝ (M.position '' (e : Set M.Vertex)) =
      segment ℝ (M.position a) (M.position b) := by
    rw [show M.position '' (e : Set M.Vertex) = {M.position a, M.position b} by
      ext p; simp [e, eq_comm]]
    exact convexHull_pair _ _
  intro x hx
  have hxCommon : x ∈ convexHull ℝ
      (M.position '' ((t ∩ e : Finset M.Vertex) : Set M.Vertex)) := by
    rw [← hface, hcarrier]
    exact hx
  obtain hempty | hne := (t ∩ e).eq_empty_or_nonempty
  · rw [hempty] at hxCommon
    simp at hxCommon
  · obtain ⟨v, hv⟩ := hne
    have hsingleton : t ∩ e = {v} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hv, fun w hw => ?_⟩
      by_contra hwv
      have hpairs : ({v, w} : Finset M.Vertex) ⊆ t ∩ e := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hvw : v ≠ w := Ne.symm hwv
      have htwo : ({v, w} : Finset M.Vertex).card = 2 := by simp [hvw]
      have := Finset.card_le_card hpairs
      rw [htwo] at this
      omega
    rw [hsingleton] at hxCommon
    have hxv : x = M.position v := by simpa using hxCommon
    rw [hxv]
    have hvEdge : v ∈ e := (Finset.mem_inter.mp hv).2
    have hvab : v = a ∨ v = b := by simpa [e] using hvEdge
    rcases hvab with rfl | rfl <;> simp

open scoped Classical in
private theorem frontier_inter_triangleCarrier_crosscut_side
    (M : TriangleMesh) {C A₁ A₂ : Set Plane} {a b : M.Vertex}
    (hsupport : M.toPlaneComplex.support = closure (inside C))
    (he : ({a, b} : Finset M.Vertex) ∈ M.edges)
    (h : IsCrosscut C (segment ℝ (M.position a) (M.position b))
      (M.position a) (M.position b))
    (hcut : IsCutPair C (M.position a) (M.position b) A₁ A₂)
    {t : Finset M.Vertex}
    (ht : t ∈ (M.restrictTriangles (fun u =>
      (interior (M.triangleCarrier u) ∩
        inside (A₁ ∪ segment ℝ (M.position a) (M.position b))).Nonempty)).triangles)
    (hchord : ¬({a, b} : Finset M.Vertex) ⊆ t) :
    frontier M.toPlaneComplex.support ∩ M.triangleCarrier t =
      frontier (M.restrictTriangles (fun u =>
        (interior (M.triangleCarrier u) ∩
          inside (A₁ ∪ segment ℝ (M.position a) (M.position b))).Nonempty)).toPlaneComplex.support ∩
            M.triangleCarrier t := by
  classical
  let E := segment ℝ (M.position a) (M.position b)
  let f := fun u : Finset M.Vertex => (interior (M.triangleCarrier u) ∩ inside (A₁ ∪ E)).Nonempty
  let N := M.restrictTriangles f
  have htM := ((M.mem_restrictTriangles_triangles f).mp ht).1
  have hcarrier : convexHull ℝ (M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex)) =
      E := by
    rw [show M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex) =
      {M.position a, M.position b} by ext p; simp [eq_comm]]
    exact convexHull_pair _ _
  have hs : N.toPlaneComplex.support = closure (inside (A₁ ∪ E)) :=
    (restrict_triangles_crosscut_partition M hsupport he hcarrier h hcut).1
  have htriangleSubset : M.triangleCarrier t ⊆ closure (inside (A₁ ∪ E)) := by
    rw [← hs, N.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset t (Set.subset_iUnion_of_subset ht subset_rfl)
  have hchordMeet := triangle_inter_crosscut_subset_endpoints M he htM hchord
  have hcross := crosscut_theorem h hcut
  have htrace : closure (inside (A₁ ∪ E)) ∩ C = A₁ := hcross.2.2.2.2.2.2.2.2.1
  change frontier M.toPlaneComplex.support ∩ M.triangleCarrier t =
    frontier N.toPlaneComplex.support ∩ M.triangleCarrier t
  rw [hsupport, hs, frontier_closure_inside_eq_curve (jordan_curve_theorem h.curve),
    frontier_closure_inside_eq_curve (jordan_curve_theorem (h.isJordanCurve_union hcut))]
  ext x
  constructor
  · rintro ⟨hxC, hxT⟩
    exact ⟨Or.inl (htrace ▸ ⟨htriangleSubset hxT, hxC⟩), hxT⟩
  · rintro ⟨hxA | hxE, hxT⟩
    · exact ⟨hcut.union_eq ▸ Or.inl hxA, hxT⟩
    · have hxEnds := hchordMeet ⟨hxT, hxE⟩
      rcases hxEnds with rfl | rfl
      · exact ⟨h.left_mem, hxT⟩
      · exact ⟨h.right_mem, hxT⟩

open scoped Classical in
private theorem isGeometricallyFreeTriangle_of_crosscut_side
    (M : TriangleMesh) {C A₁ A₂ : Set Plane} {a b : M.Vertex}
    (hsupport : M.toPlaneComplex.support = closure (inside C))
    (he : ({a, b} : Finset M.Vertex) ∈ M.edges)
    (h : IsCrosscut C (segment ℝ (M.position a) (M.position b))
      (M.position a) (M.position b))
    (hcut : IsCutPair C (M.position a) (M.position b) A₁ A₂)
    (T : (M.restrictTriangles (fun u =>
      (interior (M.triangleCarrier u) ∩
        inside (A₁ ∪ segment ℝ (M.position a) (M.position b))).Nonempty)).Triangle)
    (hfree : (M.restrictTriangles (fun u =>
      (interior (M.triangleCarrier u) ∩
        inside (A₁ ∪ segment ℝ (M.position a) (M.position b))).Nonempty)).IsGeometricallyFreeTriangle T)
    (hchord : ¬({a, b} : Finset M.Vertex) ⊆ T.1) :
    M.IsGeometricallyFreeTriangle
      ⟨T.1, ((M.mem_restrictTriangles_triangles _).mp T.2).1⟩ := by
  classical
  obtain ⟨k, hfree | hfree⟩ := hfree
  · refine ⟨k, Or.inl ?_⟩
    rw [TriangleMesh.IsOneEdgeFreeTriangle,
      frontier_inter_triangleCarrier_crosscut_side M hsupport he h hcut T.2 hchord]
    exact hfree
  · refine ⟨k, Or.inr ?_⟩
    rw [TriangleMesh.IsTwoEdgeFreeTriangle,
      frontier_inter_triangleCarrier_crosscut_side M hsupport he h hcut T.2 hchord]
    exact hfree

end Schoenflies

namespace Schoenflies

private theorem closure_inside_crosscut_sides_inter
    {C E A R : Set Plane} {a b : Plane}
    (h : IsCrosscut C E a b) (hcut : IsCutPair C a b A R) :
    closure (inside (R ∪ E)) ∩ closure (inside (A ∪ E)) = E := by
  have hsep₁ := jordan_curve_theorem (h.isJordanCurve_union hcut)
  have hsep₂ := jordan_curve_theorem (h.isJordanCurve_union hcut.symm)
  have hd := (crosscut_theorem h hcut).2.1
  have hd₁ := hd.closure_right hsep₁.isOpen_inside
  have hd₂ := hd.closure_left hsep₂.isOpen_inside
  apply Set.Subset.antisymm
  · rintro x ⟨hx₂, hx₁⟩
    have hxa : x ∈ A ∪ E := by
      have hx := hx₁
      rw [(IsRegionOf.inside (A ∪ E)).closure_eq hsep₁] at hx
      exact hx.resolve_left fun hxi => Set.disjoint_left.mp hd₁ hxi hx₂
    have hxr : x ∈ R ∪ E := by
      have hx := hx₂
      rw [(IsRegionOf.inside (R ∪ E)).closure_eq hsep₂] at hx
      exact hx.resolve_left fun hxi => Set.disjoint_left.mp hd₂ hx₁ hxi
    rcases hxa with hxA | hxE
    · rcases hxr with hxR | hxE
      · have hxEnds : x ∈ ({a, b} : Set Plane) := hcut.inter_eq ▸ ⟨hxA, hxR⟩
        rcases hxEnds with rfl | rfl
        · exact h.arc.left_mem
        · exact h.arc.right_mem
      · exact hxE
    · exact hxE
  · intro x hx
    exact ⟨(IsRegionOf.inside (R ∪ E)).subset_closure hsep₂ (Or.inr hx),
      (IsRegionOf.inside (A ∪ E)).subset_closure hsep₁ (Or.inr hx)⟩


open scoped Classical in
private theorem exists_geometricallyFreeTriangle_of_crosscut_side_card_one
    (M : TriangleMesh) {C A₁ A₂ : Set Plane} {p q : Plane}
    (hsupport : M.toPlaneComplex.support = closure (inside C))
    {e : Finset M.Vertex} (he : e ∈ M.edges)
    (hcarrier : convexHull ℝ (M.position '' (e : Set M.Vertex)) = segment ℝ p q)
    (h : IsCrosscut C (segment ℝ p q) p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcard : (M.restrictTriangles (fun t =>
      (interior (M.triangleCarrier t) ∩ inside (A₁ ∪ segment ℝ p q)).Nonempty)).triangles.card = 1) :
    ∃ T : (M.restrictTriangles (fun t =>
      (interior (M.triangleCarrier t) ∩ inside (A₁ ∪ segment ℝ p q)).Nonempty)).Triangle,
      M.IsGeometricallyFreeTriangle
        ⟨T.1, ((M.mem_restrictTriangles_triangles _).mp T.2).1⟩ := by
  classical
  let f₁ := fun t : Finset M.Vertex =>
    (interior (M.triangleCarrier t) ∩ inside (A₁ ∪ segment ℝ p q)).Nonempty
  let f₂ := fun t : Finset M.Vertex =>
    (interior (M.triangleCarrier t) ∩ inside (A₂ ∪ segment ℝ p q)).Nonempty
  let N₁ := M.restrictTriangles f₁
  let N₂ := M.restrictTriangles f₂
  obtain ⟨hs₁, hs₂, hunion, _, _, _, _, _⟩ :=
    restrict_triangles_crosscut_partition M hsupport he hcarrier h hcut
  obtain ⟨T, hchordT, _⟩ :=
    (exists_unique_triangle_on_each_crosscut_side M hsupport he hcarrier h hcut).1
  let t : Finset M.Vertex := T.1
  change e ⊆ t at hchordT
  have hedgeCard := M.card_of_mem_edges he
  have hchordNotBoundary : ¬M.IsBoundaryEdge e := by
    intro hboundary
    obtain ⟨x, hxE, hxEndpoint⟩ := Set.not_subset.mp h.arc.not_subset_pair
    have hxInside := h.sdiff_subset ⟨hxE, hxEndpoint⟩
    have hxFrontier : x ∈ frontier M.toPlaneComplex.support :=
      M.boundaryEdgeCarrier_subset_frontier hboundary (by rwa [hcarrier])
    rw [hsupport] at hxFrontier
    have hxC : x ∈ C :=
      (frontier_closure_subset.trans_eq (jordan_curve_theorem h.curve).frontier_inside) hxFrontier
    exact inside_subset_compl hxInside hxC
  have hTM : t ∈ M.triangles := ((M.mem_restrictTriangles_triangles f₁).mp T.2).1
  have hboundary : M.boundaryEdges t = (M.triangleEdges t).erase e := by
    ext d
    rw [M.mem_boundaryEdges_iff, Finset.mem_erase]
    constructor
    · rintro ⟨hdT, hdcard, hdBoundary⟩
      refine ⟨?_, Finset.mem_powersetCard.mpr ⟨hdT, hdcard⟩⟩
      intro hde
      exact hchordNotBoundary (hde ▸ hdBoundary)
    · rintro ⟨hdne, hdTriangle⟩
      have hdData := Finset.mem_powersetCard.mp hdTriangle
      have hdEdge : d ∈ M.edges := Finset.mem_biUnion.mpr ⟨t, hTM, hdTriangle⟩
      refine ⟨hdData.1, hdData.2, hdEdge, ?_⟩
      by_contra hdNotBoundary
      have hdNotBoundary' : ¬M.IsBoundaryEdge d := fun h => hdNotBoundary h.2
      have hincidentCard := M.card_incidentTriangles_eq_two_of_not_boundary
        hTM hdData.2 hdData.1 hdNotBoundary'
      have hTi : t ∈ M.incidentTriangles d :=
        M.mem_incidentTriangles_iff.mpr ⟨hTM, hdData.1⟩
      have hother : ∃ u ∈ M.incidentTriangles d, u ≠ t := by
        by_contra h
        push Not at h
        have hsingleton : M.incidentTriangles d = {t} := by
          ext u
          constructor
          · exact fun hu => Finset.mem_singleton.mpr (h u hu)
          · intro hu
            rw [Finset.mem_singleton.mp hu]
            exact hTi
        have hone : (M.incidentTriangles d).card = 1 := by
          rw [hsingleton, Finset.card_singleton]
        omega
      obtain ⟨u, hui, huT⟩ := hother
      have huData := M.mem_incidentTriangles_iff.mp hui
      have hu₂ : u ∈ N₂.triangles := by
        have huEither : u ∈ N₁.triangles ∪ N₂.triangles := hunion.symm ▸ huData.1
        rcases Finset.mem_union.mp huEither with hu₁ | hu₂
        · have huEq : u = t := by
            by_contra hne
            have htwo : 1 < N₁.triangles.card :=
              Finset.one_lt_card.mpr ⟨t, T.2, u, hu₁, Ne.symm hne⟩
            change N₁.triangles.card = 1 at hcard
            omega
          exact False.elim (huT huEq)
        · exact hu₂
      obtain ⟨x, hxD, hxv⟩ := M.exists_nonvertex_mem_edgeCarrier hdData.2
      have hx₁ : x ∈ closure (inside (A₁ ∪ segment ℝ p q)) := by
        rw [← hs₁, N₁.toPlaneComplex_support]
        exact Set.mem_iUnion_of_mem t <| Set.mem_iUnion_of_mem T.2 <|
          convexHull_mono (Set.image_mono hdData.1) hxD
      have hx₂ : x ∈ closure (inside (A₂ ∪ segment ℝ p q)) := by
        rw [← hs₂, N₂.toPlaneComplex_support]
        exact Set.mem_iUnion_of_mem u <| Set.mem_iUnion_of_mem hu₂ <|
          convexHull_mono (Set.image_mono huData.2) hxD
      have hxE : x ∈ segment ℝ p q :=
        closure_inside_crosscut_sides_inter h hcut ▸ ⟨hx₂, hx₁⟩
      have hde : d = e := M.edge_eq_of_nonvertex_mem_edgeCarriers hdEdge he
        hxD (by rwa [hcarrier]) hxv
      exact hdne hde
  have hboundaryCard : (M.boundaryEdges t).card = 2 := by
    rw [hboundary, Finset.card_erase_of_mem]
    · rw [M.card_triangleEdges hTM]
    · exact Finset.mem_powersetCard.mpr ⟨hchordT, hedgeCard⟩
  have hnoIsolated :=
    M.hasNoIsolatedFrontierVertex_of_boundaryEdges_card_two ⟨t, hTM⟩ hboundaryCard
  exact ⟨T, M.isGeometricallyFreeTriangle_of_boundaryEdges_card_two
    ⟨t, hTM⟩ hnoIsolated hboundaryCard⟩

end Schoenflies

namespace Schoenflies

private theorem exists_geometrically_free_triangle_not_containing_edge
    (M : TriangleMesh) (e : Finset M.Vertex)
    (T U : M.Triangle) (hne : T.1 ≠ U.1)
    (hT : M.IsGeometricallyFreeTriangle T) (hU : M.IsGeometricallyFreeTriangle U)
    (hunique : ∃! X : M.Triangle, e ⊆ X.1) :
    ∃ X : M.Triangle, M.IsGeometricallyFreeTriangle X ∧ ¬e ⊆ X.1 := by
  by_cases heT : e ⊆ T.1
  · refine ⟨U, hU, ?_⟩
    intro heU
    obtain ⟨X, _, hX⟩ := hunique
    exact hne (congrArg Subtype.val ((hX T heT).trans (hX U heU).symm))
  · exact ⟨T, hT, heT⟩

theorem _root_.LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.exists_two_geometrically_free_triangles_of_jordan_support
    (M : TriangleMesh) (C : Set Plane) (hC : IsJordanCurve C)
    (hsupport : M.toPlaneComplex.support = closure (inside C))
    (hmore : 1 < M.triangles.card) :
    ∃ T U : M.Triangle, T.1 ≠ U.1 ∧
      M.IsGeometricallyFreeTriangle T ∧ M.IsGeometricallyFreeTriangle U := by
  classical
  induction hcardM : M.triangles.card using Nat.strong_induction_on generalizing M C with
  | h n ih =>
    have hfrontier : IsJordanCurve (frontier M.toPlaneComplex.support) := by
      rw [hsupport, frontier_closure_inside_eq_curve (jordan_curve_theorem hC)]
      exact hC
    have hconnected : IsPreconnected (interior M.toPlaneComplex.support) := by
      rw [hsupport, bad_free_crosscut_interior_closure (jordan_curve_theorem hC)]
      exact (jordan_curve_theorem hC).isConnected_inside.isPreconnected
    obtain ⟨T, U, hTU, hTfree, hUfree⟩ :=
      M.exists_two_free_triangles_of_isJordanCurve_frontier hfrontier hmore
    obtain ⟨NT, hTNT, hTneighbor⟩ :=
      M.exists_edge_neighbor_of_isPreconnected_interior hconnected T hmore
    obtain ⟨NU, hUNU, hUneighbor⟩ :=
      M.exists_edge_neighbor_of_isPreconnected_interior hconnected U hmore
    have hardCase (X N : M.Triangle) (hXfree : M.IsFreeTriangle X.1)
        (hXN : X.1 ≠ N.1) (hneighbor : M.AreEdgeNeighbors X.1 N.1)
        (hbad : ¬M.HasNoIsolatedFrontierVertex X.1) :
        ∃ T U : M.Triangle, T.1 ≠ U.1 ∧
          M.IsGeometricallyFreeTriangle T ∧ M.IsGeometricallyFreeTriangle U := by
      obtain ⟨a, b, hab, he, hcross⟩ :=
        exists_mesh_crosscut_of_bad_free_triangle M hC hsupport X N
          hXfree hXN hneighbor hbad
      obtain ⟨A₁, A₂, hcut⟩ := exists_isCutPair hC hcross.left_mem hcross.right_mem
        (M.position_injective.ne hab)
      let E := segment ℝ (M.position a) (M.position b)
      have hcarrier : convexHull ℝ (M.position ''
          (({a, b} : Finset M.Vertex) : Set M.Vertex)) = E := by
        rw [show M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex) =
          {M.position a, M.position b} by ext p; simp [eq_comm]]
        exact convexHull_pair _ _
      have hside (A R : Set Plane)
          (hc : IsCutPair C (M.position a) (M.position b) A R) :
          ∃ V : (M.restrictTriangles (fun t =>
            (interior (M.triangleCarrier t) ∩ inside (A ∪ E)).Nonempty)).Triangle,
            M.IsGeometricallyFreeTriangle
              ⟨V.1, ((M.mem_restrictTriangles_triangles _).mp V.2).1⟩ := by
        let f := fun t : Finset M.Vertex =>
          (interior (M.triangleCarrier t) ∩ inside (A ∪ E)).Nonempty
        let S := M.restrictTriangles f
        obtain ⟨hs, _, _, _, hn, _, hlt, _⟩ :=
          restrict_triangles_crosscut_partition M hsupport he hcarrier hcross hc
        by_cases hcard : S.triangles.card = 1
        · exact exists_geometricallyFreeTriangle_of_crosscut_side_card_one
            M hsupport he hcarrier hcross hc hcard
        · have hmoreS : 1 < S.triangles.card := by
            have hpos := Finset.card_pos.mpr hn
            change 0 < S.triangles.card at hpos
            omega
          obtain ⟨V, W, hVW, hVgeom, hWgeom⟩ := ih S.triangles.card
            (by simpa [hcardM] using hlt) S (A ∪ E)
            (hcross.isJordanCurve_union hc) hs hmoreS rfl
          have hunique : ∃! V : S.Triangle, ({a, b} : Finset M.Vertex) ⊆ V.1 :=
            (exists_unique_triangle_on_each_crosscut_side M hsupport he hcarrier hcross hc).1
          obtain ⟨Z, hZgeom, hZchord⟩ :=
            exists_geometrically_free_triangle_not_containing_edge S {a, b}
              V W hVW hVgeom hWgeom hunique
          exact ⟨Z, isGeometricallyFreeTriangle_of_crosscut_side
            M hsupport he hcross hc Z hZgeom hZchord⟩
      obtain ⟨V, hVgeom⟩ := hside A₁ A₂ hcut
      obtain ⟨W, hWgeom⟩ := hside A₂ A₁ hcut.symm
      let VM : M.Triangle := ⟨V.1, ((M.mem_restrictTriangles_triangles _).mp V.2).1⟩
      let WM : M.Triangle := ⟨W.1, ((M.mem_restrictTriangles_triangles _).mp W.2).1⟩
      have hd := (restrict_triangles_crosscut_partition M hsupport he hcarrier hcross hcut).2.2.2.1
      have hVW : VM.1 ≠ WM.1 := by
        intro heq
        exact Finset.disjoint_left.mp hd (heq ▸ V.2) W.2
      exact ⟨VM, WM, hVW, hVgeom, hWgeom⟩
    by_cases hTvertices : M.HasNoIsolatedFrontierVertex T.1
    · have hTgeom := M.isGeometricallyFreeTriangle_of_isFreeTriangle
        T NT hTfree hTNT hTneighbor hTvertices
      by_cases hUvertices : M.HasNoIsolatedFrontierVertex U.1
      · exact ⟨T, U, hTU, hTgeom,
          M.isGeometricallyFreeTriangle_of_isFreeTriangle
            U NU hUfree hUNU hUneighbor hUvertices⟩
      · exact hardCase U NU hUfree hUNU hUneighbor hUvertices
    · exact hardCase T NT hTfree hTNT hTneighbor hTvertices

end Schoenflies

namespace Schoenflies

theorem PrePolygon.exists_triangle_mesh_inside_singleton_or_two_geometrically_free {m : ℕ}
    (P : PrePolygon m) :
    ∃ M : TriangleMesh,
      M.toPlaneComplex.support = closure (inside P.carrier) ∧
      frontier M.toPlaneComplex.support = P.carrier ∧
      (M.triangles.card = 1 ∨ ∃ T U : M.Triangle,
        T.1 ≠ U.1 ∧ M.IsGeometricallyFreeTriangle T ∧ M.IsGeometricallyFreeTriangle U) := by
  obtain ⟨M, hsupport, hfrontier⟩ := P.exists_triangle_mesh_inside
  refine ⟨M, hsupport, hfrontier, ?_⟩
  obtain ⟨x, hx⟩ := P.isSeparating_carrier.isConnected_inside.nonempty
  have hxSupport : x ∈ M.toPlaneComplex.support := by
    rw [hsupport]
    exact subset_closure hx
  rw [M.toPlaneComplex_support] at hxSupport
  obtain ⟨t, ht, -⟩ := Set.mem_iUnion₂.mp hxSupport
  have hpos : 0 < M.triangles.card := Finset.card_pos.mpr ⟨t, ht⟩
  by_cases hmore : 1 < M.triangles.card
  · exact Or.inr (M.exists_two_geometrically_free_triangles_of_jordan_support
      P.carrier P.isJordanCurve_carrier hsupport hmore)
  · exact Or.inl (by omega)

end Schoenflies
