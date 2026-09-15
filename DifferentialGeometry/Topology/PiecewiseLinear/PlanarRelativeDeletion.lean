import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLBall.image_eq_of_image_frontier_eq {P : Set Plane}
    (hP : IsPLBall 2 P) (g : Plane ≃ₜ Plane)
    (hfrontier : g '' frontier P = frontier P) : g '' P = P := by
  obtain ⟨J, hJ⟩ := exists_polygonalCircle_of_isPLBall_two hP
  have hcompact : IsCompact (g '' P) := hP.isPolyhedron.isCompact.image g.continuous
  have hboundary : frontier (g '' P) = J.carrier := by
    rw [← g.image_frontier, hfrontier, ← hJ, J.frontier_closedRegion]
  have hinterior : (interior (g '' P)).Nonempty := by
    rw [← g.image_interior]
    exact hP.interior_nonempty.image g
  exact (J.eq_closedRegion_of_isCompact_frontier_eq hcompact hboundary hinterior).trans hJ

namespace TriangleMesh

theorem isPLBall_triangleCarrier (M : TriangleMesh) (T : M.Triangle) :
    IsPLBall 2 (M.triangleCarrier T.1) := by
  apply isPLBall_two_of_isTriangle
  refine ⟨M.position ∘ M.orderedVertex T, M.orderedVertex_affineIndependent T, ?_⟩
  rw [Set.range_comp, M.range_orderedVertex T]
  rfl

theorem image_support_eq_eraseTriangle_of_restrictTriangles
    (M : TriangleMesh) (p : Finset M.Vertex → Prop) [DecidablePred p]
    (t : Finset M.Vertex) (hpt : p t) (f : Plane → Plane)
    (hlocal : f '' (M.restrictTriangles p).toPlaneComplex.support =
      ((M.restrictTriangles p).eraseTriangle t).toPlaneComplex.support)
    (houtside : ∀ u ∈ M.triangles, ¬p u → f '' M.triangleCarrier u = M.triangleCarrier u) :
    f '' M.toPlaneComplex.support = (M.eraseTriangle t).toPlaneComplex.support := by
  let N := M.restrictTriangles p
  let L := M.restrictTriangles fun u => ¬p u
  have hsupport : M.toPlaneComplex.support = N.toPlaneComplex.support ∪ L.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support, N.toPlaneComplex_support, L.toPlaneComplex_support]
    change (⋃ u ∈ M.triangles, M.triangleCarrier u) =
      (⋃ u ∈ M.triangles.filter p, M.triangleCarrier u) ∪
        ⋃ u ∈ M.triangles.filter (fun v => ¬p v), M.triangleCarrier u
    ext x
    simp only [mem_iUnion, Finset.mem_filter, mem_union]
    constructor
    · rintro ⟨u, hu, hxu⟩
      by_cases hpu : p u
      · exact Or.inl ⟨u, ⟨hu, hpu⟩, hxu⟩
      · exact Or.inr ⟨u, ⟨hu, hpu⟩, hxu⟩
    · rintro (⟨u, ⟨hu, _⟩, hxu⟩ | ⟨u, ⟨hu, _⟩, hxu⟩)
      · exact ⟨u, hu, hxu⟩
      · exact ⟨u, hu, hxu⟩
  have herase : (M.eraseTriangle t).toPlaneComplex.support =
      (N.eraseTriangle t).toPlaneComplex.support ∪ L.toPlaneComplex.support := by
    rw [(M.eraseTriangle t).toPlaneComplex_support,
      (N.eraseTriangle t).toPlaneComplex_support, L.toPlaneComplex_support]
    change (⋃ u ∈ M.triangles.erase t, M.triangleCarrier u) =
      (⋃ u ∈ (M.triangles.filter p).erase t, M.triangleCarrier u) ∪
        ⋃ u ∈ M.triangles.filter (fun v => ¬p v), M.triangleCarrier u
    ext x
    simp only [mem_iUnion, Finset.mem_filter, Finset.mem_erase, mem_union]
    constructor
    · rintro ⟨u, ⟨hut, hu⟩, hxu⟩
      by_cases hpu : p u
      · exact Or.inl ⟨u, ⟨hut, hu, hpu⟩, hxu⟩
      · exact Or.inr ⟨u, ⟨hu, hpu⟩, hxu⟩
    · rintro (⟨u, ⟨hut, hu, _⟩, hxu⟩ | ⟨u, ⟨hu, hpu⟩, hxu⟩)
      · exact ⟨u, ⟨hut, hu⟩, hxu⟩
      · exact ⟨u, ⟨fun h => hpu (h ▸ hpt), hu⟩, hxu⟩
  have hL : f '' L.toPlaneComplex.support = L.toPlaneComplex.support := by
    rw [L.toPlaneComplex_support, image_iUnion]
    apply iUnion_congr
    intro u
    rw [image_iUnion]
    apply iUnion_congr
    intro hu
    have huData := (M.mem_restrictTriangles_triangles (fun u => ¬p u)).mp hu
    exact houtside u huData.1 huData.2
  rw [hsupport, image_union, hlocal, hL, herase]

private theorem card_inter_le_one_of_subset_edge (M : TriangleMesh)
    (u t e : Finset M.Vertex) (he : e.card = 2) (hsub : u ∩ t ⊆ e) (hnot : ¬e ⊆ u) :
    (u ∩ t).card ≤ 1 := by
  by_contra h
  have heq : u ∩ t = e := Finset.eq_of_subset_of_card_le hsub (by rw [he]; omega)
  apply hnot
  rw [← heq]
  exact Finset.inter_subset_left

theorem inter_subset_freeTriangleBaseEdge_of_oneEdgeFree
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hfree : M.IsOneEdgeFreeTriangle T k) {u : Finset M.Vertex} (hu : u ∈ M.triangles)
    (hapex : M.orderedVertex T k ∉ u) :
    u ∩ T.1 ⊆ M.freeTriangleBaseEdge T k ∧ (u ∩ T.1).card ≤ 1 := by
  have hsub : u ∩ T.1 ⊆ M.freeTriangleBaseEdge T k := by
    intro v hv
    have hvT : v ∈ Set.range (M.orderedVertex T) := by
      rw [M.range_orderedVertex T]
      exact (Finset.mem_inter.mp hv).2
    obtain ⟨i, rfl⟩ := hvT
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩
    intro hik
    exact hapex (hik ▸ (Finset.mem_inter.mp hv).1)
  have hnot : ¬M.freeTriangleBaseEdge T k ⊆ u := by
    intro hbase
    have hboundary := M.isBoundaryEdge_freeTriangleBaseEdge_of_oneEdgeFree T k hfree
    have huInc : u ∈ M.incidentTriangles (M.freeTriangleBaseEdge T k) :=
      M.mem_incidentTriangles_iff.mpr ⟨hu, hbase⟩
    have hTInc : T.1 ∈ M.incidentTriangles (M.freeTriangleBaseEdge T k) :=
      M.mem_incidentTriangles_iff.mpr ⟨T.2, M.freeTriangleBaseEdge_subset T k⟩
    have huT : u = T.1 := Finset.card_le_one.mp hboundary.2.le u huInc T.1 hTInc
    exact hapex (huT ▸ M.orderedVertex_mem T k)
  exact ⟨hsub, card_inter_le_one_of_subset_edge M u T.1 (M.freeTriangleBaseEdge T k)
    (M.freeTriangleBaseEdge_card T k) hsub hnot⟩

theorem inter_subset_freeTriangleBaseEdge_of_twoEdgeFree
    (M : TriangleMesh) (hM : IsPLBall 2 M.toPlaneComplex.support)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k)
    {u : Finset M.Vertex} (hu : u ∈ M.triangles) (hbase : ¬M.freeTriangleBaseEdge T k ⊆ u) :
    u ∩ T.1 ⊆ M.freeTriangleBaseEdge T k ∧ (u ∩ T.1).card ≤ 1 := by
  have huT : u ≠ T.1 := fun h => hbase (h ▸ M.freeTriangleBaseEdge_subset T k)
  obtain ⟨J, hJ⟩ := exists_polygonalCircle_of_isPLBall_two hM
  obtain ⟨J', hregion, hinter⟩ :=
    M.exists_polygonalDisk_eraseTriangle_of_twoEdgeFree J hJ.symm T k hfree
  have hsub : u ∩ T.1 ⊆ M.freeTriangleBaseEdge T k := by
    intro v hv
    obtain ⟨hvu, hvT⟩ := Finset.mem_inter.mp hv
    apply M.vertex_mem_edge_of_position_mem_edgeCarrier T.2 hvT
      (M.freeTriangleBaseEdge_mem_edges T k)
    rw [M.freeTriangleBaseEdge_carrier T k, ← hinter, ← hregion]
    refine ⟨?_, subset_convexHull ℝ _ ⟨v, hvT, rfl⟩⟩
    rw [(M.eraseTriangle T.1).toPlaneComplex_support]
    exact mem_iUnion₂.mpr ⟨u, Finset.mem_erase.mpr ⟨huT, hu⟩,
      subset_convexHull ℝ _ ⟨v, hvu, rfl⟩⟩
  exact ⟨hsub, card_inter_le_one_of_subset_edge M u T.1 (M.freeTriangleBaseEdge T k)
    (M.freeTriangleBaseEdge_card T k) hsub hbase⟩

theorem exists_isPLHomeomorphOn_eraseTriangle_restrictTriangles
    (M : TriangleMesh) (p : Finset M.Vertex → Prop) [DecidablePred p]
    (T : (M.restrictTriangles p).Triangle) (k : Fin 3)
    (hM : IsPLBall 2 (M.restrictTriangles p).toPlaneComplex.support)
    (hfree : (M.restrictTriangles p).IsOneEdgeFreeTriangle T k ∨
      (M.restrictTriangles p).IsTwoEdgeFreeTriangle T k)
    (hmore : 1 < (M.restrictTriangles p).triangles.card)
    (hcommon : ∀ u ∈ M.triangles, ¬p u →
      u ∩ T.1 ⊆ (M.restrictTriangles p).freeTriangleBaseEdge T k)
    (hcard : ∀ u ∈ M.triangles, ¬p u → (u ∩ T.1).card ≤ 1)
    {U : Set Plane} (hU : IsOpen U) (hTU : M.triangleCarrier T.1 ⊆ U) :
    ∃ g : Plane ≃ₜ Plane, IsPLHomeomorphOn g univ univ ∧ EqOn g id Uᶜ ∧
      EqOn g id (frontier (M.restrictTriangles p).toPlaneComplex.support \ M.triangleCarrier T.1) ∧
      (∀ u ∈ M.triangles, ¬p u → g '' M.triangleCarrier u = M.triangleCarrier u) ∧
      g '' M.toPlaneComplex.support = (M.eraseTriangle T.1).toPlaneComplex.support ∧
      g '' (M.restrictTriangles p).toPlaneComplex.support =
        ((M.restrictTriangles p).eraseTriangle T.1).toPlaneComplex.support ∧
      IsPLBall 2 ((M.restrictTriangles p).eraseTriangle T.1).toPlaneComplex.support := by
  let N := M.restrictTriangles p
  have hT : T.1 ∈ M.triangles ∧ p T.1 := (M.mem_restrictTriangles_triangles p).mp T.2
  let T' : M.Triangle := ⟨T.1, hT.1⟩
  let I := {e : Finset M.Vertex // e ∈ M.edges ∧ ∃ u ∈ M.triangles, ¬p u ∧ e ⊆ u}
  let A : I → Set Plane := fun e => convexHull ℝ (M.position '' (e.1 : Set M.Vertex))
  have hA : ∀ i, ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      transportedThinKitePatch (N.freeTriangleAffineEquiv T k) δ ∩ A i ⊆
        {N.freeTriangleOrder T k 0, N.freeTriangleOrder T k 1} := by
    intro e
    obtain ⟨u, hu, hpu, heu⟩ := e.2.2
    have hinter : e.1 ∩ T.1 ⊆ u ∩ T.1 := Finset.inter_subset_inter heu subset_rfl
    exact exists_eventually_transportedThinKitePatch_inter_edge_subset_baseEndpoints
      M T' k e.1 e.2.1 (hinter.trans (hcommon u hu hpu))
      ((Finset.card_le_card hinter).trans (hcard u hu hpu))
  obtain ⟨J, hJ⟩ := exists_polygonalCircle_of_isPLBall_two hM
  obtain ⟨g, J', hg, hfix, hboundary, hfamily, hfront, hregion⟩ :
      ∃ (g : Plane ≃ₜ Plane) (J' : PolygonalCircle),
        IsPLHomeomorphOn g univ univ ∧ EqOn g id Uᶜ ∧
        EqOn g id (frontier N.toPlaneComplex.support \ N.triangleCarrier T.1) ∧
        EqOn g id (⋃ i, A i) ∧
        g '' frontier N.toPlaneComplex.support =
          frontier (N.eraseTriangle T.1).toPlaneComplex.support ∧
        (N.eraseTriangle T.1).toPlaneComplex.support = J'.closedRegion := by
    rcases hfree with hfree | hfree
    · exact exists_isPLHomeomorphOn_remove_oneEdgeFree_triangle_fixing_frontier_and_family
        N J hJ.symm T k hfree hmore A hA U hU hTU
    · exact exists_isPLHomeomorphOn_remove_twoEdgeFree_triangle_fixing_frontier_and_family
        N J hJ.symm T k hfree A hA U hU hTU
  have houtside : ∀ u ∈ M.triangles, ¬p u →
      g '' M.triangleCarrier u = M.triangleCarrier u := by
    intro u hu hpu
    apply (isPLBall_triangleCarrier M ⟨u, hu⟩).image_eq_of_image_frontier_eq g
    have hfixu : EqOn g id (frontier (M.triangleCarrier u)) := by
      intro x hx
      obtain ⟨e, hecard, heu, hxe⟩ := M.exists_edge_of_mem_frontier_triangle hu hx
      have he : e ∈ M.edges := Finset.mem_biUnion.mpr
        ⟨u, hu, Finset.mem_powersetCard.mpr ⟨heu, hecard⟩⟩
      exact hfamily (mem_iUnion.mpr ⟨⟨e, he, u, hu, hpu, heu⟩, hxe⟩)
    calc
      g '' frontier (M.triangleCarrier u) = id '' frontier (M.triangleCarrier u) := hfixu.image_eq
      _ = frontier (M.triangleCarrier u) := image_id _
  have hlocal := PolygonalCircle.TriangleMesh.image_support_eq_of_polygonalDisk_frontier
    N J' ⟨T.1, T.2⟩ g (N.eraseTriangle T.1) hfront hregion
  refine ⟨g, hg, hfix, hboundary, houtside,
    image_support_eq_eraseTriangle_of_restrictTriangles M p T.1 hT.2 g hlocal houtside,
    hlocal, ?_⟩
  rw [hregion]
  exact isPLBall_two_closedRegion J'

end TriangleMesh

end DifferentialGeometry.Topology.PiecewiseLinear
