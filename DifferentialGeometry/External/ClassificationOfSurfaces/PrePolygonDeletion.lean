/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
Adapted compact-frontier recognition from PolygonalSchoenflies.lean at
 e3c7230fe78d7b056a415d9ecae6f77887046b32 to the native separating-curve API.
See MODIFICATIONS.md and DELETION_PROVENANCE.json for source and local changes.
-/
import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.GeometricFreeTriangle
import DifferentialGeometry.External.Schoenflies.FaceCyclesProof
import DifferentialGeometry.External.Schoenflies.RealizeSubdiv
import DifferentialGeometry.External.Schoenflies.TwoArcs
import DifferentialGeometry.External.Schoenflies.PrePolygonSep
import DifferentialGeometry.External.Schoenflies.Graph.K33Land
import DifferentialGeometry.External.Schoenflies.JordanClosed

namespace Schoenflies

private theorem closure_diff_arc_of_subset_jordan
    {C A : Set Plane} {p q : Plane} (hC : IsJordanCurve C)
    (hA : IsArcBetween A p q) (hAC : A ⊆ C) :
    IsArcBetween (closure (C \ A)) p q ∧
      A ∪ closure (C \ A) = C ∧ A ∩ closure (C \ A) = {p, q} := by
  classical
  have hpq : p ≠ q := by
    obtain ⟨f, _, hi, _, hf0, hf1⟩ := hA
    intro hpq
    have h01 : (0 : ℝ) = 1 :=
      hi zero_mem_I one_mem_I (hf0.trans (hpq.trans hf1.symm))
    norm_num at h01
  obtain ⟨X, Y, hX, hY, hcover, hmeet⟩ :=
    hC.two_arcs (hAC hA.left_mem) (hAC hA.right_mem) hpq
  have hcoverDiff : A \ {p, q} ⊆ X ∪ Y := by
    intro z hz
    rw [hcover]
    exact hAC hz.1
  have hsplitDiff : A \ {p, q} ⊆ X ∨ A \ {p, q} ⊆ Y := by
    by_cases hAX : A \ {p, q} ⊆ X
    · exact Or.inl hAX
    · right
      obtain ⟨x, hx, hxX⟩ := Set.not_subset.mp hAX
      have hxY : x ∈ Y := (hcoverDiff hx).resolve_left hxX
      intro y hy
      by_contra hyY
      have hyX : y ∈ X := (hcoverDiff hy).resolve_right hyY
      obtain ⟨z, hz, hzX, hzY⟩ :=
        isPreconnected_closed_iff.mp hA.isPreconnected_diff X Y
          hX.isArc.isClosed hY.isArc.isClosed hcoverDiff
          ⟨y, hy, hyX⟩ ⟨x, hx, hxY⟩
      exact hz.2 (hmeet ▸ ⟨hzX, hzY⟩)
  have hsplit : A ⊆ X ∨ A ⊆ Y := by
    rcases hsplitDiff with hAX | hAY
    · left
      simpa only [hA.closure_diff_eq] using closure_minimal hAX hX.isArc.isClosed
    · right
      simpa only [hA.closure_diff_eq] using closure_minimal hAY hY.isArc.isClosed
  have finish (X Y : Set Plane) (hY : IsArcBetween Y p q)
      (hcover : X ∪ Y = C) (hmeet : X ∩ Y = {p, q}) (hAX : A = X) :
      IsArcBetween (closure (C \ A)) p q ∧
        A ∪ closure (C \ A) = C ∧ A ∩ closure (C \ A) = {p, q} := by
    have hdiff : C \ A = Y \ {p, q} := by
      ext z
      constructor
      · rintro ⟨hzC, hzA⟩
        have hzXY : z ∈ X ∪ Y := hcover.symm ▸ hzC
        have hzX : z ∉ X := by
          intro hzX
          exact hzA (hAX.symm ▸ hzX)
        refine ⟨hzXY.resolve_left hzX, ?_⟩
        intro hzEnds
        have hzMeet : z ∈ X ∩ Y := hmeet.symm ▸ hzEnds
        exact hzX hzMeet.1
      · rintro ⟨hzY, hzEnds⟩
        refine ⟨hcover ▸ Or.inr hzY, ?_⟩
        intro hzA
        exact hzEnds (hmeet ▸ ⟨hAX ▸ hzA, hzY⟩)
    rw [hdiff, hY.closure_diff_eq, hAX]
    exact ⟨hY, hcover, hmeet⟩
  rcases hsplit with hAX | hAY
  · exact finish X Y hY hcover hmeet (hX.eq_of_subset hA hAX)
  · exact finish Y X hX (by simpa only [Set.union_comm] using hcover)
      (by simpa only [Set.inter_comm] using hmeet) (hY.eq_of_subset hA hAY)

end Schoenflies

open LeanEval.Topology.ClassificationOfSurfaces.Moise
  (TriangleMesh segment_inter_segment_of_affineIndependent)

namespace Schoenflies

private theorem free_triangle_apex_edges_isArcBetween
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3) :
    IsArcBetween
      (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
        segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2))
      (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
  let a := M.freeTriangleOrder T k 0
  let b := M.freeTriangleOrder T k 1
  let c := M.freeTriangleOrder T k 2
  have hi := M.freeTriangleOrder_affineIndependent T k
  have hac : a ≠ c := hi.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hcb : c ≠ b := hi.injective.ne (show (2 : Fin 3) ≠ 1 by decide)
  have hacb : AffineIndependent ℝ ![a, c, b] := by
    convert hi.comp_embedding (Equiv.swap (1 : Fin 3) 2).toEmbedding using 1
    funext i
    fin_cases i <;> rfl
  have hmeet : segment ℝ a c ∩ segment ℝ c b = {c} :=
    segment_inter_segment_of_affineIndependent hacb
  have harc := (isArcBetween_segment hac).concatenate (isArcBetween_segment hcb)
    (fun z hz0 hz1 => Set.mem_singleton_iff.mp (hmeet ▸ ⟨hz0, hz1⟩))
  simpa only [segment_symm ℝ c b] using harc

private theorem jordan_frontier_erase_triangle_of_one_edge_free
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3)
    (hC : IsJordanCurve (frontier M.toPlaneComplex.support))
    (hfree : M.IsOneEdgeFreeTriangle T k) :
    let a := M.freeTriangleOrder T k 0
    let b := M.freeTriangleOrder T k 1
    let c := M.freeTriangleOrder T k 2
    let R := closure (frontier M.toPlaneComplex.support \ segment ℝ a b)
    let A := segment ℝ a c ∪ segment ℝ b c
    IsJordanCurve (frontier (M.eraseTriangle T.1).toPlaneComplex.support) ∧
      frontier (M.eraseTriangle T.1).toPlaneComplex.support = R ∪ A ∧
      R ∩ A = {a, b} ∧
      (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 = A := by
  let a := M.freeTriangleOrder T k 0
  let b := M.freeTriangleOrder T k 1
  let c := M.freeTriangleOrder T k 2
  let C := frontier M.toPlaneComplex.support
  let K := M.triangleCarrier T.1
  let B := (M.eraseTriangle T.1).toPlaneComplex.support
  let E := segment ℝ a b
  let R := closure (C \ E)
  let A := segment ℝ a c ∪ segment ℝ b c
  change IsJordanCurve (frontier B) ∧ frontier B = R ∪ A ∧
    R ∩ A = {a, b} ∧ B ∩ K = A
  have htrace : C ∩ K = E := hfree
  have hab : a ≠ b := (M.freeTriangleOrder_affineIndependent T k).injective.ne
    (show (0 : Fin 3) ≠ 1 by decide)
  have hEC : E ⊆ C := by
    intro x hx
    have hxCK : x ∈ C ∩ K := htrace.symm ▸ hx
    exact hxCK.1
  obtain ⟨hR, hcover, hbaseMeet⟩ :=
    closure_diff_arc_of_subset_jordan hC (isArcBetween_segment hab) hEC
  have hRC : R ⊆ C := by
    have hcover' : E ∪ R = C := hcover
    intro x hx
    exact hcover' ▸ Or.inr hx
  have hA : IsArcBetween A a b := free_triangle_apex_edges_isArcBetween M T k
  have hattach : B ∩ K = A :=
    M.eraseTriangle_support_inter_triangleCarrier_of_oneEdgeFree T k hfree
  have hAK : A ⊆ K := by
    intro x hx
    have hxBK : x ∈ B ∩ K := hattach.symm ▸ hx
    exact hxBK.2
  have hmeet : R ∩ A = {a, b} := by
    ext x
    constructor
    · rintro ⟨hxR, hxA⟩
      have hxE : x ∈ E := htrace ▸ ⟨hRC hxR, hAK hxA⟩
      exact hbaseMeet ▸ ⟨hxE, hxR⟩
    · rintro (rfl | rfl)
      · exact ⟨hR.left_mem, hA.left_mem⟩
      · exact ⟨hR.right_mem, hA.right_mem⟩
  have hdiff : C \ K = C \ E := by
    ext x
    constructor
    · rintro ⟨hxC, hxK⟩
      refine ⟨hxC, ?_⟩
      intro hxE
      have hxCK : x ∈ C ∩ K := htrace.symm ▸ hxE
      exact hxK hxCK.2
    · rintro ⟨hxC, hxE⟩
      exact ⟨hxC, fun hxK => hxE (htrace ▸ ⟨hxC, hxK⟩)⟩
  have hfill : (C \ E) ∪ A = R ∪ A := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl (subset_closure hx)
      · exact Or.inr hx
    · rintro (hxR | hxA)
      · by_cases hxE : x ∈ E
        · have hxEnds : x ∈ ({a, b} : Set Plane) := hbaseMeet ▸ ⟨hxE, hxR⟩
          rcases hxEnds with rfl | rfl
          · exact Or.inr hA.left_mem
          · exact Or.inr hA.right_mem
        · exact Or.inl ⟨hRC hxR, hxE⟩
      · exact Or.inr hxA
  have hupdate : frontier B = (C \ K) ∪ A :=
    M.frontier_eraseTriangle_support_of_oneEdgeFree T k hfree
  have hfrontier : frontier B = R ∪ A := by
    rw [hupdate, hdiff, hfill]
  refine ⟨?_, hfrontier, hmeet, hattach⟩
  rw [hfrontier]
  exact IsJordanCurve.two_arcs_of_two_arcs hR hA hmeet

private theorem PrePolygon.jordan_frontier_erase_triangle_of_one_edge_free
    {m : ℕ} (P : PrePolygon m) (M : TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k) :
    let a := M.freeTriangleOrder T k 0
    let b := M.freeTriangleOrder T k 1
    let c := M.freeTriangleOrder T k 2
    let R := closure (P.carrier \ segment ℝ a b)
    let A := segment ℝ a c ∪ segment ℝ b c
    IsJordanCurve (frontier (M.eraseTriangle T.1).toPlaneComplex.support) ∧
      frontier (M.eraseTriangle T.1).toPlaneComplex.support = R ∪ A ∧
      R ∩ A = {a, b} ∧
      (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 = A := by
  have hC : IsJordanCurve (frontier M.toPlaneComplex.support) :=
    hfrontier.symm ▸ P.isJordanCurve_carrier
  simpa only [hfrontier] using
    Schoenflies.jordan_frontier_erase_triangle_of_one_edge_free M T k hC hfree

end Schoenflies

namespace Schoenflies

private theorem isPolygonal_closure_diff_segment_of_subset_jordan
    {C : Set Plane} {a b : Plane} (hC : IsJordanCurve C) (hpoly : IsPolygonal C)
    (hab : a ≠ b) (hbase : segment ℝ a b ⊆ C) :
    IsPolygonal (closure (C \ segment ℝ a b)) := by
  have hE := isArcBetween_segment hab
  obtain ⟨hR, hcover, hmeet⟩ := closure_diff_arc_of_subset_jordan hC hE hbase
  obtain ⟨n, Q, j, l, _, hl1, hl2, _, _, hcase⟩ :=
    exists_prePolygon_arcs hC hpoly (hbase hE.left_mem) (hbase hE.right_mem)
      hab hE hR hcover hmeet
  rcases hcase with ⟨_, hR⟩ | ⟨hR, _⟩
  · rw [← hR]
    exact Q.isPolygonal_arc _ (by omega)
  · rw [← hR]
    exact Q.isPolygonal_arc j hl1

private theorem PrePolygon.exists_prePolygon_frontier_erase_triangle_of_one_edge_free
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k) :
    let a := M.freeTriangleOrder T k 0
    let b := M.freeTriangleOrder T k 1
    let c := M.freeTriangleOrder T k 2
    let R := closure (P.carrier \ segment ℝ a b)
    let A := segment ℝ a c ∪ segment ℝ b c
    ∃ (n : ℕ) (Q : PrePolygon n) (j : ZMod (n + 3)) (l : ℕ),
      Q.carrier = frontier (M.eraseTriangle T.1).toPlaneComplex.support ∧
      1 ≤ l ∧ l ≤ n + 2 ∧ Q.vertex j = a ∧ Q.vertex (j + (l : ZMod (n + 3))) = b ∧
      Q.arc j l = R ∧ Q.arc (j + (l : ZMod (n + 3))) (n + 3 - l) = A ∧
      (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 = A := by
  let a := M.freeTriangleOrder T k 0
  let b := M.freeTriangleOrder T k 1
  let c := M.freeTriangleOrder T k 2
  let R := closure (P.carrier \ segment ℝ a b)
  let A := segment ℝ a c ∪ segment ℝ b c
  let B := (M.eraseTriangle T.1).toPlaneComplex.support
  have hab : a ≠ b := (M.freeTriangleOrder_affineIndependent T k).injective.ne
    (show (0 : Fin 3) ≠ 1 by decide)
  have htrace : P.carrier ∩ M.triangleCarrier T.1 = segment ℝ a b := by
    rw [← hfrontier]
    exact hfree
  have hbase : segment ℝ a b ⊆ P.carrier := by
    intro x hx
    have hxmeet : x ∈ P.carrier ∩ M.triangleCarrier T.1 := htrace.symm ▸ hx
    exact hxmeet.1
  have hR : IsArcBetween R a b :=
    (closure_diff_arc_of_subset_jordan P.isJordanCurve_carrier
      (isArcBetween_segment hab) hbase).1
  have hA : IsArcBetween A a b := free_triangle_apex_edges_isArcBetween M T k
  have hpolyR : IsPolygonal R :=
    isPolygonal_closure_diff_segment_of_subset_jordan P.isJordanCurve_carrier
      P.isPolygonal_carrier hab hbase
  have hpolyA : IsPolygonal A :=
    (isPolygonal_segment a c).union (isPolygonal_segment b c)
      ⟨c, right_mem_segment ℝ a c, right_mem_segment ℝ b c⟩
  obtain ⟨hJ, hupdate, hmeet, hattach⟩ :=
    P.jordan_frontier_erase_triangle_of_one_edge_free M hfrontier T k hfree
  have hpolyB : IsPolygonal (frontier B) := by
    rw [hupdate]
    exact hpolyR.union hpolyA ⟨a, hR.left_mem, hA.left_mem⟩
  have haB : a ∈ frontier B := hupdate.symm ▸ Or.inl hR.left_mem
  have hbB : b ∈ frontier B := hupdate.symm ▸ Or.inl hR.right_mem
  obtain ⟨n, Q, j, l, hQ, hl1, hl2, hja, hjb, hRarc, hAarc⟩ :=
    exists_prePolygon_arcs_oriented hJ hpolyB haB hbB hab hR hA hupdate.symm hmeet
  exact ⟨n, Q, j, l, hQ, hl1, hl2, hja, hjb, hRarc, hAarc, hattach⟩

end Schoenflies

namespace Schoenflies

/-- A compact set with nonempty interior and polygonal frontier is the closed region bounded by
that polygon.  This recognition lemma lets Figure 3.3 identify the new disk from its frontier. -/
theorem eq_closure_inside_of_isCompact_frontier_eq
    {C S : Set Plane} (hC : IsSeparating C) (hS : IsCompact S)
    (hfrontier : frontier S = C) (hinterior : (interior S).Nonempty) :
    S = closure (Schoenflies.inside C) := by
  have hclosure : closure (Schoenflies.inside C) = Schoenflies.inside C ∪ C :=
    (IsRegionOf.inside C).closure_eq hC
  have hSclosed := hS.isClosed
  have hExteriorCover : Schoenflies.outside C ⊆ interior S ∪ Sᶜ := by
    intro p hpExt
    by_cases hpS : p ∈ S
    · left
      apply (mem_interior_iff_notMem_frontier hpS).mpr
      intro hpFrontier
      have hpCarrier : p ∈ C := hfrontier ▸ hpFrontier
      have hpCompl : p ∈ Cᶜ := by
        rw [← Schoenflies.inside_union_outside C]
        exact Or.inr hpExt
      exact hpCompl hpCarrier
    · exact Or.inr hpS
  have hExteriorNotS : (Schoenflies.outside C ∩ Sᶜ).Nonempty := by
    by_contra h
    have hExtSub : Schoenflies.outside C ⊆ S := by
      intro p hpExt
      by_contra hpS
      exact h ⟨p, hpExt, hpS⟩
    exact hC.not_isBounded_outside (hS.isBounded.subset hExtSub)
  have hExteriorSub : Schoenflies.outside C ⊆ Sᶜ :=
    hC.isConnected_outside.isPreconnected.subset_right_of_subset_union
      isOpen_interior hSclosed.isOpen_compl
      (Set.disjoint_left.mpr fun _ hpInt hpCompl => hpCompl (interior_subset hpInt))
      hExteriorCover hExteriorNotS
  have hSSub : S ⊆ closure (Schoenflies.inside C) := by
    intro p hpS
    by_cases hpCarrier : p ∈ C
    · rw [hclosure]
      exact Or.inr hpCarrier
    · have hpSplit : p ∈ Schoenflies.inside C ∪ Schoenflies.outside C := by
        rw [Schoenflies.inside_union_outside C]
        exact hpCarrier
      rcases hpSplit with hpInt | hpExt
      · rw [hclosure]
        exact Or.inl hpInt
      · exact False.elim (hExteriorSub hpExt hpS)
  obtain ⟨p, hpInteriorS⟩ := hinterior
  have hpNotCarrier : p ∉ C := by
    rw [← hfrontier]
    exact fun hpFrontier =>
      Set.disjoint_left.mp disjoint_interior_frontier hpInteriorS hpFrontier
  have hpInteriorJ : p ∈ Schoenflies.inside C := by
    have hpSplit : p ∈ Schoenflies.inside C ∪ Schoenflies.outside C := by
      rw [Schoenflies.inside_union_outside C]
      exact hpNotCarrier
    exact hpSplit.resolve_right fun hpExt => hExteriorSub hpExt (interior_subset hpInteriorS)
  have hInteriorCover : Schoenflies.inside C ⊆ interior S ∪ Sᶜ := by
    intro q hqInt
    by_cases hqS : q ∈ S
    · left
      apply (mem_interior_iff_notMem_frontier hqS).mpr
      intro hqFrontier
      have hqCarrier : q ∈ C := hfrontier ▸ hqFrontier
      have hqCompl : q ∈ Cᶜ := by
        rw [← Schoenflies.inside_union_outside C]
        exact Or.inl hqInt
      exact hqCompl hqCarrier
    · exact Or.inr hqS
  have hInteriorSub : Schoenflies.inside C ⊆ interior S :=
    hC.isConnected_inside.isPreconnected.subset_left_of_subset_union
      isOpen_interior hSclosed.isOpen_compl
      (Set.disjoint_left.mpr fun _ hpInt hpCompl => hpCompl (interior_subset hpInt))
      hInteriorCover ⟨p, hpInteriorJ, hpInteriorS⟩
  apply Set.Subset.antisymm hSSub
  rw [hclosure]
  exact Set.union_subset (hInteriorSub.trans interior_subset)
    (by rw [← hfrontier]; exact frontier_subset_closure.trans_eq hSclosed.closure_eq)

private theorem interior_erase_triangle_support_nonempty_of_one_edge_free
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k) :
    (interior (M.eraseTriangle T.1).toPlaneComplex.support).Nonempty := by
  let N := M.eraseTriangle T.1
  let a := M.freeTriangleOrder T k 0
  have hattach := M.eraseTriangle_support_inter_triangleCarrier_of_oneEdgeFree T k hfree
  have ha : a ∈ N.toPlaneComplex.support := by
    have haMeet : a ∈ N.toPlaneComplex.support ∩ M.triangleCarrier T.1 :=
      hattach.symm ▸ Or.inl (left_mem_segment ℝ a (M.freeTriangleOrder T k 2))
    exact haMeet.1
  rw [N.toPlaneComplex_support] at ha
  obtain ⟨t, ht, _⟩ := Set.mem_iUnion₂.mp ha
  have htriangle : N.triangleCarrier t ⊆ N.toPlaneComplex.support := by
    rw [N.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset t (Set.subset_iUnion_of_subset ht (by rfl))
  exact (N.interior_triangleCarrier_nonempty ⟨t, ht⟩).mono (interior_mono htriangle)

theorem PrePolygon.exists_prePolygon_closed_region_erase_triangle_of_one_edge_free
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k) :
    let a := M.freeTriangleOrder T k 0
    let b := M.freeTriangleOrder T k 1
    let c := M.freeTriangleOrder T k 2
    let R := closure (P.carrier \ segment ℝ a b)
    let A := segment ℝ a c ∪ segment ℝ b c
    ∃ (n : ℕ) (Q : PrePolygon n) (j : ZMod (n + 3)) (l : ℕ),
      Q.carrier = frontier (M.eraseTriangle T.1).toPlaneComplex.support ∧
      (M.eraseTriangle T.1).toPlaneComplex.support = closure (Schoenflies.inside Q.carrier) ∧
      1 ≤ l ∧ l ≤ n + 2 ∧ Q.vertex j = a ∧ Q.vertex (j + (l : ZMod (n + 3))) = b ∧
      Q.arc j l = R ∧ Q.arc (j + (l : ZMod (n + 3))) (n + 3 - l) = A ∧
      (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 = A := by
  obtain ⟨n, Q, j, l, hQ, hl1, hl2, hja, hjb, hRarc, hAarc, hattach⟩ :=
    P.exists_prePolygon_frontier_erase_triangle_of_one_edge_free M hfrontier T k hfree
  have hregion : (M.eraseTriangle T.1).toPlaneComplex.support =
      closure (Schoenflies.inside Q.carrier) :=
    eq_closure_inside_of_isCompact_frontier_eq Q.isSeparating_carrier
      (M.eraseTriangle T.1).toPlaneComplex.isCompact_support hQ.symm
      (interior_erase_triangle_support_nonempty_of_one_edge_free M T k hfree)
  exact ⟨n, Q, j, l, hQ, hregion, hl1, hl2, hja, hjb, hRarc, hAarc, hattach⟩

private theorem free_triangle_frontier_eq_edges
    (M : TriangleMesh) (T : M.Triangle) (k : Fin 3) :
    frontier (M.triangleCarrier T.1) =
      (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 2) ∪
        segment ℝ (M.freeTriangleOrder T k 1) (M.freeTriangleOrder T k 2)) ∪
          segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
  have hedge {e : Finset M.Vertex} (hecard : e.card = 2) (heT : e ⊆ T.1) :
      convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
        frontier (M.triangleCarrier T.1) := by
    intro x hx
    have hxT : x ∈ M.triangleCarrier T.1 :=
      convexHull_mono (Set.image_mono heT) hx
    apply (mem_frontier_iff_notMem_interior hxT).mpr
    intro hxi
    exact Set.disjoint_left.mp
      (M.disjoint_interior_triangleCarrier_convexHull_of_subset_card_le_two
        T heT (by omega)) hxi hx
  apply Set.Subset.antisymm
  · simpa only [Set.union_comm] using M.frontier_triangleCarrier_subset_freeTriangleEdges T k
  · rintro x ((hx | hx) | hx)
    · apply hedge (M.freeTriangleApexEdge0_card T k) (M.freeTriangleApexEdge0_subset T k)
      rwa [M.freeTriangleApexEdge0_carrier T k]
    · apply hedge (M.freeTriangleApexEdge1_card T k) (M.freeTriangleApexEdge1_subset T k)
      rwa [M.freeTriangleApexEdge1_carrier T k]
    · apply hedge (M.freeTriangleBaseEdge_card T k) (M.freeTriangleBaseEdge_subset T k)
      rwa [M.freeTriangleBaseEdge_carrier T k]

private theorem closure_diff_crosscut_side
    {C E A R : Set Plane} {a b : Plane}
    (h : IsCrosscut C E a b) (hcut : IsCutPair C a b A R) :
    closure (closure (inside C) \ closure (inside (A ∪ E))) =
      closure (inside (R ∪ E)) := by
  have hsep := jordan_curve_theorem h.curve
  have hsep₁ := jordan_curve_theorem (h.isJordanCurve_union hcut)
  have hsep₂ := jordan_curve_theorem (h.isJordanCurve_union hcut.symm)
  have hsplit := (crosscut_theorem h hcut).1
  have hdisjoint : Disjoint (closure (inside (A ∪ E))) (inside (R ∪ E)) :=
    ((crosscut_theorem h hcut).2.1).closure_left hsep₂.isOpen_inside
  have hE : E ⊆ closure (inside (A ∪ E)) :=
    Set.Subset.trans Set.subset_union_right ((IsRegionOf.inside (A ∪ E)).subset_closure hsep₁)
  apply Set.Subset.antisymm
  · apply closure_minimal _ isClosed_closure
    rintro x ⟨hxC, hxK⟩
    rw [(IsRegionOf.inside C).closure_eq hsep] at hxC
    rcases hxC with hxi | hxc
    · have hxE : x ∉ E := fun hxe => hxK (hE hxe)
      have hxSides : x ∈ inside (A ∪ E) ∪ inside (R ∪ E) := hsplit ▸ ⟨hxi, hxE⟩
      exact subset_closure (hxSides.resolve_left fun hx₁ => hxK (subset_closure hx₁))
    · have hxR : x ∈ R := by
        have hxAR : x ∈ A ∪ R := hcut.union_eq.symm ▸ hxc
        exact hxAR.resolve_left fun hxA =>
          hxK ((IsRegionOf.inside (A ∪ E)).subset_closure hsep₁ (Or.inl hxA))
      exact (IsRegionOf.inside (R ∪ E)).subset_closure hsep₂ (Or.inl hxR)
  · apply closure_mono
    intro x hx
    exact ⟨subset_closure ((h.side_subset (fun _ hJ => jordan_curve_theorem hJ) hcut.symm hx).1),
      fun hxK => Set.disjoint_left.mp hdisjoint hxK hx⟩

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

private theorem PrePolygon.two_edge_free_crosscut
    {m : ℕ} (P : PrePolygon m) (M : TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k) :
    IsCrosscut P.carrier
      (segment ℝ (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1))
      (M.freeTriangleOrder T k 0) (M.freeTriangleOrder T k 1) := by
  let a := M.freeTriangleOrder T k 0
  let b := M.freeTriangleOrder T k 1
  let c := M.freeTriangleOrder T k 2
  have htrace : P.carrier ∩ M.triangleCarrier T.1 = segment ℝ a c ∪ segment ℝ b c := by
    rw [← hfrontier]
    exact hfree
  have hTsub : M.triangleCarrier T.1 ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset T.1 (Set.subset_iUnion_of_subset T.2 subset_rfl)
  have hsupport : M.toPlaneComplex.support = closure (inside P.carrier) :=
    eq_closure_inside_of_isCompact_frontier_eq P.isSeparating_carrier
      M.toPlaneComplex.isCompact_support hfrontier
      ((M.interior_triangleCarrier_nonempty T).mono (interior_mono hTsub))
  have ha : a ∈ P.carrier := by
    have hh : a ∈ P.carrier ∩ M.triangleCarrier T.1 :=
      htrace.symm ▸ Or.inl (left_mem_segment ℝ a c)
    exact hh.1
  have hb : b ∈ P.carrier := by
    have hh : b ∈ P.carrier ∩ M.triangleCarrier T.1 :=
      htrace.symm ▸ Or.inr (left_mem_segment ℝ b c)
    exact hh.1
  refine ⟨P.isJordanCurve_carrier,
    isArcBetween_segment ((M.freeTriangleOrder_affineIndependent T k).injective.ne (by decide)),
    isPolygonal_segment a b, ha, hb, ?_⟩
  intro x hx
  have hxT : x ∈ M.triangleCarrier T.1 := by
    apply convexHull_mono (Set.image_mono (M.freeTriangleBaseEdge_subset T k))
    rw [M.freeTriangleBaseEdge_carrier T k]
    exact hx.1
  have hxC : x ∉ P.carrier := by
    intro hxc
    exact Set.disjoint_left.mp (M.freeTriangleBase_diff_endpoints_disjoint_apexEdges T k)
      hx (htrace ▸ ⟨hxc, hxT⟩)
  have hxClosed : x ∈ closure (inside P.carrier) := hsupport ▸ hTsub hxT
  rw [(IsRegionOf.inside P.carrier).closure_eq P.isSeparating_carrier] at hxClosed
  exact hxClosed.resolve_right hxC

private theorem PrePolygon.two_edge_free_region_and_attachment
    {m : ℕ} (P : PrePolygon m) (M : TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k) :
    let a := M.freeTriangleOrder T k 0
    let b := M.freeTriangleOrder T k 1
    let c := M.freeTriangleOrder T k 2
    let A := segment ℝ a c ∪ segment ℝ b c
    let R := closure (P.carrier \ A)
    let E := segment ℝ a b
    IsCutPair P.carrier a b A R ∧
      IsJordanCurve (R ∪ E) ∧
      (M.eraseTriangle T.1).toPlaneComplex.support = closure (inside (R ∪ E)) ∧
      (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 = E := by
  let a := M.freeTriangleOrder T k 0
  let b := M.freeTriangleOrder T k 1
  let c := M.freeTriangleOrder T k 2
  let A := segment ℝ a c ∪ segment ℝ b c
  let R := closure (P.carrier \ A)
  let E := segment ℝ a b
  let K := M.triangleCarrier T.1
  have htrace : P.carrier ∩ K = A := by rw [← hfrontier]; exact hfree
  have hAC : A ⊆ P.carrier := by
    intro x hx
    have hh : x ∈ P.carrier ∩ K := htrace.symm ▸ hx
    exact hh.1
  have hA : IsArcBetween A a b := free_triangle_apex_edges_isArcBetween M T k
  obtain ⟨hR, hcover, hmeet⟩ :=
    closure_diff_arc_of_subset_jordan P.isJordanCurve_carrier hA hAC
  have hcut : IsCutPair P.carrier a b A R := ⟨hA, hR, hcover, hmeet⟩
  have hcross : IsCrosscut P.carrier E a b := P.two_edge_free_crosscut M hfrontier T k hfree
  have hKregion : K = closure (inside (A ∪ E)) :=
    eq_closure_inside_of_isCompact_frontier_eq
      (jordan_curve_theorem (hcross.isJordanCurve_union hcut))
      ((T.1.finite_toSet.image M.position).isCompact_convexHull ℝ)
      (free_triangle_frontier_eq_edges M T k) (M.interior_triangleCarrier_nonempty T)
  have hTsub : K ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset T.1 (Set.subset_iUnion_of_subset T.2 subset_rfl)
  have hsupport : M.toPlaneComplex.support = closure (inside P.carrier) :=
    eq_closure_inside_of_isCompact_frontier_eq P.isSeparating_carrier
      M.toPlaneComplex.isCompact_support hfrontier
      ((M.interior_triangleCarrier_nonempty T).mono (interior_mono hTsub))
  have hremaining : (M.eraseTriangle T.1).toPlaneComplex.support =
      closure (inside (R ∪ E)) := by
    rw [M.eraseTriangle_support_eq_closure_diff_triangleCarrier T, hsupport]
    change closure (closure (inside P.carrier) \ K) = closure (inside (R ∪ E))
    rw [hKregion]
    exact closure_diff_crosscut_side hcross hcut
  refine ⟨hcut, hcross.isJordanCurve_union hcut.symm, hremaining, ?_⟩
  change (M.eraseTriangle T.1).toPlaneComplex.support ∩ K = E
  rw [hremaining, hKregion]
  exact closure_inside_crosscut_sides_inter hcross hcut

theorem PrePolygon.exists_prePolygon_closed_region_erase_triangle_of_two_edge_free
    {m : ℕ} (P : PrePolygon m) (M : TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsTwoEdgeFreeTriangle T k) :
    let a := M.freeTriangleOrder T k 0
    let b := M.freeTriangleOrder T k 1
    let c := M.freeTriangleOrder T k 2
    let R := closure (P.carrier \ (segment ℝ a c ∪ segment ℝ b c))
    let E := segment ℝ a b
    ∃ (n : ℕ) (Q : PrePolygon n) (j : ZMod (n + 3)) (l : ℕ),
      Q.carrier = frontier (M.eraseTriangle T.1).toPlaneComplex.support ∧
      (M.eraseTriangle T.1).toPlaneComplex.support = closure (inside Q.carrier) ∧
      1 ≤ l ∧ l ≤ n + 2 ∧ Q.vertex j = a ∧ Q.vertex (j + (l : ZMod (n + 3))) = b ∧
      Q.arc j l = R ∧ Q.arc (j + (l : ZMod (n + 3))) (n + 3 - l) = E ∧
      (M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1 = E := by
  let a := M.freeTriangleOrder T k 0
  let b := M.freeTriangleOrder T k 1
  let c := M.freeTriangleOrder T k 2
  let A := segment ℝ a c ∪ segment ℝ b c
  let R := closure (P.carrier \ A)
  let E := segment ℝ a b
  let B := (M.eraseTriangle T.1).toPlaneComplex.support
  let K := M.triangleCarrier T.1
  obtain ⟨hcut, hJ, hregion, hattach⟩ :=
    P.two_edge_free_region_and_attachment M hfrontier T k hfree
  have hcut' : IsCutPair P.carrier a b A R := hcut
  have hR := hcut'.snd
  have hcross : IsCrosscut P.carrier E a b := P.two_edge_free_crosscut M hfrontier T k hfree
  have hE := hcross.arc
  have hab : a ≠ b := (M.freeTriangleOrder_affineIndependent T k).injective.ne (by decide)
  have htrace : P.carrier ∩ K = A := by rw [← hfrontier]; exact hfree
  have hdiff : P.carrier \ K = P.carrier \ A := by
    ext x
    constructor
    · rintro ⟨hxC, hxK⟩
      refine ⟨hxC, ?_⟩
      intro hxA
      have hh : x ∈ P.carrier ∩ K := htrace.symm ▸ hxA
      exact hxK hh.2
    · rintro ⟨hxC, hxA⟩
      exact ⟨hxC, fun hxK => hxA (htrace ▸ ⟨hxC, hxK⟩)⟩
  have hfill : (P.carrier \ A) ∪ E = R ∪ E := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl (subset_closure hx)
      · exact Or.inr hx
    · rintro (hxR | hxE)
      · by_cases hxA : x ∈ A
        · have hxEnds : x ∈ ({a, b} : Set Plane) := hcut'.inter_eq ▸ ⟨hxA, hxR⟩
          rcases hxEnds with rfl | rfl
          · exact Or.inr hE.left_mem
          · exact Or.inr hE.right_mem
        · exact Or.inl ⟨hcut'.snd_subset hxR, hxA⟩
      · exact Or.inr hxE
  have hupdate : frontier B = R ∪ E := by
    have hattach' : B ∩ K = E := hattach
    have hu : frontier B = (frontier M.toPlaneComplex.support \ K) ∪ (B ∩ K) :=
      M.frontier_eraseTriangle_support T
    rw [hu, hfrontier, hattach', hdiff, hfill]
  have hmeet : R ∩ E = {a, b} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxR, hxE⟩
      exact hcross.inter_eq ▸ ⟨hxE, hcut'.snd_subset hxR⟩
    · rintro x (rfl | rfl)
      · exact ⟨hR.left_mem, hE.left_mem⟩
      · exact ⟨hR.right_mem, hE.right_mem⟩
  have hpolyR : IsPolygonal R := by
    obtain ⟨n, Q, j, l, _, hl1, hl2, _, _, hcase⟩ :=
      exists_prePolygon_arcs P.isJordanCurve_carrier P.isPolygonal_carrier
        hcross.left_mem hcross.right_mem hab hcut'.fst hR hcut'.union_eq hcut'.inter_eq
    rcases hcase with ⟨_, hRarc⟩ | ⟨hRarc, _⟩
    · rw [← hRarc]
      exact Q.isPolygonal_arc _ (by omega)
    · rw [← hRarc]
      exact Q.isPolygonal_arc j hl1
  have hpoly : IsPolygonal (R ∪ E) :=
    hpolyR.union (isPolygonal_segment a b) ⟨a, hR.left_mem, hE.left_mem⟩
  obtain ⟨n, Q, j, l, hQ, hl1, hl2, hja, hjb, hRarc, hEarc⟩ :=
    exists_prePolygon_arcs_oriented hJ hpoly (Or.inl hR.left_mem) (Or.inl hR.right_mem)
      hab hR hE rfl hmeet
  refine ⟨n, Q, j, l, hQ.trans hupdate.symm, ?_, hl1, hl2, hja, hjb, hRarc, hEarc, hattach⟩
  rw [hQ]
  exact hregion


end Schoenflies
