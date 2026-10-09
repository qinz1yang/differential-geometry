/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodResidualRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualSplitSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualVertexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnEndpoints

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem boundaryComplex_splittingDisk_one_eq_upperLink
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {e : Finset E} (he : e ∈ K.faces)
    (hcard : e.card = 2) :
    boundaryComplex 1 (splittingDisk K e he) =
      upperLink (dualCell K e he) {e.centroid ℝ id} := by
  let D := dualCell K e he
  let _ : Finite D.faces := (dualCell_faces_finite K he).to_subtype
  have hD : IsPLBall 1 D.space :=
    hK.isCombinatorialManifoldWithBoundary.isPLBall_dualCell K he (k := 1) hcard (by decide)
  have hc : {e.centroid ℝ id} ∈ D.faces := singleton_centroid_mem_dualCell K he
  have hlink : IsPLSphere 0 (SimplicialComplex.geometricLink D {e.centroid ℝ id}).space := by
    rw [show D = dualCell K e he from rfl, geometricLink_dualCell K he]
    exact hK.isPLSphere_upperLink K he (k := 1) hcard (by decide)
  have hsub := barycentricSubdivision_isSubdivision D
  have hlink' : IsPLSphere 0
      (SimplicialComplex.geometricLink (barycentricSubdivision D) {e.centroid ℝ id}).space :=
    (isPLSphere_geometricLink_iff_of_isSubdivision hsub hc).mpr hlink
  change boundaryComplex 1 (starComplex (barycentricSubdivision D) (e.centroid ℝ id)) = _
  rw [boundaryComplex_starComplex_eq_geometricLink _
    hD.isCombinatorialManifoldWithBoundary.barycentricSubdivision (hsub.singleton_mem hc) hlink',
    geometricLink_barycentricSubdivision_singleton D hc]

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem compactDualCutBoundary_outerArc_eq_splitBoundary_inter_frontier
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (q : Section34CompactOuterEdgeIndex K K) :
    compactDualCutBoundary M K hKM (.outerArc q) =
      compactDualCutBoundary M K hKM (.splitDisk q.1) ∩ frontier K.space := by
  let dNative : DecidableEq E3 := inferInstance
  let : DecidableEq E3 := Classical.decEq E3
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  let B := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hB : IsCombinatorialManifold 2 B := isCombinatorialManifold_boundaryComplex K hK
  have hBM : B.faces ⊆ M.faces := (boundaryComplex_faces_subset 3 K).trans hKM
  have heB : q.1.1 ∈ B.faces := by
    apply mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset 3 K) q.1.2.1
      (centroid_mem_openSimplex_of_mem_faces K q.1.1 q.1.2.1)
    rw [← frontier_space_eq_boundaryComplex_space (n := 2) hK]
    exact q.2 (q.1.1.centroid_mem_convexHull (K.nonempty_of_mem_faces q.1.2.1))
  have heM : q.1.1 ∉ (boundaryComplex 3 M).faces :=
    hM.notMem_boundaryComplex_faces_of_forall_mem_interior (by simp) (hKM q.1.2.1)
      (fun v hv => hint (K.subset_space q.1.2.1 hv))
  let D := splittingDisk B q.1.1 heB
  let _ : Finite D.faces := (splittingDisk_faces_finite B heB).to_subtype
  have hD : IsPLBall 1 D.space := hB.isCombinatorialManifoldWithBoundary.isPLBall_splittingDisk
    B heB (k := 1) q.1.2.2.1 (by decide)
  have hDTransport : @boundaryComplex E3 _ _ dNative 2
      (splittingDisk M q.1.1 (hKM q.1.2.1)) =
        boundaryComplex 2 (splittingDisk M q.1.1 (hKM q.1.2.1)) :=
    congrArg (fun d : DecidableEq E3 =>
      @boundaryComplex E3 _ _ d 2 (splittingDisk M q.1.1 (hKM q.1.2.1)))
      (Subsingleton.elim _ _)
  have htrace : compactDualCutBoundary M K hKM (.splitDisk q.1) ∩ frontier K.space =
      (boundaryComplex 1 D).space := by
    have hsplit : compactDualCutBoundary M K hKM (.splitDisk q.1) =
        (boundaryComplex 2 (splittingDisk M q.1.1 (hKM q.1.2.1))).space :=
      (compactDualCutBoundary_splitDisk M K hKM q.1).trans
        (congrArg Geometry.SimplicialComplex.space hDTransport)
    have hfront : frontier K.space = B.space :=
      frontier_space_eq_boundaryComplex_space (n := 2) hK
    calc
      _ = (boundaryComplex 2 (splittingDisk M q.1.1 (hKM q.1.2.1))).space ∩
          frontier K.space := congrArg (fun S : Set E3 => S ∩ frontier K.space) hsplit
      _ = (boundaryComplex 2 (splittingDisk M q.1.1 (hKM q.1.2.1))).space ∩ B.space :=
        congrArg (fun S : Set E3 =>
          (boundaryComplex 2 (splittingDisk M q.1.1 (hKM q.1.2.1))).space ∩ S) hfront
      _ = (upperLink (dualCell B q.1.1 heB) {q.1.1.centroid ℝ id}).space :=
        boundaryComplex_splittingDisk_inter_subcomplex M B hM hBM heB q.1.2.2.1 heM
      _ = (boundaryComplex 1 D).space :=
        (congrArg Geometry.SimplicialComplex.space
          (boundaryComplex_splittingDisk_one_eq_upperLink B hB heB q.1.2.2.1)).symm
  have hcell := isPLCellOn_compactDualCutCell_of_isPLBall M K hKM (.outerArc q)
    (isPLBall_compactDualCutCell_outerArc M K hM hK hKM hint q)
  obtain ⟨a, b, hab, habd⟩ := hcell.exists_boundary_eq_pair
  obtain ⟨c, d, hcd, hcdB⟩ := isPLSphere_zero_iff.mp
    (isPLSphere_boundaryComplex_space_of_isPLBall D hD)
  have hsub : compactDualCutBoundary M K hKM (.outerArc q) ⊆
      compactDualCutBoundary M K hKM (.splitDisk q.1) ∩ frontier K.space := by
    rw [compactDualCutBoundary_outerArc_eq_inter M K hM hK hKM hint q]
    rintro x ⟨hxO, hxK⟩
    have havoid : compactDualCutCell M K hKM (.outerArc q) ⊆ (interior K.space)ᶜ := by
      apply closure_minimal
      · exact fun _ hx hxi => hx.2 (interior_subset hxi)
      · exact isOpen_interior.isClosed_compl
    exact ⟨compactDualOuterArc_subset_splitBoundary M K hKM q hxO,
      subset_closure hxK, havoid hxO⟩
  have hfinite :
      (compactDualCutBoundary M K hKM (.splitDisk q.1) ∩ frontier K.space).Finite := by
    rw [htrace, hcdB]
    exact (finite_singleton d).insert c
  apply Set.eq_of_subset_of_ncard_le hsub ?_ hfinite
  rw [habd, htrace, hcdB, ncard_pair hab, ncard_pair hcd]

open Classical in
theorem compactDualOuterArc_eq_splitBoundary_inter_complement
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (q : Section34CompactOuterEdgeIndex K K) :
    compactDualCutCell M K hKM (.outerArc q) =
      compactDualCutBoundary M K hKM (.splitDisk q.1) ∩ closure (M.space \ K.space) := by
  let dNative : DecidableEq E3 := inferInstance
  let : DecidableEq E3 := Classical.decEq E3
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  have hdis : Disjoint K.space (boundaryComplex 3 M).space := by
    rw [← frontier_space_eq_boundaryComplex_space (n := 2) hM]
    exact disjoint_left.mpr fun x hxK hxB => hxB.2 (hint hxK)
  have hmeet := inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary M K hM hK
    (space_mono_of_faces_subset hKM) hdis
  have hDsub : compactDualSplitDisk M K hKM q.1 ⊆ M.space := by
    exact (splittingDisk_space_subset_dualCell M (hKM q.1.2.1)).trans
      ((space_mono_of_faces_subset (dualCell_faces_subset M (hKM q.1.2.1))).trans
        (barycentricSubdivision_isSubdivision M).space_eq.subset)
  have hDTransport : @boundaryComplex E3 _ _ dNative 2
      (splittingDisk M q.1.1 (hKM q.1.2.1)) =
        boundaryComplex 2 (splittingDisk M q.1.1 (hKM q.1.2.1)) :=
    congrArg (fun d : DecidableEq E3 =>
      @boundaryComplex E3 _ _ d 2 (splittingDisk M q.1.1 (hKM q.1.2.1)))
      (Subsingleton.elim _ _)
  apply Subset.antisymm
  · intro x hx
    refine ⟨compactDualOuterArc_subset_splitBoundary M K hKM q hx, ?_⟩
    apply closure_mono (t := M.space \ K.space) ?_ hx
    rintro y ⟨hy, hyK⟩
    exact ⟨hDsub (boundaryComplex_space_subset 2 _ (hDTransport ▸ hy)), hyK⟩
  · rintro x ⟨hxD, hxQ⟩
    by_cases hxK : x ∈ K.space
    · have hxB : x ∈ frontier K.space := by
        rw [frontier_space_eq_boundaryComplex_space (n := 2) hK, ← hmeet]
        exact ⟨hxK, hxQ⟩
      have hxo : x ∈ compactDualCutBoundary M K hKM (.outerArc q) := by
        rw [compactDualCutBoundary_outerArc_eq_splitBoundary_inter_frontier
          M K hM hK hKM hint q]
        exact ⟨hxD, hxB⟩
      exact (isPLCellOn_compactDualCutCell_of_isPLBall M K hKM (.outerArc q)
        (isPLBall_compactDualCutCell_outerArc M K hM hK hKM hint q)).boundary_subset hxo
    · apply subset_closure
      rw [compactDualCutBoundary_splitDisk M K hKM q.1] at hxD
      exact ⟨hxD, hxK⟩

open Classical in
theorem compactDualOuterFace_eq_inter_frontier_complement
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (o : Section34CompactOuterVertexIndex K K) :
    compactDualCutCell M K hKM (.outerFace o) =
      (compactDualVertexBall M K o.1 ∩ frontier (compactDualNeighborhood M K)) ∩
        closure (M.space \ K.space) := by
  let dNative : DecidableEq E3 := inferInstance
  let : DecidableEq E3 := Classical.decEq E3
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  let L := restrict K (section34CompactGraphSkeleton K)
  let Q := subcomplexGeneratedBy M K.facesᶜ
  let G := restrict L Q.space
  let v := o.1.1.centroid ℝ id
  let C := compactDualVertexBall M K o.1
  let N := compactDualNeighborhood M K
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hQM : Q.faces ⊆ M.faces := subcomplexGeneratedBy_faces_subset M K.facesᶜ
  have hQsp : Q.space = closure (M.space \ K.space) :=
    (closure_space_sdiff_space_eq_subcomplexGeneratedBy M M K Subset.rfl hKM).symm
  have hvs : {v} = o.1.1 := singleton_centroid_eq_compactVertexIndex o.1
  have hvL : {v} ∈ L.faces := by
    rw [hvs]
    exact ⟨o.1.2.1, o.1.2.2.2⟩
  have hvB : {v} ∈ (boundaryComplex 3 K).faces := by
    apply mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset 3 K)
      (show {v} ∈ K.faces by rw [hvs]; exact o.1.2.1)
      (by simpa only [Finset.centroid_singleton, id_eq] using
        centroid_mem_openSimplex (Finset.singleton_nonempty v))
    rw [← frontier_space_eq_boundaryComplex_space (n := 2) hK]
    exact o.2 (hvs ▸ Finset.mem_singleton_self v)
  have hdis : Disjoint K.space (boundaryComplex 3 M).space := by
    rw [← frontier_space_eq_boundaryComplex_space (n := 2) hM]
    exact disjoint_left.mpr fun x hxK hxB => hxB.2 (hint hxK)
  have hmeet := inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary M K hM hK
    (space_mono_of_faces_subset hKM) hdis
  have hvQsp : v ∈ Q.space := by
    rw [hQsp]
    exact (hmeet.symm ▸ (boundaryComplex 3 K).subset_space hvB
      (Finset.mem_singleton_self v)).2
  have hvQ : {v} ∈ Q.faces := mem_faces_of_mem_openSimplex_of_mem_space hQM (hLM hvL)
    (by simpa only [Finset.centroid_singleton, id_eq] using
      centroid_mem_openSimplex (Finset.singleton_nonempty v)) hvQsp
  have hBTransport : @boundaryComplex E3 _ _ dNative 3 K = boundaryComplex 3 K :=
    congrArg (fun d : DecidableEq E3 => @boundaryComplex E3 _ _ d 3 K)
      (Subsingleton.elim _ _)
  have hvBNative : {v} ∈ (@boundaryComplex E3 _ _ dNative 3 K).faces := hBTransport.symm ▸ hvB
  have hgen := graphDualCell_outer_boundary_eq_residual M K L hM hK hKM
    (restrict_faces_subset K _)
    (fun _ hs => card_le_two_of_mem_restrict_section34CompactGraphSkeleton hs)
    hint hvL hvBNative
  have hU : (⋃ e : {e : Finset E3 // e ∈ L.faces ∧ e.card = 2},
      (splittingDisk M e.1 (hKM ((restrict_faces_subset K _) e.2.1))).space) =
        ⋃ e : Section34CompactEdgeIndex K K, compactDualSplitDisk M K hKM e := by
    ext x
    constructor
    · intro hx
      obtain ⟨e, hxe⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨⟨e.1, e.2.1.1, e.2.2, e.2.1.2⟩, hxe⟩
    · intro hx
      obtain ⟨e, hxe⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨⟨e.1, ⟨e.2.1, e.2.2.2⟩, e.2.2.1⟩, hxe⟩
  dsimp only at hgen
  have hNTransport : @derivedNeighborhood E3 _ _ dNative Q G = derivedNeighborhood Q G :=
    congrArg (fun d : DecidableEq E3 => @derivedNeighborhood E3 _ _ d Q G)
      (Subsingleton.elim _ _)
  rw [hU, hNTransport] at hgen
  change compactDualCutCell M K hKM (.outerFace o) =
    (graphDualCell Q G v).space ∩ closure (Q.space \ (derivedNeighborhood Q G).space) at hgen
  have hCG : C ∩ Q.space = (graphDualCell Q G v).space :=
    graphDualCell_space_inter_subcomplex_restrict M Q L hQM hLM hvQ
  have hN : N = (derivedNeighborhood M L).space := by
    change (⋃ v ∈ K.vertices, (graphDualCell M L v).space) = _
    rw [vertices_eq_setOf_restrict_section34CompactGraphSkeleton]
    exact iUnion_graphDualCell_space M L hLM
  have hres := closure_sdiff_derivedNeighborhood_inter_subcomplex M M Q L
    Subset.rfl hQM hLM
  rw [← hN] at hres
  rw [derivedNeighborhood_restrict_right M Q L hQM hLM, ← hres, ← hCG] at hgen
  have hCN : C ⊆ N := compactDualVertexBall_subset_neighborhood M K o.1
  have hNint : N ⊆ interior M.space := by
    rw [hN]
    exact derivedNeighborhood_space_subset_interior (n := 2) (by simp) hM hLM
      ((space_mono_of_faces_subset (restrict_faces_subset K _)).trans hint)
  have hCM : C ⊆ M.space := hCN.trans (hNint.trans interior_subset)
  have hrim : ∀ x ∈ C, x ∈ closure (M.space \ N) ↔ x ∈ frontier N := by
    intro x hxC
    constructor
    · intro hxR
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure (hCN hxC), closure_mono (fun y hy => hy.2) hxR⟩
    · intro hxF
      rw [hN] at hxF ⊢
      exact frontier_derivedNeighborhood_inter_subcomplex_subset_residual M M L
        Subset.rfl hLM (hN ▸ hNint) ⟨hxF, hCM hxC⟩
  rw [hgen, ← hQsp]
  change (C ∩ Q.space) ∩ (closure (M.space \ N) ∩ Q.space) = (C ∩ frontier N) ∩ Q.space
  ext x
  exact ⟨fun h => ⟨⟨h.1.1, (hrim x h.1.1).mp h.2.1⟩, h.1.2⟩,
    fun h => ⟨⟨h.1.1, h.2⟩, (hrim x h.1.1).mpr h.1.2, h.2⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
