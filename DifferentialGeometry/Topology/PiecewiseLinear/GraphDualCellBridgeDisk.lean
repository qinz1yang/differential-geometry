/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDisk
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellCurveTrace

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem centroid_mem_frontier_graphDualCell_of_edge
    (M L : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hLM : L.faces ⊆ M.faces)
    (hcard : ∀ e ∈ L.faces, e.card ≤ 2) {e : Finset E3}
    (he : e ∈ L.faces) (hec : e.card = 2) {v : E3} (hve : v ∈ e) :
    e.centroid ℝ id ∈ frontier (graphDualCell M L v).space := by
  obtain ⟨w, hwe, hwv⟩ := Finset.exists_mem_ne (by omega : 1 < e.card) v
  have hwL : {w} ∈ L.faces := L.down_closed he
    (Finset.singleton_subset_iff.mpr hwe) (Finset.singleton_nonempty w)
  have hinter := graphDualCell_space_inter_of_mem M L hLM hcard he hve hwe hwv.symm
  have hI : IsPLBall 2 ((graphDualCell M L v).space ∩ (graphDualCell M L w).space) := by
    rw [hinter]
    exact hM.isPLBall_splittingDisk M (hLM he) hec (by norm_num : 1 ≤ 2)
  exact (hM.isPLBall_graphDualCell M L hLM hcard hwL).inter_subset_frontier_of_isPLBall
    hI (by decide) (hinter.symm ▸ centroid_mem_splittingDisk_space M (hLM he))

open Classical in
theorem isBridgeDisk_graphDualCell
    (M L F : Geometry.SimplicialComplex ℝ E3) [Finite M.faces] [Finite F.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hLM : L.faces ⊆ M.faces) (hLdim : ∀ e ∈ L.faces, e.card ≤ 2)
    (hFM : F.faces ⊆ M.faces) (hF : IsPLBall 2 F.space)
    (hFint : F.space ⊆ interior M.space)
    (hJL : (boundaryComplex 2 F).faces ⊆ L.faces)
    {u v w : E3} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h0 : ({u, v} : Finset E3) ∈ (boundaryComplex 2 F).faces)
    (h1 : ({v, w} : Finset E3) ∈ (boundaryComplex 2 F).faces) :
    IsBridgeDisk (graphDualCell M L v).space
      ((boundaryComplex 2 F).space ∩ (graphDualCell M L v).space)
      (F.space ∩ (graphDualCell M L v).space)
      (({u, v} : Finset E3).centroid ℝ id)
      (({v, w} : Finset E3).centroid ℝ id) := by
  let dNative : DecidableEq E3 := inferInstance
  let : DecidableEq E3 := Classical.decEq E3
  have hboundary : @boundaryComplex E3 _ _ dNative 2 F = boundaryComplex 2 F :=
    congrArg (fun d : DecidableEq E3 => @boundaryComplex E3 _ _ d 2 F)
      (Subsingleton.elim _ _)
  have hpair (a b : E3) :
      @insert E3 (Finset E3) (@Finset.instInsert E3 dNative) a {b} = ({a, b} : Finset E3) :=
    congrArg (fun d : DecidableEq E3 => @insert E3 (Finset E3) (@Finset.instInsert E3 d) a {b})
      (Subsingleton.elim _ _)
  rw [hboundary] at hJL h0 h1 ⊢
  rw [hpair u v] at h0 ⊢
  rw [hpair v w] at h1 ⊢
  let H := boundaryComplex 2 F
  let G := restrict L F.space
  have hH : IsCombinatorialManifold 1 H :=
    isCombinatorialManifold_boundaryComplex F hF.isCombinatorialManifoldWithBoundary
  have hHF : H.faces ⊆ F.faces := boundaryComplex_faces_subset 2 F
  have hHM : H.faces ⊆ M.faces := hHF.trans hFM
  have hvH : {v} ∈ H.faces := H.down_closed h0 (by simp) (Finset.singleton_nonempty v)
  have hvF := hHF hvH
  have hvL := hJL hvH
  let A := dualCell H {v} hvH
  let B := graphDualCell F G v
  let _ : Finite H.faces := (boundaryComplex_faces_finite 2 F).to_subtype
  let _ : Finite A.faces := (dualCell_faces_finite H hvH).to_subtype
  let _ : Finite B.faces := (graphDualCell_faces_finite F G v).to_subtype
  have hGF : G.faces ⊆ F.faces := fun e he =>
    ((mem_restrict_faces_iff_of_faces_subset M L F hLM hFM).mp he).2
  have hGdim : ∀ e ∈ G.faces, e.card ≤ 2 := fun e he => hLdim e he.1
  have hvG : {v} ∈ G.faces := ⟨hvL, F.convexHull_subset_space hvF⟩
  have hB : IsPLBall 2 B.space :=
    hF.isCombinatorialManifoldWithBoundary.isPLBall_graphDualCell_two F G hGF hGdim hvG
  have hA : IsPLBall 1 A.space :=
    hH.isPLBall_dualCell H hvH (k := 0) (Finset.card_singleton _) (by omega)
  have htrace : (graphDualCell M L v).space ∩ F.space = B.space :=
    graphDualCell_space_inter_subcomplex_restrict M F L hFM hLM hvF
  have hcurve : (graphDualCell M L v).space ∩ H.space = A.space :=
    graphDualCell_inter_subcomplex_eq_dualCell M H L hHM hLM hJL hvH
  have hBdA : (boundaryComplex 1 A).space =
      {({u, v} : Finset E3).centroid ℝ id, ({v, w} : Finset E3).centroid ℝ id} :=
    boundary_dualCell_vertex_eq_pair H hH hvH huv hvw huw h0 h1
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := exists_isPLHomeomorphOn_Icc_with_boundary_endpoints A hA hBdA
  have hBC : B.space ⊆ (graphDualCell M L v).space := htrace.symm.subset.trans inter_subset_left
  have hBF : B.space ⊆ F.space := htrace.symm.subset.trans inter_subset_right
  have hBsub : B.faces ⊆ (secondDerived F).faces :=
    (graphDualCell_faces_subset F G v).trans (derivedNeighborhood_faces_subset F G)
  have hAB : A.space ⊆ (boundaryComplex 2 B).space := by
    intro x hx
    obtain ⟨hxC, hxH⟩ := hcurve.symm.subset hx
    have hxF := boundaryComplex_space_subset 2 F hxH
    have hxB : x ∈ B.space := htrace ▸ ⟨hxC, hxF⟩
    have hxFB : x ∈ (boundaryComplex 2 (secondDerived F)).space := by
      rw [boundaryComplex_space_of_isSubdivision F (secondDerived F)
        hF.isCombinatorialManifoldWithBoundary (secondDerived_isSubdivision F)]
      exact hxH
    exact inter_boundaryComplex_space_subset (secondDerived F) B
      hF.isCombinatorialManifoldWithBoundary.secondDerived
      hB.isCombinatorialManifoldWithBoundary hBsub ⟨hxB, hxFB⟩
  have hfront : B.space ∩ frontier (graphDualCell M L v).space ⊆
      (boundaryComplex 2 B).space := fun x hx =>
    frontier_graphDualCell_inter_surface_subset_boundary M F L
      hF.isCombinatorialManifoldWithBoundary hFM hLM hLdim hFint hvF hvL ⟨hx.2, hBF hx.1⟩
  have hcover : (boundaryComplex 2 B).space ⊆
      A.space ∪ frontier (graphDualCell M L v).space := by
    intro x hx
    rcases boundary_graphDualCell_surface_subset_boundary_union_frontier M F L
      hF.isCombinatorialManifoldWithBoundary hFM hLM hLdim hvF hvL hx with hxH | hxFr
    · exact Or.inl (hcurve ▸ ⟨hBC (boundaryComplex_space_subset 2 B hx), hxH⟩)
    · exact Or.inr hxFr
  have hends : A.space ∩ frontier (graphDualCell M L v).space = {γ 0, γ 1} := by
    rw [hγ0, hγ1]
    apply Subset.antisymm
    · rintro x ⟨hxA, hxFr⟩
      apply hBdA.subset
      exact frontier_graphDualCell_inter_curve_subset_boundary M H L hH hHM hLM hJL hLdim
        ((boundaryComplex_space_subset 2 F).trans hFint) hvH
        ⟨hxFr, (hcurve.symm.subset hxA).2⟩
    · intro x hx
      have hxA := boundaryComplex_space_subset 1 A (hBdA.symm.subset hx)
      refine ⟨hxA, ?_⟩
      rcases hx with rfl | hx
      · exact centroid_mem_frontier_graphDualCell_of_edge M L hM hLM hLdim (hJL h0)
          (Finset.card_pair huv) (v := v) (by simp)
      · rcases mem_singleton_iff.mp hx with rfl
        exact centroid_mem_frontier_graphDualCell_of_edge M L hM hLM hLdim (hJL h1)
          (Finset.card_pair hvw) (v := v) (by simp)
  have hbridge := exists_isBridgeDisk_of_boundary_cover B hB hBC hγ hAB hfront hcover hends
  rw [hγ0, hγ1] at hbridge
  change IsBridgeDisk (graphDualCell M L v).space
    (H.space ∩ (graphDualCell M L v).space) (F.space ∩ (graphDualCell M L v).space) _ _
  rw [inter_comm H.space, hcurve, inter_comm F.space, htrace]
  exact hbridge

end DifferentialGeometry.Topology.PiecewiseLinear
