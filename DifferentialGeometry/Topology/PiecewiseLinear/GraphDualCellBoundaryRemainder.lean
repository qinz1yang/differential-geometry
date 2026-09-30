/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellSubgraph
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluingTwo
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_graphDualCell_boundary_remainder
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hLB : L.faces ⊆ (boundaryComplex 3 K).faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces) :
    let C := graphDualCell K L v
    let I := {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}
    let U := (boundaryComplex 3 K).space ∪ ⋃ e : I,
      (splittingDisk K e.1 (boundaryComplex_faces_subset 3 K (hLB e.2.1))).space
    ∃ q : (Fin 3 → ℝ) → E,
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        (closure ((boundaryComplex 3 C).space \ U)) ∧
      q '' stdSimplexBoundary 2 = closure ((boundaryComplex 3 C).space \ U) ∩ U := by
  let C := graphDualCell K L v
  let B := boundaryComplex 3 K
  let F := boundaryComplex 3 C
  let I := {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}
  have hLK : L.faces ⊆ K.faces := hLB.trans (boundaryComplex_faces_subset 3 K)
  let D : I → Set E := fun e => (splittingDisk K e.1 (hLK e.2.1)).space
  let Z : Set E := C.space ∩ B.space
  let U : Set E := Z ∪ ⋃ e : I, D e
  let _ : Finite C.faces := (graphDualCell_faces_finite K L v).to_subtype
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  let _ : Finite F.faces := (boundaryComplex_faces_finite 3 C).to_subtype
  let _ : Finite I := ((Set.toFinite K.faces).subset
    (fun e he => hLK he.1) : {e : Finset E | e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}.Finite).to_subtype
  let _ : Fintype I := Fintype.ofFinite I
  have hC : IsPLBall 3 C.space := hK.isPLBall_graphDualCell K L hLK hcard hv
  have hCS : C.space ⊆ K.space :=
    (graphDualCell_space_subset K L v).trans (derivedNeighborhood_space_subset K L)
  have hF : IsPLSphere 2 F.space := isPLSphere_boundaryComplex_space_of_isPLBall C hC
  have hFm : IsCombinatorialManifoldWithBoundary 2 F :=
    (IsPLSphere.isCombinatorialManifold (n := 1) hF).isCombinatorialManifoldWithBoundary
  have hFC : F.space ⊆ C.space := boundaryComplex_space_subset 3 C
  have hZ : IsPLBall 2 Z :=
    hK.isPLBall_graphDualCell_inter_boundaryComplex K L hLK hcard hv (hLB hv)
  have hZF : Z ⊆ F.space :=
    hK.graphDualCell_inter_boundaryComplex_subset_boundary K L hLK hcard hv
  have hD : ∀ e : I, IsPLBall 2 (D e) := fun e =>
    hK.isPLBall_splittingDisk K (hLK e.2.1) e.2.2.1 (by norm_num : 1 ≤ 2)
  have hDC : ∀ e : I, D e ⊆ C.space := by
    intro e
    obtain ⟨w, hw, hwv⟩ := Finset.exists_mem_ne
      (show 1 < e.1.card by rw [e.2.2.1]; norm_num) v
    have hinter := graphDualCell_space_inter_of_mem K L hLK hcard e.2.1 e.2.2.2 hw hwv.symm
    exact hinter.symm.subset.trans inter_subset_left
  have hDF : ∀ e : I, D e ⊆ F.space := by
    intro e
    obtain ⟨w, hw, hwv⟩ := Finset.exists_mem_ne
      (show 1 < e.1.card by rw [e.2.2.1]; norm_num) v
    have hwL : {w} ∈ L.faces := L.down_closed e.2.1
      (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)
    have hinter := graphDualCell_space_inter_of_mem K L hLK hcard e.2.1 e.2.2.2 hw hwv.symm
    have hW := hK.isPLBall_graphDualCell K L hLK hcard hwL
    have hWS := (graphDualCell_space_subset K L w).trans (derivedNeighborhood_space_subset K L)
    have hI : IsPLBall 2 (C.space ∩ (graphDualCell K L w).space) := hinter.symm ▸ hD e
    exact hinter.symm.subset.trans
      (hK.inter_subset_boundaryComplex_of_isPLBall C hC hCS hW hWS hI)
  have hZD : ∀ e : I, IsPLBall 1 (Z ∩ D e) := by
    intro e
    have heB : e.1 ∈ B.faces := hLB e.2.1
    have hEq : Z ∩ D e = (splittingDisk B e.1 heB).space := by
      calc
        _ = D e ∩ B.space := by
          ext x
          exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hDC e h.1, h.2⟩, h.1⟩⟩
        _ = _ := splittingDisk_space_inter_subcomplex K B (boundaryComplex_faces_subset 3 K) heB
    rw [hEq]
    exact (isCombinatorialManifold_boundaryComplex K hK).isCombinatorialManifoldWithBoundary
      |>.isPLBall_splittingDisk B heB e.2.2.1 (by norm_num : 1 ≤ 1)
  have hdis : ∀ e f : I, e ≠ f → Disjoint (D e) (D f) := by
    intro e f hef
    exact disjoint_splittingDisk_space K (hLK e.2.1) (hLK f.2.1)
      (fun h => hef (Subtype.ext h)) (e.2.2.1.trans f.2.2.1.symm)
  have hU : IsPLBall 2 U := by
    simpa only [Finset.mem_univ, iUnion_true, U] using
      hFm.isPLBall_union_iUnion_of_pairwiseDisjoint_in_surface hZ hZF Finset.univ D
        (fun e _ => hD e) (fun e _ => hDF e) (fun e _ => hZD e)
        (fun e _ f _ hef => hdis e f hef)
  have hUF : U ⊆ F.space := union_subset hZF (iUnion_subset hDF)
  have hrem : F.space \ (B.space ∪ ⋃ e : I, D e) = F.space \ U := by
    ext x
    constructor
    · rintro ⟨hx, hn⟩
      refine ⟨hx, ?_⟩
      rintro (hz | he)
      · exact hn (Or.inl hz.2)
      · exact hn (Or.inr he)
    · rintro ⟨hx, hn⟩
      refine ⟨hx, ?_⟩
      rintro (hb | he)
      · exact hn (Or.inl ⟨hFC hx, hb⟩)
      · exact hn (Or.inr he)
  obtain ⟨q, hq⟩ := hF.isPLBall_closure_sdiff hU hUF
  have hbd := hF.image_stdSimplexBoundary_complement hU hUF hq
  have hclosed : closure (F.space \ U) ⊆ F.space :=
    closure_minimal sdiff_subset hF.isPolyhedron.isClosed
  have hmeet : closure (F.space \ U) ∩ U =
      closure (F.space \ U) ∩ (B.space ∪ ⋃ e : I, D e) := by
    ext x
    constructor
    · rintro ⟨hx, hz | he⟩
      · exact ⟨hx, Or.inl hz.2⟩
      · exact ⟨hx, Or.inr he⟩
    · rintro ⟨hx, hb | he⟩
      · exact ⟨hx, Or.inl ⟨hFC (hclosed hx), hb⟩⟩
      · exact ⟨hx, Or.inr he⟩
  change ∃ q : (Fin 3 → ℝ) → E,
    IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      (closure (F.space \ (B.space ∪ ⋃ e : I, D e))) ∧
    q '' stdSimplexBoundary 2 = closure (F.space \ (B.space ∪ ⋃ e : I, D e)) ∩
      (B.space ∪ ⋃ e : I, D e)
  rw [hrem]
  exact ⟨q, hq, hbd.trans hmeet⟩

end DifferentialGeometry.Topology.PiecewiseLinear
