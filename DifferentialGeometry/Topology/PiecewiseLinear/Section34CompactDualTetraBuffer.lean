/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FiniteBallUnion
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellIncidence
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCellSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTraces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactPatchRecognition
import DifferentialGeometry.Topology.SimplicialComplex.EdgeGraph

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem isPLBall_compactDualTetra_union_vertexCells
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (t : Section34CompactSimplexIndex K 4) :
    let L := restrict K (section34CompactGraphSkeleton K)
    IsPLBall 3 (compactDualResidualCell M K t.1 ∪
      ⋃ v ∈ (t.1 : Set E3), (graphDualCell M L v).space) := by
  let : DecidableEq E3 := Classical.decEq E3
  dsimp only
  let L := restrict K (section34CompactGraphSkeleton K)
  let R := compactDualResidualCell M K t.1
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hcard : ∀ e ∈ L.faces, e.card ≤ 2 :=
    fun _ he => card_le_two_of_mem_restrict_section34CompactGraphSkeleton he
  have hvK (v : E3) (hv : v ∈ t.1) : {v} ∈ K.faces :=
    K.down_closed t.2.1 (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hvL (v : E3) (hv : v ∈ t.1) : {v} ∈ L.faces :=
    ⟨hvK v hv, convexHull_subset_section34CompactGraphSkeleton (hvK v hv) (by simp)⟩
  have hpair (v : E3) (hv : v ∈ t.1) (w : E3) (hw : w ∈ t.1) : {v, w} ⊆ t.1 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hv
    · exact hw
  have heK (v : E3) (hv : v ∈ t.1) (w : E3) (hw : w ∈ t.1) : {v, w} ∈ K.faces :=
    K.down_closed t.2.1 (hpair v hv w hw) (Finset.insert_nonempty _ _)
  have heL (v : E3) (hv : v ∈ t.1) (w : E3) (hw : w ∈ t.1) (hne : v ≠ w) :
      {v, w} ∈ L.faces :=
    ⟨heK v hv w hw, convexHull_subset_section34CompactGraphSkeleton (heK v hv w hw)
      (by rw [Finset.card_pair hne])⟩
  have hV (v : E3) (hv : v ∈ t.1) : IsPLBall 3 (graphDualCell M L v).space :=
    hM.isPLBall_graphDualCell M L hLM hcard (hvL v hv)
  have hVR (v : E3) (hv : v ∈ t.1) : IsPLBall 2 ((graphDualCell M L v).space ∩ R) := by
    let w : Section34CompactVertexIndex K K :=
      ⟨{v}, hvK v hv, by simp, (hvL v hv).2⟩
    let p : Section34CompactPatchIndex K K :=
      ⟨(t, w), (Finset.coe_subset.mpr (Finset.singleton_subset_iff.mpr hv)).trans
        (subset_convexHull ℝ _)⟩
    simpa only [compactDualCutCell, compactDualVertexBall, p, w,
      Finset.centroid_singleton, id_eq, inter_comm] using
      isPLBall_compactDualCutCell_patch M K hKM p
  have hVV (v : E3) (hv : v ∈ t.1) (w : E3) (hw : w ∈ t.1) (hne : v ≠ w) :
      IsPLBall 2 ((graphDualCell M L v).space ∩ (graphDualCell M L w).space) := by
    rw [graphDualCell_space_inter M L hLM hcard hne (heL v hv w hw hne)]
    exact hM.isPLBall_splittingDisk M (hKM (heK v hv w hw))
      (k := 1) (Finset.card_pair hne) (by decide)
  have hVRV (v : E3) (hv : v ∈ t.1) (w : E3) (hw : w ∈ t.1) (hne : v ≠ w) :
      IsPLBall 1 (((graphDualCell M L v).space ∩ R) ∩ (graphDualCell M L w).space) := by
    let e : Section34CompactEdgeIndex K K :=
      ⟨{v, w}, heK v hv w hw, Finset.card_pair hne, (heL v hv w hw hne).2⟩
    let i : Section34CompactEdgeArcIndex K K :=
      ⟨(t, e), (Finset.coe_subset.mpr (hpair v hv w hw)).trans (subset_convexHull ℝ _)⟩
    obtain ⟨G, -, hG, hball⟩ := exists_subcomplex_compactDualEdgeArc M K hKM i
    have hiBall : IsPLBall 1 (compactDualCutCell M K hKM (.edgeArc i)) := hG ▸ hball
    change IsPLBall 1 (R ∩ (splittingDisk M {v, w} (hKM (heK v hv w hw))).space) at hiBall
    have hI := graphDualCell_space_inter M L hLM hcard hne (heL v hv w hw hne)
    have heq : ((graphDualCell M L v).space ∩ R) ∩ (graphDualCell M L w).space =
        R ∩ (splittingDisk M {v, w} (hKM (heK v hv w hw))).space := by
      calc
        _ = R ∩ ((graphDualCell M L v).space ∩ (graphDualCell M L w).space) := by
          ext x
          simp only [mem_inter_iff]
          tauto
        _ = _ := congrArg (fun S : Set E3 => R ∩ S) hI
    exact heq.symm ▸ hiBall
  exact isPLBall_union_iUnion_of_disk_intersections
    (isPLBall_compactDualResidualCell_tetrahedron M K hKM t) t.1
    (fun v => (graphDualCell M L v).space) hV hVR hVV hVRV
    (fun v hv w hw z hz hvw hvz hwz => graphDualCell_triple_inter_eq_empty M L hLM hcard
      (hvL v hv) (hvL w hw) (hvL z hz) hvw hvz hwz)

open Classical in
theorem compactDualTetra_union_vertexCells_eq
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces)
    (t : Section34CompactSimplexIndex K 4) :
    let L := restrict K (section34CompactGraphSkeleton K)
    compactDualResidualCell M K t.1 ∪ ⋃ v ∈ (t.1 : Set E3), (graphDualCell M L v).space =
      convexHull ℝ (t.1 : Set E3) ∪ ⋃ v ∈ (t.1 : Set E3), (graphDualCell M L v).space := by
  dsimp only
  let L := restrict K (section34CompactGraphSkeleton K)
  apply Subset.antisymm
  · exact union_subset_union
      (closure_minimal sdiff_subset (t.1.finite_toSet.isCompact_convexHull ℝ).isClosed) subset_rfl
  · rintro x (hxt | hxV)
    · by_cases hxN : x ∈ compactDualNeighborhood M K
      · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxN
        have hvt : v ∈ t.1 := by
          by_contra hn
          exact (eq_empty_iff_forall_notMem.mp
            (graphDualCell_space_inter_convexHull_eq_empty L (hKM hv) (hKM t.2.1) hn))
            x ⟨hxv, hxt⟩
        exact Or.inr (mem_iUnion₂.mpr ⟨v, hvt, hxv⟩)
      · exact Or.inl (subset_closure ⟨hxt, hxN⟩)
    · exact Or.inr hxV

open Classical in
theorem isPLBall_convexHull_union_graphDualCells
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (t : Section34CompactSimplexIndex K 4) :
    let L := restrict K (section34CompactGraphSkeleton K)
    IsPLBall 3 (convexHull ℝ (t.1 : Set E3) ∪
      ⋃ v ∈ (t.1 : Set E3), (graphDualCell M L v).space) := by
  dsimp only
  rw [← compactDualTetra_union_vertexCells_eq M K hKM t]
  exact isPLBall_compactDualTetra_union_vertexCells M K hKM hM t

open Classical in
theorem exists_compactTetraExteriorBuffer
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hKM : K.faces ⊆ M.faces)
    (hKint : K.space ⊆ interior M.space) (t : Section34CompactSimplexIndex K 4) :
    let L := restrict K (section34CompactGraphSkeleton K)
    ∃ B : Set E3, IsPLBall 3 B ∧ B ⊆ interior M.space ∧
      (convexHull ℝ (t.1 : Set E3) ∪
        ⋃ v ∈ (t.1 : Set E3), (graphDualCell M L v).space) ⊆ interior B ∧
      Disjoint B (K.vertices \ (t.1 : Set E3)) := by
  let : DecidableEq E3 := Classical.decEq E3
  dsimp only
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  let L := restrict K (section34CompactGraphSkeleton K)
  let A := convexHull ℝ (t.1 : Set E3) ∪
    ⋃ v ∈ (t.1 : Set E3), (graphDualCell M L v).space
  let F := K.vertices \ (t.1 : Set E3)
  have hA : IsPLBall 3 A := isPLBall_convexHull_union_graphDualCells M K hKM hM t
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hNint : (derivedNeighborhood M L).space ⊆ interior M.space :=
    derivedNeighborhood_space_subset_interior (n := 2) (by simp) hM hLM
      ((space_mono_of_faces_subset (restrict_faces_subset K _)).trans hKint)
  have hAint : A ⊆ interior M.space := union_subset
    ((K.convexHull_subset_space t.2.1).trans hKint)
    (iUnion₂_subset fun v _ => (graphDualCell_space_subset M L v).trans hNint)
  have hAF : Disjoint A F := by
    rw [Set.disjoint_left]
    rintro x (hxt | hxV) hxF
    · exact hxF.2 (mem_of_mem_convexHull_of_singleton_mem K hxF.1 t.2.1 hxt)
    · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxV
      have hvK : {v} ∈ K.faces := K.down_closed t.2.1
        (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      have hvx : v ≠ x := fun h => hxF.2 (h ▸ hv)
      exact notMem_graphDualCell_space_of_ne L (hKM hvK) (hKM hxF.1) hvx hxv
  have hFfin : F.Finite := (SimplicialComplex.finite_vertices K).sdiff
  have hFc : IsClosed F := hFfin.isClosed
  obtain ⟨B, hB, hAB, hBU⟩ := hA.exists_isPLBall_subset_interior_of_isOpen
    (isOpen_interior.sdiff hFc)
    (fun x hx => ⟨hAint hx, fun hxF => Set.disjoint_left.mp hAF hx hxF⟩)
  exact ⟨B, hB, hBU.trans sdiff_subset, hAB,
    Set.disjoint_left.mpr (fun x hxB hxF => (hBU hxB).2 hxF)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
