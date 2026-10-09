/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterFace
import DifferentialGeometry.Topology.PiecewiseLinear.SplittingDiskBoundaryTrace

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
private theorem exists_parametrization_compact_outerFace
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (o : Section34CompactOuterVertexIndex K K) :
    ∃ r : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (compactDualCutCell M K hKM (.outerFace o)) ∧
      r '' stdSimplexBoundary 2 = compactDualCutCell M K hKM (.outerFace o) ∩
        (K.space ∪ ⋃ e : Section34CompactEdgeIndex K K, compactDualSplitDisk M K hKM e) := by
  let dNative : DecidableEq E3 := inferInstance
  let : DecidableEq E3 := Classical.decEq E3
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  let L := restrict K (section34CompactGraphSkeleton K)
  let v := o.1.1.centroid ℝ id
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
  have hBTransport : @boundaryComplex E3 _ _ dNative 3 K = boundaryComplex 3 K :=
    congrArg (fun d : DecidableEq E3 => @boundaryComplex E3 _ _ d 3 K)
      (Subsingleton.elim _ _)
  have hvBNative : {v} ∈ (@boundaryComplex E3 _ _ dNative 3 K).faces := hBTransport.symm ▸ hvB
  obtain ⟨r, hr, hrb⟩ := exists_isPLHomeomorphOn_graphDualCell_outer_boundary M K L hM hK hKM
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
  rw [hU] at hr hrb
  exact ⟨r, hr, hrb⟩

open Classical in
theorem isPLBall_compactDualCutCell_outerFace
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (o : Section34CompactOuterVertexIndex K K) :
    IsPLBall 2 (compactDualCutCell M K hKM (.outerFace o)) := by
  obtain ⟨r, hr, -⟩ := exists_parametrization_compact_outerFace M K hM hK hKM hint o
  exact ⟨r, hr⟩

open Classical in
theorem compactDualCutBoundary_outerFace_eq_inter
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (o : Section34CompactOuterVertexIndex K K) :
    compactDualCutBoundary M K hKM (.outerFace o) =
      compactDualCutCell M K hKM (.outerFace o) ∩
        (K.space ∪ ⋃ e : Section34CompactEdgeIndex K K, compactDualSplitDisk M K hKM e) := by
  obtain ⟨r, hr, hrb⟩ := exists_parametrization_compact_outerFace M K hM hK hKM hint o
  let R := restrict (secondDerived M) (compactDualCutCell M K hKM (.outerFace o))
  let _ : Finite R.faces := (restrict_faces_finite (secondDerived M) _).to_subtype
  have hR := restrict_compactDualCutCell_space M K hKM (.outerFace o)
  exact (hr.image_stdSimplexBoundary_eq_boundaryComplex R hR).symm.trans hrb

theorem compactDualCutCell_outerFace_inter_base_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (o : Section34CompactOuterVertexIndex K K) :
    compactDualCutCell M K hKM (.outerFace o) ∩ K.space ⊆
      compactDualCutBoundary M K hKM (.outerFace o) := by
  rw [compactDualCutBoundary_outerFace_eq_inter M K hM hK hKM hint o]
  exact fun _ hx => ⟨hx.1, Or.inl hx.2⟩

open Classical in
private theorem exists_parametrization_compact_outerArc
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (q : Section34CompactOuterEdgeIndex K K) :
    ∃ r : (Fin 2 → ℝ) → E3,
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) (compactDualCutCell M K hKM (.outerArc q)) ∧
      r '' stdSimplexBoundary 1 = compactDualCutCell M K hKM (.outerArc q) ∩ K.space := by
  let dNative : DecidableEq E3 := inferInstance
  let : DecidableEq E3 := Classical.decEq E3
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  let D := splittingDisk M q.1.1 (hKM q.1.2.1)
  let _ : Finite D.faces := (splittingDisk_faces_finite M (hKM q.1.2.1)).to_subtype
  let S := (boundaryComplex 2 D).space
  have hDTransport : @boundaryComplex E3 _ _ dNative 2 D = boundaryComplex 2 D :=
    congrArg (fun d : DecidableEq E3 => @boundaryComplex E3 _ _ d 2 D)
      (Subsingleton.elim _ _)
  have hOuter : compactDualCutCell M K hKM (.outerArc q) = closure (S \ K.space) := by
    change closure ((@boundaryComplex E3 _ _ dNative 2 D).space \ K.space) = _
    rw [hDTransport]
  rw [hOuter]
  have heB : q.1.1 ∈ (boundaryComplex 3 K).faces := by
    apply mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset 3 K) q.1.2.1
      (centroid_mem_openSimplex_of_mem_faces K q.1.1 q.1.2.1)
    rw [← frontier_space_eq_boundaryComplex_space (n := 2) hK]
    exact q.2 (q.1.1.centroid_mem_convexHull (K.nonempty_of_mem_faces q.1.2.1))
  have heM : q.1.1 ∉ (boundaryComplex 3 M).faces :=
    hM.notMem_boundaryComplex_faces_of_forall_mem_interior (by simp) (hKM q.1.2.1)
      (fun v hv => hint (K.subset_space q.1.2.1 hv))
  obtain ⟨γ, δ, -, hδ, hδ0, hδ1, hmeet⟩ :=
    exists_parametrizations_boundary_splittingDisk_complement M K hM hK hKM heB q.1.2.2.1 heM
  obtain ⟨hr, hrb⟩ := hδ.image_stdSimplexBoundary_one_of_Icc
  refine ⟨_, hr, ?_⟩
  rw [hrb, hδ0, hδ1, ← hmeet]
  have hsub : closure (S \ K.space) ⊆ S :=
    closure_minimal sdiff_subset (isPolyhedron_space (boundaryComplex 2 D)).isClosed
  change (S ∩ K.space) ∩ closure (S \ K.space) = closure (S \ K.space) ∩ K.space
  ext x
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩⟩

open Classical in
theorem isPLBall_compactDualCutCell_outerArc
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (q : Section34CompactOuterEdgeIndex K K) :
    IsPLBall 1 (compactDualCutCell M K hKM (.outerArc q)) := by
  obtain ⟨r, hr, -⟩ := exists_parametrization_compact_outerArc M K hM hK hKM hint q
  exact ⟨r, hr⟩

open Classical in
theorem compactDualCutBoundary_outerArc_eq_inter
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (q : Section34CompactOuterEdgeIndex K K) :
    compactDualCutBoundary M K hKM (.outerArc q) =
      compactDualCutCell M K hKM (.outerArc q) ∩ K.space := by
  obtain ⟨r, hr, hrb⟩ := exists_parametrization_compact_outerArc M K hM hK hKM hint q
  let R := restrict (secondDerived M) (compactDualCutCell M K hKM (.outerArc q))
  let _ : Finite R.faces := (restrict_faces_finite (secondDerived M) _).to_subtype
  have hR := restrict_compactDualCutCell_space M K hKM (.outerArc q)
  exact (hr.image_stdSimplexBoundary_eq_boundaryComplex R hR).symm.trans hrb

theorem compactDualCutCell_outerArc_inter_base_subset_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (q : Section34CompactOuterEdgeIndex K K) :
    compactDualCutCell M K hKM (.outerArc q) ∩ K.space ⊆
      compactDualCutBoundary M K hKM (.outerArc q) := by
  exact (compactDualCutBoundary_outerArc_eq_inter M K hM hK hKM hint q).symm.subset

end DifferentialGeometry.Topology.PiecewiseLinear
