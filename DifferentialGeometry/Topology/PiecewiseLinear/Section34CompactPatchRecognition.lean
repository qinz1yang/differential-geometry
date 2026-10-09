/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellBoundaryRemainder
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellResidualTrace
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualCells
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexSubcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem compactDualNeighborhood_eq_derivedNeighborhood
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces) :
    compactDualNeighborhood M K =
      (derivedNeighborhood M (restrict K (section34CompactGraphSkeleton K))).space := by
  unfold compactDualNeighborhood
  rw [vertices_eq_setOf_restrict_section34CompactGraphSkeleton]
  exact (iUnion_graphDualCell_space M _ ((restrict_faces_subset K _).trans hKM)).trans
    (congrArg (fun d : DecidableEq E3 => (@derivedNeighborhood E3 _ _ d M
      (restrict K (section34CompactGraphSkeleton K))).space) (Subsingleton.elim _ _))

open Classical in
theorem exists_isPLHomeomorphOn_compactDualPatch_with_boundary
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (x : Section34CompactPatchIndex K K) :
    let S := restrict M (convexHull ℝ (x.1.1.1 : Set E3))
    let G := restrict (restrict K (section34CompactGraphSkeleton K)) S.space
    let I := {e : Finset E3 // e ∈ G.faces ∧ e.card = 2 ∧ x.1.2.1.centroid ℝ id ∈ e}
    ∃ q : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (compactDualCutCell M K hKM (.patch x)) ∧
      q '' stdSimplexBoundary 2 = compactDualCutCell M K hKM (.patch x) ∩
        ((boundaryComplex 3 S).space ∪ ⋃ e : I,
          (splittingDisk M e.1 (hKM e.2.1.1.1)).space) := by
  dsimp only
  let dNative : DecidableEq E3 := inferInstance
  let : DecidableEq E3 := Classical.decEq E3
  let t := x.1.1
  let w := x.1.2
  let v := w.1.centroid ℝ id
  let L := restrict K (section34CompactGraphSkeleton K)
  let S := restrict M (convexHull ℝ (t.1 : Set E3))
  let G := restrict L S.space
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hSM : S.faces ⊆ M.faces := restrict_faces_subset M _
  have hGS : G.faces ⊆ S.faces := fun e he =>
    ((mem_restrict_faces_iff_of_faces_subset M L S hLM hSM).mp he).2
  have hGcard : ∀ e ∈ G.faces, e.card ≤ 2 :=
    fun e he => card_le_two_of_mem_restrict_section34CompactGraphSkeleton he.1
  let _ : Finite S.faces := (restrict_faces_finite M _).to_subtype
  have hSsp : S.space = convexHull ℝ (t.1 : Set E3) := restrict_convexHull_space (hKM t.2.1)
  have hSball : IsPLBall 3 S.space := by
    rw [hSsp]
    exact isPLBall_convexHull_of_affineIndependent t.1 (M.indep (hKM t.2.1)) t.2.2
  have hS : IsCombinatorialManifoldWithBoundary 3 S := hSball.isCombinatorialManifoldWithBoundary
  have hSB : boundaryComplex 3 S = simplexBoundary t.1 (M.indep (hKM t.2.1)) := by
    dsimp only [S]
    rw [restrict_convexHull_eq_simplexComplex M (hKM t.2.1)]
    exact boundaryComplex_simplexComplex (M.indep (hKM t.2.1)) t.2.2
  have hGB : G.faces ⊆ (boundaryComplex 3 S).faces := by
    intro e he
    obtain ⟨hne, het⟩ := (mem_restrict_convexHull_faces_iff M (hKM t.2.1)).mp (hGS he)
    rw [hSB]
    refine ⟨het, hne, ?_⟩
    intro heq
    have hle := hGcard e he
    rw [heq, t.2.2] at hle
    omega
  have hvK : {v} ∈ K.faces := centroid_mem_vertices_compactVertexIndex w
  have hvt : v ∈ convexHull ℝ (t.1 : Set E3) := by
    apply x.2
    change v ∈ (w.1 : Set E3)
    rw [← singleton_centroid_eq_compactVertexIndex w]
    exact Finset.mem_singleton_self _
  have hvS : {v} ∈ S.faces :=
    ⟨hKM hvK, by simpa only [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff]
      using hvt⟩
  have hvL : {v} ∈ L.faces :=
    ⟨hvK, convexHull_subset_section34CompactGraphSkeleton hvK (by simp)⟩
  have hvG : {v} ∈ G.faces := ⟨hvL, S.convexHull_subset_space hvS⟩
  have hN : compactDualNeighborhood M K = (derivedNeighborhood M L).space := by
    change (⋃ v ∈ K.vertices, (graphDualCell M L v).space) = _
    rw [vertices_eq_setOf_restrict_section34CompactGraphSkeleton]
    exact iUnion_graphDualCell_space M L hLM
  have hres : compactDualResidualCell M K t.1 =
      closure (S.space \ (derivedNeighborhood S G).space) := by
    rw [compactDualResidualCell, hN,
      ← hSsp, derivedNeighborhood_restrict_right M S L hSM hLM]
    congr 1
    rw [← derivedNeighborhood_space_inter_subcomplex M S L hSM]
    ext z
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hresS : compactDualResidualCell M K t.1 ⊆ S.space := by
    rw [hres]
    exact closure_minimal sdiff_subset (isPolyhedron_space S).isClosed
  have hpatch : compactDualCutCell M K hKM (.patch x) =
      (graphDualCell S G v).space ∩ closure (S.space \ (derivedNeighborhood S G).space) := by
    change compactDualResidualCell M K t.1 ∩ (graphDualCell M L v).space = _
    calc
      _ = ((graphDualCell M L v).space ∩ S.space) ∩ compactDualResidualCell M K t.1 := by
        ext z
        exact ⟨fun h => ⟨⟨h.2, hresS h.1⟩, h.1⟩, fun h => ⟨h.2, h.1.1⟩⟩
      _ = _ := by
        rw [graphDualCell_space_inter_subcomplex_restrict M S L hSM hLM hvS, hres]
  let I := {e : Finset E3 // e ∈ G.faces ∧ e.card = 2 ∧ v ∈ e}
  have hfree := graphDualCell_inter_residual_eq_boundary_remainder S G hS hGS hGcard hvG
  have hpatchFree := hpatch.trans hfree
  obtain ⟨q, hq, hqb⟩ :=
    hS.exists_isPLHomeomorphOn_graphDualCell_boundary_remainder S G hGB hGcard hvG
  have hq' : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      (compactDualCutCell M K hKM (.patch x)) := hpatchFree.symm ▸ hq
  refine ⟨q, hq', ?_⟩
  have hB : @boundaryComplex E3 _ _ dNative 3 S = boundaryComplex 3 S :=
    congrArg (fun d : DecidableEq E3 => @boundaryComplex E3 _ _ d 3 S)
      (Subsingleton.elim _ _)
  rw [hB]
  have hb : q '' stdSimplexBoundary 2 = compactDualCutCell M K hKM (.patch x) ∩
      ((boundaryComplex 3 S).space ∪ ⋃ e : I, (splittingDisk S e.1 (hGS e.2.1)).space) := by
    rw [hpatchFree]
    exact hqb
  rw [hb]
  have hsplit (e : I) : (splittingDisk S e.1 (hGS e.2.1)).space =
      (splittingDisk M e.1 (hKM e.2.1.1.1)).space ∩ S.space :=
    (splittingDisk_space_inter_subcomplex M S hSM (hGS e.2.1)).symm
  have hPS : compactDualCutCell M K hKM (.patch x) ⊆ S.space :=
    fun z hz => hresS hz.1
  ext z
  constructor
  · rintro ⟨hp, hb | he⟩
    · exact ⟨hp, Or.inl hb⟩
    · obtain ⟨e, he⟩ := mem_iUnion.mp he
      rw [hsplit e] at he
      exact ⟨hp, Or.inr (mem_iUnion.mpr ⟨e, he.1⟩)⟩
  · rintro ⟨hp, hb | he⟩
    · exact ⟨hp, Or.inl hb⟩
    · obtain ⟨e, he⟩ := mem_iUnion.mp he
      refine ⟨hp, Or.inr (mem_iUnion.mpr ⟨e, ?_⟩)⟩
      rw [hsplit e]
      exact ⟨he, hPS hp⟩

open Classical in
theorem isPLBall_compactDualCutCell_patch
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (x : Section34CompactPatchIndex K K) :
    IsPLBall 2 (compactDualCutCell M K hKM (.patch x)) := by
  obtain ⟨q, hq, -⟩ := exists_isPLHomeomorphOn_compactDualPatch_with_boundary M K hKM x
  exact ⟨q, hq⟩

end DifferentialGeometry.Topology.PiecewiseLinear
