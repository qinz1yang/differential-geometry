/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualSource
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceTorusCycle
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactIncidentEdges

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem mem_interior_subfamily {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {D : ι → Set X} (hD : ∀ i, IsClosed (D i)) {J : Set ι} {x : X}
    (hx : x ∈ interior (⋃ i, D i)) (hforeign : ∀ i ∉ J, x ∉ D i) :
    x ∈ interior (⋃ i ∈ J, D i) := by
  classical
  let F := ⋃ i ∉ J, D i
  have hF : IsClosed F :=
    isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ => hD i
  have hxF : x ∉ F := by
    intro hxF
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxF
    obtain ⟨hiJ, hxi⟩ := mem_iUnion.mp hi
    exact hforeign i hiJ hxi
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset ((isOpen_interior.sdiff hF).mem_nhds ⟨hx, hxF⟩) ?_
  rintro y ⟨hy, hyF⟩
  obtain ⟨i, hyi⟩ := mem_iUnion.mp (interior_subset hy)
  by_cases hi : i ∈ J
  · exact mem_iUnion₂.mpr ⟨i, hi, hyi⟩
  · exact (hyF (mem_iUnion₂.mpr ⟨i, hi, hyi⟩)).elim

theorem image_graphSkeleton_inter_convexHull_subset_interior_graphDualCells
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces] [Finite K.faces]
    {f h : E3 → E3} (hf : ContinuousOn f (compactDualNeighborhood M K))
    (hN : f '' compactDualNeighborhood M K ∈ nhdsSet (h '' section34CompactGraphSkeleton K))
    (havoid : ∀ v ∈ K.vertices, ∀ s ∈ K.faces, v ∉ s →
      Disjoint (f '' (graphDualCell M (restrict K (section34CompactGraphSkeleton K)) v).space)
        (h '' convexHull ℝ (s : Set E3))) {s : Finset E3} (hs : s ∈ K.faces) :
    h '' (section34CompactGraphSkeleton K ∩ convexHull ℝ (s : Set E3)) ⊆
      interior (f '' (⋃ v ∈ (s : Set E3),
        (graphDualCell M (restrict K (section34CompactGraphSkeleton K)) v).space)) := by
  classical
  let L := restrict K (section34CompactGraphSkeleton K)
  let D (v : K.vertices) := f '' (graphDualCell M L v).space
  let _ : Finite K.vertices := (SimplicialComplex.finite_vertices K).to_subtype
  have hD : ∀ v, IsClosed (D v) := by
    intro v
    let _ : Finite (graphDualCell M L v).faces := (graphDualCell_faces_finite M L v).to_subtype
    exact ((SimplicialComplex.isCompact_geometricSpace _).image_of_continuousOn
      (hf.mono (subset_iUnion₂_of_subset (v : E3) v.2 subset_rfl))).isClosed
  have hDN : (⋃ v, D v) = f '' compactDualNeighborhood M K := by
    simp only [D, ← image_iUnion, iUnion_coe_set, compactDualNeighborhood, L]
  rintro y ⟨x, hx, rfl⟩
  have hxN : h x ∈ interior (⋃ v, D v) := by
    rw [hDN]
    exact subset_interior_iff_mem_nhdsSet.mpr hN ⟨x, hx.1, rfl⟩
  have hxJ := mem_interior_subfamily hD (J := {v : K.vertices | (v : E3) ∈ s}) hxN
    (fun v hv hvD => (Set.disjoint_left.mp (havoid v v.2 s hs hv)) hvD ⟨x, hx.2, rfl⟩)
  apply interior_mono ?_ hxJ
  refine iUnion₂_subset fun v hv => image_mono ?_
  exact subset_iUnion₂_of_subset (v : E3) hv subset_rfl

theorem section34CompactGraphRecognition
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) {f h : E3 → E3}
    (hf : ContinuousOn f (compactDualNeighborhood M K))
    (hN : f '' compactDualNeighborhood M K ∈ nhdsSet (h '' section34CompactGraphSkeleton K))
    (havoid : ∀ v ∈ K.vertices, ∀ s ∈ K.faces, v ∉ s →
      Disjoint (f '' (graphDualCell M (restrict K (section34CompactGraphSkeleton K)) v).space)
        (h '' convexHull ℝ (s : Set E3))) :
    (∀ w : Section34CompactVertexIndex K K, h '' (w.1 : Set E3) ⊆
      interior (section34CompactVertexBallImage (compactDualCutCell M K hKM) f w)) ∧
    (∀ (e : Section34CompactEdgeIndex K K) (s : Section34CompactSimplexIndex K 3),
      (section34CompactSplitDiskImage (compactDualCutCell M K hKM) f e ∩
        h '' convexHull ℝ (s.1 : Set E3)).Nonempty → Section34Incident e.1 s.1) ∧
    (∀ (w : Section34CompactVertexIndex K K) (s : Section34CompactSimplexIndex K 3),
      (section34CompactVertexBallImage (compactDualCutCell M K hKM) f w ∩
        h '' convexHull ℝ (s.1 : Set E3)).Nonempty → Section34Incident w.1 s.1) ∧
    (∀ s : Section34CompactSimplexIndex K 3, h '' section34CompactSimplexRim s.1 ⊆
      interior (section34CompactFaceTorus
        (section34CompactVertexBallImage (compactDualCutCell M K hKM) f) s)) := by
  classical
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  have hinc (w : Section34CompactVertexIndex K K) (s : Finset E3) (hs : s ∈ K.faces)
      (hx : (f '' compactDualVertexBall M K w ∩ h '' convexHull ℝ (s : Set E3)).Nonempty) :
      Section34Incident w.1 s := by
    by_contra hnot
    have hv : w.1.centroid ℝ id ∉ s := by
      intro hv
      apply hnot
      rw [Section34Incident, ← singleton_centroid_eq_compactVertexIndex w,
        Finset.coe_singleton, singleton_subset_iff]
      exact subset_convexHull ℝ _ hv
    obtain ⟨x, hx⟩ := hx
    exact (Set.disjoint_left.mp (havoid _ (centroid_mem_vertices_compactVertexIndex w)
      s hs hv)) hx.1 hx.2
  refine ⟨?_, ?_, fun w s => hinc w s.1 s.2.1, ?_⟩
  · intro w
    have hw := image_graphSkeleton_inter_convexHull_subset_interior_graphDualCells
      M K hf hN havoid w.2.1
    have hsrc : (w.1 : Set E3) ⊆
        section34CompactGraphSkeleton K ∩ convexHull ℝ (w.1 : Set E3) :=
      subset_inter ((subset_convexHull ℝ _).trans w.2.2.2) (subset_convexHull ℝ _)
    have hout := (image_mono hsrc).trans hw
    have hset : (w.1 : Set E3) = {w.1.centroid ℝ id} := by
      simpa only [Finset.coe_singleton] using
        congrArg (fun t : Finset E3 => (t : Set E3))
          (singleton_centroid_eq_compactVertexIndex w).symm
    simpa only [hset, biUnion_singleton, compactDualVertexBall, section34CompactVertexBallImage,
      compactDualCutCell] using hout
  · intro e s hx
    obtain ⟨w, w', -, he, hD⟩ := compactDualSplitDisk_eq_inter_vertexBalls M K hKM e
    obtain ⟨x, hxD, hxs⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hxD
    change z ∈ compactDualSplitDisk M K hKM e at hz
    rw [hD] at hz
    have hw := hinc w s.1 s.2.1 ⟨f z, ⟨z, hz.1, rfl⟩, hxs⟩
    have hw' := hinc w' s.1 s.2.1 ⟨f z, ⟨z, hz.2, rfl⟩, hxs⟩
    change (e.1 : Set E3) ⊆ convexHull ℝ (s.1 : Set E3)
    rw [he]
    exact union_subset hw hw'
  · intro s
    rw [section34CompactFaceTorus_compactDual_eq M K hKM f s]
    exact (image_mono (subset_inter
      (section34CompactSimplexRim_subset_graphSkeleton s.2.1 s.2.2.le)
      (section34CompactSimplexRim_subset s.1))).trans
        (image_graphSkeleton_inter_convexHull_subset_interior_graphDualCells
          M K hf hN havoid s.2.1)

end DifferentialGeometry.Topology.PiecewiseLinear
