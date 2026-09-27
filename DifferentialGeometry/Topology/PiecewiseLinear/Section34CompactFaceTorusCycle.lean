/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CyclicBallUnion
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellIncidence
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem section34CompactFaceTorus_compactDual_eq
    (M K : Geometry.SimplicialComplex ℝ E3) (hKM : K.faces ⊆ M.faces)
    (f : E3 → E3) (s : Section34CompactSimplexIndex K 3) :
    section34CompactFaceTorus
      (section34CompactVertexBallImage (compactDualCutCell M K hKM) f) s =
        f '' (⋃ v ∈ (s.1 : Set E3),
          (graphDualCell M (restrict K (section34CompactGraphSkeleton K)) v).space) := by
  let : DecidableEq E3 := Classical.decEq E3
  apply Subset.antisymm
  · intro y hy
    obtain ⟨a, ha, hy⟩ := mem_iUnion₂.mp hy
    let w := a.1.2
    have hvK := centroid_mem_vertices_compactVertexIndex w
    have hvw : w.1.centroid ℝ id ∈ w.1 := by
      rw [← singleton_centroid_eq_compactVertexIndex w]
      simp only [Finset.centroid_singleton, id_eq, Finset.mem_singleton]
    have hws : Section34Incident w.1 s.1 := ha ▸ a.2
    have hvs := mem_of_mem_convexHull_of_singleton_mem K hvK s.2.1 (hws hvw)
    exact image_mono (subset_iUnion₂_of_subset (w.1.centroid ℝ id) hvs subset_rfl) hy
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    have hvK : {v} ∈ K.faces := K.down_closed s.2.1
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    let w : Section34CompactVertexIndex K K := ⟨{v}, hvK, by simp,
      convexHull_subset_section34CompactGraphSkeleton hvK (by simp)⟩
    let a : Section34CompactArcIndex K K := ⟨(s, w), by
      change (({v} : Finset E3) : Set E3) ⊆ convexHull ℝ (s.1 : Set E3)
      rw [Finset.coe_singleton, singleton_subset_iff]
      exact subset_convexHull ℝ _ hv⟩
    refine mem_iUnion₂.mpr ⟨a, rfl, x, ?_, rfl⟩
    simpa only [compactDualCutCell, compactDualVertexBall, a, w,
      Finset.centroid_singleton, id_eq] using hxv

open Classical in
theorem isCombinatorialSolidTorus_image_iUnion_graphDualCells
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hKM : K.faces ⊆ M.faces)
    (s : Section34CompactSimplexIndex K 3) {f : E3 → E3}
    (hf : IsPLHomeomorphOn f (compactDualNeighborhood M K)
      (f '' compactDualNeighborhood M K)) :
    IsCombinatorialSolidTorus (f '' (⋃ v ∈ (s.1 : Set E3),
      (graphDualCell M (restrict K (section34CompactGraphSkeleton K)) v).space)) := by
  let : DecidableEq E3 := Classical.decEq E3
  let L := restrict K (section34CompactGraphSkeleton K)
  let e : Fin 3 ≃ s.1 := (Fintype.equivFinOfCardEq (by simpa using s.2.2)).symm
  let v (i : Fin 3) : E3 := e i
  let C (i : Fin 3) := (graphDualCell M L (v i)).space
  have hv (i : Fin 3) : v i ∈ s.1 := (e i).2
  have hvK (i : Fin 3) : {v i} ∈ K.faces := K.down_closed s.2.1
    (Finset.singleton_subset_iff.mpr (hv i)) (Finset.singleton_nonempty _)
  have hvL (i : Fin 3) : {v i} ∈ L.faces :=
    ⟨hvK i, convexHull_subset_section34CompactGraphSkeleton (hvK i) (by simp)⟩
  have hinj : Function.Injective v := fun i j hij => e.injective (Subtype.ext hij)
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hcard : ∀ t ∈ L.faces, t.card ≤ 2 :=
    fun _ ht => card_le_two_of_mem_restrict_section34CompactGraphSkeleton ht
  have hCN (i : Fin 3) : C i ⊆ compactDualNeighborhood M K :=
    subset_iUnion₂_of_subset (v i) (hvK i) subset_rfl
  have hC (i : Fin 3) : IsPLBall 3 (C i) :=
    hM.isPLBall_graphDualCell M L hLM hcard (hvL i)
  have hCC (i j : Fin 3) (hij : i ≠ j) : IsPLBall 2 (C i ∩ C j) := by
    have hne : v i ≠ v j := fun h => hij (hinj h)
    have hpair : {v i, v j} ⊆ s.1 := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hv i
      · exact hv j
    have heK := K.down_closed s.2.1 hpair (Finset.insert_nonempty _ _)
    have heL : {v i, v j} ∈ L.faces := ⟨heK,
      convexHull_subset_section34CompactGraphSkeleton heK (by rw [Finset.card_pair hne])⟩
    rw [show C i ∩ C j = (splittingDisk M {v i, v j} (hKM heK)).space from
      graphDualCell_space_inter M L hLM hcard hne heL]
    exact hM.isPLBall_splittingDisk M (hKM heK) (k := 1) (Finset.card_pair hne) (by decide)
  have hAdj : ∀ i j : Fin 3, i ≠ j → (SimpleGraph.cycleGraph 3).Adj i j := by decide
  have hball : IsCombinatorialSolidTorus (⋃ i : Fin 3, f '' C i) := by
    apply isCombinatorialSolidTorus_iUnion_of_cycle (n := 0)
      (fun i => f '' C i)
    · intro i
      exact (hC i).of_isPLHomeomorphOn (hf.restrict (hC i).isPolyhedron (hCN i))
    · intro i j hij
      have hd := hCC i j hij.ne
      rw [← hf.bijOn.injOn.image_inter (hCN i) (hCN j)]
      exact hd.of_isPLHomeomorphOn (hf.restrict hd.isPolyhedron
        (inter_subset_left.trans (hCN i)))
    · intro i j hij hnot
      exact (hnot (hAdj i j hij)).elim
    · intro i j k hij hik hjk
      rw [← hf.bijOn.injOn.image_inter (hCN i) (hCN j),
        ← hf.bijOn.injOn.image_inter (inter_subset_left.trans (hCN i)) (hCN k)]
      have htr := graphDualCell_triple_inter_eq_empty M L hLM hcard
        (hvL i) (hvL j) (hvL k) (fun h => hij (hinj h))
        (fun h => hik (hinj h)) (fun h => hjk (hinj h))
      change f '' ((C i ∩ C j) ∩ C k) = ∅
      rw [htr, image_empty]
  have heq : (⋃ i : Fin 3, C i) = ⋃ z ∈ (s.1 : Set E3), (graphDualCell M L z).space := by
    apply Subset.antisymm
    · exact iUnion_subset fun i => subset_iUnion₂_of_subset (v i) (hv i) subset_rfl
    · refine iUnion₂_subset fun z hz => ?_
      obtain ⟨i, hi⟩ := e.surjective ⟨z, hz⟩
      have hiz : v i = z := congrArg Subtype.val hi
      exact subset_iUnion_of_subset i (by rw [← hiz])
  rw [← image_iUnion, heq] at hball
  exact hball

open Classical in
theorem isCombinatorialSolidTorus_compactFaceTorus_of_cycle
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hKM : K.faces ⊆ M.faces)
    {f : E3 → E3} (hf : IsPLHomeomorphOn f (compactDualNeighborhood M K)
      (f '' compactDualNeighborhood M K)) (s : Section34CompactSimplexIndex K 3) :
    IsCombinatorialSolidTorus (section34CompactFaceTorus
      (section34CompactVertexBallImage (compactDualCutCell M K hKM) f) s) := by
  rw [section34CompactFaceTorus_compactDual_eq M K hKM f s]
  exact isCombinatorialSolidTorus_image_iUnion_graphDualCells M K hM hKM s hf

end DifferentialGeometry.Topology.PiecewiseLinear
