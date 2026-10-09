/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactMarkedCaps
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedBridgePrism
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedPrismCycleBuffer
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRayEmbedding

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "Δ" => Convexity.StdSimplex.coordinateSet ℝ (Fin 3)
local notation "p" => (stdCenter 1 : Fin 3 → ℝ)

theorem exists_marked_graphDualCell_prisms_triangle
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hKM : K.faces ⊆ M.faces)
    (hKint : K.space ⊆ interior M.space) (s : Section34CompactSimplexIndex K 3)
    (v : Fin 3 → E3) (hv : ∀ i, v i ∈ s.1) (hinj : Function.Injective v) :
    let L := restrict K (section34CompactGraphSkeleton K)
    let C := fun i => (graphDualCell M L (v i)).space
    ∃ ρ : Fin 3 → (Fin 3 → ℝ) × ℝ → E3,
      (∀ i, IsPLHomeomorphOn (ρ i) (Δ ×ˢ Icc (0 : ℝ) 1) (C i)) ∧
      (∀ i, ρ i '' (Δ ×ˢ {(0 : ℝ)}) = C (i + 2) ∩ C i) ∧
      (∀ i, ρ i '' (Δ ×ˢ {(1 : ℝ)}) = C i ∩ C (i + 1)) ∧
      (∀ i, ρ i (p, 1) = ρ (i + 1) (p, 0)) ∧
      ∀ i, ρ i '' ({p} ×ˢ Icc (0 : ℝ) 1) = section34CompactSimplexRim s.1 ∩ C i := by
  classical
  let L := restrict K (section34CompactGraphSkeleton K)
  let C := fun i => (graphDualCell M L (v i)).space
  have hvK (i : Fin 3) : {v i} ∈ K.faces := K.down_closed s.2.1
    (Finset.singleton_subset_iff.mpr (hv i)) (Finset.singleton_nonempty _)
  have hvL (i : Fin 3) : {v i} ∈ L.faces :=
    ⟨hvK i, convexHull_subset_section34CompactGraphSkeleton (hvK i) (by simp)⟩
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hcard : ∀ t ∈ L.faces, t.card ≤ 2 :=
    fun _ ht => card_le_two_of_mem_restrict_section34CompactGraphSkeleton ht
  have hC (i : Fin 3) : IsPLBall 3 (C i) :=
    hM.isPLBall_graphDualCell M L hLM hcard (hvL i)
  have hprev (i : Fin 3) : i + 2 ≠ i := by decide +revert
  have hnext (i : Fin 3) : i ≠ i + 1 := by decide +revert
  have hprevnext (i : Fin 3) : i + 2 ≠ i + 1 := by decide +revert
  have hcyc (i : Fin 3) : (i + 2) + 1 = i := by decide +revert
  have hcyc' (i : Fin 3) : (i + 1) + 2 = i := by decide +revert
  obtain ⟨r, hr⟩ := exists_centered_graphDualCell_caps_triangle M K hM hKM hKint s v hv hinj
  have hr0 (i : Fin 3) : IsPLHomeomorphOn (r (i + 2)) Δ (C (i + 2) ∩ C i) := by
    simpa only [hcyc] using (hr (i + 2)).1
  have hr1 (i : Fin 3) : IsPLHomeomorphOn (r i) Δ (C i ∩ C (i + 1)) := (hr i).1
  have hD0 (i : Fin 3) : C (i + 2) ∩ C i ⊆ frontier (C i) := by
    have hd : IsPLBall 2 (C i ∩ C (i + 2)) := by
      rw [inter_comm]
      exact ⟨r (i + 2), hr0 i⟩
    exact fun _ hx => (hC (i + 2)).inter_subset_frontier_of_isPLBall hd (by decide)
      ⟨hx.2, hx.1⟩
  have hD1 (i : Fin 3) : C i ∩ C (i + 1) ⊆ frontier (C i) :=
    (hC (i + 1)).inter_subset_frontier_of_isPLBall ⟨r i, hr1 i⟩ (by decide)
  have hdis (i : Fin 3) : Disjoint (C (i + 2) ∩ C i) (C i ∩ C (i + 1)) := by
    have ht := graphDualCell_triple_inter_eq_empty M L hLM hcard
      (hvL (i + 2)) (hvL i) (hvL (i + 1))
      (fun h => hprev i (hinj h)) (fun h => hprevnext i (hinj h))
      (fun h => hnext i (hinj h))
    exact disjoint_left.mpr fun x hx hy =>
      Set.notMem_empty x (ht ▸ show x ∈ (C (i + 2) ∩ C i) ∩ C (i + 1) from ⟨hx, hy.2⟩)
  have hprism (i : Fin 3) := exists_marked_prism_of_isBridgeDisk (hC i) (hD0 i) (hD1 i)
    (hdis i) (hr0 i) (hr1 i) (hr i).2.2
  choose ρ hρ hρ0 hρ1 hmark0 hmark1 haxis using hprism
  refine ⟨ρ, hρ, hρ0, hρ1, fun i => ?_, haxis⟩
  rw [hmark1, hmark0, hcyc']

theorem exists_compactRimCoreBuffer
    {M K : Geometry.SimplicialComplex ℝ E3} [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hKM : K.faces ⊆ M.faces)
    (hKint : K.space ⊆ interior M.space) (s : Section34CompactSimplexIndex K 3) :
    let L := restrict K (section34CompactGraphSkeleton K)
    let Ns := ⋃ v ∈ (s.1 : Set E3), (graphDualCell M L v).space
    ∃ P : Set E3, P ⊆ interior M.space ∧ Ns ⊆ interior P ∧
      ∃ Φ : (Metric.closedBall (0 : E2) 1 × Metric.sphere (0 : E2) 1) ≃ₜ P,
        section34CompactSimplexRim s.1 =
          Subtype.val '' (Φ '' {q | (q.1 : E2) = 0}) := by
  classical
  let : DecidableEq E3 := Classical.decEq E3
  let L := restrict K (section34CompactGraphSkeleton K)
  let e : Fin 3 ≃ s.1 := (Fintype.equivFinOfCardEq (by simpa using s.2.2)).symm
  let v (i : Fin 3) : E3 := e i
  let C (i : Fin 3) := (graphDualCell M L (v i)).space
  have hv (i : Fin 3) : v i ∈ s.1 := (e i).2
  have hinj : Function.Injective v := fun i j hij => e.injective (Subtype.ext hij)
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hcyc' (i : Fin 3) : (i + 1) + 2 = i := by decide +revert
  obtain ⟨ρ, hρ, hρ0, hρ1, hmark, haxis⟩ :=
    exists_marked_graphDualCell_prisms_triangle M K hM hKM hKint s v hv hinj
  have hmeet (i : Fin 3) : C i ∩ C (i + 1) = ρ i '' (Δ ×ˢ {(1 : ℝ)}) :=
    (hρ1 i).symm
  have hcap (i : Fin 3) : ρ i '' (Δ ×ˢ {(1 : ℝ)}) =
      ρ (i + 1) '' (Δ ×ˢ {(0 : ℝ)}) := by
    rw [hρ1, hρ0, hcyc']
  have hfar (i j : Fin 3) (hij : i ≠ j) (hji : j ≠ i + 1) (hij' : i ≠ j + 1) :
      Disjoint (C i) (C j) := by
    have hc : ∀ i j : Fin 3, i ≠ j → j ≠ i + 1 → i ≠ j + 1 → False := by decide
    exact (hc i j hij hji hij').elim
  have hNint : (derivedNeighborhood M L).space ⊆ interior M.space :=
    derivedNeighborhood_space_subset_interior (A := M) (K := L) (n := 2) (by simp) hM hLM
      ((space_mono_of_faces_subset (restrict_faces_subset K _)).trans hKint)
  obtain ⟨P, hPM, hCP, Φ, hΦ⟩ := exists_thickening_marked_cycle 0 C ρ hρ hmeet hcap hfar
    hmark isOpen_interior (fun i => (graphDualCell_space_subset M L (v i)).trans hNint)
  have heq : (⋃ i : Fin 3, C i) = ⋃ z ∈ (s.1 : Set E3), (graphDualCell M L z).space := by
    apply Subset.antisymm
    · exact iUnion_subset fun i => subset_iUnion₂_of_subset (v i) (hv i) subset_rfl
    · refine iUnion₂_subset fun z hz => ?_
      obtain ⟨i, hi⟩ := e.surjective ⟨z, hz⟩
      have hiz : v i = z := congrArg Subtype.val hi
      exact subset_iUnion_of_subset i (by rw [← hiz])
  have hrim : section34CompactSimplexRim s.1 ⊆ ⋃ i, C i := by
    rw [heq]
    exact section34CompactSimplexRim_subset_iUnion_graphDualCells M K hKM s
  have haxes : (⋃ i, ρ i '' ({p} ×ˢ Icc (0 : ℝ) 1)) =
      section34CompactSimplexRim s.1 := by
    simp_rw [haxis]
    rw [← inter_iUnion, inter_eq_left.mpr hrim]
  exact ⟨P, hPM, heq ▸ hCP, Φ, haxes.symm.trans hΦ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
