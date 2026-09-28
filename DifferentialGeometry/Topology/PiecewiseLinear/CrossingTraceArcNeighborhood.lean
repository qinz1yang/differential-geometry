/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingTraceCircles
import DifferentialGeometry.Topology.PiecewiseLinear.PLSphereLocallyPlanar
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDeletion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_arc_neighborhood_of_finite_circle_union
    {ι : Type*} [Finite ι] (C : ι → Set E) (hC : ∀ i, IsPLSphere 1 (C i))
    (hdis : Pairwise fun i j => Disjoint (C i) (C j))
    {D F U : Set E} (hF : IsPLBall 1 F) (hDF : D ∩ (⋃ i, C i) = F)
    (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (A : Set E) (q : (Fin 2 → ℝ) → E) (O : Set E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) A ∧ A ⊆ (⋃ i, C i) ∩ U ∧
      D ∩ A = F ∧ Disjoint D (q '' stdSimplexBoundary 1) ∧
      IsOpen O ∧ D ⊆ O ∧ O ⊆ U ∧ O ∩ (⋃ i, C i) = O ∩ A := by
  classical
  have hFD : F ⊆ D := fun x hx => (hDF.symm ▸ hx).1
  have hFC : F ⊆ ⋃ i, C i := fun x hx => (hDF.symm ▸ hx).2
  obtain ⟨i, hFi⟩ := subset_of_isPreconnected_of_iUnion_isClosed
    (fun i => (hC i).isPolyhedron.isClosed) hdis hF.isConnected.isPreconnected hF.nonempty hFC
  obtain ⟨A, q, hq, hAi, hFA, hnhds, hends⟩ :=
    (hC i).exists_isPLBall_one_neighborhood hF hFi hU (hFD.trans hDU)
  have hAC : A ⊆ ⋃ j, C j := hAi.trans (inter_subset_left.trans (subset_iUnion C i))
  obtain ⟨V, hV, hFV, hVA⟩ := mem_nhdsSetWithin.mp hnhds
  let R := ⋃ j ∈ {j : ι | j ≠ i}, C j
  have hR : IsClosed R := (Set.toFinite {j : ι | j ≠ i}).isClosed_biUnion
    (fun j _ => (hC j).isPolyhedron.isClosed)
  let W := V \ R
  have hW : IsOpen W := hV.sdiff hR
  have hFW : F ⊆ W := by
    intro x hx
    refine ⟨hFV hx, ?_⟩
    intro hxR
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxR
    exact disjoint_left.mp (hdis hj) hxj (hFi hx)
  have hWA : W ∩ (⋃ j, C j) ⊆ A := by
    rintro x ⟨hxW, hxC⟩
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxC
    by_cases hji : j = i
    · exact hVA ⟨hxW.1, hji ▸ hxj⟩
    · exact (hxW.2 (mem_iUnion₂.mpr ⟨j, hji, hxj⟩)).elim
  have hclW : closure ((⋃ j, C j) \ A) ⊆ Wᶜ :=
    closure_minimal (fun x hx hxW => hx.2 (hWA ⟨hxW, hx.1⟩)) hW.isClosed_compl
  have hclC : closure ((⋃ j, C j) \ A) ⊆ ⋃ j, C j :=
    closure_minimal sdiff_subset (isClosed_iUnion_of_finite fun j => (hC j).isPolyhedron.isClosed)
  have hDcl : Disjoint D (closure ((⋃ j, C j) \ A)) := by
    refine disjoint_left.mpr fun x hxD hxcl => ?_
    have hxF : x ∈ F := hDF ▸ ⟨hxD, hclC hxcl⟩
    exact hclW hxcl (hFW hxF)
  let O := U \ closure ((⋃ j, C j) \ A)
  refine ⟨A, q, O, hq, fun x hx => ⟨hAC hx, (hAi hx).2⟩, ?_, ?_,
    hU.sdiff isClosed_closure, ?_, fun x hx => hx.1, ?_⟩
  · exact subset_antisymm (fun x hx => hDF ▸ ⟨hx.1, hAC hx.2⟩)
      (fun x hx => ⟨hFD hx, hFA hx⟩)
  · refine disjoint_left.mpr fun x hxD hxend => ?_
    have hxA : x ∈ A := by
      obtain ⟨z, hz, rfl⟩ := hxend
      exact hq.bijOn.mapsTo hz.1
    exact disjoint_left.mp hends (hDF ▸ ⟨hxD, hAC hxA⟩) hxend
  · exact fun x hx => ⟨hDU hx, fun h => disjoint_left.mp hDcl hx h⟩
  · ext x
    constructor
    · rintro ⟨hxO, hxC⟩
      exact ⟨hxO, by_contra fun hxA => hxO.2 (subset_closure ⟨hxC, hxA⟩)⟩
    · exact fun hx => ⟨hx.1, hAC hx.2⟩

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLSphere.exists_arc_neighborhood_of_crossing_trace {S X D F U : Set E3}
    (hS : IsPLSphere 2 S) (hX : IsPolyhedron X) (hreg : X ⊆ closure (interior X))
    (hcross : ∀ x ∈ S ∩ frontier X, HasPLCrossingAt S (frontier X) x)
    (hF : IsPLBall 1 F) (hDF : D ∩ (S ∩ frontier X) = F)
    (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (A : Set E3) (q : (Fin 2 → ℝ) → E3) (O : Set E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) A ∧ A ⊆ (S ∩ frontier X) ∩ U ∧
      D ∩ A = F ∧ Disjoint D (q '' stdSimplexBoundary 1) ∧
      IsOpen O ∧ D ⊆ O ∧ O ⊆ U ∧ O ∩ (S ∩ frontier X) = O ∩ A := by
  obtain ⟨ι, hι, C, hC, hdis, heq⟩ := exists_iUnion_isPLSphere_one_of_forall_lineChart
    (hS.isPolyhedron.inter hX.frontier) hcross (fun x hx =>
      (hcross x hx).exists_lineChart hx.1 (hS.exists_isOpen_inter_homeomorph_of_two hx.1)
        hX.isClosed (hreg (hX.isClosed.frontier_subset hx.2)))
  let _ : Finite ι := hι
  rw [heq] at hDF ⊢
  exact exists_arc_neighborhood_of_finite_circle_union C hC hdis hF hDF hU hDU

end DifferentialGeometry.Topology.PiecewiseLinear
