/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.Frontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.SphereInnermostDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPseudoCell.exists_disk_on_frontier_of_crosses
    {Ec Eint Ebd Bl : Set E3} {P : E3} (hE : IsPseudoCell Ec Eint Ebd P)
    (hBl : IsPLBall 3 Bl) (hP : P ∈ interior Bl) (hBE : Bl ∩ Ec ⊆ Eint)
    (hgp : CrossesPseudoCell (frontier Bl) Ec Eint P) :
    ∃ (Δ : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
      Δ ⊆ frontier Bl ∧ r '' stdSimplexBoundary 2 = Δ ∩ Ec := by
  classical
  have hEint : Eint ⊆ Ec := by
    rw [hE.carrierEq]
    exact subset_union_left
  have hEbd : Ebd ⊆ Ec := by
    rw [hE.carrierEq]
    exact subset_union_right
  have hconn : IsPreconnected Ec := by
    obtain ⟨ψ⟩ := hE.isOpenCell
    have : PreconnectedSpace (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      isPreconnected_iff_preconnectedSpace.mp (convex_ball 0 1).isPreconnected
    have hr := isPreconnected_range (continuous_subtype_val.comp ψ.symm.continuous)
    rw [range_comp, ψ.symm.surjective.range_eq, image_univ, Subtype.range_coe] at hr
    simpa only [hE.closureEq, ← hE.carrierEq] using hr.closure
  have htrace : (frontier Bl ∩ Ec).Nonempty := by
    by_contra hnone
    have hdisj : Disjoint Ec (frontier Bl) := Set.disjoint_left.mpr fun x hxE hxB =>
      hnone ⟨x, hxB, hxE⟩
    have hsub :=
      DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
        hconn hdisj ⟨P, hEint hE.centerMem, hP⟩
    obtain ⟨ψ⟩ := hE.isSphere
    obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty
      (x := (0 : EuclideanSpace ℝ (Fin 2))) (r := 1)).mpr zero_le_one
    let y : Ebd := ψ.symm ⟨v, hv⟩
    exact Set.disjoint_left.mp hE.disjointRim
      (hBE ⟨interior_subset (hsub (hEbd y.2)), hEbd y.2⟩) y.2
  obtain ⟨n, G, hG, hdisj, htraceEq, -, -⟩ := hgp
  have : Nonempty (Fin n) := by
    obtain ⟨x, hx⟩ := htrace
    rw [htraceEq] at hx
    obtain ⟨i, -⟩ := mem_iUnion.mp hx
    exact ⟨i⟩
  have hGsub : ∀ i, G i ⊆ frontier Bl := by
    intro i x hx
    have hmem : x ∈ frontier Bl ∩ Ec := by
      rw [htraceEq]
      exact mem_iUnion.mpr ⟨i, hx⟩
    exact hmem.1
  obtain ⟨i, Δ, r, hr, hΔ, hrim, hother⟩ :=
    hBl.isPLSphere_frontier.exists_innermost_disk hG hGsub hdisj
  refine ⟨Δ, r, hr, hΔ, hrim.trans ?_⟩
  apply Subset.antisymm
  · intro x hx
    have hxΔ : x ∈ Δ := by
      rw [← hrim] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      exact hr.bijOn.mapsTo hq.1
    have hxtrace : x ∈ frontier Bl ∩ Ec := by
      rw [htraceEq]
      exact mem_iUnion.mpr ⟨i, hx⟩
    exact ⟨hxΔ, hxtrace.2⟩
  · rintro x ⟨hxΔ, hxE⟩
    have hxtrace : x ∈ ⋃ j, G j := by
      rw [← htraceEq]
      exact ⟨hΔ hxΔ, hxE⟩
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxtrace
    by_cases hji : j = i
    · simpa only [hji] using hxj
    · exact (Set.disjoint_left.mp (hother j hji) hxΔ hxj).elim

end DifferentialGeometry.Topology.PiecewiseLinear
