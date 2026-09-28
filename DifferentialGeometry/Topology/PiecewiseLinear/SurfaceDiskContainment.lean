/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FourArcSphere
import DifferentialGeometry.Topology.PiecewiseLinear.SphereSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SphereCircleCapSplit

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_disk_subset_of_circle_subset_disk {S D₀ J : Set E}
    (hS : IsPLSphere 2 S) (hD₀ : IsPLBall 2 D₀) (hD₀S : D₀ ⊆ S)
    (hJ : IsPLSphere 1 J) (hJD₀ : J ⊆ D₀) :
    ∃ (D : Set E) (q : (Fin 3 → ℝ) → E), IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ D₀ ∧ q '' stdSimplexBoundary 2 = J := by
  have hY := hS.isConnected_sdiff_of_isPLBall_two hD₀ hD₀S
  have hYJ : Disjoint (S \ D₀) J := Set.disjoint_left.mpr fun x hx hxJ => hx.2 (hJD₀ hxJ)
  obtain ⟨D, q, hq, hDS, hYD, hqJ⟩ :=
    hS.exists_isPLBall_with_boundary_disjoint_of_isPreconnected hY.isPreconnected sdiff_subset
      hJ (hJD₀.trans hD₀S) hYJ
  refine ⟨D, q, hq, ?_, hqJ⟩
  intro x hx
  by_contra hx₀
  exact Set.disjoint_left.mp hYD ⟨hDS hx, hx₀⟩ hx

theorem IsPLSphere.disk_inter_boundary_subset_boundary {S D D₀ : Set E}
    (hS : IsPLSphere 2 S) {q q₀ : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀) (hDD₀ : D ⊆ D₀) (hD₀S : D₀ ⊆ S) :
    D ∩ (q₀ '' stdSimplexBoundary 2) ⊆ q '' stdSimplexBoundary 2 := by
  have hJ₀ := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq₀ hD₀S
  have hJ := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq (hDD₀.trans hD₀S)
  rintro x ⟨hxD, hxJ₀⟩
  have hxcl := (hJ₀.symm.subset hxJ₀).2
  have hdiff : S \ D₀ ⊆ S \ D := fun y hy => ⟨hy.1, fun hyD => hy.2 (hDD₀ hyD)⟩
  exact hJ.subset ⟨hxD, closure_mono hdiff hxcl⟩

theorem IsPLSphere.exists_disk_between_proper_arc_and_boundary_arc {S D₀ A B : Set E}
    (hS : IsPLSphere 2 S) {q₀ : (Fin 3 → ℝ) → E}
    (hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀) (hD₀S : D₀ ⊆ S)
    {γ δ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) B) (hδ0 : δ 0 = γ 0) (hδ1 : δ 1 = γ 1)
    (hAD₀ : A ⊆ D₀) (hBJ₀ : B ⊆ q₀ '' stdSimplexBoundary 2)
    (hAJ₀ : A ∩ (q₀ '' stdSimplexBoundary 2) = {γ 0, γ 1}) :
    ∃ (D : Set E) (q : (Fin 3 → ℝ) → E), IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ D₀ ∧ q '' stdSimplexBoundary 2 = A ∪ B ∧ D ∩ (q₀ '' stdSimplexBoundary 2) = B := by
  have hendsB : ({γ 0, γ 1} : Set E) ⊆ B := by
    rw [← hδ0, ← hδ1]
    exact pair_subset (hδ.bijOn.mapsTo (by norm_num)) (hδ.bijOn.mapsTo (by norm_num))
  have hAB : A ∩ B = {γ 0, γ 1} := Subset.antisymm
    (fun x hx => hAJ₀.subset ⟨hx.1, hBJ₀ hx.2⟩)
    (fun x hx => ⟨(pair_subset (hγ.bijOn.mapsTo (by norm_num))
      (hγ.bijOn.mapsTo (by norm_num))) hx, hendsB hx⟩)
  have hJ : IsPLSphere 1 (A ∪ B) :=
    isPLSphere_one_union_of_isPLHomeomorphOn_Icc hγ hδ hδ0 hδ1 hAB
  have hJ₀D₀ : q₀ '' stdSimplexBoundary 2 ⊆ D₀ := by
    rw [← hq₀.image_eq]
    exact image_mono fun x hx => hx.1
  let Q := closure (S \ D₀)
  have hD₀ : IsPLBall 2 D₀ := ⟨q₀, hq₀⟩
  have hQS : Q ⊆ S := closure_minimal sdiff_subset hS.isPolyhedron.isClosed
  obtain ⟨r, hr⟩ : IsPLBall 2 Q := hS.isPLBall_closure_sdiff hD₀ hD₀S
  have hD₀Q : D₀ ∩ Q = q₀ '' stdSimplexBoundary 2 :=
    hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq₀ hD₀S
  have hrJ : r '' stdSimplexBoundary 2 = q₀ '' stdSimplexBoundary 2 :=
    (hS.image_stdSimplexBoundary_complement hD₀ hD₀S hr).trans
      ((inter_comm Q D₀).trans hD₀Q)
  have hX : IsPreconnected (Q \ B) :=
    (hr.isPreconnected_sdiff_of_subset_boundary (hBJ₀.trans hrJ.symm.subset)).1
  have hXJ : Disjoint (Q \ B) (A ∪ B) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨hxQ, hxB⟩ (hxA | hxB')
    · exact hxB (hendsB (hAJ₀.subset ⟨hxA, hD₀Q.subset ⟨hAD₀ hxA, hxQ⟩⟩))
    · exact hxB hxB'
  obtain ⟨D, q, hq, hDS, hXD, hqJ⟩ :=
    hS.exists_isPLBall_with_boundary_disjoint_of_isPreconnected hX (sdiff_subset.trans hQS)
      hJ ((union_subset hAD₀ (hBJ₀.trans hJ₀D₀)).trans hD₀S) hXJ
  have hDD₀ : D ⊆ D₀ := by
    intro x hx
    by_contra hx₀
    exact Set.disjoint_left.mp hXD
      ⟨subset_closure ⟨hDS hx, hx₀⟩, fun hxB => hx₀ (hJ₀D₀ (hBJ₀ hxB))⟩ hx
  refine ⟨D, q, hq, hDD₀, hqJ, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxD, hxJ₀⟩
    by_contra hxB
    exact Set.disjoint_left.mp hXD ⟨(hD₀Q.symm.subset hxJ₀).2, hxB⟩ hxD
  · intro x hxB
    obtain ⟨a, ha, hax⟩ := hqJ.symm.subset (Or.inr hxB)
    exact ⟨hax ▸ hq.bijOn.mapsTo ha.1, hBJ₀ hxB⟩

end DifferentialGeometry.Topology.PiecewiseLinear
