/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem dist_le_two_mul_of_forall_mem_Icc {c y : E3} {r : ℝ} (hr : 0 ≤ r)
    (hy : ∀ i, y i ∈ Icc (c i - r) (c i + r)) : dist y c ≤ 2 * r := by
  rw [EuclideanSpace.dist_eq]
  have hi : ∀ i, dist (y i) (c i) ^ 2 ≤ r ^ 2 := fun i => by
    rw [Real.dist_eq, sq_abs]
    exact sq_le_sq' (by linarith [(hy i).1]) (by linarith [(hy i).2])
  have hsum : ∑ i, dist (y i) (c i) ^ 2 ≤ (2 * r) ^ 2 := by
    calc ∑ i, dist (y i) (c i) ^ 2 ≤ ∑ _i : Fin 3, r ^ 2 := Finset.sum_le_sum fun i _ => hi i
      _ = 3 * r ^ 2 := by simp
      _ ≤ (2 * r) ^ 2 := by nlinarith
  calc √(∑ i, dist (y i) (c i) ^ 2) ≤ √((2 * r) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 2 * r := Real.sqrt_sq (by linarith)

theorem exists_isPLCellOn_frontier_subset_interior_of_diam_lt {S : Set E3}
    (hS : Bornology.IsBounded S) {ε : ℝ} (hε : 0 < ε) (hdiam : Metric.diam S < ε / 4) :
    ∃ H : Set E3, IsPLCellOn 3 H (frontier H) ∧ S ⊆ interior H ∧
      ∀ y ∈ H, ∀ z ∈ H, dist y z < ε := by
  obtain ⟨c, r, hr, hrε, hSc⟩ : ∃ (c : E3) (r : ℝ), 0 < r ∧ r < ε / 4 ∧
      S ⊆ Metric.ball c r := by
    rcases S.eq_empty_or_nonempty with hSe | ⟨c, hc⟩
    · exact ⟨0, ε / 8, by positivity, by linarith, by rw [hSe]; exact empty_subset _⟩
    · have hd := Metric.diam_nonneg (s := S)
      refine ⟨c, (Metric.diam S + ε / 4) / 2, by linarith, by linarith, fun x hx => ?_⟩
      rw [Metric.mem_ball]
      calc dist x c ≤ Metric.diam S := Metric.dist_le_diam_of_mem hS hx hc
        _ < (Metric.diam S + ε / 4) / 2 := by linarith
  set H : Set E3 := ⋂ i : Fin 3, euclideanCoord i ⁻¹' Icc (c i - r) (c i + r) with hHdef
  have hmem : ∀ y : E3, y ∈ H ↔ ∀ i, y i ∈ Icc (c i - r) (c i + r) := by
    intro y
    simp only [hHdef, mem_iInter, mem_preimage, euclideanCoord_apply]
  have hball : Metric.ball c r ⊆ H := by
    intro y hy
    rw [hmem]
    intro i
    have h1 := (PiLp.dist_apply_le y c i).trans_lt (Metric.mem_ball.mp hy)
    rw [Real.dist_eq, abs_lt] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hclosed : IsClosed H := isClosed_iInter fun i =>
    isClosed_Icc.preimage (euclideanCoord i).continuous_of_finiteDimensional
  have hbdd : Bornology.IsBounded H := by
    refine (Metric.isBounded_closedBall (x := c) (r := 2 * r)).subset fun y hy => ?_
    exact Metric.mem_closedBall.mpr (dist_le_two_mul_of_forall_mem_Icc hr.le ((hmem y).mp hy))
  have hcpt : IsCompact H := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hpoly : IsHPolytope H := isHPolytope_of_coordBox hcpt (fun i => c i - r)
    (fun i => c i + r) (by ext y; exact hmem y)
  have hint : Metric.ball c r ⊆ interior H := interior_maximal hball Metric.isOpen_ball
  have hball3 : IsPLBall 3 H := by
    have h := hpoly.isPLBall ⟨c, hint (Metric.mem_ball_self hr)⟩
    rwa [finrank_euclideanSpace_fin] at h
  refine ⟨H, hball3.isPLCellOn_frontier, hSc.trans hint, fun y hy z hz => ?_⟩
  have h1 := dist_le_two_mul_of_forall_mem_Icc hr.le ((hmem y).mp hy)
  have h2 := dist_le_two_mul_of_forall_mem_Icc hr.le ((hmem z).mp hz)
  calc dist y z ≤ dist y c + dist z c := dist_triangle_right y z c
    _ < ε := by linarith

theorem exists_section34CompactCarrierControl (K : Geometry.SimplicialComplex ℝ E3)
    {h : E3 → E3} {ε : ℝ} (hε : 0 < ε) {X : Finset E3 → Set E3}
    (hX : ∀ t ∈ K.faces, h '' section34CompactCarrierSupport K t ⊆ X t)
    (hXb : ∀ t ∈ K.faces, Bornology.IsBounded (X t))
    (hXd : ∀ t ∈ K.faces, Metric.diam (X t) < ε / 4) :
    ∃ H : Finset E3 → Set E3, Section34CompactCarrierControl K h ε H ∧
      ∀ t ∈ K.faces, X t ⊆ interior (H t) := by
  have hex : ∀ t : Finset E3, ∃ Ht : Set E3, t ∈ K.faces →
      IsPLCellOn 3 Ht (frontier Ht) ∧ X t ⊆ interior Ht ∧ ∀ y ∈ Ht, ∀ z ∈ Ht, dist y z < ε := by
    intro t
    by_cases ht : t ∈ K.faces
    · obtain ⟨Ht, hHt⟩ := exists_isPLCellOn_frontier_subset_interior_of_diam_lt (hXb t ht) hε
        (hXd t ht)
      exact ⟨Ht, fun _ => hHt⟩
    · exact ⟨∅, fun h' => absurd h' ht⟩
  choose H hH using hex
  exact ⟨H, ⟨fun t ht => (hX t ht).trans (hH t ht).2.1, fun t ht => (hH t ht).2.2,
    fun t ht => (hH t ht).1⟩, fun t ht => (hH t ht).2.1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
