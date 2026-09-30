import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y]
variable [TopologicalSpace Z] [CompactSpace Z]

theorem exists_onto_ball_map_of_compact_parameters
    (Γ : Z → X) (q : Z → Y) (hΓ : Continuous Γ) (z₀ : Z)
    {S β ω : ℝ}
    (hradial : ∀ z, dist (Γ z) (Γ z₀) = dist (q z) (q z₀))
    (hparameters : ∀ z, q z ∈ closedBall (q z₀) S)
    (honto : ∀ y ∈ closedBall (q z₀) S, ∃ z, q z = y)
    (hcontraction : ∀ z w, dist (q z) (q w) ≤ dist (Γ z) (Γ w))
    (herror : ∀ z w, dist (Γ z) (Γ w) - dist (q z) (q w) ≤ ω)
    (hdensity : ∀ x ∈ closedBall (Γ z₀) S, infDist x (range Γ) ≤ β) :
    ∃ f : X → Y, f (Γ z₀) = q z₀ ∧ (∀ z, f (Γ z) = q z) ∧
      (∀ x, f x ∈ closedBall (q z₀) S) ∧
      (∀ x ∈ closedBall (Γ z₀) S, ∀ y ∈ closedBall (Γ z₀) S,
        |dist (f x) (f y) - dist x y| ≤ 2 * β + ω) ∧
      ∀ y ∈ closedBall (q z₀) S, ∃ x ∈ closedBall (Γ z₀) S,
        f x = y ∧ dist x (Γ z₀) = dist y (q z₀) := by
  classical
  have hmin (x : X) : ∃ z, infDist x (range Γ) = dist x (Γ z) := by
    obtain ⟨v, ⟨z, rfl⟩, hz⟩ := (isCompact_range hΓ).exists_infDist_eq_dist ⟨Γ z₀, z₀, rfl⟩ x
    exact ⟨z, hz⟩
  choose sel hsel using hmin
  have hfix (z : Z) : q (sel (Γ z)) = q z := by
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    have hm : infDist (Γ z) (range Γ) = 0 := infDist_zero_of_mem (mem_range_self z)
    have hd : dist (Γ (sel (Γ z))) (Γ z) = 0 := by
      rw [dist_comm, ← hsel, hm]
    simpa only [hd] using hcontraction (sel (Γ z)) z
  refine ⟨fun x => q (sel x), hfix z₀, hfix, fun x => hparameters (sel x), ?_, ?_⟩
  · intro x hx y hy
    have hdx : dist x (Γ (sel x)) ≤ β := by rw [← hsel]; exact hdensity x hx
    have hdy : dist y (Γ (sel y)) ≤ β := by rw [← hsel]; exact hdensity y hy
    have hp := dist_dist_dist_le x y (Γ (sel x)) (Γ (sel y))
    rw [Real.dist_eq] at hp
    have htarget : |dist (q (sel x)) (q (sel y)) - dist (Γ (sel x)) (Γ (sel y))| ≤ ω := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hcontraction _ _)), neg_sub]
      exact herror _ _
    have hsum := abs_add_le (dist (q (sel x)) (q (sel y)) - dist (Γ (sel x)) (Γ (sel y)))
      (dist (Γ (sel x)) (Γ (sel y)) - dist x y)
    rw [sub_add_sub_cancel, abs_sub_comm (dist (Γ (sel x)) (Γ (sel y))) (dist x y)] at hsum
    linarith
  · intro y hy
    obtain ⟨z, rfl⟩ := honto y hy
    exact ⟨Γ z, by simpa only [mem_closedBall, hradial] using hy, hfix z, hradial z⟩

theorem exists_kleinerLott_approx_of_compact_parameters
    (Γ : Z → X) (q : Z → Y) (hΓ : Continuous Γ) (z₀ : Z)
    {δ β ω : ℝ} (hδ : 0 < δ) (hδone : δ < 1) (hbudget : 2 * β + ω ≤ δ)
    (hradial : ∀ z, dist (Γ z) (Γ z₀) = dist (q z) (q z₀))
    (hparameters : ∀ z, q z ∈ closedBall (q z₀) δ⁻¹)
    (honto : ∀ y ∈ closedBall (q z₀) δ⁻¹, ∃ z, q z = y)
    (hcontraction : ∀ z w, dist (q z) (q w) ≤ dist (Γ z) (Γ w))
    (herror : ∀ z w, dist (Γ z) (Γ w) - dist (q z) (q w) ≤ ω)
    (hdensity : ∀ x ∈ closedBall (Γ z₀) δ⁻¹, infDist x (range Γ) ≤ β) :
    ∃ f : KleinerLottApprox (Γ z₀) (q z₀) δ, (∀ z, f.toFun (Γ z) = q z) ∧
      (∀ x, f.toFun x ∈ closedBall (q z₀) δ⁻¹) ∧
      ∀ y ∈ closedBall (q z₀) δ⁻¹, ∃ x ∈ closedBall (Γ z₀) δ⁻¹,
        f.toFun x = y ∧ dist x (Γ z₀) = dist y (q z₀) := by
  obtain ⟨f, hbase, hfix, himage, hdist, hsurj⟩ := exists_onto_ball_map_of_compact_parameters
    Γ q hΓ z₀ hradial hparameters honto hcontraction herror hdensity
  refine ⟨⟨hδ, hδone, f, hbase, ?_, ?_⟩, hfix, himage, hsurj⟩
  · intro x hx y hy
    exact (hdist x (mem_closedBall.mpr (mem_ball.mp hx).le)
      y (mem_closedBall.mpr (mem_ball.mp hy).le)).trans hbudget
  · intro y hy
    obtain ⟨x, _, hxy, hr⟩ := hsurj y (by change dist y (q z₀) ≤ δ⁻¹; linarith)
    have hx : x ∈ ball (Γ z₀) δ⁻¹ := by rw [mem_ball, hr]; linarith
    have hm : y ∈ f '' ball (Γ z₀) δ⁻¹ := ⟨x, hx, hxy⟩
    rw [infDist_zero_of_mem hm]
    exact hδ.le

end GC.MetricGeometry
