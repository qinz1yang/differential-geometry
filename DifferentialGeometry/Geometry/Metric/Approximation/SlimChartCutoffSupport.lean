import DifferentialGeometry.Analysis.Calculus.Cutoff.IntervalProfiles
import DifferentialGeometry.Geometry.Metric.Approximation.ProductCollapse

set_option autoImplicit false
open Set Metric DifferentialGeometry.Analysis

namespace GC.MetricGeometry

variable {X Z : Type*} [MetricSpace X] [MetricSpace Z]

theorem tsupport_slim_chart_cutoff_subset {p : X} {Δ : ℝ} (hΔ : 0 < Δ) (z₀ : Z)
    (φ : ball p (1000000 * Δ) → WithLp 2 (ℝ × Z)) (η : ball p (1000000 * Δ) → ℝ)
    (hbase : φ ⟨p, mem_ball_self (by positivity)⟩ = WithLp.toLp 2 (0, z₀))
    (hdist : ∀ x y, |dist (φ x) (φ y) - dist x.val y.val| ≤ Δ)
    (hfactor : ∀ z : Z, dist z z₀ ≤ 1000 * Δ)
    (hvalue : ∀ x, |η x - (φ x).fst| ≤ Δ) :
    let ζ := (Subtype.val : ball p (1000000 * Δ) → X).extend
      (fun x => intervalPlateauProfile (-900000) (-800000) 800000 900000 (η x / Δ)) 0
    tsupport ζ ⊆ closedBall p (901002 * Δ) ∧ closedBall p (901002 * Δ) ⊆ ball p (950000 * Δ) := by
  let F : ball p (1000000 * Δ) → ℝ :=
    fun x => intervalPlateauProfile (-900000) (-800000) 800000 900000 (η x / Δ)
  refine ⟨?_, closedBall_subset_ball (by linarith)⟩
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Function.support_extend_zero_subset hx
  have hηlo : -900000 < η y / Δ := by
    by_contra! hh
    exact hy (intervalPlateauProfile_zero_left (by norm_num) hh)
  have hηhi : η y / Δ < 900000 := by
    by_contra! hh
    exact hy (intervalPlateauProfile_zero_right (by norm_num) hh)
  have hηlo' := (lt_div_iff₀ hΔ).mp hηlo
  have hηhi' := (div_lt_iff₀ hΔ).mp hηhi
  have herr := abs_le.mp (hvalue y)
  have hu : |(φ y).fst| ≤ 900001 * Δ := abs_le.mpr ⟨by linarith, by linarith⟩
  have hprod := (abs_le.mp (WithLp.prod_dist_sub_dist_fst_le (φ y) (WithLp.toLp 2 (0, z₀)))).2
  change dist (φ y) (WithLp.toLp 2 (0, z₀)) - dist (φ y).fst 0 ≤ dist (φ y).snd z₀ at hprod
  rw [Real.dist_eq, sub_zero] at hprod
  have hd := (abs_le.mp (hdist y ⟨p, mem_ball_self (by positivity)⟩)).1
  rw [hbase] at hd
  change dist y.val p ≤ 901002 * Δ
  linarith [hfactor (φ y).snd]

end GC.MetricGeometry
