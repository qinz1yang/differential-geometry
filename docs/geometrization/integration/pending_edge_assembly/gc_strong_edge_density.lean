import DifferentialGeometry.Geometry.Metric.Approximation.StrongEdgeLifts

set_option autoImplicit false
open Set Metric
namespace GC.MetricGeometry

private theorem dist_lt_scale_of_endpoint_radius {X : Type*} [MetricSpace X]
    {p a : X} {Δ e s h : ℝ} {Λ : NNReal} {ρ : X → ℝ}
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1) (hΔ : 1 ≤ Δ)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ))
    (he : e ≤ s / 1000) (hs : s < 1 / 100) (hh : h ≤ Δ / 2)
    (ha : dist a p < h + 3 * e) : dist a p < Δ * ρ a := by
  have hΔpos : 0 < Δ := by linarith
  have hrad : dist a p < 51 / 100 * Δ := by linarith only [ha, hh, he, hs, hΔ]
  have hΛΔ : (Λ : ℝ) * (1000000 * Δ) < 1 := (lt_div_iff₀ (by positivity)).mp hscale
  have hrho : |ρ a - 1| ≤ (Λ : ℝ) * Δ := by
    have hd := hρ.dist_le_mul a p
    rw [Real.dist_eq, hρp] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (by linarith only [hrad, hΔ] : dist a p ≤ Δ) Λ.coe_nonneg)
  have hlower : 99 / 100 < ρ a := by nlinarith only [hΛΔ, (abs_le.mp hrho).1]
  nlinarith only [hrad, hΔpos, mul_lt_mul_of_pos_left hlower hΔpos]

universe u v
variable {X : Type u} {Y : Type v} [mX : MetricSpace X] [MetricSpace Y]
variable {p : X} {q : Y} {Δ β βE s η e θ : ℝ} {Λ : NNReal} {ρ : X → ℝ}

theorem exists_strong_edge_near_interval_model {C : ℝ} {o : Icc (0 : ℝ) C}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β)
    (G : KleinerLottApprox q o η)
    (H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), o)) e)
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) (hρp : ρ p = 1)
    (hΔ : 1 ≤ Δ) (hC : 500 * Δ < C) (hβE : βE < 1 / 100)
    (hβsmall : β < βE / 100) (hβdomain : β < 1 / (100 * Δ + 100 / βE))
    (hs : 0 < s) (hssmall : s < 1 / 100)
    (hηs : η ≤ s / 1000) (hηΔ : η ≤ 1 / (100000 * Δ))
    (he : e ≤ s / 1000) (heΔ : e ≤ 1 / (1000 * Δ)) (hθ : θ ≤ s / 1000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ)) (ho : o.val ≤ Δ / 2)
    (hcompat : ∀ x ∈ ball p (1000 * Δ),
      dist (G.toFun (F.toFun x).snd) (H.toFun x).snd < θ) :
    ∃ a : X, (@isEdgePoint.{u, v} X
      (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧ dist a p < Δ * ρ a := by
  obtain ⟨a, hrad, hed, _⟩ := exists_strong_edge_interval_lift F G H hρ hρpos hρp
    hΔ hC hβE hβsmall hβdomain hs hssmall hηs hηΔ he heΔ hθ hscale ho hcompat
    0 (by simp only [abs_zero]; positivity)
  refine ⟨a, hed, ?_⟩
  apply dist_lt_scale_of_endpoint_radius hρ hρp hΔ hscale he hssmall ho
  simpa only [abs_zero, zero_add] using hrad

theorem exists_strong_edge_near_ray_model {o : Ici (0 : ℝ)}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β)
    (G : KleinerLottApprox q o η)
    (H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), o)) e)
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) (hρp : ρ p = 1)
    (hΔ : 1 ≤ Δ) (hβE : βE < 1 / 100)
    (hβsmall : β < βE / 100) (hβdomain : β < 1 / (100 * Δ + 100 / βE))
    (hs : 0 < s) (hssmall : s < 1 / 100)
    (hηs : η ≤ s / 1000) (hηΔ : η ≤ 1 / (100000 * Δ))
    (he : e ≤ s / 1000) (heΔ : e ≤ 1 / (1000 * Δ)) (hθ : θ ≤ s / 1000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ)) (ho : o.val ≤ Δ / 2)
    (hcompat : ∀ x ∈ ball p (1000 * Δ),
      dist (G.toFun (F.toFun x).snd) (H.toFun x).snd < θ) :
    ∃ a : X, (@isEdgePoint.{u, v} X
      (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧ dist a p < Δ * ρ a := by
  obtain ⟨a, hrad, hed, _⟩ := exists_strong_edge_ray_lift F G H hρ hρpos hρp
    hΔ hβE hβsmall hβdomain hs hssmall hηs hηΔ he heΔ hθ hscale ho hcompat
    0 (by simp only [abs_zero]; positivity)
  refine ⟨a, hed, ?_⟩
  apply dist_lt_scale_of_endpoint_radius hρ hρp hΔ hscale he hssmall ho
  simpa only [abs_zero, zero_add] using hrad

end GC.MetricGeometry
