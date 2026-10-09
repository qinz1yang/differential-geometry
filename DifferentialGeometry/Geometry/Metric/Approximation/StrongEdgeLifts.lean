import DifferentialGeometry.Geometry.Metric.Approximation.StrongEdgePoint
import DifferentialGeometry.Geometry.Metric.Approximation.EndpointProductLifts
import DifferentialGeometry.Geometry.Metric.Scaling.LipschitzScale

set_option autoImplicit false
open Set Metric
namespace GC.MetricGeometry

private theorem exists_endpoint_lift_data {X : Type*} [MetricSpace X]
    {p : X} {S : Set ℝ} {o : S} {Δ e θ : ℝ} {Λ : NNReal} {ρ : X → ℝ}
    (H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), o)) e)
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) (hρp : ρ p = 1)
    (hΔ : 1 ≤ Δ) (hscale : (Λ : ℝ) < 1 / (1000000 * Δ))
    (heΔ : e ≤ 1 / (1000 * Δ)) (V : X → S)
    (hcompat : ∀ x ∈ ball p (1000 * Δ), dist (V x) (H.toFun x).snd < θ)
    (z : S) (hz : z.val = 0) (ho : dist z o ≤ Δ / 2) (t : ℝ) (ht : |t| ≤ 12 * Δ) :
    ∃ a : X, dist a p < |t| + dist z o + 3 * e ∧ dist a p < 13 * Δ ∧
      (ρ a)⁻¹ ∈ Icc (1 / 2 : ℝ) 2 ∧ (V a).val ≤ 2 * e + θ ∧
      dist (H.toFun a) (WithLp.toLp 2 (t, z)) < 2 * e := by
  obtain ⟨a, hrad, ha, hclose, hfactor⟩ := H.exists_nearby_product_lift hΔ heΔ t z ht ho
  have hΔpos : 0 < Δ := by linarith
  have hΛΔ : (Λ : ℝ) * (1000000 * Δ) < 1 := (lt_div_iff₀ (by positivity)).mp hscale
  have hρbound : |ρ a - 1| ≤ (Λ : ℝ) * (13 * Δ) := by
    have hh := hρ.dist_le_mul a p
    rw [Real.dist_eq, hρp] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left ha.le Λ.coe_nonneg)
  have hlo : 1 / 2 < ρ a := by nlinarith only [hΛΔ, (abs_le.mp hρbound).1]
  have hhi : ρ a < 2 := by nlinarith only [hΛΔ, (abs_le.mp hρbound).2]
  have hcinv : (ρ a)⁻¹ ∈ Icc (1 / 2 : ℝ) 2 := by
    rw [← one_div]
    constructor
    · exact (le_div_iff₀ (hρpos a)).mpr (by linarith only [hhi])
    · exact (div_le_iff₀ (hρpos a)).mpr (by linarith only [hlo])
  have hca := hcompat a (ha.trans (by linarith only [hΔpos]))
  have htri := dist_triangle (V a) (H.toFun a).snd z
  have hv : (V a).val ≤ dist (V a) z := by
    rw [Subtype.dist_eq, Real.dist_eq, hz, sub_zero]
    exact le_abs_self _
  exact ⟨a, hrad, ha, hcinv, by linarith only [hv, htri, hca, hfactor], hclose⟩

universe u v
variable {X : Type u} {Y : Type v} [mX : MetricSpace X] [MetricSpace Y]
variable {p : X} {q : Y} {Δ β βE s η e θ : ℝ} {Λ : NNReal} {ρ : X → ℝ}

theorem exists_strong_edge_interval_lift {C : ℝ} {o : Icc (0 : ℝ) C}
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
      dist (G.toFun (F.toFun x).snd) (H.toFun x).snd < θ)
    (t : ℝ) (ht : |t| ≤ 12 * Δ) :
    let z : Icc (0 : ℝ) C := ⟨0, le_rfl, o.property.1.trans o.property.2⟩
    ∃ a : X, dist a p < |t| + o.val + 3 * e ∧
      (@isEdgePoint.{u, v} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧
      dist (H.toFun a) (WithLp.toLp 2 (t, z)) < 2 * e := by
  let z : Icc (0 : ℝ) C := ⟨0, le_rfl, o.property.1.trans o.property.2⟩
  have hzo : dist z o = o.val := by
    rw [Subtype.dist_eq, Real.dist_eq]
    change |0 - o.val| = o.val
    rw [zero_sub, abs_neg, abs_of_nonneg o.property.1]
  obtain ⟨a, hrad, ha, hc, hheight, hclose⟩ := exists_endpoint_lift_data H hρ hρpos hρp
    hΔ hscale heΔ (fun x => G.toFun (F.toFun x).snd) hcompat z rfl (by rwa [hzo]) t ht
  refine ⟨a, by rwa [hzo] at hrad, ?_, hclose⟩
  exact isEdgePoint_of_marked_interval_model F G hΔ hC hβE hβsmall hβdomain hs hssmall
    hηs hηΔ hc ha.le ho he hθ hheight

theorem exists_strong_edge_ray_lift {o : Ici (0 : ℝ)}
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
      dist (G.toFun (F.toFun x).snd) (H.toFun x).snd < θ)
    (t : ℝ) (ht : |t| ≤ 12 * Δ) :
    let z : Ici (0 : ℝ) := ⟨0, by norm_num⟩
    ∃ a : X, dist a p < |t| + o.val + 3 * e ∧
      (@isEdgePoint.{u, v} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ βE s) ∧
      dist (H.toFun a) (WithLp.toLp 2 (t, z)) < 2 * e := by
  let z : Ici (0 : ℝ) := ⟨0, by norm_num⟩
  have hzo : dist z o = o.val := by
    rw [Subtype.dist_eq, Real.dist_eq]
    change |0 - o.val| = o.val
    rw [zero_sub, abs_neg, abs_of_nonneg o.property]
  obtain ⟨a, hrad, ha, hc, hheight, hclose⟩ := exists_endpoint_lift_data H hρ hρpos hρp
    hΔ hscale heΔ (fun x => G.toFun (F.toFun x).snd) hcompat z rfl (by rwa [hzo]) t ht
  refine ⟨a, by rwa [hzo] at hrad, ?_, hclose⟩
  exact isEdgePoint_of_ray_model F G hΔ hβE hβsmall hβdomain hs hssmall
    hηs hηΔ hc ha.le ho he hθ hheight

end GC.MetricGeometry
