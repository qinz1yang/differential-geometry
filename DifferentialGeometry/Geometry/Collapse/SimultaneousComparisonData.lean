import DifferentialGeometry.Geometry.Comparison.TriangleExcessAngle
import DifferentialGeometry.Geometry.Comparison.EqualLegAngleDefect
import DifferentialGeometry.Topology.MetricSpace.EqualRadiusEndpoints
import DifferentialGeometry.Geometry.Metric.Approximation.TestedResidualParameter

/-!
Actual shortened arms retain their original triangle excess, and the tested circle residual
threshold is chosen before all model, source and approximation data.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Real
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

variable {X : Type*} [MetricSpace X]

theorem simultaneous_prefix_excess_le (q a b u v : X)
    (hu : dist q u + dist u a = dist q a)
    (hv : dist q v + dist v b = dist q b) :
    0 ≤ dist q u + dist q v - dist u v ∧
      dist q u + dist q v - dist u v ≤ dist q a + dist q b - dist a b := by
  have htri := dist_triangle u q v
  have h1 := dist_triangle a u b
  have h2 := dist_triangle u v b
  rw [dist_comm u q] at htri
  rw [dist_comm a u] at h1
  constructor <;> linarith

theorem simultaneous_mixed_prefix_excess_le (q p z v : X)
    (hv : dist q v + dist v z = dist q z) :
    0 ≤ dist q p + dist q v - dist p v ∧
      dist q p + dist q v - dist p v ≤ dist q p + dist q z - dist p z := by
  have h1 := dist_triangle p q v
  have h2 := dist_triangle p v z
  rw [dist_comm p q] at h1
  constructor <;> linarith

theorem simultaneous_annular_prefix_model_angle (p q z u v : X)
    {κ a δ τ : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) (har : a ≤ dist q p)
    (hκr : κ * dist q p ≤ 1 / 3) (hqp : dist q z = dist q p)
    (hu : dist q u = 2 * dist q p / 5)
    (hv : dist q v = 2 * dist q p / 5)
    (hup : dist q u + dist u p = dist q p)
    (hvz : dist q v + dist v z = dist q z)
    (hexcess : dist q p + dist q z - dist p z < 15 * δ)
    (hτ : 0 ≤ τ) (hbudget : 90 * δ / a < 1 - cos τ) :
    π - τ < comparisonAngleNegCurvature (κ ^ 2) (dist q u) (dist q v) (dist u v) := by
  obtain ⟨hnonneg, hle⟩ := simultaneous_prefix_excess_le q p z u v hup hvz
  rw [hu, hv] at hnonneg hle
  rw [hqp] at hle hexcess
  rw [hu, hv]
  apply pi_sub_lt_comparisonAngle_annular hκ ha har dist_nonneg
    (by linarith) hκr (by linarith) hτ hbudget

theorem exists_simultaneous_short_annular_model_angle
    (hsegments : ∀ x y : X, ∃ c : Icc (0 : ℝ) 1 → X,
      c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (c s) (c t) = dist x y * dist s t)
    (p q z : X) {a δ θ : ℝ} (ha : 0 < a) (haone : a ≤ 1)
    (haD : a ≤ dist q p) (hqz : dist q z = dist q p)
    (hexcess : dist q p + dist q z - dist p z < 15 * δ)
    (hθ : 0 ≤ θ) (hbudget : 60 * δ / a < 1 - cos θ) :
    ∃ u v : X, dist q u = min (dist q p) 1 ∧ dist q v = min (dist q p) 1 ∧
      dist q u + dist u p = dist q p ∧ dist q v + dist v z = dist q z ∧
      π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2)
        (dist q u) (dist q v) (dist u v) := by
  let r := min (dist q p) 1
  have hr : 0 < r := lt_min (ha.trans_le haD) zero_lt_one
  have har : a ≤ r := le_min haD haone
  have hrD : r ≤ dist q p := min_le_left _ _
  have hrz : r ≤ dist q z := hqz ▸ hrD
  obtain ⟨u, v, hu, hv, hup, hvz, hn, he⟩ :=
    exists_equal_radius_endpoints_with_excess_le hsegments q p z hr.le hrD hrz
  have hδ : 0 < δ := by linarith
  have hangle : π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) r r (dist u v) := by
    apply pi_sub_lt_comparisonAngle_equal (by norm_num) hr dist_nonneg (by linarith)
      (by have hh : r ≤ 1 := min_le_right _ _; linarith) hθ
    calc
      4 * (2 * r - dist u v) / r < 60 * δ / r :=
        (div_lt_div_iff_of_pos_right hr).mpr (by linarith)
      _ ≤ 60 * δ / a := div_le_div_of_nonneg_left (by positivity) ha har
      _ < _ := hbudget
  refine ⟨u, v, hu, hv, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · simpa only [hu, hv] using hangle

theorem simultaneous_edge_model_angle_bound {κ Δ τ a b c : ℝ}
    (hκ : 0 ≤ κ) (hΔ : 0 < Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000)
    (ha : Δ / 2 ≤ a) (hb : (1 / 2 - 4 * τ) * Δ ≤ b)
    (hsmall : κ * (a + b) ≤ 1) (hlo : |a - b| ≤ c) (hhi : c ≤ a + b)
    (hexcess : a + b - c ≤ 11 * τ * Δ) :
    1 + cos (comparisonAngleNegCurvature (κ ^ 2) a b c) < 100 * τ := by
  have hapos : 0 < a := (half_pos hΔ).trans_le ha
  have hb49 : (49 / 100) * Δ < b := by nlinarith
  have hbpos : 0 < b := (mul_pos (by norm_num) hΔ).trans hb49
  have hs0 : 0 ≤ κ * (a + b) := mul_nonneg hκ (add_pos hapos hbpos).le
  have hcosh : cosh (κ * (a + b)) ≤ 2 := by
    have h := cosh_sub_one_le_sq hs0 hsmall
    nlinarith [sq_nonneg (1 - κ * (a + b))]
  have hbound := one_add_cos_comparisonAngle_le_excess hκ hapos hbpos hlo hhi
  have he0 : 0 ≤ a + b - c := sub_nonneg.mpr hhi
  have hinva : 1 / a ≤ 2 / Δ := by
    have h := div_le_div_of_nonneg_left zero_le_one (half_pos hΔ) ha
    have he : (1 : ℝ) / (Δ / 2) = 2 / Δ := by field_simp
    exact he ▸ h
  have hinvb : 1 / b < (100 / 49) / Δ := by
    have h := div_lt_div_of_pos_left zero_lt_one (mul_pos (by norm_num) hΔ) hb49
    have he : (1 : ℝ) / ((49 / 100) * Δ) = (100 / 49) / Δ := by field_simp
    exact he ▸ h
  have hcoef : 22 * τ * Δ * (1 / a + 1 / b) < 100 * τ := by
    have hsum : 1 / a + 1 / b < (2 + 100 / 49) / Δ := by
      rw [add_div]
      linarith
    have hm := mul_lt_mul_of_pos_left hsum (by positivity : 0 < 22 * τ * Δ)
    have he : 22 * τ * Δ * ((2 + 100 / 49) / Δ) = 22 * (2 + 100 / 49) * τ := by
      field_simp
    rw [he] at hm
    nlinarith
  apply lt_of_le_of_lt hbound
  apply lt_of_le_of_lt (b := 22 * τ * Δ * (1 / a + 1 / b))
  · apply (div_le_iff₀ (mul_pos hapos hbpos)).mpr
    have hprod := mul_le_mul_of_nonneg_right
      (mul_le_mul hcosh hexcess he0 (by norm_num : (0 : ℝ) ≤ 2)) (add_pos hapos hbpos).le
    have he : 22 * τ * Δ * (1 / a + 1 / b) * (a * b) =
        2 * (11 * τ * Δ) * (a + b) := by
      field_simp
      ring
    rw [he]
    exact hprod
  · exact hcoef

end DifferentialGeometry.Geometry.Collapse

namespace GC.MetricGeometry

universe u v w

theorem exists_simultaneous_circle_residual_threshold :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 10 ∧
      ∀ (Z : Type u) [MetricSpace Z] (z : Z)
        (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∀ e : ℝ, 0 < e →
        ∃ γ : unitInterval → C, Continuous γ ∧ γ 0 = x ∧ γ 1 = y ∧
          eVariationOn γ univ < ENNReal.ofReal (dist x y + e)) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
      ∀ (A : Type w) [MetricSpace A] (a : A) (σ β : ℝ), σ ≤ η → β ≤ η →
        KleinerLottApprox z c σ →
        ∀ F : KleinerLottApprox z (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), a)) β,
          ∀ x : Z, dist x z ≤ 201 → dist (F.toFun x).snd a < 1 :=
  exists_tested_residual_parameter_of_nonnegative_models (by norm_num) 201 1 zero_lt_one

end GC.MetricGeometry
