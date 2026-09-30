import DifferentialGeometry.Analysis.Calculus.Cutoff.EdgeNetworkProfiles
import DifferentialGeometry.Geometry.Metric.Approximation.PaddedStripBoundary
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
open Set Metric DifferentialGeometry.Analysis

namespace GC.MetricGeometry

variable {X : Type*} [MetricSpace X]

theorem tsupport_edge_chart_cutoff_subset {p : X} {Δ δ C : ℝ} {Λ : NNReal}
    (hΔ : 1 ≤ Δ) (hδ : 0 < δ) (hδsmall : δ ≤ Δ / 1000000) (hC : 200 * Δ < C)
    (ρ P : X → ℝ) (hρ : LipschitzWith Λ ρ) (hpos : ∀ x, 0 < ρ x)
    (hρp : ρ p = 1) (hslow : Δ * Λ ≤ 1 / 10000)
    (E : Set X) (hE : E.Nonempty)
    (hP : ∀ x ∈ ball p (100 * Δ), |P x - infDist x E| ≤ ρ x / 100)
    (Q : X → WithLp 2 (ℝ × ℝ)) (hQp : Q p = 0)
    (hQdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ δ)
    (hcover : ∀ y : WithLp 2 (ℝ × ℝ), y.snd ∈ Icc 0 C → ‖y‖ < 200 * Δ - δ →
      infDist y (Q '' ball p (200 * Δ)) ≤ δ)
    (hQheight : ∀ x ∈ ball p (100 * Δ), 0 ≤ (Q x).snd)
    (hweak : ∀ z ∈ E, z ∈ ball p (120 * Δ) →
      ∃ W : X → WithLp 2 (ℝ × ℝ), W z = 0 ∧
        (∀ x ∈ ball z Δ, 0 ≤ (W x).snd) ∧
        ∀ x ∈ ball z Δ, ∀ y ∈ ball z Δ, |dist (W x) (W y) - dist x y| ≤ δ)
    (η : ball p (100 * Δ) → ℝ) (hvalue : ∀ x, |η x - (Q x.val).fst| ≤ Δ / 100) :
    let ζ := (Subtype.val : ball p (100 * Δ) → X).extend
      (fun x => edgeCoordinateProfile (η x / Δ) * edgeHeightProfile (P x.val / (Δ * ρ x.val))) 0
    tsupport ζ ⊆ closedBall p (15 * Δ) ∧ closedBall p (15 * Δ) ⊆ ball p (20 * Δ) := by
  have hΔ0 : 0 < Δ := by linarith
  have hpD : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  refine ⟨?_, closedBall_subset_ball (by linarith)⟩
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Function.support_extend_zero_subset hx
  change edgeCoordinateProfile (η y / Δ) * edgeHeightProfile (P y.val / (Δ * ρ y.val)) ≠ 0 at hy
  have hyD : y.val ∈ ball p (100 * Δ) := y.property
  have hy200 : y.val ∈ ball p (200 * Δ) :=
    (show dist y.val p < 100 * Δ from hyD).trans (by linarith)
  have hηlo : -9 < η y / Δ := by
    by_contra! hh
    exact hy (by rw [show edgeCoordinateProfile (η y / Δ) = 0 from
      intervalPlateauProfile_zero_left (by norm_num) hh, zero_mul])
  have hηhi : η y / Δ < 9 := by
    by_contra! hh
    exact hy (by rw [show edgeCoordinateProfile (η y / Δ) = 0 from
      intervalPlateauProfile_zero_right (by norm_num) hh, zero_mul])
  have hPcut : P y.val / (Δ * ρ y.val) < 9 := by
    by_contra! hh
    exact hy (by rw [show edgeHeightProfile (P y.val / (Δ * ρ y.val)) = 0 from
      descendingIntervalProfile_zero (by norm_num) hh, mul_zero])
  have hηlo' := (lt_div_iff₀ hΔ0).mp hηlo
  have hηhi' := (div_lt_iff₀ hΔ0).mp hηhi
  have hPcut' := (div_lt_iff₀ (mul_pos hΔ0 (hpos y.val))).mp hPcut
  have hscale : ρ y.val ≤ 101 / 100 := by
    have hh := hρ.dist_le_mul y.val p
    rw [Real.dist_eq, hρp] at hh
    have h1 := mul_le_mul_of_nonneg_left hyD.le (NNReal.coe_nonneg Λ)
    nlinarith [(abs_le.mp hh).2]
  have hnear : infDist y.val E < 46 * Δ / 5 := by
    have hh := (abs_le.mp (hP y.val hyD)).1
    have h1 := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 9 * Δ + 1 / 100 by positivity)
    nlinarith
  obtain ⟨z, hzE, hyz⟩ := (infDist_lt_iff hE).mp hnear
  have hz120 : z ∈ ball p (120 * Δ) := by
    have ht := dist_triangle z y.val p
    rw [dist_comm z y.val] at ht
    change dist z p < 120 * Δ
    change dist y.val p < 100 * Δ at hyD
    linarith
  have hz200 : z ∈ ball p (200 * Δ) :=
    (show dist z p < 120 * Δ from hz120).trans (by linarith)
  obtain ⟨W, hWz, hWheight, hWdist⟩ := hweak z hzE hz120
  have hheightz := padded_strip_height_lt_of_half_plane_model hΔ0 hδ hδsmall hC Q W hQp hWz
    hQdist hcover hWheight hWdist hz120
  have hu : |(Q y.val).fst| ≤ 10 * Δ := by
    have hh := abs_le.mp (hvalue y)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hv : (Q y.val).snd ≤ 10 * Δ := by
    have h1 := (abs_le.mp (hQdist y.val hy200 z hz200)).2
    have h2 := WithLp.dist_snd_le (Q y.val) (Q z)
    rw [Real.dist_eq] at h2
    linarith [(abs_le.mp h2).2]
  have hnorm : ‖Q y.val‖ < 149 / 10 * Δ := by
    have hs := WithLp.prod_norm_sq_eq_of_L2 (Q y.val)
    simp only [Real.norm_eq_abs, sq_abs] at hs
    have hu2 := pow_le_pow_left₀ (abs_nonneg (Q y.val).fst) hu 2
    rw [sq_abs] at hu2
    have hv2 := pow_le_pow_left₀ (hQheight y.val y.property) hv 2
    by_contra! hh
    have hsq := pow_le_pow_left₀ (show 0 ≤ 149 / 10 * Δ by positivity) hh 2
    nlinarith [sq_pos_of_pos hΔ0]
  have hd := (abs_le.mp (hQdist y.val hy200 p hpD)).1
  rw [hQp, dist_zero_right] at hd
  change dist y.val p ≤ 15 * Δ
  linarith

end GC.MetricGeometry
