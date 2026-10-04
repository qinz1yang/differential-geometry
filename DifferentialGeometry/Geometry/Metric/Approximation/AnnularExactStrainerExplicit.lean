import DifferentialGeometry.Geometry.Metric.Approximation.AnnularExactStrainer
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# LC65 with the blueprint's explicit constants

Blueprint `master207A.tex`, LC65 (`lem:collapse-annular-exact-strainer`, constants at 23735–23763).
For `0 < σ < 1` put `L = σ⁻¹`, `a = 1/10`, `b = 10`, `κ = 1/60` and
`c_σ = (2/√σ) arsinh(sinh(√σ L) cos(σ/2))` (`annularStrainerSide σ`), the opposite side of the
equal-leg model triangle with legs `L`, angle `π - σ` and curvature `-σ`. For EVERY auxiliary
angle `0 < θ < π/2` with `2 L cos(θ/2) > c_σ` (the blueprint's choice of `θ`), the blueprint's
constants
`δσ = min {a/60, 1/(4b+20), a(1 - cos θ)/60}`, `Λσ = max {2L/a, κ/√σ, 2}`
(written literally) give the LC65 one-strainer: `annular_exact_scale_strainer_explicit`.

The committed kernel `GC.MetricGeometry.exists_annular_exact_scale_strainer` exports the constants
only existentially, with `θ` chosen by a different (excess-bound) criterion. Here the last step
follows the blueprint: the scaled opposite side exceeds `2 L cos(θ/2) > c_σ`, and strict
monotonicity of the model angle in the opposite side gives an angle above `π - σ`
(`pi_sub_lt_comparisonAngleNegCurvature_of_annularStrainerSide_lt`). Such `θ` exist
(`exists_annularStrainer_blueprint_angle`, from `c_σ < 2L`, `annularStrainerSide_lt_two_mul`).
-/

set_option autoImplicit false

open Set Metric Real
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

/-- The blueprint's side `c_σ = (2/√σ) arsinh(sinh(√σ σ⁻¹) cos(σ/2))` of LC65. -/
noncomputable def annularStrainerSide (σ : ℝ) : ℝ :=
  2 / sqrt σ * arsinh (sinh (sqrt σ * σ⁻¹) * cos (σ / 2))

theorem cos_half_mem_Ioo {σ : ℝ} (hσ : 0 < σ) (hσone : σ < 1) :
    0 < cos (σ / 2) ∧ cos (σ / 2) < 1 := by
  refine ⟨cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [two_le_pi]⟩, ?_⟩
  have h := cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [two_le_pi])
    (show (0 : ℝ) < σ / 2 by linarith)
  rwa [cos_zero] at h

theorem annularStrainerSide_nonneg {σ : ℝ} (hσ : 0 < σ) (hσone : σ < 1) :
    0 ≤ annularStrainerSide σ := by
  have hA : 0 < sqrt σ * σ⁻¹ := mul_pos (sqrt_pos.mpr hσ) (inv_pos.mpr hσ)
  have hS : 0 < sinh (sqrt σ * σ⁻¹) := sinh_pos_iff.mpr hA
  have hc := cos_half_mem_Ioo hσ hσone
  unfold annularStrainerSide
  have : 0 ≤ arsinh (sinh (sqrt σ * σ⁻¹) * cos (σ / 2)) :=
    arsinh_nonneg_iff.mpr (mul_pos hS hc.1).le
  have h2 : 0 ≤ 2 / sqrt σ := div_nonneg (by norm_num) (sqrt_nonneg σ)
  positivity

/-- `c_σ < 2 L`. -/
theorem annularStrainerSide_lt_two_mul {σ : ℝ} (hσ : 0 < σ) (hσone : σ < 1) :
    annularStrainerSide σ < 2 * σ⁻¹ := by
  have hs : 0 < sqrt σ := sqrt_pos.mpr hσ
  have hA : 0 < sqrt σ * σ⁻¹ := mul_pos hs (inv_pos.mpr hσ)
  have hS : 0 < sinh (sqrt σ * σ⁻¹) := sinh_pos_iff.mpr hA
  have hc := cos_half_mem_Ioo hσ hσone
  have hlt : arsinh (sinh (sqrt σ * σ⁻¹) * cos (σ / 2)) < sqrt σ * σ⁻¹ := by
    have h := arsinh_lt_arsinh.mpr (show sinh (sqrt σ * σ⁻¹) * cos (σ / 2) < sinh (sqrt σ * σ⁻¹) by
      nlinarith [hc.2])
    rwa [arsinh_sinh] at h
  unfold annularStrainerSide
  calc 2 / sqrt σ * arsinh (sinh (sqrt σ * σ⁻¹) * cos (σ / 2))
      < 2 / sqrt σ * (sqrt σ * σ⁻¹) := mul_lt_mul_of_pos_left hlt (by positivity)
    _ = 2 * σ⁻¹ := by field_simp

/-- The blueprint's auxiliary angle exists: some `0 < θ < π/2` has `2 L cos(θ/2) > c_σ`. -/
theorem exists_annularStrainer_blueprint_angle {σ : ℝ} (hσ : 0 < σ) (hσone : σ < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧ annularStrainerSide σ < 2 * σ⁻¹ * cos (θ / 2) := by
  have hcont : Continuous fun θ : ℝ => 2 * σ⁻¹ * cos (θ / 2) := by fun_prop
  have hev : ∀ᶠ θ in nhds (0 : ℝ), annularStrainerSide σ < 2 * σ⁻¹ * cos (θ / 2) := by
    apply continuousAt_const.eventually_lt hcont.continuousAt
    simpa using annularStrainerSide_lt_two_mul hσ hσone
  obtain ⟨θ, hθ, hθ'⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < π / 2))).exists
  exact ⟨θ, hθ'.1, hθ'.2, hθ⟩

/-- The blueprint's last step of LC65: in curvature `-σ`, an equal-leg triangle with legs
`L = σ⁻¹` and opposite side larger than `c_σ` has its angle above `π - σ`. -/
theorem pi_sub_lt_comparisonAngleNegCurvature_of_annularStrainerSide_lt {σ c : ℝ} (hσ : 0 < σ)
    (hσone : σ < 1) (hc : annularStrainerSide σ < c) :
    π - σ < comparisonAngleNegCurvature σ σ⁻¹ σ⁻¹ c := by
  have hs : 0 < sqrt σ := sqrt_pos.mpr hσ
  set A : ℝ := sqrt σ * σ⁻¹ with hAdef
  have hA : 0 < A := mul_pos hs (inv_pos.mpr hσ)
  set S : ℝ := sinh A with hSdef
  have hS : 0 < S := sinh_pos_iff.mpr hA
  have hcos := cos_half_mem_Ioo hσ hσone
  have hcσ := annularStrainerSide_nonneg hσ hσone
  -- `cosh (√σ c_σ) = 1 + S² (1 + cos σ)`
  have hside : cosh (sqrt σ * annularStrainerSide σ) = 1 + S ^ 2 * (1 + cos σ) := by
    have h1 : sqrt σ * annularStrainerSide σ = 2 * arsinh (S * cos (σ / 2)) := by
      have he : annularStrainerSide σ = 2 / sqrt σ * arsinh (S * cos (σ / 2)) := rfl
      rw [he]
      field_simp
    rw [h1, cosh_two_mul, cosh_sq, sinh_arsinh]
    have h2 : cos (σ / 2) ^ 2 = 1 / 2 + cos σ / 2 := by
      have h := cos_sq (σ / 2)
      rwa [show 2 * (σ / 2) = σ by ring] at h
    nlinarith [h2]
  have hlt : cosh (sqrt σ * annularStrainerSide σ) < cosh (sqrt σ * c) := by
    rw [cosh_lt_cosh, abs_of_nonneg (mul_nonneg hs.le hcσ),
      abs_of_nonneg (mul_nonneg hs.le (hcσ.trans hc.le))]
    exact mul_lt_mul_of_pos_left hc hs
  have hX : (cosh A * cosh A - cosh (sqrt σ * c)) / (S * S) < -cos σ := by
    rw [div_lt_iff₀ (mul_pos hS hS)]
    have hch : cosh A ^ 2 = S ^ 2 + 1 := cosh_sq A
    nlinarith
  unfold comparisonAngleNegCurvature
  have hne : ¬ σ = 0 := hσ.ne'
  simp only [hne, ↓reduceIte]
  change π - σ < arccos ((cosh A * cosh A - cosh (sqrt σ * c)) / (sinh A * sinh A))
  have hσpi : σ ≤ π := by linarith [two_le_pi]
  by_cases hm : -1 ≤ (cosh A * cosh A - cosh (sqrt σ * c)) / (S * S)
  · have h := arccos_lt_arccos hm hX (by linarith [neg_one_le_cos σ])
    rwa [arccos_neg, arccos_cos hσ.le hσpi] at h
  · rw [arccos_of_le_neg_one (le_of_not_ge hm)]
    linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

/-- **LC65 (metric kernel) with the blueprint's explicit constants.** For `0 < σ < 1`, every
`0 < θ < π/2` with `2 σ⁻¹ cos(θ/2) > c_σ`, a geodesic space `X`, a pointed Kleiner–Lott `δ`-map from
`(X, p)` to a cone with `RadialConeData` with `δ < δσ = min {a/60, 1/(4b+20), a(1 - cos θ)/60}`
(`a = 1/10`, `b = 10`), and four-point comparison at curvature `-(1/60)²` on `B(p, 21)`: every `q` of
the closed shell `1/10 ≤ d(p,q) ≤ 10` and every `λ ≥ Λσ = max {2σ⁻¹/a, (1/60)/√σ, 2}` carry the
one-strainer of quality `σ` at the exact scale `σ⁻¹` of `λ d`, comparison curvature `-σ`. -/
theorem annular_exact_scale_strainer_explicit {σ θ : ℝ} (hσ : 0 < σ) (hσone : σ < 1)
    (hθ : 0 < θ) (hθpi : θ < π / 2) (hθside : annularStrainerSide σ < 2 * σ⁻¹ * cos (θ / 2))
    {X C : Type*} [MetricSpace X] [MetricSpace C]
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (p : X) (o : C) (H : RadialConeData o) {δ : ℝ} (φ : KleinerLottApprox p o δ)
    (hδ : δ < min ((1 / 10) / 60) (min (1 / (4 * 10 + 20)) ((1 / 10) * (1 - cos θ) / 60)))
    (hcomp : fourPointComparison ((1 / 60) ^ 2) (ball p 21))
    (q : X) (hq1 : 1 / 10 ≤ dist p q) (hq2 : dist p q ≤ 10) (lam : ℝ)
    (hlam : max (2 * σ⁻¹ / (1 / 10)) (max ((1 / 60) / sqrt σ) 2) ≤ lam) :
    ∃ a b z : X,
      dist q z = dist p q ∧ 2 * dist p q - dist p z < 15 * δ ∧
      π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) (dist q p) (dist q z) (dist p z) ∧
      dist q a = σ⁻¹ / lam ∧ dist q b = σ⁻¹ / lam ∧
      dist q a + dist a p = dist q p ∧ dist q b + dist b z = dist q z ∧
      π - σ < comparisonAngleNegCurvature σ (lam * dist q a) (lam * dist q b)
        (lam * dist a b) := by
  set L : ℝ := σ⁻¹ with hL
  have hLpos : 0 < L := inv_pos.mpr hσ
  have hlam20 : 20 * L ≤ lam := by
    have h := (le_max_left _ _).trans hlam
    have he : 2 * L / (1 / 10) = 20 * L := by ring
    rwa [he] at h
  have hseg' : ∀ x y : X, ∃ c : Icc (0 : ℝ) 1 → X,
      c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (c s) (c t) = dist x y * dist s t := by
    intro x y
    obtain ⟨f, _, h0, h1, hd⟩ := hsegments x y
    exact ⟨f, h0, h1, hd⟩
  have hδpos := φ.error_pos
  have hδ1 : δ < 1 / 100 := by
    have h := hδ.trans_le (min_le_left _ _)
    linarith
  have hδ2 : δ < (1 - cos θ) / 600 := by
    have h := (hδ.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
    linarith
  set D : ℝ := dist p q with hD
  have hDpos : 0 < D := by linarith
  -- LC25: the outward point at twice the radius.
  obtain ⟨q', hpq', hlow, hhigh⟩ := φ.exists_outward_point_on_annulus H hsegments
    (a := 1 / 10) (b := 10) (by norm_num) (by norm_num) (by linarith) (by linarith) ⟨hq1, hq2⟩
  -- The point `z` at distance `D` from `q` on a segment towards `q'`.
  obtain ⟨z, -, hqz, -, hzq', -, -, -⟩ :=
    exists_equal_radius_endpoints_with_excess_le hseg' q q' q' dist_nonneg hlow hlow
  have hpz_low : 2 * D - 15 * δ < dist p z := by
    have h := dist_triangle p z q'
    linarith
  have hpz_up : dist p z ≤ 2 * D := by
    have h := dist_triangle p q z
    linarith
  have hpz_nonneg : 0 ≤ dist p z := dist_nonneg
  have hqp : dist q p = D := dist_comm q p
  -- The angle at `q` of `(q; p, z)` at curvature `-(1/60)²`.
  have hangle0 : π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) D D (dist p z) := by
    apply pi_sub_lt_comparisonAngle_equal (by norm_num) hDpos hpz_nonneg hpz_up
      (by nlinarith) hθ.le
    rw [div_lt_iff₀ hDpos]
    have : 4 * (2 * D - dist p z) < 60 * δ := by linarith
    nlinarith
  -- Shortening to the exact length `s = L / λ`.
  set s : ℝ := L / lam with hs
  have hlampos : 0 < lam := lt_of_lt_of_le (by positivity) hlam20
  have hspos : 0 < s := div_pos hLpos hlampos
  have hs20 : s ≤ 1 / 20 := by
    rw [hs, div_le_iff₀ hlampos]
    linarith
  have hsD : s ≤ D := by linarith
  obtain ⟨a, b, hqa, hqb, hap, hbz, -, -⟩ :=
    exists_equal_radius_endpoints_with_excess_le hseg' q p z hspos.le
      (by rw [hqp]; exact hsD) (by rw [hqz]; exact hsD)
  have hmem (x : X) (hx : dist x p < 21) : x ∈ ball p 21 := hx
  have hpB : p ∈ ball p 21 := mem_ball_self (by norm_num)
  have hqB : q ∈ ball p 21 := hmem q (by rw [hqp]; linarith)
  have hzB : z ∈ ball p 21 := hmem z (by rw [dist_comm]; linarith)
  have haB : a ∈ ball p 21 := hmem a (by rw [hap, hqp]; linarith)
  have hbB : b ∈ ball p 21 := hmem b (by
    have h := dist_triangle b q p
    rw [dist_comm b q, hqb, hqp] at h
    linarith)
  have hzq : z ≠ q := by
    intro h
    rw [h, dist_self] at hqz
    linarith
  have haq : a ≠ q := by
    intro h
    rw [h, dist_self] at hqa
    linarith
  have hκ : (0 : ℝ) ≤ (1 / 60) ^ 2 := by positivity
  have hsh1 := comparisonAngleNegCurvature_le_of_shortening_left hκ hcomp hqB haB hpB hzB
    (by rw [hqa]; exact hspos) hzq (by rw [hqa, hap]; ring)
  have hsh2 := comparisonAngleNegCurvature_le_of_shortening_right hκ hcomp hqB hbB hzB haB
    (by rw [hqb]; exact hspos) haq (by rw [hqb, hbz]; ring)
  have hangle_s : π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) s s (dist a b) := by
    have h0 : π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) (dist q p) (dist q z)
        (dist p z) := by rw [hqp, hqz]; exact hangle0
    have h := (h0.trans_le hsh1).trans_le hsh2
    rwa [hqa, hqb] at h
  have hab_up : dist a b ≤ 2 * s := by
    have h := dist_triangle a q b
    rw [dist_comm a q, hqa, hqb] at h
    linarith
  have hchord := two_mul_cos_half_lt_of_pi_sub_lt_comparisonAngleNegCurvature hκ hspos
    dist_nonneg hab_up hθ.le (by linarith [pi_pos]) hangle_s
  -- The blueprint's last step: the scaled opposite side exceeds `2 L cos(θ/2) > c_σ`.
  have hlams : lam * s = L := by
    rw [hs]
    field_simp
  have hc_low : 2 * L * cos (θ / 2) < lam * dist a b := by nlinarith
  refine ⟨a, b, z, hqz, by linarith, by rw [hqp, hqz]; exact hangle0, hqa, hqb,
    by rw [hqa, hap]; ring, by rw [hqb, hbz]; ring, ?_⟩
  rw [hqa, hqb, hlams]
  exact pi_sub_lt_comparisonAngleNegCurvature_of_annularStrainerSide_lt hσ hσone
    (hθside.trans hc_low)

end GC.MetricGeometry
