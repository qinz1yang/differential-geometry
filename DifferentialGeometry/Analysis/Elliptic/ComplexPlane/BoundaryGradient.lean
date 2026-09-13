import DifferentialGeometry.Analysis.Elliptic.Euclidean.InteriorGradient
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.BoundaryGrowth
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace DifferentialGeometry.Analysis

private theorem exists_bound_fderiv_of_linear_boundary_growth
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℂ → F} {R β K : ℝ} (hR : 0 < R) (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hd : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ContDiffAt ℝ 2 f z)
    (hg : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ‖f z‖ ≤ K * z.im)
    (hΔ : ∀ z : ℂ, ‖z‖ < R → 0 < z.im →
      ‖Laplacian.laplacian f z‖ ≤ β * ‖fderiv ℝ f z‖ ^ 2) :
    ∃ r > (0 : ℝ), r < R ∧ ∃ C > (0 : ℝ),
      ∀ z : ℂ, ‖z‖ < r → 0 < z.im → ‖fderiv ℝ f z‖ ≤ C := by
  obtain ⟨ε, hε, C, hC, hint⟩ :=
    exists_pos_norm_fderiv_le_of_quadratic_laplacian_bound (V := ℂ) (F := F)
  let r := min (R / 4) (ε / (2 * β * K + 1))
  have hden : 0 < 2 * β * K + 1 := by positivity
  have hr : 0 < r := lt_min (by positivity) (div_pos hε hden)
  have hrR : r < R := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨r, hr, hrR, 4 * C * (K + 1), by positivity, ?_⟩
  intro z hz hzi
  have hzir : z.im < r := (Complex.im_le_norm z).trans_lt hz
  have hr4 : r ≤ R / 4 := min_le_left _ _
  have hsmall : β * (2 * K * z.im) ≤ ε := by
    have hh := (le_div_iff₀ hden).mp (min_le_right (R / 4) (ε / (2 * β * K + 1)))
    change r * (2 * β * K + 1) ≤ ε at hh
    have hm := mul_le_mul_of_nonneg_left hzir.le (mul_nonneg hβ hK)
    nlinarith only [hh, hm, hr]
  have hball (w : ℂ) (hw : w ∈ Metric.ball z (z.im / 2)) :
      ‖w‖ < R ∧ 0 < w.im ∧ w.im ≤ 2 * z.im := by
    have hdist : ‖w - z‖ < z.im / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have him := Complex.abs_im_le_norm (w - z)
    rw [Complex.sub_im, abs_le] at him
    have hn := norm_le_norm_sub_add w z
    constructor
    · linarith
    constructor <;> linarith
  have h := hint f z (z.im / 2) β (2 * K * z.im) (by positivity) hβ hsmall
    (fun w hw => (hd w (hball w hw).1 (hball w hw).2.1).contDiffWithinAt)
    (fun w hw => (hg w (hball w hw).1 (hball w hw).2.1).trans (by
      have hm := mul_le_mul_of_nonneg_left (hball w hw).2.2 hK
      nlinarith only [hm]))
    (fun w hw => hΔ w (hball w hw).1 (hball w hw).2.1)
  have hm : z.im * ‖fderiv ℝ f z‖ ≤ z.im * (4 * C * K) := by nlinarith only [h]
  have hD := le_of_mul_le_mul_left hm hzi
  have hCK : 4 * C * K ≤ 4 * C * (K + 1) := by nlinarith
  exact hD.trans hCK


theorem exists_bound_fderiv_near_zero_of_norm_laplacian_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : ℂ → F} {R β : ℝ} (hR : 0 < R) (hβ : 0 ≤ β)
    (hf : ContinuousOn f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hd : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ContDiffAt ℝ 2 f z)
    (hΔ : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ‖Laplacian.laplacian f z‖ ≤
      β * (fderiv ℝ f z).hilbertSchmidtInner (fderiv ℝ f z))
    (hzero : ∀ z : ℂ, ‖z‖ ≤ R → z.im = 0 → f z = 0) :
    ∃ r > (0 : ℝ), r < R ∧ ∃ C > (0 : ℝ),
      ∀ z : ℂ, ‖z‖ < r → 0 < z.im → ‖fderiv ℝ f z‖ ≤ C := by
  let δ : ℝ := 1 / (2 * (β + 1))
  have hden : 0 < 2 * (β + 1) := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : β * δ < 1 := by
    have he : β * δ = β / (2 * (β + 1)) := by dsimp [δ]; ring
    rw [he]
    exact (div_lt_one hden).2 (by linarith)
  have h00 : (0 : ℂ) ∈ {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} := by simp [hR.le]
  have hf0 : f 0 = 0 := hzero 0 (by simpa using hR.le) (by simp)
  obtain ⟨d, hd0, hcont⟩ := Metric.continuousWithinAt_iff.mp (hf 0 h00) δ hδ
  let ρ : ℝ := min (R / 2) (d / 2)
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρR : ρ < R := (min_le_left _ _).trans_lt (by linarith)
  have hρd : ρ < d := (min_le_right _ _).trans_lt (by linarith)
  have hbound : ∀ z : ℂ, ‖z‖ ≤ ρ → 0 ≤ z.im → ‖f z‖ ≤ δ := by
    intro z hz hi
    have hzS : z ∈ {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} := ⟨hz.trans hρR.le, hi⟩
    have hdist : dist z 0 < d := by simpa only [dist_zero_right] using hz.trans_lt hρd
    have hh := hcont hzS hdist
    exact (by simpa only [hf0, dist_zero_right] using hh : ‖f z‖ < δ).le
  let K : ℝ := 2 * ρ * (δ + β / (2 * (1 - β * δ)) * δ ^ 2) / (ρ - ρ / 2) ^ 2
  have hK : 0 ≤ K := by
    have hb : 0 < 1 - β * δ := sub_pos.mpr hsmall
    dsimp [K]
    positivity
  have hg := norm_le_mul_im_of_norm_laplacian_le (R := ρ) (r := ρ / 2)
    hρ (by linarith) (hf.mono (fun z hz => ⟨hz.1.trans hρR.le, hz.2⟩))
    (fun z hz hi => hd z (hz.trans hρR) hi) hβ hsmall hbound
    (fun z hz hi => hΔ z (hz.trans hρR) hi)
    (fun z hz hi => hzero z (hz.trans hρR.le) hi)
  have hquad : ∀ z : ℂ, ‖z‖ < ρ / 2 → 0 < z.im →
      ‖Laplacian.laplacian f z‖ ≤ (2 * β) * ‖fderiv ℝ f z‖ ^ 2 := by
    intro z hz hi
    have hzR : ‖z‖ < R := hz.trans (by linarith)
    have hh := (fderiv ℝ f z).hilbertSchmidtInner_self_le_finrank_mul_norm_sq
    norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat] at hh
    have hm := mul_le_mul_of_nonneg_left hh hβ
    exact (hΔ z hzR hi).trans (by nlinarith only [hm])
  obtain ⟨r, hr, hrρ, C, hC, hboundD⟩ := exists_bound_fderiv_of_linear_boundary_growth
    (R := ρ / 2) (β := 2 * β) (K := K) (by positivity) (by positivity) hK
    (fun z hz hi => hd z (hz.trans (by linarith)) hi)
    (fun z hz hi => hg z hz.le hi.le) hquad
  exact ⟨r, hr, hrρ.trans (by linarith), C, hC, hboundD⟩

end DifferentialGeometry.Analysis
