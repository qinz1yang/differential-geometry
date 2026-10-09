import DifferentialGeometry.Analysis.Calculus.Cutoff.Ball
import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section

namespace DifferentialGeometry.Analysis

open Filter Set
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem fderiv_sq_norm_div (center : E) (r : ℝ) :
    fderiv ℝ (fun y : E ↦ ‖y - center‖ ^ 2 / r ^ 2) =
      ballCutoffArgumentFDeriv center 0 r := by
  funext x
  have h := (hasFDerivAt_ballCutoffArgument center 0 r x).sub_const 1
  simpa [ballCutoffArgument] using h.fderiv

private theorem fderiv_sq_norm_div_fderiv (center : E) (r : ℝ) :
    fderiv ℝ (ballCutoffArgumentFDeriv center 0 r) =
      fun _ ↦ ballCutoffArgumentFDeriv2 (E := E) 0 r := by
  funext x
  exact (hasFDerivAt_ballCutoffArgumentFDeriv center 0 r x).fderiv

private theorem norm_iteratedFDeriv_sq_norm_div_le
    (center x : E) {r R : ℝ} (hr : 0 < r) (hx : ‖x - center‖ ≤ R * r)
    {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun y : E ↦ ‖y - center‖ ^ 2 / r ^ 2) x‖ ≤
      (max 2 (2 * R) / r) ^ i := by
  have hM : 2 ≤ max (2 : ℝ) (2 * R) := le_max_left _ _
  have hM' : 2 * R ≤ max (2 : ℝ) (2 * R) := le_max_right _ _
  have hD : 0 ≤ max (2 : ℝ) (2 * R) / r := by positivity
  obtain i | i := i
  · omega
  obtain i | i := i
  · simp only [Nat.zero_add, pow_one]
    rw [norm_iteratedFDeriv_one, fderiv_sq_norm_div]
    simp only [ballCutoffArgumentFDeriv, zero_pow (by decide : 2 ≠ 0), sub_zero,
      norm_smul, RCLike.norm_nsmul ℝ, innerSL_apply_norm, nsmul_eq_mul,
      Real.norm_eq_abs, abs_inv, abs_of_nonneg (sq_nonneg r)]
    calc
      (r ^ 2)⁻¹ * (2 * ‖x - center‖) ≤ (r ^ 2)⁻¹ * (2 * (R * r)) := by
        gcongr
      _ = (2 * R) / r := by field_simp
      _ ≤ max 2 (2 * R) / r := div_le_div_of_nonneg_right hM' hr.le
  · rw [← norm_iteratedFDeriv_fderiv, fderiv_sq_norm_div,
      ← norm_iteratedFDeriv_fderiv, fderiv_sq_norm_div_fderiv]
    obtain i | i := i
    · rw [norm_iteratedFDeriv_zero]
      change ‖ballCutoffArgumentFDeriv2 (E := E) 0 r‖ ≤ (max 2 (2 * R) / r) ^ 2
      have hq := norm_ballCutoffArgumentFDeriv2_le (E := E) (r := 0) (by norm_num) hr
      simp only [zero_pow (by decide : 2 ≠ 0), sub_zero] at hq
      refine hq.trans ?_
      rw [div_pow]
      apply div_le_div_of_nonneg_right _ (sq_nonneg r)
      nlinarith
    · simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
      exact pow_nonneg hD _

theorem norm_iteratedFDeriv_comp_sq_norm_div_le
    {φ : ℝ → ℝ} {n : ℕ} (hφ : ContDiff ℝ n φ)
    (center x : E) {r R B : ℝ} (hr : 0 < r) (hx : ‖x - center‖ ≤ R * r)
    (hB : ∀ j ≤ n, ‖iteratedFDeriv ℝ j φ (‖x - center‖ ^ 2 / r ^ 2)‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y : E ↦ φ (‖y - center‖ ^ 2 / r ^ 2)) x‖ ≤
      (n.factorial : ℝ) * B * (max 2 (2 * R) / r) ^ n := by
  exact norm_iteratedFDeriv_comp_le hφ
    (((contDiff_id.sub contDiff_const).norm_sq ℝ).div_const (r ^ 2))
    le_rfl x hB (fun i hi _ ↦ norm_iteratedFDeriv_sq_norm_div_le center x hr hx hi)

omit [InnerProductSpace ℝ E] in
theorem ballCutoff_eq_comp_sq_norm_div (center : E) (r : ℝ) :
    ballCutoff center r (2 * r) =
      fun x ↦ CutoffProfile.value (1 + (‖x - center‖ ^ 2 / r ^ 2 - 1) / 3) := by
  by_cases hr : r = 0
  · subst r
    funext x
    norm_num [ballCutoff, ballCutoffArgument, CutoffProfile.one_of_le_one]
  funext x
  unfold ballCutoff ballCutoffArgument
  congr 1
  have hden : (2 * r) ^ 2 - r ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hr]
  field_simp
  ring

private def scaledProfile (t : ℝ) : ℝ := CutoffProfile.value (1 + (t - 1) / 3)

private theorem scaledProfile_contDiff : ContDiff ℝ ∞ scaledProfile :=
  CutoffProfile.contDiff.comp
    (contDiff_const.add ((contDiff_id.sub contDiff_const).div_const 3))

private theorem scaledProfile_one {t : ℝ} (ht : t ≤ 1) : scaledProfile t = 1 :=
  CutoffProfile.one_of_le_one (by linarith)

private theorem scaledProfile_zero {t : ℝ} (ht : 4 ≤ t) : scaledProfile t = 0 :=
  CutoffProfile.zero_of_two_le (by linarith)

private theorem scaledProfile_fderiv_hasCompactSupport :
    HasCompactSupport (fderiv ℝ scaledProfile) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 4))
  intro t ht
  by_cases h1 : t < 1
  · have heq : scaledProfile =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds h1] with s hs
      exact scaledProfile_one hs.le
    rw [heq.fderiv_eq, fderiv_const_apply]
  · have h4 : 4 < t := by
      by_contra! h4
      exact ht ⟨le_of_not_gt h1, h4⟩
    have heq : scaledProfile =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h4] with s hs
      exact scaledProfile_zero hs.le
    rw [heq.fderiv_eq, fderiv_const_apply]

private theorem exists_scaledProfile_jet_bound (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j ≤ n, ∀ t, ‖iteratedFDeriv ℝ j scaledProfile t‖ ≤ B := by
  obtain ⟨B, -, hb⟩ := scaledProfile_fderiv_hasCompactSupport.exists_bound_iteratedFDeriv
    (scaledProfile_contDiff.fderiv_right (m := ∞) (by simp)) n
  refine ⟨max 1 B, le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro j hj t
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    have hval := CutoffProfile.mem_Icc (1 + (t - 1) / 3)
    have hval' : ‖scaledProfile t‖ ≤ 1 := by
      simpa only [scaledProfile, Real.norm_eq_abs, abs_of_nonneg hval.1] using hval.2
    exact hval'.trans (le_max_left _ _)
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv]
    exact (hb j (by omega) t).trans (le_max_right _ _)

universe u

theorem exists_bound_iteratedFDeriv_ballCutoff (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
        (center : F) (r : ℝ), 0 < r → ∀ j ≤ n, ∀ x : F,
        ‖iteratedFDeriv ℝ j (ballCutoff center r (2 * r)) x‖ ≤ C / r ^ j := by
  obtain ⟨B, hB, hb⟩ := exists_scaledProfile_jet_bound n
  refine ⟨(n.factorial : ℝ) * B * 4 ^ n, by positivity, ?_⟩
  intro F _ _ center r hr j hj x
  by_cases hx : ‖x - center‖ ≤ 2 * r
  · rw [ballCutoff_eq_comp_sq_norm_div center r]
    have h := norm_iteratedFDeriv_comp_sq_norm_div_le
      (scaledProfile_contDiff.of_le (by simp)) center x hr hx
      (fun i hi ↦ hb i (hi.trans hj) (‖x - center‖ ^ 2 / r ^ 2))
    change ‖iteratedFDeriv ℝ j (fun y : F ↦ scaledProfile (‖y - center‖ ^ 2 / r ^ 2)) x‖ ≤ _
    refine h.trans ?_
    simp only [show (2 : ℝ) * 2 = 4 by norm_num,
      max_eq_right (by norm_num : (2 : ℝ) ≤ 4), div_pow]
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hB
    · exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj
    · positivity
    · positivity
  · have heq : ballCutoff center r (2 * r) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
      have hdist : 2 * r < dist x center := by simpa [dist_eq_norm] using not_le.mp hx
      filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds
        hdist] with y hy
      exact ballCutoff_eq_zero_of_le_dist hr.le (by linarith) hy.le
    rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    positivity

end DifferentialGeometry.Analysis
