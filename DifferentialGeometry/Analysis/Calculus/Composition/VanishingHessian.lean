import DifferentialGeometry.Analysis.Calculus.BilinearBounds
import DifferentialGeometry.Analysis.Calculus.FDeriv.Punctured
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem norm_second_fderiv_comp_sub_le
    {h : ℂ → ℝ} {σ : ℂ → ℂ} {w : ℂ}
    (hh : ContDiffAt ℝ 2 h (σ w)) (hσ : ContDiffAt ℝ 2 σ w) (c : ℝ) :
    ‖fderiv ℝ (fderiv ℝ (fun y => h (σ y) - c)) w‖ ≤
      ‖fderiv ℝ (fderiv ℝ h) (σ w)‖ * ‖fderiv ℝ σ w‖ ^ 2 +
        ‖fderiv ℝ h (σ w)‖ * ‖fderiv ℝ (fderiv ℝ σ) w‖ := by
  let T := ContinuousLinearMap.compL ℝ ℂ ℂ ℝ
  have hdσ := hσ.differentiableAt (by norm_num)
  have hdh := (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hdσ' := (hσ.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have heq : fderiv ℝ (fun y => h (σ y) - c) =ᶠ[𝓝 w]
      fun y => T (fderiv ℝ h (σ y)) (fderiv ℝ σ y) := by
    filter_upwards [hσ.eventually (by norm_num),
      hσ.continuousAt.eventually (hh.eventually (by norm_num))] with y hy hhy
    exact (((hhy.differentiableAt (by norm_num)).hasFDerivAt.comp y
      (hy.differentiableAt (by norm_num)).hasFDerivAt).sub_const c).fderiv
  rw [heq.fderiv_eq]
  have hbil := ContinuousLinearMap.norm_fderiv_bilinear_le
    (E := ℂ →L[ℝ] ℝ) (F := ℂ →L[ℝ] ℂ) (G := ℂ →L[ℝ] ℝ) (X := ℂ) T
    (f := fun y => fderiv ℝ h (σ y)) (g := fderiv ℝ σ) (x := w)
    (hdh.comp w hdσ) hdσ'
  have hchain : ‖fderiv ℝ (fun y => fderiv ℝ h (σ y)) w‖ ≤
      ‖fderiv ℝ (fderiv ℝ h) (σ w)‖ * ‖fderiv ℝ σ w‖ := by
    change ‖fderiv ℝ (fderiv ℝ h ∘ σ) w‖ ≤
      ‖fderiv ℝ (fderiv ℝ h) (σ w)‖ * ‖fderiv ℝ σ w‖
    rw [(hdh.hasFDerivAt.comp w hdσ.hasFDerivAt).fderiv]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have hT : ‖T‖ ≤ 1 := ContinuousLinearMap.norm_compL_le ℝ ℂ ℂ ℝ
  have h1 := mul_le_mul_of_nonneg_right hT
    (show 0 ≤ ‖fderiv ℝ h (σ w)‖ * ‖fderiv ℝ (fderiv ℝ σ) w‖ +
      ‖fderiv ℝ (fun y => fderiv ℝ h (σ y)) w‖ * ‖fderiv ℝ σ w‖ by positivity)
  have h2 := mul_le_mul_of_nonneg_right hchain (norm_nonneg (fderiv ℝ σ w))
  nlinarith

private theorem norm_fderiv_order_of_hessian_order
    {h : ℂ → ℝ} {a : ℂ} {m : ℕ} {C : ℝ}
    (hh : ContDiffAt ℝ 2 h a) (ha : fderiv ℝ h a = 0) (hC : 0 ≤ C)
    (hbound : ∀ᶠ z in 𝓝 a,
      ‖fderiv ℝ (fderiv ℝ h) z‖ ≤ C * ‖z - a‖ ^ m) :
    ∀ᶠ z in 𝓝 a, ‖fderiv ℝ h z‖ ≤ C * ‖z - a‖ ^ (m + 1) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((hh.eventually (by norm_num)).and hbound)
  filter_upwards [ball_mem_nhds a hr] with z hz
  have hzlt : ‖z - a‖ < r := by simpa only [mem_ball, dist_eq_norm] using hz
  have hsub : closedBall a ‖z - a‖ ⊆ ball a r := closedBall_subset_ball hzlt
  have hd (y : ℂ) (hy : y ∈ closedBall a ‖z - a‖) :
      DifferentiableAt ℝ (fderiv ℝ h) y :=
    ((hball (hsub hy)).1.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hnorm (y : ℂ) (hy : y ∈ closedBall a ‖z - a‖) :
      ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ C * ‖z - a‖ ^ m := by
    have hrad : ‖y - a‖ ≤ ‖z - a‖ := by
      simpa only [mem_closedBall, dist_eq_norm] using hy
    exact (hball (hsub hy)).2.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hrad _) hC)
  have hmean := Convex.norm_image_sub_le_of_norm_fderiv_le hd hnorm
    (convex_closedBall a ‖z - a‖)
    (mem_closedBall_self (norm_nonneg (z - a)))
    (show z ∈ closedBall a ‖z - a‖ by simp only [mem_closedBall, dist_eq_norm, le_refl])
  simpa only [ha, sub_zero, pow_succ, mul_assoc] using hmean

/-- A height whose original Hessian vanishes at positive order remains `C²`
through the center after the supplied `C¹` coordinate change. Only its actual
punctured Hessian is bounded; no second differentiability of the coordinate
change at the center is assumed. -/
theorem contDiffAt_comp_of_vanishing_hessian
    {h : ℂ → ℝ} {a : ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hh : ContDiffAt ℝ 2 h a) (hha : fderiv ℝ h a = 0)
    (hbound : ∃ C > 0, ∀ᶠ z in 𝓝 a,
      ‖fderiv ℝ (fderiv ℝ h) z‖ ≤ C * ‖z - a‖ ^ m)
    {σ : ℂ → ℂ} (hσ : ContDiffAt ℝ 1 σ 0) (hσ0 : σ 0 = a)
    (hσ2 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ContDiffAt ℝ 2 σ w)
    (hσbound : ∃ K > 0, ∀ᶠ w in 𝓝[≠] (0 : ℂ),
      ‖fderiv ℝ (fderiv ℝ σ) w‖ ≤ K) :
    let H : ℂ → ℝ := fun w => h (σ w) - h a
    ContDiffAt ℝ 2 H 0 ∧ fderiv ℝ H 0 = 0 ∧
      fderiv ℝ (fderiv ℝ H) 0 = 0 ∧
      ∃ C > 0, ∀ᶠ w in 𝓝 (0 : ℂ),
        ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m := by
  let H : ℂ → ℝ := fun w => h (σ w) - h a
  change ContDiffAt ℝ 2 H 0 ∧ fderiv ℝ H 0 = 0 ∧
    fderiv ℝ (fderiv ℝ H) 0 = 0 ∧
    ∃ C > 0, ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m
  obtain ⟨Ch, hCh, hHb⟩ := hbound
  obtain ⟨K, hK, hσHb⟩ := hσbound
  have hDh := norm_fderiv_order_of_hessian_order hh hha hCh.le hHb
  obtain ⟨L, hL, hrad⟩ := Asymptotics.isBigO_iff'.mp hσ.differentiableAt_one.isBigO_sub
  have hrad' : ∀ᶠ w in 𝓝 (0 : ℂ), ‖σ w - a‖ ≤ L * ‖w‖ := by
    simpa only [hσ0, sub_zero] using hrad
  let D := ‖fderiv ℝ σ 0‖ + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  have hσD : ∀ᶠ w in 𝓝 (0 : ℂ), ‖fderiv ℝ σ w‖ ≤ D := by
    have hb : ∀ᶠ w in 𝓝 (0 : ℂ), ‖fderiv ℝ σ w‖ < D :=
      (hσ.continuousAt_fderiv one_ne_zero).norm.eventually (gt_mem_nhds (by
        dsimp only [D]
        linarith))
    exact hb.mono fun _ hw => hw.le
  have hσt : Tendsto σ (𝓝 (0 : ℂ)) (𝓝 a) := by
    simpa only [hσ0] using hσ.continuousAt.tendsto
  have hH1 : ContDiffAt ℝ 1 H 0 := by
    have hh1 : ContDiffAt ℝ 1 h (σ 0) := by
      simpa only [hσ0] using hh.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
    exact (hh1.comp 0 hσ).sub contDiffAt_const
  have hD0 : fderiv ℝ H 0 = 0 := by
    have hha' : HasFDerivAt h (fderiv ℝ h a) (σ 0) := by
      simpa only [hσ0] using (hh.differentiableAt (by norm_num)).hasFDerivAt
    have hd : HasFDerivAt H ((fderiv ℝ h a).comp (fderiv ℝ σ 0)) 0 :=
      (hha'.comp 0 hσ.differentiableAt_one.hasFDerivAt).sub_const (h a)
    rw [hd.fderiv, hha, ContinuousLinearMap.zero_comp]
  let C := Ch * L ^ m * D ^ 2 + Ch * L ^ (m + 1) * K + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hsmall : ∀ᶠ w in 𝓝 (0 : ℂ), ‖w‖ ≤ 1 := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with w hw
    exact (by simpa only [mem_ball, dist_zero_right] using hw : ‖w‖ < 1).le
  have hall : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ContDiffAt ℝ 2 H w ∧
      ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m := by
    filter_upwards [hσ2, hσHb,
      (hσt.eventually (hh.eventually (by norm_num))).filter_mono nhdsWithin_le_nhds,
      (hσt.eventually hHb).filter_mono nhdsWithin_le_nhds,
      (hσt.eventually hDh).filter_mono nhdsWithin_le_nhds,
      hrad'.filter_mono nhdsWithin_le_nhds,
      hσD.filter_mono nhdsWithin_le_nhds,
      hsmall.filter_mono nhdsWithin_le_nhds] with w hw2 hwK hwh hwhb hwDh hwr hwD hw1
    have hH2 : ContDiffAt ℝ 2 H w := (hwh.comp w hw2).sub contDiffAt_const
    refine ⟨hH2, ?_⟩
    have hrm : ‖σ w - a‖ ^ m ≤ (L * ‖w‖) ^ m :=
      pow_le_pow_left₀ (norm_nonneg _) hwr _
    have hrm1 : ‖σ w - a‖ ^ (m + 1) ≤ (L * ‖w‖) ^ (m + 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hwr _
    have hb2 := hwhb.trans (mul_le_mul_of_nonneg_left hrm hCh.le)
    have hb1 := hwDh.trans (mul_le_mul_of_nonneg_left hrm1 hCh.le)
    have hsq : ‖fderiv ℝ σ w‖ ^ 2 ≤ D ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hD.le).2 hwD
    have hp : ‖w‖ ^ (m + 1) ≤ ‖w‖ ^ m := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) hw1
    have hlast := mul_le_mul_of_nonneg_left hp
      (show 0 ≤ Ch * L ^ (m + 1) * K by positivity)
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ h) (σ w)‖ * ‖fderiv ℝ σ w‖ ^ 2 +
          ‖fderiv ℝ h (σ w)‖ * ‖fderiv ℝ (fderiv ℝ σ) w‖ :=
        norm_second_fderiv_comp_sub_le hwh hw2 (h a)
      _ ≤ (Ch * (L * ‖w‖) ^ m) * D ^ 2 +
          (Ch * (L * ‖w‖) ^ (m + 1)) * K :=
        add_le_add
          (mul_le_mul hb2 hsq (sq_nonneg _) (by positivity))
          (mul_le_mul hb1 hwK (norm_nonneg _) (by positivity))
      _ ≤ C * ‖w‖ ^ m := by
        simp only [mul_pow]
        dsimp only [C]
        nlinarith [pow_nonneg (norm_nonneg w) m]
  have hlim : Tendsto (fderiv ℝ (fderiv ℝ H)) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    apply squeeze_zero_norm' (hall.mono fun _ hw => hw.2)
    have ht : Tendsto (fun w : ℂ => C * ‖w‖ ^ m) (𝓝[≠] (0 : ℂ))
        (𝓝 (C * ‖(0 : ℂ)‖ ^ m)) :=
      (((continuousAt_id : ContinuousAt (fun w : ℂ => w) 0).norm.pow m).const_mul C).tendsto.mono_left
        nhdsWithin_le_nhds
    have hm0 : m ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hm)
    simpa only [norm_zero, zero_pow hm0, mul_zero] using ht
  have hcenter : HasFDerivAt (fderiv ℝ H) (0 : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) 0 :=
    DifferentialGeometry.hasFDerivAt_zero_of_punctured_tendsto
      (hall.mono fun _ hw =>
        (hw.1.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt)
      (hH1.continuousAt_fderiv one_ne_zero) hlim
  have hcont0 : ContinuousAt (fderiv ℝ (fderiv ℝ H)) 0 := by
    apply continuousAt_iff_punctured_nhds.mpr
    rw [hcenter.fderiv]
    exact hlim
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ball (0 : ℂ) r ∩ {(0 : ℂ)}ᶜ ⊆
      {w | ContDiffAt ℝ 2 H w ∧
        ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m} :=
    mem_nhdsWithin_iff.1 hall
  have hDH1 : ContDiffAt ℝ 1 (fderiv ℝ H) 0 := by
    apply contDiffAt_one_iff.mpr
    refine ⟨fderiv ℝ (fderiv ℝ H), ball (0 : ℂ) r, ball_mem_nhds 0 hr, ?_, ?_⟩
    · intro w hw
      by_cases hw0 : w = 0
      · subst w
        exact hcont0.continuousWithinAt
      · exact (((hball ⟨hw, hw0⟩).1.fderiv_right (m := 1)
          (by norm_num)).continuousAt_fderiv one_ne_zero).continuousWithinAt
    · intro w hw
      by_cases hw0 : w = 0
      · subst w
        simpa only [hcenter.fderiv] using hcenter
      · exact ((hball ⟨hw, hw0⟩).1.fderiv_right (m := 1)
          (by norm_num)).differentiableAt_one.hasFDerivAt
  have hH2 : ContDiffAt ℝ 2 H 0 := by
    apply (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mpr
    refine ⟨fderiv ℝ H, ?_, hDH1⟩
    have hd : ∀ᶠ w in 𝓝 (0 : ℂ), DifferentiableAt ℝ H w :=
      (hH1.eventually (by norm_num)).mono fun _ hw => hw.differentiableAt_one
    exact ⟨{w | DifferentiableAt ℝ H w}, hd, fun w hw => hw.hasFDerivAt⟩
  refine ⟨hH2, hD0, hcenter.fderiv, C, hC, ?_⟩
  filter_upwards [ball_mem_nhds (0 : ℂ) hr] with w hw
  by_cases hw0 : w = 0
  · subst w
    rw [hcenter.fderiv, norm_zero]
    positivity
  · exact (hball ⟨hw, hw0⟩).2

end DifferentialGeometry.Analysis
