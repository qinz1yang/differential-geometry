/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.SmallBallGauge
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.UnitGauge
import DifferentialGeometry.Analysis.Complex.CauchyTransform.PointwiseEquation
import DifferentialGeometry.Analysis.Complex.WeakHolomorphic
import DifferentialGeometry.Analysis.Calculus.Lipschitz.FrontierExtension
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace DifferentialGeometry.Analysis

private theorem ae_im_ne_zero : ∀ᵐ z : ℂ ∂volume, z.im ≠ 0 := by
  have h : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), p.2 ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurable_snd (measurableSet_singleton 0).compl)).mpr
    filter_upwards with x
    simp [ae_iff, measure_singleton]
  exact Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae h

/-- Zero extension of the actual upper-half holomorphic function has a lower-half
zero germ. A finite Lipschitz bound, rather than a derivative jump assumption,
justifies removal of the real axis. -/
private theorem eq_zero_on_upperHalfBall_of_contDiffOn
    {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ 1 f (ball 0 R))
    (hhol : DifferentiableOn ℂ f (ball 0 R ∩ {z : ℂ | 0 < z.im}))
    (hzero : ∀ z ∈ ball 0 R, z.im = 0 → f z = 0) :
    ∀ z ∈ ball 0 (R / 2), 0 ≤ z.im → f z = 0 := by
  classical
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hsmall : closedBall (0 : ℂ) (R / 2) ⊆ ball 0 R :=
    closedBall_subset_ball (by linarith)
  have hball : ball (0 : ℂ) (R / 2) ⊆ ball 0 R :=
    ball_subset_closedBall.trans hsmall
  obtain ⟨L, hL⟩ := (hf.mono hsmall).exists_lipschitzOnWith
    one_ne_zero (convex_closedBall (0 : ℂ) (R / 2))
      (isCompact_closedBall (0 : ℂ) (R / 2))
  let Z : ℂ → ℂ := U.piecewise f (fun _ => 0)
  have hZLip : LipschitzOnWith L Z (ball 0 (R / 2)) := by
    apply (hL.mono (inter_subset_right.trans ball_subset_closedBall)).piecewise_const_of_eq_on_frontier
      hU (convex_ball (0 : ℂ) (R / 2))
    intro z hz
    have hzaxis : z.im = 0 := by
      simpa only [U, Complex.frontier_setOfPred_lt_im, Set.mem_ofPred_eq] using hz.1
    exact hzero z (hball hz.2) hzaxis
  have hAE : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) (R / 2)),
      DifferentiableAt ℂ Z z := by
    filter_upwards [ae_restrict_of_ae ae_im_ne_zero,
      ae_restrict_mem isOpen_ball.measurableSet] with z hzne hz
    by_cases hzup : 0 < z.im
    · have hnear : Z =ᶠ[𝓝 z] f := by
        filter_upwards [hU.mem_nhds hzup] with w hw
        exact piecewise_eq_of_mem U f (fun _ => 0) hw
      exact ((hhol z ⟨hball hz, hzup⟩).differentiableAt
        ((isOpen_ball.inter hU).mem_nhds ⟨hball hz, hzup⟩)).congr_of_eventuallyEq hnear
    · have hzdown : z.im < 0 := lt_of_le_of_ne (le_of_not_gt hzup) hzne
      have hnear : Z =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hzdown]
          with w hw
        exact piecewise_eq_of_notMem U f (fun _ => 0) (not_lt.mpr hw.le)
      exact (differentiableAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hnear
  have hZhol := differentiableOn_of_lipschitzOnWith_of_ae_differentiableAt
    isOpen_ball hZLip hAE
  let y : ℂ := -(R / 4) • Complex.I
  have hy : y ∈ ball (0 : ℂ) (R / 2) := by
    rw [mem_ball, dist_zero_right]
    simp only [y, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity : 0 < R / 4), Complex.norm_I, mul_one]
    linarith
  have hyim : y.im < 0 := by
    simpa only [y, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero]
      using (show -(R / 4) < 0 by linarith)
  have hnear : Z =ᶠ[𝓝 y] 0 := by
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hyim]
      with w hw
    exact piecewise_eq_of_notMem U f (fun _ => 0) (not_lt.mpr hw.le)
  have hZzero : EqOn Z 0 (ball (0 : ℂ) (R / 2)) :=
    hZhol.analyticOnNhd isOpen_ball |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) (R / 2)).isPreconnected hy hnear
  intro z hz hzim
  rcases eq_or_lt_of_le hzim with hzim | hzim
  · exact hzero z (hball hz) hzim.symm
  · exact (piecewise_eq_of_mem U f (fun _ => 0) hzim).symm.trans (hZzero hz)

/-- A finite-product C¹ first-order system with zero real-diameter values has a
zero germ on the closed upper side. The unit gauge is constructed from B;
the section equation is required only on the strict upper half of the ball. -/
theorem exists_pos_radius_eq_zero_on_upperHalfBall
    {n : ℕ} {R : ℝ} (hR : 0 < R)
    (B : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (ξ : ℂ → (Fin n → ℂ))
    (hB : ContDiffOn ℝ 1 B (ball 0 R))
    (hξ : ContDiffOn ℝ 1 ξ (ball 0 R))
    (hDE : ∀ z ∈ ball 0 R, 0 < z.im →
      (1 / 2 : ℂ) • (fderiv ℝ ξ z 1 + Complex.I • fderiv ℝ ξ z Complex.I) = B z (ξ z))
    (hzero : ∀ z ∈ ball 0 R, z.im = 0 → ξ z = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧
      ∀ z ∈ ball 0 ρ, 0 ≤ z.im → ξ z = 0 := by
  classical
  let V := Fin n → ℂ
  obtain ⟨s, hs, hbuffer, B_s, hB_s, _, P, _, _, _, _, _, ⟨K, hK⟩, hP₀⟩ :=
    exists_small_ball_unit_integral_gauge isOpen_ball (mem_ball_self hR) B hB
  let f : C(closedBall (0 : ℂ) s, V →L[ℂ] V) := B_s * P
  let P₀ : ℂ → V →L[ℂ] V := fun z => 1 + ambientCauchyIntegral f z
  change (∀ z : closedBall (0 : ℂ) s, P₀ (z : ℂ) = P z) ∧
    (∀ z ∈ closedBall (0 : ℂ) s, IsUnit (P₀ z)) at hP₀
  have hinside : ball (0 : ℂ) s ⊆ ball 0 R :=
    (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith : s ≤ 2 * s))).trans hbuffer
  have hlocal : ∀ q ∈ ball (0 : ℂ) s, ∃ ε : ℝ, 0 < ε ∧ ∃ α H : ℝ≥0,
      closedBall q ε ⊆ ball 0 s ∧ 0 < α ∧ α ≤ 1 ∧
        HolderOnWith H α f {w : closedBall (0 : ℂ) s | (w : ℂ) ∈ closedBall q ε} := by
    intro q hq
    obtain ⟨ε, hε, hεball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (isOpen_ball.mem_nhds hq)
    exact ⟨ε, hε, (1 / 2 : ℝ≥0), K, hεball, by norm_num, by norm_num,
      hK.holderOnWith _⟩
  obtain ⟨hT, hTdbar⟩ :=
    contDiffOn_and_dbar_ambientCauchyIntegral_of_locally_holder
      f isOpen_ball Subset.rfl hlocal
  have hPReg : ContDiffOn ℝ 1 P₀ (ball 0 s) :=
    (contDiffOn_const (c := (1 : V →L[ℂ] V))).add hT
  have hD (q : ℂ) : fderiv ℝ P₀ q = fderiv ℝ (ambientCauchyIntegral f) q := by
    change fderiv ℝ (fun z => (1 : V →L[ℂ] V) + ambientCauchyIntegral f z) q = _
    exact fderiv_const_add 1
  have hhalf (A : V →L[ℂ] V) : (1 / 2 : ℂ) • A = (1 / 2 : ℝ) • A := by
    rw [show (1 / 2 : ℂ) = algebraMap ℝ ℂ (1 / 2 : ℝ) by norm_num, algebraMap_smul]
  have hPDE : ∀ z ∈ ball (0 : ℂ) s,
      (1 / 2 : ℂ) • (fderiv ℝ P₀ z 1 + Complex.I • fderiv ℝ P₀ z Complex.I) =
        B z * P₀ z := by
    intro z hz
    calc
      _ = (1 / 2 : ℝ) •
          (fderiv ℝ (ambientCauchyIntegral f) z 1 +
            Complex.I • fderiv ℝ (ambientCauchyIntegral f) z Complex.I) := by
        rw [hD z, hhalf]
      _ = f ⟨z, ball_subset_closedBall hz⟩ := hTdbar z hz
      _ = B z * P₀ z := by
        change B_s ⟨z, ball_subset_closedBall hz⟩ * P ⟨z, ball_subset_closedBall hz⟩ = _
        rw [hB_s, ← hP₀.1 ⟨z, ball_subset_closedBall hz⟩]
  let F : ℂ → V := fun z => (Ring.inverse (P₀ z)) (ξ z)
  have hInvReg : ContDiffOn ℝ 1 (fun z => Ring.inverse (P₀ z)) (ball 0 s) := by
    intro z hz
    obtain ⟨u, hu⟩ := hP₀.2 z (ball_subset_closedBall hz)
    have hi : ContDiffAt ℝ 1 Ring.inverse (P₀ z) := by
      rw [← hu]
      exact contDiffAt_ringInverse ℝ u
    exact (hi.comp z (hPReg.contDiffAt (isOpen_ball.mem_nhds hz))).contDiffWithinAt
  let T : (V →L[ℂ] V) →L[ℝ] (V →L[ℝ] V) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ V V ℝ ℝ).toContinuousLinearMap
  have hFReg : ContDiffOn ℝ 1 F (ball 0 s) :=
    (T.contDiff.comp_contDiffOn hInvReg).clm_apply (hξ.mono hinside)
  let U : Set ℂ := ball 0 s ∩ {z : ℂ | 0 < z.im}
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_lt continuous_const Complex.continuous_im)
  obtain ⟨hFhol, hfactor, _⟩ := analyticOnNhd_inverse_gauge_apply hU P₀ B ξ
    (hPReg.mono inter_subset_left) (hξ.mono (inter_subset_left.trans hinside))
    (fun z hz => hP₀.2 z (ball_subset_closedBall hz.1))
    (fun z hz => hPDE z hz.1) (fun z hz => hDE z (hinside hz.1) hz.2)
  have hFaxis : ∀ z ∈ ball (0 : ℂ) s, z.im = 0 → F z = 0 := by
    intro z hz hzim
    change (Ring.inverse (P₀ z)) (ξ z) = 0
    rw [hzero z (hinside hz) hzim, map_zero]
  have hFzero : ∀ z ∈ ball (0 : ℂ) (s / 2), 0 ≤ z.im → F z = 0 := by
    intro z hz hzim
    funext k
    exact eq_zero_on_upperHalfBall_of_contDiffOn hs
      (contDiffOn_pi.mp hFReg k) (differentiableOn_pi.mp hFhol.differentiableOn k)
      (fun w hw hwm => congrFun (hFaxis w hw hwm) k) z hz hzim
  let ρ : ℝ := min (s / 2) (R / 2)
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  refine ⟨ρ, hρ, lt_of_le_of_lt (min_le_right _ _) (by linarith), ?_⟩
  intro z hz hzim
  have hzhalf : z ∈ ball (0 : ℂ) (s / 2) := ball_subset_ball (min_le_left _ _) hz
  have hzs : z ∈ ball (0 : ℂ) s := ball_subset_ball (by linarith) hzhalf
  rcases eq_or_lt_of_le hzim with hzim | hzim
  · exact hzero z (hinside hzs) hzim.symm
  · calc
      ξ z = P₀ z (F z) := hfactor z ⟨hzs, hzim⟩
      _ = P₀ z 0 := congrArg (P₀ z) (hFzero z hzhalf hzim.le)
      _ = 0 := map_zero _

end DifferentialGeometry.Analysis
