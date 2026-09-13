import DifferentialGeometry.Analysis.Integration.Integral.CompactSupportDerivative
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.Module
import Mathlib.Analysis.InnerProductSpace.Laplacian

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal Convolution ContDiff
namespace DifferentialGeometry.Analysis

private theorem hasDerivAt_quadratic_boundary_kernel_integral
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ) {b : ℝ → F}
    (hb : Continuous b) (s : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => ∫ r : ℝ, (t / 2 * ρ ((s - r) / t)) • b r)
      (∫ r : ℝ, ((ρ ((s - r) / t) - (s - r) / t * deriv ρ ((s - r) / t)) / 2) • b r) t := by
  obtain ⟨R, hR, hRbound⟩ := hρc.isBounded.exists_pos_norm_le
  let T : ℝ := |t| + 1
  let S : Set ℝ := {p | p ≠ 0 ∧ |p| < T}
  have hS : IsOpen S := isOpen_ne.inter (isOpen_lt continuous_id.abs continuous_const)
  have hzero (p r : ℝ) (hp : p ∈ S) (hr : r ∉ closedBall s (T * R)) :
      ρ ((s - r) / p) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hle := hRbound _ hmem
    rw [norm_div, Real.norm_eq_abs] at hle
    have hmul : ‖s - r‖ ≤ R * |p| := (div_le_iff₀ (abs_pos.mpr hp.1)).mp hle
    apply hr
    rw [mem_closedBall, dist_comm, dist_eq_norm]
    exact hmul.trans (by nlinarith [hp.2])
  have hq : ContinuousOn (fun p : ℝ × ℝ => (s - p.2) / p.1) (S ×ˢ univ) :=
    (continuousOn_const.sub continuousOn_snd).div continuousOn_fst (fun p hp => hp.1.1)
  have hρd : Continuous (deriv ρ) := hρ.continuous_deriv_one
  apply hasDerivAt_integral_of_compact_support hS (isCompact_closedBall s (T * R))
    (f := fun t r => (t / 2 * ρ ((s - r) / t)) • b r)
    (f' := fun t r => ((ρ ((s - r) / t) - (s - r) / t * deriv ρ ((s - r) / t)) / 2) • b r)
  · intro p r hp hr
    rw [hzero p r hp hr, mul_zero, zero_smul]
  · exact ((continuousOn_fst.div_const 2).mul (hρ.continuous.comp_continuousOn hq)).smul
      (hb.comp continuous_snd).continuousOn
  · exact (((hρ.continuous.comp_continuousOn hq).sub
      (hq.mul (hρd.comp_continuousOn hq))).div_const 2).smul
      (hb.comp continuous_snd).continuousOn
  · intro p hp r
    have hdp : HasDerivAt (fun p : ℝ => (s - r) / p)
        (-(s - r) / p ^ 2) p := by
      have hdq := (hasDerivAt_const p (s - r)).div (hasDerivAt_id p) hp.1
      change HasDerivAt (fun p : ℝ => (s - r) / p) ((0 * p - (s - r) * 1) / p ^ 2) p at hdq
      simpa only [zero_mul, mul_one, zero_sub] using hdq
    have hdk := ((hasDerivAt_id p).div_const 2).mul
      ((hρ.differentiable one_ne_zero ((s - r) / p)).hasDerivAt.comp p hdp)
    have hp0 : p ≠ 0 := hp.1
    change HasDerivAt (fun p : ℝ => p / 2 * ρ ((s - r) / p))
      (1 / 2 * ρ ((s - r) / p) + p / 2 * (deriv ρ ((s - r) / p) * (-(s - r) / p ^ 2))) p at hdk
    have hcoeff : 1 / 2 * ρ ((s - r) / p) + p / 2 *
        (deriv ρ ((s - r) / p) * (-(s - r) / p ^ 2)) =
        (ρ ((s - r) / p) - (s - r) / p * deriv ρ ((s - r) / p)) / 2 := by
      field_simp [hp0]
      ring
    rw [hcoeff] at hdk
    exact hdk.smul_const (b r)
  · exact ⟨ht, by dsimp [T]; linarith⟩

private theorem integral_deriv_compact_kernel {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hc : HasCompactSupport ρ) : ∫ q, deriv ρ q = 0 := by
  exact integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => (hρ.differentiable one_ne_zero x).hasDerivAt)
    (hρ.continuous_deriv_one.integrable_of_hasCompactSupport hc.deriv)
    (hρ.continuous.integrable_of_hasCompactSupport hc)

private theorem integral_mul_deriv_compact_kernel {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hc : HasCompactSupport ρ) :
    (∫ q, q * deriv ρ q) = -(∫ q, ρ q) := by
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := id) (u' := fun _ => 1) (v := ρ) (v' := deriv ρ)
    (fun x _ => hasDerivAt_id x)
    (fun x _ => (hρ.differentiable one_ne_zero x).hasDerivAt)
    ((continuous_id.mul hρ.continuous_deriv_one).integrable_of_hasCompactSupport hc.deriv.mul_left)
    ((continuous_const.mul hρ.continuous).integrable_of_hasCompactSupport hc.mul_left)
    ((continuous_id.mul hρ.continuous).integrable_of_hasCompactSupport hc.mul_left)
  simpa using h

private theorem integral_sq_mul_deriv_deriv_compact_kernel {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hc : HasCompactSupport ρ) :
    (∫ q, q ^ 2 * deriv (deriv ρ) q) = 2 * ∫ q, ρ q := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hd : ContDiff ℝ 1 (deriv ρ) := (contDiff_succ_iff_deriv.mp hρ).2.2
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun q : ℝ => q ^ 2) (u' := fun q => 2 * q) (v := deriv ρ) (v' := deriv (deriv ρ))
    (fun x _ => by
      have hd := (hasDerivAt_id x).pow 2
      change HasDerivAt (fun q : ℝ => q ^ 2) (2 * x ^ 1 * 1) x at hd
      simpa only [pow_one, mul_one] using hd)
    (fun x _ => (hd.differentiable one_ne_zero x).hasDerivAt)
    (((continuous_id.pow 2).mul hd.continuous_deriv_one).integrable_of_hasCompactSupport hc.deriv.deriv.mul_left)
    (((continuous_const.mul continuous_id).mul hd.continuous).integrable_of_hasCompactSupport hc.deriv.mul_left)
    (((continuous_id.pow 2).mul hd.continuous).integrable_of_hasCompactSupport hc.deriv.mul_left)
  simpa only [mul_assoc, integral_const_mul, integral_mul_deriv_compact_kernel hρ1 hc, mul_neg, neg_neg] using h

private theorem integral_quadratic_laplacian_kernel {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hc : HasCompactSupport ρ) :
    (∫ q : ℝ, ((1 + q ^ 2) / 2) * deriv (deriv ρ) q) = ∫ q : ℝ, ρ q := by
  have hd : ContDiff ℝ 1 (deriv ρ) := (contDiff_succ_iff_deriv.mp hρ).2.2
  have hi : Integrable (deriv (deriv ρ)) volume := hd.continuous_deriv_one.integrable_of_hasCompactSupport hc.deriv.deriv
  have hiq : Integrable (fun q : ℝ => q ^ 2 * deriv (deriv ρ) q) volume := ((continuous_id.pow 2).mul hd.continuous_deriv_one).integrable_of_hasCompactSupport hc.deriv.deriv.mul_left
  have he (q : ℝ) : ((1 + q ^ 2) / 2) * deriv (deriv ρ) q =
      (1 / 2) * (deriv (deriv ρ) q + q ^ 2 * deriv (deriv ρ) q) := by ring
  simp_rw [he]
  rw [integral_const_mul, integral_add hi hiq, integral_deriv_compact_kernel hd hc.deriv,
    integral_sq_mul_deriv_deriv_compact_kernel hρ hc]
  ring

private theorem integral_comp_sub_mul_real {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (s t : ℝ) :
    (∫ q : ℝ, f (s - t * q)) = |t⁻¹| • ∫ r : ℝ, f r := by
  have h := Measure.integral_comp_mul_left (fun r => f (s - r)) t
  rwa [integral_sub_left_eq_self f volume s] at h

private theorem integral_scaled_kernel_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ℝ → ℝ) (b : ℝ → F) (s : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ r : ℝ, ρ ((s - r) / t) • b r) = t • ∫ q : ℝ, ρ q • b (s - t * q) := by
  have h := integral_comp_sub_mul_real (fun r => ρ ((s - r) / t) • b r) s t
  have he (q : ℝ) : (s - (s - t * q)) / t = q := by field_simp [ht.ne']; ring
  simp only [he, abs_of_pos (inv_pos.mpr ht)] at h
  rw [h, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]

private theorem hasDerivAt_integral_scaled_kernel
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ) {b : ℝ → F}
    (hb : Continuous b) (s t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ r : ℝ, ρ ((s - r) / t) • b r)
      (∫ r : ℝ, (deriv ρ ((s - r) / t) / t) • b r) s := by
  by_cases ht : t = 0
  · subst t
    simpa only [div_zero, zero_smul, integral_zero] using
      (hasDerivAt_const s (∫ r : ℝ, ρ 0 • b r))
  obtain ⟨R, hR, hRbound⟩ := hρc.isBounded.exists_pos_norm_le
  let B : ℝ := ‖s‖ + 1 + R * ‖t‖
  have hzero (p r : ℝ) (hp : p ∈ ball s 1) (hr : r ∉ closedBall 0 B) :
      ρ ((p - r) / t) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hle := hRbound _ hmem
    rw [norm_div] at hle
    have hmul : ‖p - r‖ ≤ R * ‖t‖ := (div_le_iff₀ (norm_pos_iff.mpr ht)).mp hle
    have hpbound : ‖p‖ < ‖s‖ + 1 := by
      rw [mem_ball, dist_eq_norm] at hp
      linarith [norm_sub_norm_le p s]
    have hrbound : ‖r‖ ≤ ‖p‖ + ‖p - r‖ := by
      calc
        ‖r‖ = ‖p - (p - r)‖ := by congr 1; ring
        _ ≤ ‖p‖ + ‖p - r‖ := norm_sub_le _ _
    apply hr
    rw [mem_closedBall, dist_zero_right]
    change ‖r‖ ≤ ‖s‖ + 1 + R * ‖t‖
    exact hrbound.trans (add_le_add hpbound.le hmul)
  have hq : Continuous (fun p : ℝ × ℝ => (p.1 - p.2) / t) := by fun_prop
  apply hasDerivAt_integral_of_compact_support (S := ball s 1) isOpen_ball (isCompact_closedBall 0 B)
    (f := fun s r => ρ ((s - r) / t) • b r)
    (f' := fun s r => (deriv ρ ((s - r) / t) / t) • b r)
  · intro p r hp hr
    rw [hzero p r hp hr, zero_smul]
  · exact ((hρ.continuous.comp hq).smul (hb.comp continuous_snd)).continuousOn
  · exact (((hρ.continuous_deriv_one.comp hq).div_const t).smul (hb.comp continuous_snd)).continuousOn
  · intro p hp r
    have hdp : HasDerivAt (fun s : ℝ => (s - r) / t) (1 / t) p :=
      ((hasDerivAt_id p).sub_const r).div_const t
    have h := ((hρ.differentiable one_ne_zero ((p - r) / t)).hasDerivAt.comp p hdp).smul_const (b r)
    change HasDerivAt (fun q : ℝ => ρ ((q - r) / t) • b r)
      ((deriv ρ ((p - r) / t) * (1 / t)) • b r) p at h
    simpa only [mul_one_div] using h
  · exact mem_ball_self (by norm_num)

private theorem holderWith_integral_comp_re_sub_im_mul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) {K α : ℝ≥0} (hH : HolderWith K α b) :
    HolderWith (K * (∫ q : ℝ, ‖ρ q‖ * (1 + ‖q‖) ^ (α : ℝ)).toNNReal) α
      (fun z : ℂ => ∫ q : ℝ, ρ q • b (z.re - z.im * q)) := by
  have hi (z : ℂ) : Integrable (fun q : ℝ => ρ q • b (z.re - z.im * q)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hρ.smul (hb.comp (continuous_const.sub (continuous_const.mul continuous_id)))
    · exact hc.smul_right
  have hw : Continuous (fun q : ℝ => ‖ρ q‖ * (1 + ‖q‖) ^ (α : ℝ)) := by
    apply hρ.norm.mul
    exact (continuous_const.add continuous_norm).rpow_const (fun _ => Or.inr α.coe_nonneg)
  have hwi : Integrable (fun q : ℝ => ‖ρ q‖ * (1 + ‖q‖) ^ (α : ℝ)) :=
    hw.integrable_of_hasCompactSupport hc.norm.mul_right
  have hnon : 0 ≤ ∫ q : ℝ, ‖ρ q‖ * (1 + ‖q‖) ^ (α : ℝ) :=
    integral_nonneg fun q => by positivity
  intro z w
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simp only [coe_nndist, NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal _ hnon]
  rw [dist_eq_norm, ← integral_sub (hi z) (hi w)]
  have hbound (q : ℝ) : ‖ρ q • b (z.re - z.im * q) - ρ q • b (w.re - w.im * q)‖ ≤
      (‖ρ q‖ * (1 + ‖q‖) ^ (α : ℝ)) * ((K : ℝ) * dist z w ^ (α : ℝ)) := by
    rw [← smul_sub, norm_smul]
    have hq : dist (z.re - z.im * q) (w.re - w.im * q) ≤ (1 + ‖q‖) * dist z w := by
      rw [Real.dist_eq, dist_eq_norm]
      have he : z.re - z.im * q - (w.re - w.im * q) = (z - w).re - (z - w).im * q := by
        simp only [Complex.sub_re, Complex.sub_im]
        ring
      rw [he]
      calc
        |(z - w).re - (z - w).im * q| ≤ |(z - w).re| + |(z - w).im * q| := abs_sub _ _
        _ = |(z - w).re| + |(z - w).im| * ‖q‖ := by rw [abs_mul, Real.norm_eq_abs]
        _ ≤ ‖z - w‖ + ‖z - w‖ * ‖q‖ := by
          exact add_le_add (Complex.abs_re_le_norm _)
            (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm _) (norm_nonneg _))
        _ = (1 + ‖q‖) * ‖z - w‖ := by ring
    have hh := hH.dist_le_of_le hq
    rw [dist_eq_norm] at hh
    calc
      ‖ρ q‖ * ‖b (z.re - z.im * q) - b (w.re - w.im * q)‖ ≤
          ‖ρ q‖ * ((K : ℝ) * ((1 + ‖q‖) * dist z w) ^ (α : ℝ)) :=
        mul_le_mul_of_nonneg_left hh (norm_nonneg _)
      _ = _ := by rw [Real.mul_rpow (by positivity) dist_nonneg]; ring
  calc
    ‖∫ q : ℝ, ρ q • b (z.re - z.im * q) - ρ q • b (w.re - w.im * q)‖ ≤
        ∫ q : ℝ, (‖ρ q‖ * (1 + ‖q‖) ^ (α : ℝ)) * ((K : ℝ) * dist z w ^ (α : ℝ)) :=
      norm_integral_le_of_norm_le (hwi.mul_const _) (Eventually.of_forall hbound)
    _ = _ := by rw [integral_mul_const]; ring

private theorem contDiffOn_integral_scaled_kernel
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞} {ρ : ℝ → ℝ} (hρ : ContDiff ℝ n ρ) (hc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : LocallyIntegrable b volume) :
    ContDiffOn ℝ n (fun z : ℂ => ∫ r : ℝ, ρ ((z.re - r) / z.im) • b r)
      {z : ℂ | z.im ≠ 0} := by
  obtain ⟨R, hR, hRbound⟩ := hc.isBounded.exists_pos_norm_le
  intro z hz
  let T : ℝ := |z.im| + 1
  let S : Set ℂ := {w | w.im ≠ 0 ∧ |w.im| < T}
  have hS : IsOpen S := (isOpen_ne.preimage Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im.abs continuous_const)
  have hzS : z ∈ S := ⟨hz, by dsimp [T]; linarith⟩
  have hzero (p : ℂ) (x : ℝ) (hp : p ∈ S) (hx : x ∉ closedBall 0 (T * R)) :
      ρ (x / p.im) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hle := hRbound _ hmem
    rw [norm_div, Real.norm_eq_abs] at hle
    have hmul : ‖x‖ ≤ R * |p.im| := (div_le_iff₀ (abs_pos.mpr hp.1)).mp hle
    apply hx
    rw [mem_closedBall, dist_zero_right]
    exact hmul.trans (by nlinarith [hp.2])
  have harg : ContDiffOn ℝ n (fun q : ℂ × ℝ => q.2 / q.1.im) (S ×ˢ univ) :=
    (contDiff_snd.contDiffOn : ContDiffOn ℝ n (fun q : ℂ × ℝ => q.2) (S ×ˢ univ)).div (Complex.imCLM.contDiff.comp contDiff_fst).contDiffOn (fun q hq => hq.1.1)
  have hg : ContDiffOn ℝ n (fun q : ℂ × ℝ => ρ (q.2 / q.1.im)) (S ×ˢ univ) :=
    hρ.comp_contDiffOn harg
  have h := contDiffOn_convolution_right_with_param_comp (μ := (volume : Measure ℝ))
    (ContinuousLinearMap.lsmul ℝ ℝ (E := F)).flip
    (v := fun p : ℂ => p.re) Complex.reCLM.contDiff.contDiffOn
    hS (isCompact_closedBall 0 (T * R)) hzero hb hg
  have he : (fun p : ℂ => (b ⋆[(ContinuousLinearMap.lsmul ℝ ℝ (E := F)).flip, volume]
      (fun r : ℝ => ρ (r / p.im))) p.re) =
      (fun p : ℂ => ∫ r : ℝ, ρ ((p.re - r) / p.im) • b r) := by
    rfl
  rw [he] at h
  exact ((h z hzS).contDiffAt (hS.mem_nhds hzS)).contDiffWithinAt

private theorem continuous_integral_comp_re_sub_im_mul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) :
    Continuous (fun z : ℂ => ∫ q : ℝ, ρ q • b (z.re - z.im * q)) := by
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support hc
  · apply Continuous.continuousOn
    exact (hρ.comp continuous_snd).smul (hb.comp
      ((Complex.continuous_re.comp continuous_fst).sub
        ((Complex.continuous_im.comp continuous_fst).mul continuous_snd)))
  · intro p q hp hq
    rw [image_eq_zero_of_notMem_tsupport hq, zero_smul]

def quadraticBoundaryLifting {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ℝ → ℝ) (b : ℝ → F) (z : ℂ) : F :=
  (z.im ^ 2 / 2) • ∫ q : ℝ, ρ q • b (z.re - z.im * q)

private theorem quadraticBoundaryLifting_of_im_pos
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ℝ → ℝ) (b : ℝ → F) {z : ℂ} (hz : 0 < z.im) :
    quadraticBoundaryLifting ρ b z =
      (z.im / 2) • ∫ r : ℝ, ρ ((z.re - r) / z.im) • b r := by
  rw [integral_scaled_kernel_eq ρ b z.re hz, smul_smul]
  unfold quadraticBoundaryLifting
  congr 1
  ring

theorem quadraticBoundaryLifting_real
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ℝ → ℝ) (b : ℝ → F) (s : ℝ) : quadraticBoundaryLifting ρ b (s : ℂ) = 0 := by
  simp [quadraticBoundaryLifting]

theorem contDiffOn_quadraticBoundaryLifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞} {ρ : ℝ → ℝ} (hρ : ContDiff ℝ n ρ) (hc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : LocallyIntegrable b volume) :
    ContDiffOn ℝ n (quadraticBoundaryLifting ρ b) {z : ℂ | 0 < z.im} := by
  have h := ((Complex.imCLM.contDiff.div_const 2).contDiffOn).smul
    ((contDiffOn_integral_scaled_kernel hρ hc hb).mono (fun z hz => ne_of_gt hz))
  exact h.congr (fun z hz => quadraticBoundaryLifting_of_im_pos ρ b hz)

theorem continuous_quadraticBoundaryLifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) :
    Continuous (quadraticBoundaryLifting ρ b) := by
  exact ((Complex.continuous_im.pow 2).div_const 2).smul
    (continuous_integral_comp_re_sub_im_mul hρ hc hb)

private theorem hasDerivAt_quadraticBoundaryLifting_normal
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ) {b : ℝ → F}
    (hb : Continuous b) (s : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => quadraticBoundaryLifting ρ b ⟨s, t⟩)
      ((t / 2) • ∫ q : ℝ, (ρ q - q * deriv ρ q) • b (s - t * q)) t := by
  have hd := hasDerivAt_quadratic_boundary_kernel_integral hρ hρc hb s ht.ne'
  have he : (∫ r : ℝ, ((ρ ((s - r) / t) - (s - r) / t * deriv ρ ((s - r) / t)) / 2) • b r) =
      (t / 2) • ∫ q : ℝ, (ρ q - q * deriv ρ q) • b (s - t * q) := by
    rw [integral_scaled_kernel_eq (fun q => (ρ q - q * deriv ρ q) / 2) b s ht]
    simp_rw [div_eq_inv_mul, mul_smul, integral_smul, smul_smul]
    congr 1
    ring
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with p hp
  rw [quadraticBoundaryLifting_of_im_pos ρ b (z := ⟨s, p⟩) hp, ← integral_smul]
  congr 1
  ext r
  exact (mul_smul (p / 2) (ρ ((s - r) / p)) (b r)).symm

private theorem hasDerivAt_quadraticBoundaryLifting_tangent
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ) {b : ℝ → F}
    (hb : Continuous b) (s : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => quadraticBoundaryLifting ρ b ⟨s, t⟩)
      ((t / 2) • ∫ q : ℝ, deriv ρ q • b (s - t * q)) s := by
  have hd := (hasDerivAt_integral_scaled_kernel hρ hρc hb s t).const_smul (t / 2)
  have he : (t / 2) • (∫ r : ℝ, (deriv ρ ((s - r) / t) / t) • b r) =
      (t / 2) • ∫ q : ℝ, deriv ρ q • b (s - t * q) := by
    rw [integral_scaled_kernel_eq (fun q => deriv ρ q / t) b s ht]
    simp_rw [div_eq_inv_mul, mul_smul, integral_smul, smul_smul]
    congr 1
    field_simp [ht.ne']
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  exact Eventually.of_forall fun p => quadraticBoundaryLifting_of_im_pos ρ b ht

private def quadraticBoundaryLiftingDerivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ℝ → ℝ) (b : ℝ → F) (z : ℂ) : ℂ →L[ℝ] F :=
  Complex.reCLM.smulRight ((z.im / 2) • ∫ q : ℝ, deriv ρ q • b (z.re - z.im * q)) +
    Complex.imCLM.smulRight ((z.im / 2) • ∫ q : ℝ, (ρ q - q * deriv ρ q) • b (z.re - z.im * q))

private theorem fderiv_quadraticBoundaryLifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) {z : ℂ} (hz : 0 < z.im) :
    fderiv ℝ (quadraticBoundaryLifting ρ b) z = quadraticBoundaryLiftingDerivative ρ b z := by
  have hdiff := ((contDiffOn_quadraticBoundaryLifting hρ hρc hb.locallyIntegrable z hz).contDiffAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)).differentiableAt one_ne_zero
  have hlineS : HasDerivAt (fun r : ℝ => (⟨r, z.im⟩ : ℂ)) 1 z.re := by
    have he : (fun r : ℝ => (⟨r, z.im⟩ : ℂ)) = (fun r : ℝ => (r : ℂ) + (z.im : ℂ) * Complex.I) := by
      funext r
      apply Complex.ext <;> simp
    rw [he]
    have h := (Complex.ofRealCLM.hasDerivAt (x := z.re)).add_const ((z.im : ℂ) * Complex.I)
    change HasDerivAt (fun r : ℝ => (r : ℂ) + (z.im : ℂ) * Complex.I) (Complex.ofRealCLM 1) z.re at h
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using h
  have hlineT : HasDerivAt (fun r : ℝ => (⟨z.re, r⟩ : ℂ)) Complex.I z.im := by
    have he : (fun r : ℝ => (⟨z.re, r⟩ : ℂ)) = (fun r : ℝ => (z.re : ℂ) + (r : ℂ) * Complex.I) := by
      funext r
      apply Complex.ext <;> simp
    rw [he]
    have h := ((Complex.ofRealCLM.hasDerivAt (x := z.im)).mul_const Complex.I).const_add (z.re : ℂ)
    change HasDerivAt (fun r : ℝ => (z.re : ℂ) + (r : ℂ) * Complex.I) (Complex.ofRealCLM 1 * Complex.I) z.im at h
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using h
  have hds : HasDerivAt (fun r : ℝ => quadraticBoundaryLifting ρ b ⟨r, z.im⟩)
      (fderiv ℝ (quadraticBoundaryLifting ρ b) z 1) z.re := by
    have h := HasFDerivAt.comp_hasDerivAt (l := quadraticBoundaryLifting ρ b)
      (l' := fderiv ℝ (quadraticBoundaryLifting ρ b) z) (f := fun r : ℝ => (⟨r, z.im⟩ : ℂ))
      z.re hdiff.hasFDerivAt hlineS
    change HasDerivAt (fun r : ℝ => quadraticBoundaryLifting ρ b ⟨r, z.im⟩)
      (fderiv ℝ (quadraticBoundaryLifting ρ b) z 1) z.re at h
    exact h
  have hdt : HasDerivAt (fun r : ℝ => quadraticBoundaryLifting ρ b ⟨z.re, r⟩)
      (fderiv ℝ (quadraticBoundaryLifting ρ b) z Complex.I) z.im := by
    have h := HasFDerivAt.comp_hasDerivAt (l := quadraticBoundaryLifting ρ b)
      (l' := fderiv ℝ (quadraticBoundaryLifting ρ b) z) (f := fun r : ℝ => (⟨z.re, r⟩ : ℂ))
      z.im hdiff.hasFDerivAt hlineT
    change HasDerivAt (fun r : ℝ => quadraticBoundaryLifting ρ b ⟨z.re, r⟩)
      (fderiv ℝ (quadraticBoundaryLifting ρ b) z Complex.I) z.im at h
    exact h
  have hs := hds.unique (hasDerivAt_quadraticBoundaryLifting_tangent hρ hρc hb z.re hz)
  have ht := hdt.unique (hasDerivAt_quadraticBoundaryLifting_normal hρ hρc hb z.re hz)
  apply ContinuousLinearMap.ext
  intro v
  have he : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simp only [Complex.real_smul, mul_one, Complex.re_add_im]
  calc
    fderiv ℝ (quadraticBoundaryLifting ρ b) z v =
        v.re • fderiv ℝ (quadraticBoundaryLifting ρ b) z 1 +
          v.im • fderiv ℝ (quadraticBoundaryLifting ρ b) z Complex.I := by
      conv_lhs => rw [he]
      rw [map_add, map_smul, map_smul]
    _ = quadraticBoundaryLiftingDerivative ρ b z v := by
      rw [hs, ht]
      rfl

private theorem continuous_quadraticBoundaryLiftingDerivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ) (hc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) :
    Continuous (quadraticBoundaryLiftingDerivative ρ b) := by
  have hs := continuous_integral_comp_re_sub_im_mul hρ.continuous_deriv_one hc.deriv hb
  have ht := continuous_integral_comp_re_sub_im_mul
    (hρ.continuous.sub (continuous_id.mul hρ.continuous_deriv_one)) (hc.sub hc.deriv.mul_left) hb
  exact (((ContinuousLinearMap.smulRightL ℝ ℂ F) Complex.reCLM).continuous.comp
    ((Complex.continuous_im.div_const 2).smul hs)).add
    (((ContinuousLinearMap.smulRightL ℝ ℂ F) Complex.imCLM).continuous.comp
      ((Complex.continuous_im.div_const 2).smul ht))

private theorem hasFDerivWithinAt_quadraticBoundaryLifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) (z : ℂ) :
    HasFDerivWithinAt (quadraticBoundaryLifting ρ b) (quadraticBoundaryLiftingDerivative ρ b z)
      {w : ℂ | 0 ≤ w.im} z := by
  have hs : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  rw [← Complex.closure_setOfPred_lt_im]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    ((contDiffOn_quadraticBoundaryLifting hρ hρc hb.locallyIntegrable).differentiableOn one_ne_zero)
    (convex_halfSpace_im_gt 0) hs
    (fun w _ => (continuous_quadraticBoundaryLifting hρ.continuous hρc hb).continuousWithinAt)
  apply (tendsto_congr' (show fderiv ℝ (quadraticBoundaryLifting ρ b) =ᶠ[𝓝[{w : ℂ | 0 < w.im}] z]
    quadraticBoundaryLiftingDerivative ρ b from ?_)).mpr
    ((continuous_quadraticBoundaryLiftingDerivative hρ hρc hb).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with w hw using fderiv_quadraticBoundaryLifting hρ hρc hb hw

theorem contDiffOn_one_quadraticBoundaryLifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) :
    ContDiffOn ℝ 1 (quadraticBoundaryLifting ρ b) {z : ℂ | 0 ≤ z.im} := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt (by simp : (0 : ℕ∞ω) ≠ ∞)]
  intro z hz
  refine ⟨{z : ℂ | 0 ≤ z.im}, ?_, by simp, quadraticBoundaryLiftingDerivative ρ b, ?_, ?_⟩
  · simpa only [insert_eq_of_mem hz] using
      (self_mem_nhdsWithin : {z : ℂ | 0 ≤ z.im} ∈ 𝓝[{z : ℂ | 0 ≤ z.im}] z)
  · intro w hw
    exact hasFDerivWithinAt_quadraticBoundaryLifting hρ hρc hb w
  · exact contDiffOn_zero.mpr (continuous_quadraticBoundaryLiftingDerivative hρ hρc hb).continuousOn

theorem hasFDerivWithinAt_zero_quadraticBoundaryLifting_real
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) (s : ℝ) :
    HasFDerivWithinAt (quadraticBoundaryLifting ρ b) (0 : ℂ →L[ℝ] F) {z : ℂ | 0 ≤ z.im} (s : ℂ) := by
  simpa only [quadraticBoundaryLiftingDerivative, Complex.ofReal_im, zero_div, zero_smul,
    ContinuousLinearMap.smulRight_zero, add_zero] using
    hasFDerivWithinAt_quadraticBoundaryLifting hρ hρc hb (s : ℂ)

private theorem hasFDerivAt_linear_boundary_average
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) {z : ℂ} (hz : 0 < z.im) :
    HasFDerivAt (fun w : ℂ => (w.im / 2) • ∫ q : ℝ, ρ q • b (w.re - w.im * q))
      (Complex.reCLM.smulRight ((1 / 2 : ℝ) • ∫ q : ℝ, deriv ρ q • b (z.re - z.im * q)) +
        Complex.imCLM.smulRight ((-1 / 2 : ℝ) • ∫ q : ℝ, (q * deriv ρ q) • b (z.re - z.im * q))) z := by
  have hQ : HasFDerivAt (quadraticBoundaryLifting ρ b) (quadraticBoundaryLiftingDerivative ρ b z) z := by
    rw [← fderiv_quadraticBoundaryLifting hρ hρc hb hz]
    exact (((contDiffOn_quadraticBoundaryLifting hρ hρc hb.locallyIntegrable) z hz).contDiffAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)).differentiableAt one_ne_zero |>.hasFDerivAt
  have hi := (hasDerivAt_inv hz.ne').comp_hasFDerivAt z Complex.imCLM.hasFDerivAt
  have hd := hi.smul hQ
  have hB : Continuous (fun q : ℝ => b (z.re - z.im * q)) := by fun_prop
  have hi0 : Integrable (fun q : ℝ => ρ q • b (z.re - z.im * q)) :=
    (hρ.continuous.smul hB).integrable_of_hasCompactSupport hρc.smul_right
  have hiq : Integrable (fun q : ℝ => (q * deriv ρ q) • b (z.re - z.im * q)) :=
    ((continuous_id.mul hρ.continuous_deriv_one).smul hB).integrable_of_hasCompactSupport hρc.deriv.mul_left.smul_right
  have hsub : (∫ q : ℝ, (ρ q - q * deriv ρ q) • b (z.re - z.im * q)) =
      (∫ q : ℝ, ρ q • b (z.re - z.im * q)) - (∫ q : ℝ, (q * deriv ρ q) • b (z.re - z.im * q)) := by
    simp_rw [sub_smul]
    exact integral_sub hi0 hiq
  have he : z.im⁻¹ • quadraticBoundaryLiftingDerivative ρ b z +
      ((-(z.im ^ 2)⁻¹) • Complex.imCLM).smulRight (quadraticBoundaryLifting ρ b z) =
      Complex.reCLM.smulRight ((1 / 2 : ℝ) • ∫ q : ℝ, deriv ρ q • b (z.re - z.im * q)) +
        Complex.imCLM.smulRight ((-1 / 2 : ℝ) • ∫ q : ℝ, (q * deriv ρ q) • b (z.re - z.im * q)) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [quadraticBoundaryLiftingDerivative, quadraticBoundaryLifting,
      add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.imCLM_apply,
      smul_eq_mul, hsub, smul_add, smul_sub, smul_smul]
    have h1 : z.im⁻¹ * (v.re * (z.im / 2)) = v.re * (1 / 2) := by field_simp [hz.ne']
    have h2 : z.im⁻¹ * (v.im * (z.im / 2)) = v.im * (1 / 2) := by field_simp [hz.ne']
    have h3 : (-(z.im ^ 2)⁻¹ * v.im) * (z.im ^ 2 / 2) = -(v.im * (1 / 2)) := by field_simp [hz.ne']
    rw [h1, h2, h3]
    module
  change HasFDerivAt (fun w : ℂ => w.im⁻¹ • quadraticBoundaryLifting ρ b w)
    (z.im⁻¹ • quadraticBoundaryLiftingDerivative ρ b z +
      ((-(z.im ^ 2)⁻¹) • Complex.imCLM).smulRight (quadraticBoundaryLifting ρ b z)) z at hd
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
  unfold quadraticBoundaryLifting
  rw [smul_smul]
  congr 1
  field_simp [ne_of_gt hw]

private def quadraticBoundaryLiftingHessian
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ℝ → ℝ) (b : ℝ → F) (z : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] F :=
  Complex.reCLM.smulRight
    (Complex.reCLM.smulRight ((1 / 2 : ℝ) • ∫ q : ℝ, deriv (deriv ρ) q • b (z.re - z.im * q)) +
      Complex.imCLM.smulRight ((-1 / 2 : ℝ) • ∫ q : ℝ, (q * deriv (deriv ρ) q) • b (z.re - z.im * q))) +
    Complex.imCLM.smulRight
      (Complex.reCLM.smulRight ((-1 / 2 : ℝ) • ∫ q : ℝ, (q * deriv (deriv ρ) q) • b (z.re - z.im * q)) +
        Complex.imCLM.smulRight ((1 / 2 : ℝ) • ∫ q : ℝ, (q ^ 2 * deriv (deriv ρ) q) • b (z.re - z.im * q)))

private theorem hasFDerivAt_quadraticBoundaryLiftingDerivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) {z : ℂ} (hz : 0 < z.im) :
    HasFDerivAt (quadraticBoundaryLiftingDerivative ρ b) (quadraticBoundaryLiftingHessian ρ b z) z := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hρd : ContDiff ℝ 1 (deriv ρ) := (contDiff_succ_iff_deriv.mp hρ).2.2
  let k : ℝ → ℝ := fun q => ρ q - q * deriv ρ q
  have hk : ContDiff ℝ 1 k := hρ1.sub (contDiff_id.mul hρd)
  have hkc : HasCompactSupport k := hρc.sub hρc.deriv.mul_left
  have hdk : deriv k = fun q : ℝ => -(q * deriv (deriv ρ) q) := by
    funext q
    have h := (hρ1.differentiable one_ne_zero q).hasDerivAt.sub
      ((hasDerivAt_id q).mul (hρd.differentiable one_ne_zero q).hasDerivAt)
    change HasDerivAt k (deriv ρ q - (1 * deriv ρ q + q * deriv (deriv ρ) q)) q at h
    rw [h.deriv]
    ring
  have hs := hasFDerivAt_linear_boundary_average hρd hρc.deriv hb hz
  have ht := hasFDerivAt_linear_boundary_average hk hkc hb hz
  rw [hdk] at ht
  have heq (q : ℝ) : q * -(q * deriv (deriv ρ) q) = -(q ^ 2 * deriv (deriv ρ) q) := by ring
  simp_rw [heq, neg_smul, integral_neg, smul_neg, neg_div, neg_smul, neg_neg] at ht
  let A := (ContinuousLinearMap.smulRightL ℝ ℂ F) Complex.reCLM
  let B := (ContinuousLinearMap.smulRightL ℝ ℂ F) Complex.imCLM
  have hd := (A.hasFDerivAt.comp z hs).add (B.hasFDerivAt.comp z ht)
  change HasFDerivAt (quadraticBoundaryLiftingDerivative ρ b)
    (A.comp (Complex.reCLM.smulRight ((1 / 2 : ℝ) • ∫ q : ℝ, deriv (deriv ρ) q • b (z.re - z.im * q)) +
      Complex.imCLM.smulRight ((-1 / 2 : ℝ) • ∫ q : ℝ, (q * deriv (deriv ρ) q) • b (z.re - z.im * q))) +
    B.comp (Complex.reCLM.smulRight (-((1 / 2 : ℝ) • ∫ q : ℝ, (q * deriv (deriv ρ) q) • b (z.re - z.im * q))) +
      Complex.imCLM.smulRight ((1 / 2 : ℝ) • ∫ q : ℝ, (q ^ 2 * deriv (deriv ρ) q) • b (z.re - z.im * q)))) z at hd
  convert hd using 1
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [quadraticBoundaryLiftingHessian, A, B, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  module

private theorem continuous_quadraticBoundaryLiftingHessian
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) : Continuous (quadraticBoundaryLiftingHessian ρ b) := by
  have hρd : ContDiff ℝ 1 (deriv ρ) := (contDiff_succ_iff_deriv.mp hρ).2.2
  have h0 := (continuous_const (y := (1 / 2 : ℝ))).smul (continuous_integral_comp_re_sub_im_mul
    hρd.continuous_deriv_one hc.deriv.deriv hb)
  have h1 := (continuous_const (y := (-1 / 2 : ℝ))).smul (continuous_integral_comp_re_sub_im_mul
    (continuous_id.mul hρd.continuous_deriv_one) hc.deriv.deriv.mul_left hb)
  have h2 := (continuous_const (y := (1 / 2 : ℝ))).smul (continuous_integral_comp_re_sub_im_mul
    ((continuous_id.pow 2).mul hρd.continuous_deriv_one) hc.deriv.deriv.mul_left hb)
  exact (((ContinuousLinearMap.smulRightL ℝ ℂ (ℂ →L[ℝ] F)) Complex.reCLM).continuous.comp
      ((((ContinuousLinearMap.smulRightL ℝ ℂ F) Complex.reCLM).continuous.comp h0).add
        (((ContinuousLinearMap.smulRightL ℝ ℂ F) Complex.imCLM).continuous.comp h1))).add
    (((ContinuousLinearMap.smulRightL ℝ ℂ (ℂ →L[ℝ] F)) Complex.imCLM).continuous.comp
      ((((ContinuousLinearMap.smulRightL ℝ ℂ F) Complex.reCLM).continuous.comp h1).add
        (((ContinuousLinearMap.smulRightL ℝ ℂ F) Complex.imCLM).continuous.comp h2)))

private theorem hasFDerivWithinAt_quadraticBoundaryLiftingDerivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) (z : ℂ) :
    HasFDerivWithinAt (quadraticBoundaryLiftingDerivative ρ b) (quadraticBoundaryLiftingHessian ρ b z)
      {w : ℂ | 0 ≤ w.im} z := by
  have hs : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  rw [← Complex.closure_setOfPred_lt_im]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun w hw => (hasFDerivAt_quadraticBoundaryLiftingDerivative hρ hρc hb hw).differentiableAt.differentiableWithinAt)
    (convex_halfSpace_im_gt 0) hs
    (fun w _ => (continuous_quadraticBoundaryLiftingDerivative hρ1 hρc hb).continuousWithinAt)
  apply (tendsto_congr' (show fderiv ℝ (quadraticBoundaryLiftingDerivative ρ b) =ᶠ[𝓝[{w : ℂ | 0 < w.im}] z]
    quadraticBoundaryLiftingHessian ρ b from ?_)).mpr
    ((continuous_quadraticBoundaryLiftingHessian hρ hρc hb).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with w hw using
    (hasFDerivAt_quadraticBoundaryLiftingDerivative hρ hρc hb hw).fderiv

private theorem contDiffOn_one_quadraticBoundaryLiftingDerivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) :
    ContDiffOn ℝ 1 (quadraticBoundaryLiftingDerivative ρ b) {z : ℂ | 0 ≤ z.im} := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt (by simp : (0 : ℕ∞ω) ≠ ∞)]
  intro z hz
  refine ⟨{z : ℂ | 0 ≤ z.im}, ?_, by simp, quadraticBoundaryLiftingHessian ρ b, ?_, ?_⟩
  · simpa only [insert_eq_of_mem hz] using
      (self_mem_nhdsWithin : {z : ℂ | 0 ≤ z.im} ∈ 𝓝[{z : ℂ | 0 ≤ z.im}] z)
  · intro w hw
    exact hasFDerivWithinAt_quadraticBoundaryLiftingDerivative hρ hρc hb w
  · exact contDiffOn_zero.mpr (continuous_quadraticBoundaryLiftingHessian hρ hρc hb).continuousOn

theorem contDiffOn_two_quadraticBoundaryLifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) :
    ContDiffOn ℝ 2 (quadraticBoundaryLifting ρ b) {z : ℂ | 0 ≤ z.im} := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt (by simp : (1 : ℕ∞ω) ≠ ∞)]
  intro z hz
  refine ⟨{z : ℂ | 0 ≤ z.im}, ?_, by simp, quadraticBoundaryLiftingDerivative ρ b, ?_, ?_⟩
  · simpa only [insert_eq_of_mem hz] using
      (self_mem_nhdsWithin : {z : ℂ | 0 ≤ z.im} ∈ 𝓝[{z : ℂ | 0 ≤ z.im}] z)
  · intro w hw
    exact hasFDerivWithinAt_quadraticBoundaryLifting (hρ.of_le (by norm_num)) hρc hb w
  · exact contDiffOn_one_quadraticBoundaryLiftingDerivative hρ hρc hb

private theorem quadraticBoundaryLiftingHessian_real
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hc : HasCompactSupport ρ)
    (b : ℝ → F) (s : ℝ) :
    quadraticBoundaryLiftingHessian ρ b (s : ℂ) =
      Complex.imCLM.smulRight (Complex.imCLM.smulRight ((∫ q : ℝ, ρ q) • b s)) := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hd : ContDiff ℝ 1 (deriv ρ) := (contDiff_succ_iff_deriv.mp hρ).2.2
  have he : (1 / 2 : ℝ) * (2 * ∫ q : ℝ, ρ q) = ∫ q : ℝ, ρ q := by ring
  simp only [quadraticBoundaryLiftingHessian, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    integral_smul_const, integral_deriv_compact_kernel hd hc.deriv,
    integral_mul_deriv_compact_kernel hd hc.deriv, integral_deriv_compact_kernel hρ1 hc,
    integral_sq_mul_deriv_deriv_compact_kernel hρ hc, neg_zero, zero_smul, smul_zero,
    ContinuousLinearMap.smulRight_zero, zero_add, add_zero, smul_smul, he]

private theorem uniqueDiffOn_nonneg_im : UniqueDiffOn ℝ {z : ℂ | 0 ≤ z.im} := by
  apply uniqueDiffOn_convex (convex_halfSpace_im_ge 0)
  refine ⟨Complex.I, mem_interior_iff_mem_nhds.mpr ?_⟩
  have hH : {z : ℂ | 0 < z.im} ∈ 𝓝 Complex.I :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simp)
  exact mem_of_superset hH (fun z hz => (show 0 ≤ z.im from hz.le))

private theorem fderivWithin_fderivWithin_quadraticBoundaryLifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) {z : ℂ} (hz : 0 ≤ z.im) :
    fderivWithin ℝ (fderivWithin ℝ (quadraticBoundaryLifting ρ b) {w : ℂ | 0 ≤ w.im})
      {w : ℂ | 0 ≤ w.im} z = quadraticBoundaryLiftingHessian ρ b z := by
  have he : EqOn (fderivWithin ℝ (quadraticBoundaryLifting ρ b) {w : ℂ | 0 ≤ w.im})
      (quadraticBoundaryLiftingDerivative ρ b) {w : ℂ | 0 ≤ w.im} := by
    intro w hw
    exact (hasFDerivWithinAt_quadraticBoundaryLifting (hρ.of_le (by norm_num)) hρc hb w).fderivWithin
      (uniqueDiffOn_nonneg_im w hw)
  rw [fderivWithin_congr' he hz]
  exact (hasFDerivWithinAt_quadraticBoundaryLiftingDerivative hρ hρc hb z).fderivWithin
    (uniqueDiffOn_nonneg_im z hz)

theorem fderivWithin_two_quadraticBoundaryLifting_real
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) (s : ℝ) :
    fderivWithin ℝ (fderivWithin ℝ (quadraticBoundaryLifting ρ b) {w : ℂ | 0 ≤ w.im})
      {w : ℂ | 0 ≤ w.im} (s : ℂ) =
      Complex.imCLM.smulRight (Complex.imCLM.smulRight ((∫ q : ℝ, ρ q) • b s)) := by
  rw [fderivWithin_fderivWithin_quadraticBoundaryLifting hρ hρc hb
    (by simp : 0 ≤ (s : ℂ).im), quadraticBoundaryLiftingHessian_real hρ hρc]

theorem laplacianWithin_quadraticBoundaryLifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) {z : ℂ} (hz : 0 ≤ z.im) :
    InnerProductSpace.laplacianWithin (quadraticBoundaryLifting ρ b) {w : ℂ | 0 ≤ w.im} z =
      ∫ q : ℝ, (((1 + q ^ 2) / 2) * deriv (deriv ρ) q) • b (z.re - z.im * q) := by
  rw [InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_complexPlane _ uniqueDiffOn_nonneg_im hz]
  simp only [iteratedFDerivWithin_two_apply _ uniqueDiffOn_nonneg_im hz,
    fderivWithin_fderivWithin_quadraticBoundaryLifting hρ hρc hb hz,
    quadraticBoundaryLiftingHessian, add_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    one_smul, zero_smul, zero_add, add_zero]
  have hd : ContDiff ℝ 1 (deriv ρ) := (contDiff_succ_iff_deriv.mp hρ).2.2
  have hB : Continuous (fun q : ℝ => b (z.re - z.im * q)) := by fun_prop
  have h0 : Integrable (fun q : ℝ => deriv (deriv ρ) q • b (z.re - z.im * q)) :=
    (hd.continuous_deriv_one.smul hB).integrable_of_hasCompactSupport hρc.deriv.deriv.smul_right
  have h2 : Integrable (fun q : ℝ => (q ^ 2 * deriv (deriv ρ) q) • b (z.re - z.im * q)) :=
    (((continuous_id.pow 2).mul hd.continuous_deriv_one).smul hB).integrable_of_hasCompactSupport hρc.deriv.deriv.mul_left.smul_right
  rw [← smul_add, ← integral_add h0 h2, ← integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun q => by
    dsimp only
    rw [← add_smul, smul_smul]
    congr 1
    ring

theorem laplacianWithin_quadraticBoundaryLifting_real
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) (s : ℝ) :
    InnerProductSpace.laplacianWithin (quadraticBoundaryLifting ρ b) {w : ℂ | 0 ≤ w.im} (s : ℂ) =
      (∫ q : ℝ, ρ q) • b s := by
  rw [laplacianWithin_quadraticBoundaryLifting hρ hρc hb (by simp : 0 ≤ (s : ℂ).im)]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, integral_smul_const,
    integral_quadratic_laplacian_kernel hρ hρc]

private theorem holderWith_clm_comp
    {X E F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {f : X → E} {K α : ℝ≥0} (hf : HolderWith K α f) :
    HolderWith (‖L‖₊ * K) α (fun x => L (f x)) := by
  simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul, Function.comp_def] using
    L.lipschitz.holderWith.comp hf

private theorem exists_holderWith_quadraticBoundaryLiftingHessian
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) {K α : ℝ≥0} (hH : HolderWith K α b) :
    ∃ C : ℝ≥0, HolderWith C α (quadraticBoundaryLiftingHessian ρ b) := by
  have hd : ContDiff ℝ 1 (deriv ρ) := (contDiff_succ_iff_deriv.mp hρ).2.2
  have h0 := (holderWith_integral_comp_re_sub_im_mul hd.continuous_deriv_one hc.deriv.deriv hb hH).smul (1 / 2 : ℝ)
  have h1 := (holderWith_integral_comp_re_sub_im_mul
    (continuous_id.mul hd.continuous_deriv_one) hc.deriv.deriv.mul_left hb hH).smul (-1 / 2 : ℝ)
  have h2 := (holderWith_integral_comp_re_sub_im_mul
    ((continuous_id.pow 2).mul hd.continuous_deriv_one) hc.deriv.deriv.mul_left hb hH).smul (1 / 2 : ℝ)
  let A := (ContinuousLinearMap.smulRightL ℝ ℂ F) Complex.reCLM
  let B := (ContinuousLinearMap.smulRightL ℝ ℂ F) Complex.imCLM
  let A' := (ContinuousLinearMap.smulRightL ℝ ℂ (ℂ →L[ℝ] F)) Complex.reCLM
  let B' := (ContinuousLinearMap.smulRightL ℝ ℂ (ℂ →L[ℝ] F)) Complex.imCLM
  have hs := (holderWith_clm_comp A h0).add (holderWith_clm_comp B h1)
  have ht := (holderWith_clm_comp A h1).add (holderWith_clm_comp B h2)
  have hs' := holderWith_clm_comp (X := ℂ) (E := ℂ →L[ℝ] F)
    (F := ℂ →L[ℝ] ℂ →L[ℝ] F) A' hs
  have ht' := holderWith_clm_comp (X := ℂ) (E := ℂ →L[ℝ] F)
    (F := ℂ →L[ℝ] ℂ →L[ℝ] F) B' ht
  have h := hs'.add ht'
  exact ⟨_, h⟩

theorem exists_holderOnWith_fderivWithin_two_quadraticBoundaryLifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b)
    {K α : ℝ≥0} (hH : HolderWith K α b) :
    ∃ C : ℝ≥0, HolderOnWith C α
      (fderivWithin ℝ (fderivWithin ℝ (quadraticBoundaryLifting ρ b) {w : ℂ | 0 ≤ w.im})
        {w : ℂ | 0 ≤ w.im}) {w : ℂ | 0 ≤ w.im} := by
  obtain ⟨C, hC⟩ := exists_holderWith_quadraticBoundaryLiftingHessian hρ hρc hb hH
  refine ⟨C, ?_⟩
  intro z hz w hw
  rw [fderivWithin_fderivWithin_quadraticBoundaryLifting hρ hρc hb hz,
    fderivWithin_fderivWithin_quadraticBoundaryLifting hρ hρc hb hw]
  exact hC z w

theorem exists_holderOnWith_laplacianWithin_quadraticBoundaryLifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) {K α : ℝ≥0} (hH : HolderWith K α b) :
    ∃ C : ℝ≥0, HolderOnWith C α
      (InnerProductSpace.laplacianWithin (quadraticBoundaryLifting ρ b) {w : ℂ | 0 ≤ w.im})
      {w : ℂ | 0 ≤ w.im} := by
  have hd : ContDiff ℝ 1 (deriv ρ) := (contDiff_succ_iff_deriv.mp hρ).2.2
  have hk : Continuous (fun q : ℝ => ((1 + q ^ 2) / 2) * deriv (deriv ρ) q) :=
    ((continuous_const.add (continuous_id.pow 2)).div_const 2).mul hd.continuous_deriv_one
  have h := holderWith_integral_comp_re_sub_im_mul hk hρc.deriv.deriv.mul_left hb hH
  refine ⟨K * (∫ q : ℝ, ‖((1 + q ^ 2) / 2) * deriv (deriv ρ) q‖ *
    (1 + ‖q‖) ^ (α : ℝ)).toNNReal, ?_⟩
  intro z hz w hw
  rw [laplacianWithin_quadraticBoundaryLifting hρ hρc hb hz,
    laplacianWithin_quadraticBoundaryLifting hρ hρc hb hw]
  exact h z w

end DifferentialGeometry.Analysis
