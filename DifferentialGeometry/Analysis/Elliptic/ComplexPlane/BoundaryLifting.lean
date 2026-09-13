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
import DifferentialGeometry.Analysis.Schauder.Holder.CompactRegularity
import DifferentialGeometry.Analysis.Schauder.Holder.Localization
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LaplacianCalculus
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Gradient

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

theorem hasCompactSupport_smul_quadraticBoundaryLifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ ζ : ℝ → ℝ} (hρ : HasCompactSupport ρ) (hζ : HasCompactSupport ζ)
    {b : ℝ → F} (hb : HasCompactSupport b) :
    HasCompactSupport (fun z : ℂ => ζ z.im • quadraticBoundaryLifting ρ b z) := by
  obtain ⟨R, hR, hRbound⟩ := hρ.isBounded.exists_pos_norm_le
  obtain ⟨T, hT, hTbound⟩ := hζ.isBounded.exists_pos_norm_le
  obtain ⟨A, hA, hAbound⟩ := hb.isBounded.exists_pos_norm_le
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (A + T * R + T))
  intro z hz
  by_cases hζz : ζ z.im = 0
  · rw [hζz, zero_smul]
  have ht : |z.im| ≤ T := hTbound _ (subset_tsupport _ hζz)
  have hi : (∫ q : ℝ, ρ q • b (z.re - z.im * q)) = 0 := by
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun q => by
      change ρ q • b (z.re - z.im * q) = 0
      by_cases hρq : ρ q = 0
      · rw [hρq, zero_smul]
      have hq : |q| ≤ R := hRbound _ (subset_tsupport _ hρq)
      have hbq : b (z.re - z.im * q) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have hr : |z.re - z.im * q| ≤ A := hAbound _ hmem
        have hs : |z.re| ≤ A + T * R := by
          calc
            |z.re| = |(z.re - z.im * q) + z.im * q| := by congr 1; ring
            _ ≤ |z.re - z.im * q| + |z.im * q| := by
              simpa only [Real.norm_eq_abs] using norm_add_le (z.re - z.im * q) (z.im * q)
            _ ≤ A + T * R := add_le_add hr (by
              rw [abs_mul]
              exact mul_le_mul ht hq (abs_nonneg _) hT.le)
        apply hz
        rw [mem_closedBall, dist_zero_right]
        exact (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hs ht)
      rw [hbq, smul_zero]
  simp only [quadraticBoundaryLifting, hi, smul_zero]

private theorem contDiffOn_two_laplacian_trace_lifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {b : ℝ → F} (hb : Continuous b) (hc : HasCompactSupport b)
    (η : ContDiffBump (0 : ℝ)) :
    let L : ℂ → F := fun z => η z.im • quadraticBoundaryLifting (η.normed volume) b z
    HasCompactSupport L ∧
      ContDiffOn ℝ 2 L {z : ℂ | 0 ≤ z.im} ∧
      ContDiffOn ℝ ∞ L {z : ℂ | 0 < z.im} ∧
      ∀ s : ℝ, L (s : ℂ) = 0 ∧
        HasFDerivWithinAt L (0 : ℂ →L[ℝ] F) {z : ℂ | 0 ≤ z.im} (s : ℂ) ∧
        InnerProductSpace.laplacianWithin L {z : ℂ | 0 ≤ z.im} (s : ℂ) = b s := by
  let ρ : ℝ → ℝ := η.normed volume
  let L : ℂ → F := fun z => η z.im • quadraticBoundaryLifting ρ b z
  have hL : HasCompactSupport L :=
    hasCompactSupport_smul_quadraticBoundaryLifting η.hasCompactSupport_normed η.hasCompactSupport hc
  have hC2 : ContDiffOn ℝ 2 L {z : ℂ | 0 ≤ z.im} :=
    (η.contDiff.comp Complex.imCLM.contDiff).contDiffOn.smul
      (contDiffOn_two_quadraticBoundaryLifting η.contDiff_normed η.hasCompactSupport_normed hb)
  have hCinf : ContDiffOn ℝ ∞ L {z : ℂ | 0 < z.im} :=
    (η.contDiff.comp Complex.imCLM.contDiff).contDiffOn.smul
      (contDiffOn_quadraticBoundaryLifting η.contDiff_normed η.hasCompactSupport_normed hb.locallyIntegrable)
  refine ⟨hL, hC2, hCinf, ?_⟩
  intro s
  have he : L =ᶠ[𝓝 (s : ℂ)] quadraticBoundaryLifting ρ b := by
    have ht : Tendsto Complex.im (𝓝 (s : ℂ)) (𝓝 0) := by
      simpa only [Complex.ofReal_im] using Complex.continuous_im.continuousAt.tendsto (x := (s : ℂ))
    filter_upwards [ht.eventually η.eventuallyEq_one] with z hz
    change η z.im = (1 : ℝ) at hz
    change η z.im • quadraticBoundaryLifting ρ b z = quadraticBoundaryLifting ρ b z
    rw [hz, one_smul]
  have hew : L =ᶠ[𝓝[{z : ℂ | 0 ≤ z.im}] (s : ℂ)] quadraticBoundaryLifting ρ b :=
    he.filter_mono nhdsWithin_le_nhds
  refine ⟨?_, ?_, ?_⟩
  · change L (s : ℂ) = 0
    rw [he.eq_of_nhds, quadraticBoundaryLifting_real]
  · exact (hasFDerivWithinAt_zero_quadraticBoundaryLifting_real η.contDiff_normed
      η.hasCompactSupport_normed hb s).congr_of_eventuallyEq hew he.eq_of_nhds
  · change InnerProductSpace.laplacianWithin L {z : ℂ | 0 ≤ z.im} (s : ℂ) = b s
    rw [(InnerProductSpace.laplacianWithin_congr_nhdsWithin hew uniqueDiffOn_nonneg_im).eq_of_nhdsWithin
      (by simp : (s : ℂ) ∈ {z : ℂ | 0 ≤ z.im}),
      laplacianWithin_quadraticBoundaryLifting_real η.contDiff_normed η.hasCompactSupport_normed hb s]
    rw [show (∫ q : ℝ, ρ q) = 1 from η.integral_normed, one_smul]

theorem exists_contDiffOn_two_laplacian_trace_lifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {b : ℝ → F} (hb : Continuous b) (hc : HasCompactSupport b) :
    ∃ L : ℂ → F, HasCompactSupport L ∧
      ContDiffOn ℝ 2 L {z : ℂ | 0 ≤ z.im} ∧
      ContDiffOn ℝ ∞ L {z : ℂ | 0 < z.im} ∧
      ∀ s : ℝ, L (s : ℂ) = 0 ∧
        HasFDerivWithinAt L (0 : ℂ →L[ℝ] F) {z : ℂ | 0 ≤ z.im} (s : ℂ) ∧
        InnerProductSpace.laplacianWithin L {z : ℂ | 0 ≤ z.im} (s : ℂ) = b s := by
  exact ⟨_, contDiffOn_two_laplacian_trace_lifting hb hc
    (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ))⟩

private theorem exists_holderWith_smul_comp_im_of_norm_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    {f : ℂ → F} {N K α : ℝ≥0} (hf : HolderWith K α f)
    (hN : ∀ z, ‖f z‖ ≤ N) (hα : α ≤ 1) :
    ∃ C : ℝ≥0, HolderWith C α (fun z : ℂ => a z.im • f z) := by
  obtain ⟨M, A, hM, hA⟩ := Schauder.exists_norm_bound_and_holderWith_of_contDiff_hasCompactSupport ha hc hα
  have hp : HolderWith (A * ‖Complex.imCLM‖₊ ^ (α : ℝ)) α (fun z : ℂ => a z.im) := by
    simpa only [mul_one, Function.comp_def, Complex.imCLM_apply] using
      hA.comp Complex.imCLM.lipschitz.holderWith
  have h := Schauder.holderWith_smul_of_norm_le hp hf (fun z => hM z.im) hN
  exact ⟨_, h⟩

private theorem norm_integral_comp_re_sub_im_mul_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ)
    {b : ℝ → F} {M : ℝ} (hM : ∀ x, ‖b x‖ ≤ M) (z : ℂ) :
    ‖∫ q : ℝ, ρ q • b (z.re - z.im * q)‖ ≤ (∫ q : ℝ, ‖ρ q‖) * M := by
  have hi : Integrable (fun q : ℝ => ‖ρ q‖) volume :=
    hρ.norm.integrable_of_hasCompactSupport hc.norm
  calc
    ‖∫ q : ℝ, ρ q • b (z.re - z.im * q)‖ ≤ ∫ q : ℝ, ‖ρ q‖ * M := by
      apply norm_integral_le_of_norm_le (hi.mul_const M)
      exact Eventually.of_forall fun q => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
    _ = _ := integral_mul_const M (fun q : ℝ => ‖ρ q‖)

private theorem exists_holderWith_weighted_boundary_average
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a ρ : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hac : HasCompactSupport a)
    (hρ : Continuous ρ) (hc : HasCompactSupport ρ)
    {b : ℝ → F} (hb : Continuous b) (hbc : HasCompactSupport b)
    {K α : ℝ≥0} (hH : HolderWith K α b) (hα : α ≤ 1) :
    ∃ C : ℝ≥0, HolderWith C α
      (fun z : ℂ => a z.im • ∫ q : ℝ, ρ q • b (z.re - z.im * q)) := by
  obtain ⟨B, hB⟩ := hbc.exists_bound_of_continuous hb
  have hA := holderWith_integral_comp_re_sub_im_mul hρ hc hb hH
  have hN (z : ℂ) : ‖∫ q : ℝ, ρ q • b (z.re - z.im * q)‖ ≤
      ((∫ q : ℝ, ‖ρ q‖) * max B 0).toNNReal :=
    (norm_integral_comp_re_sub_im_mul_le hρ hc
      (fun x => (hB x).trans (le_max_left _ _)) z).trans (Real.le_coe_toNNReal _)
  exact exists_holderWith_smul_comp_im_of_norm_le ha hac hA hN hα

private def boundaryLiftingLaplacian
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ ζ : ℝ → ℝ) (b : ℝ → F) (z : ℂ) : F :=
  ζ z.im • (∫ q : ℝ, (((1 + q ^ 2) / 2) * deriv (deriv ρ) q) • b (z.re - z.im * q)) +
    (z.im * deriv ζ z.im) • (∫ q : ℝ, (ρ q - q * deriv ρ q) • b (z.re - z.im * q)) +
    (z.im ^ 2 / 2 * deriv (deriv ζ) z.im) • (∫ q : ℝ, ρ q • b (z.re - z.im * q))

private theorem exists_holderWith_boundaryLiftingLaplacian
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ ζ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ)
    (hζ : ContDiff ℝ 3 ζ) (hζc : HasCompactSupport ζ)
    {b : ℝ → F} (hb : Continuous b) (hbc : HasCompactSupport b)
    {K α : ℝ≥0} (hH : HolderWith K α b) (hα : α ≤ 1) :
    ∃ C : ℝ≥0, HolderWith C α (boundaryLiftingLaplacian ρ ζ b) := by
  have hρd : ContDiff ℝ 1 (deriv ρ) := (contDiff_succ_iff_deriv.mp hρ).2.2
  have hζd : ContDiff ℝ 2 (deriv ζ) := (contDiff_succ_iff_deriv.mp hζ).2.2
  have hζdd : ContDiff ℝ 1 (deriv (deriv ζ)) := (contDiff_succ_iff_deriv.mp hζd).2.2
  obtain ⟨C0, h0⟩ := exists_holderWith_weighted_boundary_average
    (hζ.of_le (by norm_num)) hζc
    (((continuous_const.add (continuous_id.pow 2)).div_const 2).mul hρd.continuous_deriv_one)
    hρc.deriv.deriv.mul_left hb hbc hH hα
  obtain ⟨C1, h1⟩ := exists_holderWith_weighted_boundary_average
    (contDiff_id.mul (hζd.of_le (by norm_num))) hζc.deriv.mul_left
    (hρ.continuous.sub (continuous_id.mul hρd.continuous))
    (hρc.sub hρc.deriv.mul_left) hb hbc hH hα
  obtain ⟨C2, h2⟩ := exists_holderWith_weighted_boundary_average
    (((contDiff_id.pow 2).div_const 2).mul hζdd) hζc.deriv.deriv.mul_left
    hρ.continuous hρc hb hbc hH hα
  exact ⟨C0 + C1 + C2, (h0.add h1).add h2⟩

private theorem laplacian_comp_im
    {ζ : ℝ → ℝ} (hζ : ContDiff ℝ 2 ζ) (z : ℂ) :
    Laplacian.laplacian (fun w : ℂ => ζ w.im) z = deriv (deriv ζ) z.im := by
  have hi : fderiv ℝ Complex.im = fun _ : ℂ => Complex.imCLM := by
    funext w
    exact Complex.imCLM.fderiv
  have hzero : Laplacian.laplacian Complex.im z = 0 := by
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
      iteratedFDeriv_two_apply, hi, fderiv_const_apply, zero_apply, add_zero]
  have h := laplacian_comp_scalar (f := Complex.im) (φ := ζ)
    Complex.imCLM.contDiff.contDiffAt (hζ.contDiffAt (x := z.im))
  simpa only [Function.comp_def, hzero, hi, Complex.imCLM_apply, Complex.one_im,
    Complex.I_im, zero_pow (by norm_num : (2 : ℕ) ≠ 0), one_pow, zero_add,
    mul_zero, mul_one] using h

private theorem gradient_comp_im
    {ζ : ℝ → ℝ} (hζ : Differentiable ℝ ζ) (z : ℂ) :
    gradient (fun w : ℂ => ζ w.im) z = deriv ζ z.im • Complex.I := by
  have hd := (hζ z.im).hasDerivAt.comp_hasFDerivAt z Complex.imCLM.hasFDerivAt
  change HasFDerivAt (fun w : ℂ => ζ w.im) (deriv ζ z.im • Complex.imCLM) z at hd
  apply Complex.ext
  · simp only [gradient_complex_re, hd.fderiv, smul_apply, Complex.imCLM_apply,
      Complex.one_im, smul_eq_mul, mul_zero, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      zero_mul, zero_sub, neg_zero]
  · simp only [gradient_complex_im, hd.fderiv, smul_apply, Complex.imCLM_apply,
      Complex.I_im, smul_eq_mul, mul_one, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, zero_mul, add_zero]

private theorem laplacian_smul_quadraticBoundaryLifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ ζ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ)
    (hζ : ContDiff ℝ 2 ζ) {b : ℝ → F} (hb : Continuous b) {z : ℂ} (hz : 0 < z.im) :
    Laplacian.laplacian (fun w : ℂ => ζ w.im • quadraticBoundaryLifting ρ b w) z =
      boundaryLiftingLaplacian ρ ζ b z := by
  have hQ : ContDiffAt ℝ 2 (quadraticBoundaryLifting ρ b) z :=
    (contDiffOn_quadraticBoundaryLifting hρ hρc hb.locallyIntegrable z hz).contDiffAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
  have he : InnerProductSpace.laplacianWithin (quadraticBoundaryLifting ρ b)
      {w : ℂ | 0 ≤ w.im} z = Laplacian.laplacian (quadraticBoundaryLifting ρ b) z := by
    rw [InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_complexPlane _ uniqueDiffOn_nonneg_im hz.le,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_nonneg_im hQ hz.le]
  have hΔ := (laplacianWithin_quadraticBoundaryLifting hρ hρc hb hz.le)
  rw [he] at hΔ
  have hζi : ContDiffAt ℝ 2 (fun w : ℂ => ζ w.im) z :=
    (hζ.comp Complex.imCLM.contDiff).contDiffAt
  rw [hζi.laplacian_fun_smul hQ,
    hΔ, gradient_comp_im (hζ.differentiable (by norm_num)), laplacian_comp_im hζ,
    fderiv_quadraticBoundaryLifting (hρ.of_le (by norm_num)) hρc hb hz]
  simp only [quadraticBoundaryLiftingDerivative, quadraticBoundaryLifting,
    boundaryLiftingLaplacian, add_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub,
    add_zero, smul_smul]
  module

theorem exists_holderOnWith_laplacianWithin_lifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {b : ℝ → F} (hb : Continuous b) (hc : HasCompactSupport b)
    {K α : ℝ≥0} (hH : HolderWith K α b) (hα : α ≤ 1) :
    ∃ L : ℂ → F, HasCompactSupport L ∧
      ContDiffOn ℝ 2 L {z : ℂ | 0 ≤ z.im} ∧
      ContDiffOn ℝ ∞ L {z : ℂ | 0 < z.im} ∧
      (∀ s : ℝ, L (s : ℂ) = 0 ∧
        HasFDerivWithinAt L (0 : ℂ →L[ℝ] F) {z : ℂ | 0 ≤ z.im} (s : ℂ) ∧
        InnerProductSpace.laplacianWithin L {z : ℂ | 0 ≤ z.im} (s : ℂ) = b s) ∧
      ∃ C : ℝ≥0, HolderOnWith C α
        (InnerProductSpace.laplacianWithin L {z : ℂ | 0 ≤ z.im}) {z : ℂ | 0 ≤ z.im} := by
  let η : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let ρ : ℝ → ℝ := η.normed volume
  let L : ℂ → F := fun z => η z.im • quadraticBoundaryLifting ρ b z
  obtain ⟨hL, hC2, hCinf, hjet⟩ := contDiffOn_two_laplacian_trace_lifting hb hc η
  obtain ⟨C, hG⟩ := exists_holderWith_boundaryLiftingLaplacian (ρ := ρ) (ζ := (η : ℝ → ℝ))
    η.contDiff_normed η.hasCompactSupport_normed η.contDiff η.hasCompactSupport hb hc hH hα
  refine ⟨L, hL, hC2, hCinf, hjet, C, ?_⟩
  have heq : EqOn (InnerProductSpace.laplacianWithin L {z : ℂ | 0 ≤ z.im})
      (boundaryLiftingLaplacian ρ (η : ℝ → ℝ) b) {z : ℂ | 0 ≤ z.im} := by
    intro z hz
    change 0 ≤ z.im at hz
    rcases hz.eq_or_lt with hz0 | hzpos
    · have he : (z.re : ℂ) = z := by
        apply Complex.ext
        · rfl
        · exact hz0
      rw [← he, (hjet z.re).2.2]
      have hη0 : η (0 : ℝ) = 1 := η.eventuallyEq_one.eq_of_nhds
      simp only [boundaryLiftingLaplacian, Complex.ofReal_im, Complex.ofReal_re,
        zero_mul, sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div,
        zero_smul, add_zero, hη0, one_smul, integral_smul_const]
      rw [integral_quadratic_laplacian_kernel η.contDiff_normed η.hasCompactSupport_normed,
        η.integral_normed, one_smul]
    · have hLc : ContDiffAt ℝ 2 L z :=
        hC2.contDiffAt (mem_of_superset
          ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzpos)
          (fun w hw => (show 0 < w.im from hw).le))
      rw [InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_complexPlane _ uniqueDiffOn_nonneg_im hz]
      simp only [iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_nonneg_im hLc hz]
      rw [← congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane L) z]
      exact laplacian_smul_quadraticBoundaryLifting η.contDiff_normed
        η.hasCompactSupport_normed η.contDiff hb hzpos
  intro z hz w hw
  rw [heq hz, heq hw]
  exact hG z w

end DifferentialGeometry.Analysis
