import DifferentialGeometry.Analysis.Elliptic.Planar.FirstOrderReduction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.TietzeExtension
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Interval

namespace DifferentialGeometry.Analysis

private def polarCircle (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

private theorem smooth_polarCircle : ContDiff ℝ ∞ polarCircle :=
  Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)

private theorem deriv_polarCircle (θ : ℝ) :
    HasDerivAt polarCircle (Complex.I * polarCircle θ) θ := by
  change HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) _ θ
  simpa [polarCircle, mul_comm] using
    (((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I).cexp

private theorem norm_polarCircle (θ : ℝ) : ‖polarCircle θ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

private theorem polarCircle_periodic : Function.Periodic polarCircle (2 * Real.pi) := by
  intro θ
  simpa only [polarCircle, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat] using
    Complex.exp_mul_I_periodic (θ : ℂ)

private theorem exists_continuous_extension_complex {s : Set ℂ} (hs : IsClosed s)
    {b : ℂ → ℂ} (hb : ContinuousOn b s) :
    ∃ B : ℂ → ℂ, Continuous B ∧ EqOn B b s := by
  let : TietzeExtension ℂ :=
    TietzeExtension.of_homeo Complex.equivRealProdCLM.toHomeomorph
  obtain ⟨B, hB⟩ :=
    (⟨fun z : s => b z, hb.domRestrict⟩ : C(s, ℂ)).exists_restrict_eq hs
  refine ⟨B, B.continuous, ?_⟩
  intro z hz
  exact congrArg (fun f : C(s, ℂ) => f ⟨z, hz⟩) hB

private def polarIntegral (a : ℂ) (k : ℕ) (B : ℂ → ℂ) (p : ℝ × ℝ) : ℝ :=
  2 * ∫ t in (0 : ℝ)..1,
    t ^ k * (polarCircle p.2 ^ (k + 1) * B (a + (t * p.1) • polarCircle p.2)).re

private theorem continuous_polarIntegral (a : ℂ) (k : ℕ) {B : ℂ → ℂ}
    (hB : Continuous B) : Continuous (polarIntegral a k B) := by
  have hc := smooth_polarCircle.continuous
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  change Continuous (fun p : (ℝ × ℝ) × ℝ =>
    p.2 ^ k * (polarCircle p.1.2 ^ (k + 1) *
      B (a + (p.2 * p.1.1) • polarCircle p.1.2)).re)
  fun_prop

private theorem polarIntegral_zero (a : ℂ) (k : ℕ) (B : ℂ → ℂ) (θ : ℝ) :
    polarIntegral a k B (0, θ) =
      (2 / ((k + 1 : ℕ) : ℝ)) * (B a * polarCircle θ ^ (k + 1)).re := by
  simp only [polarIntegral, mul_zero, zero_smul, add_zero]
  rw [intervalIntegral.integral_mul_const, integral_pow]
  simp only [one_pow, Nat.cast_add, Nat.cast_one, zero_pow (Nat.succ_ne_zero k), sub_zero]
  rw [mul_comm (polarCircle θ ^ (k + 1)) (B a)]
  ring

private theorem polarIntegral_periodic (a : ℂ) (k : ℕ) (B : ℂ → ℂ) (r : ℝ) :
    Function.Periodic (fun θ => polarIntegral a k B (r, θ)) (2 * Real.pi) := by
  intro θ
  simp only [polarIntegral, polarCircle_periodic θ]

private theorem polar_segment_mem {a : ℂ} {ε r t : ℝ} (hr : r ∈ Ico 0 ε) (ht : t ∈ Icc 0 1) (θ : ℝ) :
    a + (t * r) • polarCircle θ ∈ closedBall a ε := by
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
    norm_polarCircle, mul_one, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.1 hr.1)]
  calc t * r ≤ 1 * r := mul_le_mul_of_nonneg_right ht.2 hr.1
    _ ≤ ε := by simpa using hr.2.le

private theorem polar_radial_identity {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ}
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v Ω) (hva : v a = 0)
    (k : ℕ) {B : ℂ → ℂ} (hB : Continuous B)
    {ε : ℝ} (hball : closedBall a ε ⊆ Ω)
    (hDv : ∀ z ∈ closedBall a ε, ∀ w : ℂ,
      fderiv ℝ v z w = 2 * (w * ((z - a) ^ k * B z)).re)
    {r : ℝ} (hr : r ∈ Ico 0 ε) (θ : ℝ) :
    v (a + r • polarCircle θ) = r ^ (k + 1) * polarIntegral a k B (r, θ) := by
  have hderiv (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt (fun s : ℝ => v (a + (s * r) • polarCircle θ))
        (r ^ (k + 1) * (2 * (t ^ k *
          (polarCircle θ ^ (k + 1) * B (a + (t * r) • polarCircle θ)).re))) t := by
    have hz := polar_segment_mem (a := a) hr ht θ
    have hd := ((hv _ (hball hz)).contDiffAt (hΩ.mem_nhds (hball hz))).differentiableAt
      (by norm_num)
    have hp : HasDerivAt (fun s : ℝ => a + (s * r) • polarCircle θ)
        (r • polarCircle θ) t := by
      simpa using (((hasDerivAt_id t).mul_const r).smul_const (polarCircle θ)).const_add a
    convert hd.hasFDerivAt.comp_hasDerivAt t hp using 1 <;> try rfl
    rw [hDv _ hz]
    simp [add_sub_cancel_left, Complex.real_smul, mul_pow, ← Complex.ofReal_pow, pow_succ,
      Complex.mul_re, Complex.mul_im]
    ring
  have hint : IntervalIntegrable (fun t : ℝ => r ^ (k + 1) * (2 *
      (t ^ k * (polarCircle θ ^ (k + 1) * B (a + (t * r) • polarCircle θ)).re))) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable 0 1
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hderiv t (by simpa using ht)) hint
  simp only [one_mul, zero_mul, zero_smul, add_zero, hva, sub_zero] at hh
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hh
  exact hh.symm


private theorem polar_data_on_ball {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ}
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v Ω) (hva : v a = 0)
    (k : ℕ) {B : ℂ → ℂ} (hB : Continuous B)
    {ε : ℝ} (hball : closedBall a ε ⊆ Ω)
    (hDv : ∀ z ∈ closedBall a ε, ∀ w : ℂ,
      fderiv ℝ v z w = 2 * (w * ((z - a) ^ k * B z)).re) :
    ∃ W A R : (ℝ × ℝ) → ℝ,
      ContinuousOn W (Ico 0 ε ×ˢ univ) ∧
      ContDiffOn ℝ 1 W (Ioo 0 ε ×ˢ univ) ∧
      (∀ r ∈ Ico 0 ε, ∀ θ, v (a + r • polarCircle θ) = r ^ (k + 1) * W (r, θ)) ∧
      (∀ θ, W (0, θ) = (2 / ((k + 1 : ℕ) : ℝ)) * (B a * polarCircle θ ^ (k + 1)).re) ∧
      ContinuousOn A (Ico 0 ε ×ˢ univ) ∧
      (∀ r ∈ Ico 0 ε, ∀ θ, HasDerivAt (fun t => W (r, t)) (A (r, θ)) θ) ∧
      (∀ θ, A (0, θ) = 2 * (Complex.I * B a * polarCircle θ ^ (k + 1)).re) ∧
      (∀ r ∈ Ioo 0 ε, ∀ θ, A (r, θ) =
        2 * ((Complex.I * polarCircle θ ^ (k + 1)) * B (a + r • polarCircle θ)).re) ∧
      ContinuousOn R (Ico 0 ε ×ˢ univ) ∧
      (∀ θ, R (0, θ) = 0) ∧
      (∀ r ∈ Ioo 0 ε, ∀ θ, R (r, θ) = r * fderiv ℝ W (r, θ) (1, 0)) ∧
      (∀ r ∈ Ico 0 ε, Function.Periodic (fun θ => W (r, θ)) (2 * Real.pi)) := by
  let W := polarIntegral a k B
  let A : (ℝ × ℝ) → ℝ := fun p =>
    2 * ((Complex.I * polarCircle p.2 ^ (k + 1)) * B (a + p.1 • polarCircle p.2)).re
  let R : (ℝ × ℝ) → ℝ := fun p =>
    2 * (polarCircle p.2 ^ (k + 1) * B (a + p.1 • polarCircle p.2)).re -
      ((k + 1 : ℕ) : ℝ) * W p
  have hc := smooth_polarCircle
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => a + p.1 • polarCircle p.2) := by fun_prop
  have hmem {r : ℝ} (hr : r ∈ Ico 0 ε) (θ : ℝ) :
      a + r • polarCircle θ ∈ closedBall a ε := by
    simpa using polar_segment_mem (a := a) hr (show (1 : ℝ) ∈ Icc 0 1 by simp) θ
  have hfactor {r : ℝ} (hr : r ∈ Ico 0 ε) (θ : ℝ) :=
    polar_radial_identity hΩ hv hva k hB hball hDv hr θ
  have hWq (p : ℝ × ℝ) (hp : p ∈ Ioo 0 ε ×ˢ (univ : Set ℝ)) :
      W p = v (a + p.1 • polarCircle p.2) / p.1 ^ (k + 1) := by
    apply (eq_div_iff (pow_ne_zero _ hp.1.1.ne')).2
    simpa only [mul_comm] using (hfactor ⟨hp.1.1.le, hp.1.2⟩ p.2).symm
  have hW : ContDiffOn ℝ 1 W (Ioo 0 ε ×ˢ (univ : Set ℝ)) := by
    have hcomp : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => v (a + p.1 • polarCircle p.2))
        (Ioo 0 ε ×ˢ (univ : Set ℝ)) := hv.comp (hmap.of_le (by simp)).contDiffOn
      (fun p hp => hball (hmem ⟨hp.1.1.le, hp.1.2⟩ p.2))
    have hh := hcomp.div (contDiffOn_fst.pow (k + 1))
      (fun p hp => pow_ne_zero _ hp.1.1.ne')
    exact hh.congr (fun p hp => hWq p hp)
  have hWc : Continuous W := continuous_polarIntegral a k hB
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hRc : Continuous R := by dsimp [R]; fun_prop
  have hzero (θ : ℝ) : W (0, θ) =
      (2 / ((k + 1 : ℕ) : ℝ)) * (B a * polarCircle θ ^ (k + 1)).re :=
    polarIntegral_zero a k B θ
  have hn : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hangular (r : ℝ) (hr : r ∈ Ico 0 ε) (θ : ℝ) :
      HasDerivAt (fun t => W (r, t)) (A (r, θ)) θ := by
    by_cases hr0 : r = 0
    · subst r
      have hd := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ
        (((deriv_polarCircle θ).pow (k + 1)).const_mul (B a))).const_mul
          (2 / ((k + 1 : ℕ) : ℝ))
      have heq : (fun t => W (0, t)) =
          (fun t => (2 / ((k + 1 : ℕ) : ℝ)) * (B a * polarCircle t ^ (k + 1)).re) :=
        funext hzero
      rw [heq]
      convert hd using 1 <;> try rfl
      simp [A, pow_succ, Complex.mul_re, Complex.mul_im]
      field_simp
      ring
    · have hp : (r, θ) ∈ Ioo 0 ε ×ˢ (univ : Set ℝ) :=
        ⟨⟨lt_of_le_of_ne hr.1 (Ne.symm hr0), hr.2⟩, mem_univ θ⟩
      have hdv := ((hv _ (hball (hmem hr θ))).contDiffAt
        (hΩ.mem_nhds (hball (hmem hr θ)))).differentiableAt (by norm_num)
      have harg : HasDerivAt (fun t : ℝ => a + r • polarCircle t)
          (r • (Complex.I * polarCircle θ)) θ :=
        ((deriv_polarCircle θ).const_smul r).const_add a
      have hd := (hdv.hasFDerivAt.comp_hasDerivAt θ harg).div_const (r ^ (k + 1))
      have hdeq : fderiv ℝ v (a + r • polarCircle θ)
          (r • (Complex.I * polarCircle θ)) / r ^ (k + 1) = A (r, θ) := by
        apply (div_eq_iff (pow_ne_zero _ hr0)).2
        rw [hDv _ (hmem hr θ)]
        dsimp [A]
        simp [add_sub_cancel_left, mul_pow, ← Complex.ofReal_pow,
          pow_succ, Complex.mul_re, Complex.mul_im]
        ring
      rw [hdeq] at hd
      exact hd.congr_of_eventuallyEq (Eventually.of_forall
        (fun t => hWq (r, t) ⟨hp.1, mem_univ t⟩))
  have hRzero (θ : ℝ) : R (0, θ) = 0 := by
    simp only [R, zero_smul, add_zero]
    rw [hzero]
    rw [mul_comm (polarCircle θ ^ (k + 1)) (B a)]
    field_simp
    ring
  have hradial (r : ℝ) (hr : r ∈ Ioo 0 ε) (θ : ℝ) :
      R (r, θ) = r * fderiv ℝ W (r, θ) (1, 0) := by
    have hp : (r, θ) ∈ Ioo 0 ε ×ˢ (univ : Set ℝ) := ⟨hr, mem_univ θ⟩
    have hWd := ((hW _ hp).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt
      (by norm_num)
    have hpair : HasDerivAt (fun s : ℝ => (s, θ)) (1, 0) r :=
      (hasDerivAt_id r).prodMk (hasDerivAt_const r θ)
    have hdW := hWd.hasFDerivAt.comp_hasDerivAt r hpair
    have hdprod := ((hasDerivAt_id r).pow (k + 1)).mul hdW
    have hdv := ((hv _ (hball (hmem ⟨hr.1.le, hr.2⟩ θ))).contDiffAt
      (hΩ.mem_nhds (hball (hmem ⟨hr.1.le, hr.2⟩ θ)))).differentiableAt (by norm_num)
    have hd := hdv.hasFDerivAt.comp_hasDerivAt r
      (((hasDerivAt_id r).smul_const (polarCircle θ)).const_add a)
    have hevent : (fun s : ℝ => v (a + s • polarCircle θ)) =ᶠ[𝓝 r]
        (fun s : ℝ => s ^ (k + 1) * W (s, θ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
      exact hfactor ⟨hs.1.le, hs.2⟩ θ
    have heq := hd.unique (hdprod.congr_of_eventuallyEq hevent)
    simp only [Nat.add_sub_cancel, mul_one, one_smul, Function.comp_apply,
      id_eq, Pi.pow_apply] at heq
    rw [hDv _ (hmem ⟨hr.1.le, hr.2⟩ θ)] at heq
    have halg : 2 * (polarCircle θ *
        ((a + r • polarCircle θ - a) ^ k * B (a + r • polarCircle θ))).re =
        r ^ k * (2 * (polarCircle θ ^ (k + 1) * B (a + r • polarCircle θ)).re) := by
      simp [add_sub_cancel_left, Complex.real_smul, mul_pow, ← Complex.ofReal_pow,
        pow_succ, Complex.mul_re, Complex.mul_im]
      ring
    rw [halg, show r ^ (k + 1) = r ^ k * r from pow_succ r k] at heq
    have heq' : 2 * (polarCircle θ ^ (k + 1) * B (a + r • polarCircle θ)).re =
        ((k + 1 : ℕ) : ℝ) * W (r, θ) + r * fderiv ℝ W (r, θ) (1, 0) := by
      apply (mul_left_cancel₀ (pow_ne_zero k hr.1.ne'))
      convert heq using 1
      ring
    change 2 * (polarCircle θ ^ (k + 1) * B (a + r • polarCircle θ)).re -
      ((k + 1 : ℕ) : ℝ) * W (r, θ) = r * fderiv ℝ W (r, θ) (1, 0)
    linarith
  refine ⟨W, A, R, hWc.continuousOn, hW, (fun r hr θ => hfactor hr θ), hzero, hAc.continuousOn,
    hangular, ?_, ?_, hRc.continuousOn, hRzero, hradial, ?_⟩
  · intro θ
    simp [A, mul_comm, mul_left_comm, mul_assoc]
  · intro r _ θ
    rfl
  · intro r _
    exact polarIntegral_periodic a k B r


private theorem exists_polar_data_of_fderiv_factor {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {a : ℂ} (ha : a ∈ Ω) {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v Ω)
    (hva : v a = 0) (k : ℕ) {b : ℂ → ℂ} (hb : ContinuousOn b Ω)
    (hDv : ∀ z ∈ Ω, ∀ w : ℂ,
      fderiv ℝ v z w = 2 * (w * ((z - a) ^ k * b z)).re) :
    ∃ ε > 0, closedBall a ε ⊆ Ω ∧ ∃ W A R : (ℝ × ℝ) → ℝ,
      ContinuousOn W (Ico 0 ε ×ˢ univ) ∧
      ContDiffOn ℝ 1 W (Ioo 0 ε ×ˢ univ) ∧
      (∀ r ∈ Ico 0 ε, ∀ θ : ℝ, v (a + r • Complex.exp ((θ : ℂ) * Complex.I)) = r ^ (k + 1) * W (r, θ)) ∧
      (∀ θ : ℝ, W (0, θ) = (2 / ((k + 1 : ℕ) : ℝ)) * (b a * Complex.exp ((θ : ℂ) * Complex.I) ^ (k + 1)).re) ∧
      ContinuousOn A (Ico 0 ε ×ˢ univ) ∧
      (∀ r ∈ Ico 0 ε, ∀ θ : ℝ, HasDerivAt (fun t => W (r, t)) (A (r, θ)) θ) ∧
      (∀ θ : ℝ, A (0, θ) = 2 * (Complex.I * b a * Complex.exp ((θ : ℂ) * Complex.I) ^ (k + 1)).re) ∧
      (∀ r ∈ Ioo 0 ε, ∀ θ : ℝ, A (r, θ) =
        2 * ((Complex.I * Complex.exp ((θ : ℂ) * Complex.I) ^ (k + 1)) * b (a + r • Complex.exp ((θ : ℂ) * Complex.I))).re) ∧
      ContinuousOn R (Ico 0 ε ×ˢ univ) ∧
      (∀ θ : ℝ, R (0, θ) = 0) ∧
      (∀ r ∈ Ioo 0 ε, ∀ θ : ℝ, R (r, θ) = r * fderiv ℝ W (r, θ) (1, 0)) ∧
      (∀ r ∈ Ico 0 ε, Function.Periodic (fun θ => W (r, θ)) (2 * Real.pi)) := by
  obtain ⟨η, hη, hηΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds ha)
  let ε := η / 2
  have hε : 0 < ε := half_pos hη
  have hball : closedBall a ε ⊆ Ω :=
    (closedBall_subset_ball (half_lt_self hη)).trans hηΩ
  obtain ⟨B, hB, hBb⟩ := exists_continuous_extension_complex isClosed_closedBall (hb.mono hball)
  have hBa : B a = b a := hBb (mem_closedBall_self hε.le)
  have hdB (z : ℂ) (hz : z ∈ closedBall a ε) (w : ℂ) :
      fderiv ℝ v z w = 2 * (w * ((z - a) ^ k * B z)).re := by
    rw [hBb hz]
    exact hDv z (hball hz) w
  obtain ⟨W, A, R, hWc, hW, hfactor, hzero, hAc, hangular, hA0, hA,
    hRc, hR0, hR, hperiod⟩ := polar_data_on_ball hΩ hv hva k hB hball hdB
  refine ⟨ε, hε, hball, W, A, R, hWc, hW, hfactor, ?_, hAc, hangular,
    ?_, ?_, hRc, hR0, hR, hperiod⟩
  · intro θ
    simpa only [hBa, polarCircle] using hzero θ
  · intro θ
    simpa only [hBa, polarCircle] using hA0 θ
  · intro r hr θ
    have hm : a + r • polarCircle θ ∈ closedBall a ε := by
      simpa using polar_segment_mem (a := a) ⟨hr.1.le, hr.2⟩
        (show (1 : ℝ) ∈ Icc 0 1 by simp) θ
    have hh := hA r hr θ
    rw [hBb hm] at hh
    simpa only [polarCircle] using hh

private theorem realLinearMap_eq_twice_re (L : ℂ →L[ℝ] ℝ) (w : ℂ) :
    L w = 2 * (w * (⟨L 1 / 2, -L Complex.I / 2⟩ : ℂ)).re := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hw, map_add, map_smul, map_smul]
  simp only [Complex.mul_re, smul_eq_mul]
  ring

/-- A continuous factor of the actual complex gradient produces polar data for the same
scalar function. The angular derivative extends continuously to radius zero, and the
radial derivative multiplied by radius extends continuously with value zero. Only the
original scalar is differentiated; the factor is merely continuous. -/
theorem exists_polar_data_of_complex_gradient_factor {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {a : ℂ} (ha : a ∈ Ω) {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v Ω)
    (hva : v a = 0) (k : ℕ) {b : ℂ → ℂ} (hb : ContinuousOn b Ω)
    (hfactor : ∀ z ∈ Ω, planarComplexGradient v z = (z - a) ^ k * b z) :
    ∃ ε > 0, closedBall a ε ⊆ Ω ∧ ∃ W A R : (ℝ × ℝ) → ℝ,
      ContinuousOn W (Ico 0 ε ×ˢ univ) ∧
      ContDiffOn ℝ 1 W (Ioo 0 ε ×ˢ univ) ∧
      (∀ r ∈ Ico 0 ε, ∀ θ : ℝ, v (a + r • Complex.exp ((θ : ℂ) * Complex.I)) = r ^ (k + 1) * W (r, θ)) ∧
      (∀ θ : ℝ, W (0, θ) = (2 / ((k + 1 : ℕ) : ℝ)) * (b a * Complex.exp ((θ : ℂ) * Complex.I) ^ (k + 1)).re) ∧
      ContinuousOn A (Ico 0 ε ×ˢ univ) ∧
      (∀ r ∈ Ico 0 ε, ∀ θ : ℝ, HasDerivAt (fun t => W (r, t)) (A (r, θ)) θ) ∧
      (∀ θ : ℝ, A (0, θ) = 2 * (Complex.I * b a * Complex.exp ((θ : ℂ) * Complex.I) ^ (k + 1)).re) ∧
      (∀ r ∈ Ioo 0 ε, ∀ θ : ℝ, A (r, θ) =
        2 * ((Complex.I * Complex.exp ((θ : ℂ) * Complex.I) ^ (k + 1)) * b (a + r • Complex.exp ((θ : ℂ) * Complex.I))).re) ∧
      ContinuousOn R (Ico 0 ε ×ˢ univ) ∧
      (∀ θ : ℝ, R (0, θ) = 0) ∧
      (∀ r ∈ Ioo 0 ε, ∀ θ : ℝ, R (r, θ) = r * fderiv ℝ W (r, θ) (1, 0)) ∧
      (∀ r ∈ Ico 0 ε, Function.Periodic (fun θ => W (r, θ)) (2 * Real.pi)) := by
  apply exists_polar_data_of_fderiv_factor hΩ ha hv hva k hb
  intro z hz w
  rw [realLinearMap_eq_twice_re (fderiv ℝ v z) w]
  change 2 * (w * planarComplexGradient v z).re = _
  rw [hfactor z hz]

end DifferentialGeometry.Analysis
