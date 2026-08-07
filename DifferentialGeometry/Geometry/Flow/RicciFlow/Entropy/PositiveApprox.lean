import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.WEstimate
import DifferentialGeometry.Analysis.Integration.EntropyMix
import DifferentialGeometry.Analysis.Integration.L2.Basic
import DifferentialGeometry.Geometry.Metric.MetricBounds
import Mathlib.Analysis.SpecificLimits.Basic
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

/-!
# Positive approximation of square-form amplitudes

A smooth unit-mass amplitude may vanish.  This file mixes its squared density
with a small uniform density, takes the positive square root, and controls the
resulting square-form energy without differentiating through a limiting tensor.
-/

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open MeasureTheory Filter
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Integration
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.L2
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private theorem grad_sqrt_mix
    (g : SmoothRiemannianMetric I M) {v : M → ℝ}
    (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (x : M) :
    gradientFun (I := I) g
        (fun y : M => Real.sqrt (a * v y ^ 2 + b)) x =
      (a * v x / Real.sqrt (a * v x ^ 2 + b)) •
        gradientFun (I := I) g v x := by
  let q : M → ℝ := fun y => a * v y ^ 2 + b
  let w : M → ℝ := fun y => Real.sqrt (q y)
  have hqpos (y : M) : 0 < q y := by
    dsimp only [q]
    exact lt_of_lt_of_le hb (le_add_of_nonneg_left (mul_nonneg ha (sq_nonneg _)))
  have hq : ContMDiff I 𝓘(ℝ, ℝ) ∞ q := by
    dsimp only [q]
    have ha_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => a) :=
      contMDiff_const
    have hb_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => b) :=
      contMDiff_const
    simpa only [pow_two] using (ha_smooth.mul (hv.mul hv)).add hb_smooth
  have hw : ContMDiff I 𝓘(ℝ, ℝ) ∞ w := by
    intro y
    have hsqrt : ContDiffAt ℝ ∞ Real.sqrt (q y) :=
      Real.contDiffAt_sqrt (hqpos y).ne'
    exact hsqrt.contMDiffAt.comp y (hq y)
  have hwpos (y : M) : 0 < w y := Real.sqrt_pos.2 (hqpos y)
  have hsq : (fun y : M => w y * w y) = q := by
    funext y
    exact Real.mul_self_sqrt (hqpos y).le
  have hgradq : gradientFun (I := I) g q x =
      (2 * a * v x) • gradientFun (I := I) g v x := by
    have hvd : MDifferentiableAt I 𝓘(ℝ, ℝ) v x :=
      hv.mdifferentiableAt (by norm_num)
    have hvsq : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => v y * v y) x :=
      hvd.mul hvd
    have hscale := gradientFun_const_smul (I := I) g a hvsq
    have hadd :
        gradientFun (I := I) g
            (fun y : M => (a • (fun z : M => v z * v z)) y + b) x =
          gradientFun (I := I) g (a • (fun y : M => v y * v y)) x +
            gradientFun (I := I) g (fun _ : M => b) x :=
      gradientFun_add (I := I) g (hvsq.const_smul a)
        (mdifferentiableAt_const (c := b))
    rw [gradientFun_const] at hadd
    simp only [add_zero] at hadd
    rw [show q = fun y : M => a * (v y * v y) + b by
      funext y
      simp only [q, pow_two]]
    rw [show (fun y : M => a * (v y * v y) + b) =
        fun y : M => (a • (fun z : M => v z * v z)) y + b by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]]
    rw [hadd, hscale, gradientFun_mul_self (I := I) g hvd]
    simp only [smul_smul]
    congr 1
    ring
  have hcancel :
      (2 * w x) • gradientFun (I := I) g w x =
        (2 * a * v x) • gradientFun (I := I) g v x := by
    calc
      (2 * w x) • gradientFun (I := I) g w x =
          gradientFun (I := I) g (fun y : M => w y * w y) x :=
        (gradientFun_mul_self (I := I) g
          (hw.mdifferentiableAt (by norm_num))).symm
      _ = gradientFun (I := I) g q x := by rw [hsq]
      _ = (2 * a * v x) • gradientFun (I := I) g v x := hgradq
  change gradientFun (I := I) g w x =
    (a * v x / w x) • gradientFun (I := I) g v x
  apply smul_right_injective (TangentSpace I x)
    (show (2 * w x : ℝ) ≠ 0 from
      mul_ne_zero (by norm_num) (hwpos x).ne')
  calc
    (2 * w x) • gradientFun (I := I) g w x =
        (2 * a * v x) • gradientFun (I := I) g v x := hcancel
    _ = (2 * w x) •
        ((a * v x / w x) • gradientFun (I := I) g v x) := by
      rw [smul_smul]
      congr 1
      field_simp [(hwpos x).ne']

private theorem energy_mix_le
    (g : SmoothRiemannianMetric I M) {v : M → ℝ}
    (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v) {a b : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (x : M) :
    g.inner x
        (gradientFun (I := I) g
          (fun y : M => Real.sqrt (a * v y ^ 2 + b)) x)
        (gradientFun (I := I) g
          (fun y : M => Real.sqrt (a * v y ^ 2 + b)) x) ≤
      g.inner x (gradientFun (I := I) g v x)
        (gradientFun (I := I) g v x) := by
  let w : ℝ := Real.sqrt (a * v x ^ 2 + b)
  have hwpos : 0 < w := Real.sqrt_pos.2 <|
    lt_of_lt_of_le hb (le_add_of_nonneg_left (mul_nonneg ha (sq_nonneg _)))
  have hw_sq : w ^ 2 = a * v x ^ 2 + b := by
    exact Real.sq_sqrt <|
      (lt_of_lt_of_le hb
        (le_add_of_nonneg_left (mul_nonneg ha (sq_nonneg _)))).le
  have hcoef : (a * v x / w) ^ 2 ≤ a := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hwpos)).2
    nlinarith [mul_nonneg ha hb.le]
  rw [grad_sqrt_mix (I := I) g hv ha hb x]
  rw [(g.inner x).map_smul, ContinuousLinearMap.smul_apply,
    smul_eq_mul,
    (g.inner x (gradientFun (I := I) g v x)).map_smul, smul_eq_mul]
  rw [← mul_assoc, ← pow_two]
  exact mul_le_of_le_one_left
    (metric_inner_self_nonneg (I := I) (M := M) g x _) <|
      hcoef.trans ha1

variable [T2Space M] [CompactSpace M]
variable [Nonempty M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A smooth unit-mass amplitude, allowed to vanish, admits strictly positive
smooth unit-mass approximants whose square-form value is arbitrarily close
from above. -/
theorem exists_pos_wform
    (g : SmoothRiemannianMetric I M) {v : M → ℝ}
    (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v)
    (hmass : (∫ x, v x ^ 2 ∂(riemannianVolumeMeasure I M g)) = 1)
    (hvgradi : Integrable (fun x => g.inner x
      (gradientFun (I := I) g v x) (gradientFun (I := I) g v x))
      (riemannianVolumeMeasure I M g))
    {R : M → ℝ} (hR : Continuous R) {tau C δ : ℝ}
    (htau : 0 ≤ tau) (hδ : 0 < δ) :
    ∃ w : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ w ∧
      (∀ x : M, 0 < w x) ∧
      (∫ x, w x ^ 2 ∂(riemannianVolumeMeasure I M g)) = 1 ∧
      (∫ x, 4 * tau * g.inner x
            (gradientFun (I := I) g w x) (gradientFun (I := I) g w x) +
          tau * R x * w x ^ 2 - w x ^ 2 * Real.log (w x ^ 2) + C * w x ^ 2
        ∂(riemannianVolumeMeasure I M g)) ≤
        (∫ x, 4 * tau * g.inner x
              (gradientFun (I := I) g v x) (gradientFun (I := I) g v x) +
            tau * R x * v x ^ 2 - v x ^ 2 * Real.log (v x ^ 2) + C * v x ^ 2
          ∂(riemannianVolumeMeasure I M g)) + δ := by
  classical
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  letI : μ.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  have hμpos : 0 < μ Set.univ :=
    isOpen_univ.measure_pos μ Set.univ_nonempty
  letI : NeZero μ := ⟨by
    intro hμ
    have hz : μ Set.univ = 0 := by
      rw [hμ, Measure.coe_zero, Pi.zero_apply]
    exact (ne_of_gt hμpos) hz⟩
  let V : ℝ := μ.real Set.univ
  have hVpos : 0 < V := by
    simpa only [V] using (measureReal_univ_pos (μ := μ))
  let p : M → ℝ := fun x => v x ^ 2
  let energy : M → ℝ := fun x => g.inner x
    (gradientFun (I := I) g v x) (gradientFun (I := I) g v x)
  let S : ℝ := ∫ x, R x * p x ∂μ
  let H₀ : ℝ := ∫ x, Real.negMulLog (p x) ∂μ
  let R₀ : ℝ := ∫ x, R x ∂μ
  have hpcont : Continuous p := by
    simpa only [p, pow_two] using (hv.mul hv).continuous
  have hpint : Integrable p μ :=
    integrable_of_continuous_compactSpace (I := I) (M := M) g hpcont
  have hRpint : Integrable (fun x => R x * p x) μ :=
    integrable_of_continuous_compactSpace (I := I) (M := M) g (hR.mul hpcont)
  have hRent : Integrable R μ :=
    integrable_of_continuous_compactSpace (I := I) (M := M) g hR
  have hHcont : Continuous (fun x => Real.negMulLog (p x)) :=
    Real.continuous_negMulLog.comp hpcont
  have hHint : Integrable (fun x => Real.negMulLog (p x)) μ :=
    integrable_of_continuous_compactSpace (I := I) (M := M) g hHcont
  let err : ℝ → ℝ := fun e =>
    tau * e * |R₀ / V - S| + Real.negMulLog (1 - e) +
      V * Real.negMulLog (e / V) + e * |H₀|
  have herrcont : Continuous err := by
    dsimp only [err]
    fun_prop
  have herr0 : err 0 = 0 := by
    simp only [err, mul_zero, zero_mul, sub_zero, Real.negMulLog_one,
      Real.negMulLog_zero, add_zero, zero_div]
  let eSeq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have heSeq : Tendsto eSeq atTop (𝓝 0) := by
    simpa only [eSeq] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have herrt : Tendsto (fun n => err (eSeq n)) atTop (𝓝 0) := by
    rw [← herr0]
    exact herrcont.continuousAt.tendsto.comp heSeq
  have hevent : ∀ᶠ n in atTop, err (eSeq n) < δ :=
    herrt.eventually (Iio_mem_nhds hδ)
  obtain ⟨n, hn1, hnerr⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and hevent).exists
  let e : ℝ := eSeq n
  have hepos : 0 < e := by
    dsimp only [e, eSeq]
    positivity
  have helt : e < 1 := by
    dsimp only [e, eSeq]
    apply (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
    exact_mod_cast Nat.lt_succ_of_le hn1
  let a : ℝ := 1 - e
  let b : ℝ := e / V
  have ha : 0 ≤ a := sub_nonneg.2 helt.le
  have ha1 : a ≤ 1 := by dsimp only [a]; linarith
  have hb : 0 < b := div_pos hepos hVpos
  let q : M → ℝ := fun x => a * v x ^ 2 + b
  let w : M → ℝ := fun x => Real.sqrt (q x)
  have hqpos (x : M) : 0 < q x := by
    dsimp only [q]
    exact lt_of_lt_of_le hb (le_add_of_nonneg_left (mul_nonneg ha (sq_nonneg _)))
  have hq : ContMDiff I 𝓘(ℝ, ℝ) ∞ q := by
    dsimp only [q]
    have ha_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => a) := contMDiff_const
    have hb_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => b) := contMDiff_const
    simpa only [pow_two] using (ha_smooth.mul (hv.mul hv)).add hb_smooth
  have hw : ContMDiff I 𝓘(ℝ, ℝ) ∞ w := by
    intro x
    exact (Real.contDiffAt_sqrt (hqpos x).ne').contMDiffAt.comp x (hq x)
  have hwpos (x : M) : 0 < w x := Real.sqrt_pos.2 (hqpos x)
  have hw_sq (x : M) : w x ^ 2 = q x := by
    exact Real.sq_sqrt (hqpos x).le
  have hmassw : (∫ x, w x ^ 2 ∂μ) = 1 := by
    calc
      (∫ x, w x ^ 2 ∂μ) = ∫ x, q x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        exact hw_sq x
      _ = ∫ x, a * p x + b ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        rfl
      _ = a * (∫ x, p x ∂μ) + ∫ _ : M, b ∂μ := by
        rw [integral_add (hpint.const_mul a) (integrable_const b), integral_const_mul]
      _ = 1 := by
        rw [show (∫ x, p x ∂μ) = 1 by simpa only [p, μ] using hmass,
          integral_const]
        simp only [smul_eq_mul]
        dsimp only [a, b]
        field_simp [hVpos.ne']
        ring
  have hqmass : (∫ x, q x ∂μ) = 1 := by
    calc
      (∫ x, q x ∂μ) = ∫ x, w x ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        exact (hw_sq x).symm
      _ = 1 := hmassw
  let energyW : M → ℝ := fun x => g.inner x
    (gradientFun (I := I) g w x) (gradientFun (I := I) g w x)
  let coef : M → ℝ := fun x => (a * v x / w x) ^ 2
  have hcoefcont : Continuous coef := by
    dsimp only [coef]
    exact ((continuous_const.mul hv.continuous).div hw.continuous
      (fun x => (hwpos x).ne')).pow 2
  have henergy_eq (x : M) : energyW x = coef x * energy x := by
    have hgrad := grad_sqrt_mix (I := I) g hv ha hb x
    change gradientFun (I := I) g w x =
      (a * v x / w x) • gradientFun (I := I) g v x at hgrad
    dsimp only [energyW, coef, energy]
    rw [hgrad, (g.inner x).map_smul, ContinuousLinearMap.smul_apply,
      smul_eq_mul, (g.inner x (gradientFun (I := I) g v x)).map_smul,
      smul_eq_mul]
    ring
  have henergyW_aesm : AEStronglyMeasurable energyW μ :=
    (hcoefcont.aestronglyMeasurable.mul hvgradi.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun x => (henergy_eq x).symm)
  have henergyW_nonneg : ∀ᵐ x ∂μ, 0 ≤ energyW x :=
    Filter.Eventually.of_forall fun x =>
      metric_inner_self_nonneg (I := I) (M := M) g x _
  have henergyW_le : ∀ᵐ x ∂μ, energyW x ≤ energy x :=
    Filter.Eventually.of_forall fun x =>
      energy_mix_le (I := I) g hv ha ha1 hb x
  have henergyWint : Integrable energyW μ :=
    Integrable.mono_nonneg hvgradi henergyW_aesm henergyW_nonneg henergyW_le
  have henergy_int_le : (∫ x, energyW x ∂μ) ≤ ∫ x, energy x ∂μ :=
    integral_mono henergyWint hvgradi (fun x => energy_mix_le (I := I) g hv ha ha1 hb x)
  have hqcont : Continuous q := hq.continuous
  have hqint : Integrable q μ :=
    integrable_of_continuous_compactSpace (I := I) (M := M) g hqcont
  have hRqint : Integrable (fun x => R x * q x) μ :=
    integrable_of_continuous_compactSpace (I := I) (M := M) g (hR.mul hqcont)
  have hHqint : Integrable (fun x => Real.negMulLog (q x)) μ :=
    integrable_of_continuous_compactSpace (I := I) (M := M) g
      (Real.continuous_negMulLog.comp hqcont)
  have hscalar : (∫ x, R x * q x ∂μ) = a * S + b * R₀ := by
    calc
      (∫ x, R x * q x ∂μ) = ∫ x, a * (R x * p x) + b * R x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [q, p]
        ring
      _ = a * (∫ x, R x * p x ∂μ) + b * (∫ x, R x ∂μ) := by
        rw [integral_add (hRpint.const_mul a) (hRent.const_mul b),
          integral_const_mul, integral_const_mul]
      _ = a * S + b * R₀ := by rfl
  have hent_point (x : M) :
      Real.negMulLog (q x) ≤
        p x * Real.negMulLog a + a * Real.negMulLog (p x) +
          Real.negMulLog b := by
    calc
      Real.negMulLog (q x) = Real.negMulLog (a * p x + b) := by rfl
      _ ≤ Real.negMulLog (a * p x) + Real.negMulLog b :=
        negMulLog_add_le (mul_nonneg ha (sq_nonneg _)) hb.le
      _ = p x * Real.negMulLog a + a * Real.negMulLog (p x) +
          Real.negMulLog b := by
        rw [Real.negMulLog_mul]
  have hent_rhs_int : Integrable (fun x =>
      p x * Real.negMulLog a + a * Real.negMulLog (p x) +
        Real.negMulLog b) μ :=
    ((hpint.mul_const _).add (hHint.const_mul a)).add (integrable_const _)
  have hentropy : (∫ x, Real.negMulLog (q x) ∂μ) ≤
      a * H₀ + Real.negMulLog a + V * Real.negMulLog b := by
    calc
      (∫ x, Real.negMulLog (q x) ∂μ) ≤
          ∫ x, p x * Real.negMulLog a + a * Real.negMulLog (p x) +
            Real.negMulLog b ∂μ :=
        integral_mono hHqint hent_rhs_int hent_point
      _ = a * H₀ + Real.negMulLog a + V * Real.negMulLog b := by
        calc
          (∫ x, p x * Real.negMulLog a + a * Real.negMulLog (p x) +
              Real.negMulLog b ∂μ) =
              (∫ x, p x * Real.negMulLog a +
                a * Real.negMulLog (p x) ∂μ) +
                ∫ _ : M, Real.negMulLog b ∂μ := by
            simpa only [Pi.add_apply] using
              integral_add ((hpint.mul_const _).add (hHint.const_mul a))
                (integrable_const (Real.negMulLog b))
          _ = ((∫ x, p x * Real.negMulLog a ∂μ) +
                ∫ x, a * Real.negMulLog (p x) ∂μ) +
                ∫ _ : M, Real.negMulLog b ∂μ := by
            rw [show (∫ x, p x * Real.negMulLog a +
                a * Real.negMulLog (p x) ∂μ) =
                (∫ x, p x * Real.negMulLog a ∂μ) +
                  ∫ x, a * Real.negMulLog (p x) ∂μ by
              simpa only [Pi.add_apply] using
                integral_add (hpint.mul_const _) (hHint.const_mul a)]
          _ = a * H₀ + Real.negMulLog a + V * Real.negMulLog b := by
            rw [integral_mul_const, integral_const_mul, integral_const]
            simp only [smul_eq_mul]
            rw [show (∫ x, p x ∂μ) = 1 by simpa only [p, μ] using hmass]
            dsimp only [H₀, V]
            ring
  have hdir : 4 * tau * (∫ x, energyW x ∂μ) ≤
      4 * tau * (∫ x, energy x ∂μ) :=
    mul_le_mul_of_nonneg_left henergy_int_le (mul_nonneg (by norm_num) htau)
  have hA : e * (R₀ / V - S) ≤ e * |R₀ / V - S| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hepos.le
  have hscerr : tau * (a * S + b * R₀) ≤
      tau * S + tau * e * |R₀ / V - S| := by
    have hcore : a * S + b * R₀ = S + e * (R₀ / V - S) := by
      dsimp only [a, b]
      field_simp [hVpos.ne']
      ring
    rw [hcore]
    nlinarith [mul_le_mul_of_nonneg_left hA htau]
  have hHabs : -e * H₀ ≤ e * |H₀| := by
    nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs H₀) hepos.le]
  have hHcond : a * H₀ + Real.negMulLog a + V * Real.negMulLog b ≤
      H₀ + Real.negMulLog a + V * Real.negMulLog b + e * |H₀| := by
    dsimp only [a]
    nlinarith
  have hFw :
      (∫ x, 4 * tau * energyW x + tau * R x * w x ^ 2 -
          w x ^ 2 * Real.log (w x ^ 2) + C * w x ^ 2 ∂μ) =
        4 * tau * (∫ x, energyW x ∂μ) +
          tau * (∫ x, R x * q x ∂μ) +
          (∫ x, Real.negMulLog (q x) ∂μ) + C := by
    have hdirint : Integrable (fun x => (4 * tau) * energyW x) μ :=
      henergyWint.const_mul (4 * tau)
    have hscint : Integrable (fun x => tau * (R x * q x)) μ :=
      hRqint.const_mul tau
    have hnormint : Integrable (fun x => C * q x) μ :=
      hqint.const_mul C
    calc
      (∫ x, 4 * tau * energyW x + tau * R x * w x ^ 2 -
          w x ^ 2 * Real.log (w x ^ 2) + C * w x ^ 2 ∂μ) =
          ∫ x, (4 * tau) * energyW x + tau * (R x * q x) +
            Real.negMulLog (q x) + C * q x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hw_sq x]
        simp only [Real.negMulLog]
        ring
      _ = 4 * tau * (∫ x, energyW x ∂μ) +
          tau * (∫ x, R x * q x ∂μ) +
          (∫ x, Real.negMulLog (q x) ∂μ) + C := by
        calc
          (∫ x, (4 * tau) * energyW x + tau * (R x * q x) +
              Real.negMulLog (q x) + C * q x ∂μ) =
              (∫ x, (4 * tau) * energyW x + tau * (R x * q x) +
                Real.negMulLog (q x) ∂μ) + ∫ x, C * q x ∂μ := by
            simpa only [Pi.add_apply] using
              integral_add ((hdirint.add hscint).add hHqint) hnormint
          _ = ((∫ x, (4 * tau) * energyW x + tau * (R x * q x) ∂μ) +
                ∫ x, Real.negMulLog (q x) ∂μ) + ∫ x, C * q x ∂μ := by
            rw [show (∫ x, (4 * tau) * energyW x + tau * (R x * q x) +
                Real.negMulLog (q x) ∂μ) =
                (∫ x, (4 * tau) * energyW x + tau * (R x * q x) ∂μ) +
                  ∫ x, Real.negMulLog (q x) ∂μ by
              simpa only [Pi.add_apply] using
                integral_add (hdirint.add hscint) hHqint]
          _ = (((∫ x, (4 * tau) * energyW x ∂μ) +
                ∫ x, tau * (R x * q x) ∂μ) +
                ∫ x, Real.negMulLog (q x) ∂μ) + ∫ x, C * q x ∂μ := by
            rw [show (∫ x, (4 * tau) * energyW x + tau * (R x * q x) ∂μ) =
                (∫ x, (4 * tau) * energyW x ∂μ) +
                  ∫ x, tau * (R x * q x) ∂μ by
              simpa only [Pi.add_apply] using integral_add hdirint hscint]
          _ = 4 * tau * (∫ x, energyW x ∂μ) +
              tau * (∫ x, R x * q x ∂μ) +
              (∫ x, Real.negMulLog (q x) ∂μ) + C := by
            rw [integral_const_mul, integral_const_mul, integral_const_mul, hqmass]
            ring
  have hFv :
      (∫ x, 4 * tau * energy x + tau * R x * v x ^ 2 -
          v x ^ 2 * Real.log (v x ^ 2) + C * v x ^ 2 ∂μ) =
        4 * tau * (∫ x, energy x ∂μ) + tau * S + H₀ + C := by
    have hdirint : Integrable (fun x => (4 * tau) * energy x) μ :=
      hvgradi.const_mul (4 * tau)
    have hscint : Integrable (fun x => tau * (R x * p x)) μ :=
      hRpint.const_mul tau
    have hnormint : Integrable (fun x => C * p x) μ := hpint.const_mul C
    calc
      (∫ x, 4 * tau * energy x + tau * R x * v x ^ 2 -
          v x ^ 2 * Real.log (v x ^ 2) + C * v x ^ 2 ∂μ) =
          ∫ x, (4 * tau) * energy x + tau * (R x * p x) +
            Real.negMulLog (p x) + C * p x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [p, Real.negMulLog]
        ring
      _ = 4 * tau * (∫ x, energy x ∂μ) + tau * S + H₀ + C := by
        calc
          (∫ x, (4 * tau) * energy x + tau * (R x * p x) +
              Real.negMulLog (p x) + C * p x ∂μ) =
              (∫ x, (4 * tau) * energy x + tau * (R x * p x) +
                Real.negMulLog (p x) ∂μ) + ∫ x, C * p x ∂μ := by
            simpa only [Pi.add_apply] using
              integral_add ((hdirint.add hscint).add hHint) hnormint
          _ = ((∫ x, (4 * tau) * energy x + tau * (R x * p x) ∂μ) +
                ∫ x, Real.negMulLog (p x) ∂μ) + ∫ x, C * p x ∂μ := by
            rw [show (∫ x, (4 * tau) * energy x + tau * (R x * p x) +
                Real.negMulLog (p x) ∂μ) =
                (∫ x, (4 * tau) * energy x + tau * (R x * p x) ∂μ) +
                  ∫ x, Real.negMulLog (p x) ∂μ by
              simpa only [Pi.add_apply] using
                integral_add (hdirint.add hscint) hHint]
          _ = (((∫ x, (4 * tau) * energy x ∂μ) +
                ∫ x, tau * (R x * p x) ∂μ) +
                ∫ x, Real.negMulLog (p x) ∂μ) + ∫ x, C * p x ∂μ := by
            rw [show (∫ x, (4 * tau) * energy x + tau * (R x * p x) ∂μ) =
                (∫ x, (4 * tau) * energy x ∂μ) +
                  ∫ x, tau * (R x * p x) ∂μ by
              simpa only [Pi.add_apply] using integral_add hdirint hscint]
          _ = 4 * tau * (∫ x, energy x ∂μ) + tau * S + H₀ + C := by
            rw [integral_const_mul, integral_const_mul, integral_const_mul]
            rw [show (∫ x, p x ∂μ) = 1 by simpa only [p, μ] using hmass]
            dsimp only [S, H₀]
            ring
  refine ⟨w, hw, hwpos, ?_, ?_⟩
  · simpa only [μ] using hmassw
  · simpa only [μ, energyW, energy] using (show
      (∫ x, 4 * tau * energyW x + tau * R x * w x ^ 2 -
          w x ^ 2 * Real.log (w x ^ 2) + C * w x ^ 2 ∂μ) ≤
        (∫ x, 4 * tau * energy x + tau * R x * v x ^ 2 -
          v x ^ 2 * Real.log (v x ^ 2) + C * v x ^ 2 ∂μ) + δ by
      rw [hFw, hFv, hscalar]
      have herr_lt :
          tau * e * |R₀ / V - S| + Real.negMulLog a +
              V * Real.negMulLog b + e * |H₀| < δ := by
        simpa only [e, a, b] using hnerr
      linarith)

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
