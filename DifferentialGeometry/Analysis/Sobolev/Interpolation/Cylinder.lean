import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

open Set MeasureTheory Filter ContinuousLinearMap
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def affineCylinderInterpolation (h : ℝ) (a b : ℝ → F) (z : ℝ × ℝ) : F :=
  (1 - z.1 / h) • a z.2 + (z.1 / h) • b z.2

private theorem fderiv_affineCylinderInterpolation
    {h : ℝ} {a b : ℝ → F} {z : ℝ × ℝ}
    (ha : DifferentiableAt ℝ a z.2) (hb : DifferentiableAt ℝ b z.2) :
    fderiv ℝ (affineCylinderInterpolation h a b) z =
      (1 - z.1 / h) • ((fderiv ℝ a z.2).comp (snd ℝ ℝ ℝ)) +
      (0 - h⁻¹ • fst ℝ ℝ ℝ).smulRight (a z.2) +
      ((z.1 / h) • ((fderiv ℝ b z.2).comp (snd ℝ ℝ ℝ)) +
        (h⁻¹ • fst ℝ ℝ ℝ).smulRight (b z.2)) := by
  have hs : HasFDerivAt (fun z : ℝ × ℝ => z.1 / h) (h⁻¹ • fst ℝ ℝ ℝ) z := by
    simpa only [div_eq_mul_inv, mul_comm] using (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).const_mul h⁻¹
  have ht := (hasFDerivAt_const (1 : ℝ) z).sub hs
  exact ((ht.smul (ha.hasFDerivAt.comp z hasFDerivAt_snd)).add
    (hs.smul (hb.hasFDerivAt.comp z hasFDerivAt_snd))).fderiv

theorem fderiv_affineCylinderInterpolation_fst
    {h : ℝ} {a b : ℝ → F} {z : ℝ × ℝ}
    (ha : DifferentiableAt ℝ a z.2) (hb : DifferentiableAt ℝ b z.2) :
    fderiv ℝ (affineCylinderInterpolation h a b) z (1, 0) =
      h⁻¹ • (b z.2 - a z.2) := by
  rw [fderiv_affineCylinderInterpolation ha hb]
  simp only [add_apply, zero_sub, neg_apply, smul_apply, comp_apply, coe_snd', map_zero, smul_zero,
    coe_fst', smulRight_apply, smul_eq_mul, mul_one, zero_add, neg_smul]
  rw [smul_sub]
  abel

theorem fderiv_affineCylinderInterpolation_snd
    {h : ℝ} {a b : ℝ → F} {z : ℝ × ℝ}
    (ha : DifferentiableAt ℝ a z.2) (hb : DifferentiableAt ℝ b z.2) :
    fderiv ℝ (affineCylinderInterpolation h a b) z (0, 1) =
      (1 - z.1 / h) • deriv a z.2 + (z.1 / h) • deriv b z.2 := by
  rw [fderiv_affineCylinderInterpolation ha hb]
  simp only [add_apply, zero_sub, neg_apply, smul_apply, comp_apply, coe_snd', coe_fst',
    smulRight_apply, smul_eq_mul, mul_zero, neg_zero, zero_smul, add_zero,
    fderiv_apply_one_eq_deriv]

private theorem norm_affineCombination_sq_le (v w : F) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(1 - t) • v + t • w‖ ^ 2 ≤ ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  have ht : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hn : ‖(1 - t) • v + t • w‖ ≤ (1 - t) * ‖v‖ + t * ‖w‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, abs_of_nonneg ht0] using
      norm_add_le ((1 - t) • v) (t • w)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  have hc : ((1 - t) * ‖v‖ + t * ‖w‖) ^ 2 ≤ (1 - t) * ‖v‖ ^ 2 + t * ‖w‖ ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg ht ht0) (sq_nonneg (‖v‖ - ‖w‖))]
  apply hs.trans (hc.trans ?_)
  nlinarith [mul_nonneg ht0 (sq_nonneg (‖v‖)), mul_nonneg ht (sq_nonneg (‖w‖))]

variable [FiniteDimensional ℝ F]

theorem integral_energy_affineCylinderInterpolation_le
    {h : ℝ} (hh : 0 < h) {a b : ℝ → F} {Ka Kb : ℝ≥0}
    (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b) :
    (∫ z in Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) 1,
      (‖fderiv ℝ (affineCylinderInterpolation h a b) z (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (affineCylinderInterpolation h a b) z (0, 1)‖ ^ 2) / 2) ≤
      (1 / (2 * h)) * (∫ t in Icc (0 : ℝ) 1, ‖a t - b t‖ ^ 2) +
        (h / 2) * (∫ t in Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2 + ‖deriv b t‖ ^ 2) := by
  borelize F
  let μ : Measure ℝ := volume.restrict (Icc 0 h)
  let ν : Measure ℝ := volume.restrict (Icc 0 1)
  let q (t : ℝ) := (h⁻¹ ^ 2 * ‖a t - b t‖ ^ 2 +
    (‖deriv a t‖ ^ 2 + ‖deriv b t‖ ^ 2)) / 2
  let e (z : ℝ × ℝ) :=
    (‖fderiv ℝ (affineCylinderInterpolation h a b) z (1, 0)‖ ^ 2 +
      ‖fderiv ℝ (affineCylinderInterpolation h a b) z (0, 1)‖ ^ 2) / 2
  have hval : Integrable (fun t => ‖a t - b t‖ ^ 2) ν :=
    (((ha.continuous.sub hb.continuous).norm).pow 2).integrableOn_Icc
  have hda : MemLp (deriv a) 2 ν :=
    MemLp.of_bound (measurable_deriv a).aestronglyMeasurable Ka
      (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz ha)
  have hdb : MemLp (deriv b) 2 ν :=
    MemLp.of_bound (measurable_deriv b).aestronglyMeasurable Kb
      (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hb)
  have hder : Integrable (fun t => ‖deriv a t‖ ^ 2 + ‖deriv b t‖ ^ 2) ν :=
    hda.norm.integrable_sq.add hdb.norm.integrable_sq
  have hq : Integrable q ν := ((hval.const_mul (h⁻¹ ^ 2)).add hder).div_const 2
  have hqprod : Integrable (fun z : ℝ × ℝ => q z.2) (μ.prod ν) := hq.comp_snd μ
  have hader : ∀ᵐ z ∂μ.prod ν, DifferentiableAt ℝ a z.2 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae (s := Icc 0 1) ha.ae_differentiableAt)
  have hbder : ∀ᵐ z ∂μ.prod ν, DifferentiableAt ℝ b z.2 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae (s := Icc 0 1) hb.ae_differentiableAt)
  have hzfst : ∀ᵐ z ∂μ.prod ν, z.1 ∈ Icc (0 : ℝ) h :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hbound : ∀ᵐ z ∂μ.prod ν, e z ≤ q z.2 := by
    filter_upwards [hader, hbder, hzfst] with z hza hzb hz
    have hs0 : 0 ≤ z.1 / h := div_nonneg hz.1 hh.le
    have hs1 : z.1 / h ≤ 1 := (div_le_one hh).mpr hz.2
    dsimp only [e, q]
    rw [fderiv_affineCylinderInterpolation_fst hza hzb,
      fderiv_affineCylinderInterpolation_snd hza hzb, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, norm_sub_rev (b z.2)]
    exact div_le_div_of_nonneg_right
      (add_le_add le_rfl (norm_affineCombination_sq_le (deriv a z.2) (deriv b z.2) hs0 hs1))
      (by norm_num)
  have he : Integrable e (μ.prod ν) := by
    have h₁ := (measurable_fderiv_apply_const ℝ (affineCylinderInterpolation h a b) (1, 0))
      |>.norm.pow_const 2
    have h₂ := (measurable_fderiv_apply_const ℝ (affineCylinderInterpolation h a b) (0, 1))
      |>.norm.pow_const 2
    apply hqprod.mono' (((h₁.add h₂).div_const 2).aestronglyMeasurable)
    filter_upwards [hbound] with z hz
    rw [Real.norm_of_nonneg (by dsimp [e]; positivity)]
    exact hz
  have hle := integral_mono_ae he hqprod hbound
  have hprod : volume.restrict (Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) 1) = μ.prod ν := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  change (∫ z in Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) 1, e z) ≤ _
  rw [hprod]
  apply hle.trans_eq
  rw [integral_prod _ hqprod]
  change (∫ s in Icc (0 : ℝ) h, ∫ t in Icc (0 : ℝ) 1, q t) = _
  rw [setIntegral_const]
  simp only [Measure.real, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hh.le, smul_eq_mul]
  change h * (∫ t, q t ∂ν) = _
  dsimp only [q]
  rw [integral_div, integral_add (hval.const_mul _) hder, integral_const_mul]
  field_simp
  ring

end DifferentialGeometry.Analysis.Sobolev

end

noncomputable section

open Set MeasureTheory Filter ContinuousLinearMap
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private theorem memLp_Icc_of_continuous
    {H : Type*} [NormedAddCommGroup H] {f : ℝ → H} (hf : Continuous f)
    (a b : ℝ) (p : ℝ≥0∞) : MemLp f p (volume.restrict (Icc a b)) := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc : IsCompact (Icc a b)).image hf).isBounded.exists_norm_le
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC _ (mem_image_of_mem _ hx)

omit [FiniteDimensional ℝ F] in
private theorem differentiableAt_affineCylinderInterpolation
    {h : ℝ} {a b : ℝ → F} {z : ℝ × ℝ}
    (ha : DifferentiableAt ℝ a z.2) (hb : DifferentiableAt ℝ b z.2) :
    DifferentiableAt ℝ (affineCylinderInterpolation h a b) z := by
  have hs : DifferentiableAt ℝ (fun z : ℝ × ℝ => z.1 / h) z := by
    have hd := (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).const_mul h⁻¹
    simpa only [div_eq_mul_inv, mul_comm] using hd.differentiableAt
  exact (((differentiableAt_const (1 : ℝ)).sub hs).smul
    (ha.comp z differentiableAt_snd)).add
      (hs.smul (hb.comp z differentiableAt_snd))

theorem integrableOn_energy_affineCylinderInterpolation
    (h : ℝ) {a b : ℝ → F} {Ka Kb : ℝ≥0}
    (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b) :
    IntegrableOn (fun z =>
      (‖fderiv ℝ (affineCylinderInterpolation h a b) z (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (affineCylinderInterpolation h a b) z (0, 1)‖ ^ 2) / 2)
      (Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) 1) := by
  borelize F
  let μ : Measure ℝ := volume.restrict (Icc 0 h)
  let ν : Measure ℝ := volume.restrict (Icc 0 1)
  have hda : MemLp (deriv a) 2 ν :=
    MemLp.of_bound (measurable_deriv a).aestronglyMeasurable Ka
      (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz ha)
  have hdb : MemLp (deriv b) 2 ν :=
    MemLp.of_bound (measurable_deriv b).aestronglyMeasurable Kb
      (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hb)
  have hdiff : MemLp (fun t => b t - a t) 2 ν :=
    memLp_Icc_of_continuous (hb.continuous.sub ha.continuous) 0 1 2
  have h₁ : MemLp (fun s : ℝ => 1 - s / h) ∞ μ :=
    memLp_Icc_of_continuous (by fun_prop) 0 h ∞
  have h₂ : MemLp (fun s : ℝ => s / h) ∞ μ :=
    memLp_Icc_of_continuous (by fun_prop) 0 h ∞
  have hfirst : MemLp (fun z : ℝ × ℝ => h⁻¹ • (b z.2 - a z.2)) 2 (μ.prod ν) :=
    (hdiff.comp_snd μ).const_smul h⁻¹
  have hsecond : MemLp (fun z : ℝ × ℝ =>
      (1 - z.1 / h) • deriv a z.2 + (z.1 / h) • deriv b z.2) 2 (μ.prod ν) :=
    ((hda.comp_snd μ).smul (h₁.comp_fst ν)).add
      ((hdb.comp_snd μ).smul (h₂.comp_fst ν))
  have hader : ∀ᵐ z ∂μ.prod ν, DifferentiableAt ℝ a z.2 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae (s := Icc 0 1) ha.ae_differentiableAt)
  have hbder : ∀ᵐ z ∂μ.prod ν, DifferentiableAt ℝ b z.2 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae (s := Icc 0 1) hb.ae_differentiableAt)
  have hf : MemLp (fun z => fderiv ℝ (affineCylinderInterpolation h a b) z (1, 0))
      2 (μ.prod ν) := by
    apply (memLp_congr_ae ?_).mpr hfirst
    filter_upwards [hader, hbder] with z hza hzb
    exact fderiv_affineCylinderInterpolation_fst hza hzb
  have hg : MemLp (fun z => fderiv ℝ (affineCylinderInterpolation h a b) z (0, 1))
      2 (μ.prod ν) := by
    apply (memLp_congr_ae ?_).mpr hsecond
    filter_upwards [hader, hbder] with z hza hzb
    exact fderiv_affineCylinderInterpolation_snd hza hzb
  have hi := (hf.norm.integrable_sq.add hg.norm.integrable_sq).div_const 2
  change Integrable _ (volume.restrict (Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) 1))
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact hi

theorem integral_energy_comp_affineCylinderInterpolation_le
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (h : ℝ) {a b : ℝ → F} {Ka Kb : ℝ≥0}
    (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (R : F → G) (hR : Differentiable ℝ R) {L : ℝ}
    (hL : ∀ x, ‖fderiv ℝ R x‖ ≤ L) :
    (∫ z in Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) 1,
      (‖fderiv ℝ (R ∘ affineCylinderInterpolation h a b) z (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (R ∘ affineCylinderInterpolation h a b) z (0, 1)‖ ^ 2) / 2) ≤
      L ^ 2 * (∫ z in Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ (affineCylinderInterpolation h a b) z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (affineCylinderInterpolation h a b) z (0, 1)‖ ^ 2) / 2) := by
  borelize F G
  let A := affineCylinderInterpolation h a b
  let S := Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) 1
  let e (z : ℝ × ℝ) :=
    (‖fderiv ℝ A z (1, 0)‖ ^ 2 + ‖fderiv ℝ A z (0, 1)‖ ^ 2) / 2
  let er (z : ℝ × ℝ) :=
    (‖fderiv ℝ (R ∘ A) z (1, 0)‖ ^ 2 + ‖fderiv ℝ (R ∘ A) z (0, 1)‖ ^ 2) / 2
  have hprod : volume.restrict S =
      (volume.restrict (Icc (0 : ℝ) h)).prod (volume.restrict (Icc (0 : ℝ) 1)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hader : ∀ᵐ z ∂volume.restrict S, DifferentiableAt ℝ a z.2 := by
    rw [hprod]
    exact Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_of_ae (s := Icc 0 1) ha.ae_differentiableAt)
  have hbder : ∀ᵐ z ∂volume.restrict S, DifferentiableAt ℝ b z.2 := by
    rw [hprod]
    exact Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_of_ae (s := Icc 0 1) hb.ae_differentiableAt)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hbound : ∀ᵐ z ∂volume.restrict S, er z ≤ L ^ 2 * e z := by
    filter_upwards [hader, hbder] with z hza hzb
    have hA : DifferentiableAt ℝ A z := differentiableAt_affineCylinderInterpolation hza hzb
    have hcol (v : ℝ × ℝ) : ‖fderiv ℝ (R ∘ A) z v‖ ^ 2 ≤
        L ^ 2 * ‖fderiv ℝ A z v‖ ^ 2 := by
      rw [fderiv_comp z (hR (A z)) hA]
      have hnorm : ‖fderiv ℝ R (A z) (fderiv ℝ A z v)‖ ≤ L * ‖fderiv ℝ A z v‖ :=
        ((fderiv ℝ R (A z)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hL (A z)) (norm_nonneg _))
      simpa only [mul_pow, comp_apply] using
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL0 (norm_nonneg _))).mpr hnorm
    have h₁ := hcol (1, 0)
    have h₂ := hcol (0, 1)
    dsimp only [e, er]
    nlinarith
  have he : Integrable e (volume.restrict S) :=
    integrableOn_energy_affineCylinderInterpolation h ha hb
  have her : Integrable er (volume.restrict S) := by
    have h₁ := (measurable_fderiv_apply_const ℝ (R ∘ A) (1, 0)).norm.pow_const 2
    have h₂ := (measurable_fderiv_apply_const ℝ (R ∘ A) (0, 1)).norm.pow_const 2
    apply (he.const_mul (L ^ 2)).mono' ((h₁.add h₂).div_const 2).aestronglyMeasurable
    filter_upwards [hbound] with z hz
    rw [Real.norm_of_nonneg (by dsimp [er]; positivity)]
    exact hz
  simpa only [integral_const_mul] using integral_mono_ae her (he.const_mul (L ^ 2)) hbound

end DifferentialGeometry.Analysis.Sobolev

end

noncomputable section

open Set MeasureTheory Filter
open scoped NNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem tendsto_energy_affineCylinderInterpolation_of_tendsto_integral_norm_sub_sq
    (a b : ℕ → ℝ → F) (Ka Kb : ℕ → ℝ≥0)
    (ha : ∀ n, LipschitzWith (Ka n) (a n)) (hb : ∀ n, LipschitzWith (Kb n) (b n))
    (hgap : Tendsto (fun n => ∫ t in Icc (0 : ℝ) 1, ‖a n t - b n t‖ ^ 2) atTop (𝓝 0))
    {B : ℝ} (hder : ∀ n,
      (∫ t in Icc (0 : ℝ) 1, ‖deriv (a n) t‖ ^ 2 + ‖deriv (b n) t‖ ^ 2) ≤ B) :
    let h : ℕ → ℝ := fun n =>
      Real.sqrt (∫ t in Icc (0 : ℝ) 1, ‖a n t - b n t‖ ^ 2) + 1 / ((n : ℝ) + 1)
    (∀ n, 0 < h n) ∧ Tendsto h atTop (𝓝 0) ∧
      (∀ n, (∫ z in Icc (0 : ℝ) (h n) ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ (affineCylinderInterpolation (h n) (a n) (b n)) z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (affineCylinderInterpolation (h n) (a n) (b n)) z (0, 1)‖ ^ 2) / 2) ≤
        Real.sqrt (∫ t in Icc (0 : ℝ) 1, ‖a n t - b n t‖ ^ 2) / 2 + (h n / 2) * B) ∧
      Tendsto (fun n => ∫ z in Icc (0 : ℝ) (h n) ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ (affineCylinderInterpolation (h n) (a n) (b n)) z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (affineCylinderInterpolation (h n) (a n) (b n)) z (0, 1)‖ ^ 2) / 2)
        atTop (𝓝 0) := by
  let δ (n : ℕ) : ℝ := ∫ t in Icc (0 : ℝ) 1, ‖a n t - b n t‖ ^ 2
  let h (n : ℕ) := Real.sqrt (δ n) + 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 ≤ δ n := integral_nonneg fun _ => sq_nonneg _
  have hh (n : ℕ) : 0 < h n := by dsimp [h]; positivity
  have hsqrt : Tendsto (fun n => Real.sqrt (δ n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def, δ] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hgap
  have hwidth : Tendsto h atTop (𝓝 0) := by
    simpa only [add_zero] using hsqrt.add tendsto_one_div_add_atTop_nhds_zero_nat
  let energy (n : ℕ) : ℝ := ∫ z in Icc (0 : ℝ) (h n) ×ˢ Icc (0 : ℝ) 1,
    (‖fderiv ℝ (affineCylinderInterpolation (h n) (a n) (b n)) z (1, 0)‖ ^ 2 +
      ‖fderiv ℝ (affineCylinderInterpolation (h n) (a n) (b n)) z (0, 1)‖ ^ 2) / 2
  have hbound (n : ℕ) : energy n ≤ Real.sqrt (δ n) / 2 + (h n / 2) * B := by
    have hbase := integral_energy_affineCylinderInterpolation_le (hh n) (ha n) (hb n)
    have hsmall : (1 / (2 * h n)) * δ n ≤ Real.sqrt (δ n) / 2 := by
      have hge : Real.sqrt (δ n) ≤ h n := le_add_of_nonneg_right (by positivity)
      have hm := mul_le_mul_of_nonneg_right hge (Real.sqrt_nonneg (δ n))
      have hsquare := Real.sq_sqrt (hδ n)
      calc
        (1 / (2 * h n)) * δ n = δ n / (2 * h n) := by ring
        _ ≤ Real.sqrt (δ n) / 2 := (div_le_iff₀ (by positivity : 0 < 2 * h n)).mpr
          (by nlinarith)
    exact hbase.trans (add_le_add hsmall
      (mul_le_mul_of_nonneg_left (hder n) (by positivity)))
  refine ⟨hh, hwidth, hbound, ?_⟩
  have hup : Tendsto (fun n => Real.sqrt (δ n) / 2 + (h n / 2) * B) atTop (𝓝 0) := by
    simpa only [zero_div, zero_mul, add_zero] using
      (hsqrt.div_const 2).add ((hwidth.div_const 2).mul_const B)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => integral_nonneg fun _ => by positivity) hbound

end DifferentialGeometry.Analysis.Sobolev

end
