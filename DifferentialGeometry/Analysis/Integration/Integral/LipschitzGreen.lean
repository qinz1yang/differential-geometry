import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import DifferentialGeometry.Analysis.Integration.Integral.RegionBetween
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace LipschitzWith

theorem ae_integral_fderiv_snd_eq_sub
    {K : ℝ≥0} {f : ℝ × ℝ → ℝ} (hf : LipschitzWith K f) :
    ∀ᵐ x : ℝ, ∀ a b : ℝ,
      (∫ y in a..b, fderiv ℝ f (x, y) (0, 1)) = f (x, b) - f (x, a) := by
  have hd : ∀ᵐ x : ℝ, ∀ᵐ y : ℝ, DifferentiableAt ℝ f (x, y) :=
    Measure.ae_ae_of_ae_prod hf.ae_differentiableAt
  filter_upwards [hd] with x hx
  intro a b
  have hs : LipschitzWith K (fun y : ℝ => f (x, y)) :=
    fun a b => by simpa only [Prod.edist_eq, edist_self, zero_max] using hf (x, a) (x, b)
  have hac : AbsolutelyContinuousOnInterval (fun y : ℝ => f (x, y)) a b :=
    hs.lipschitzOnWith.absolutelyContinuousOnInterval
  rw [← hac.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hx] with y hy _
  have hp : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  exact (hy.hasFDerivAt.comp_hasDerivAt y hp).deriv.symm

theorem ae_integral_mul_fderiv_snd_add_eq_boundary
    {K L : ℝ≥0} {f g : ℝ × ℝ → ℝ} (hf : LipschitzWith K f) (hg : LipschitzWith L g) :
    ∀ᵐ x : ℝ, ∀ a b : ℝ,
      (∫ y in a..b, fderiv ℝ f (x, y) (0, 1) * g (x, y) +
        f (x, y) * fderiv ℝ g (x, y) (0, 1)) =
          f (x, b) * g (x, b) - f (x, a) * g (x, a) := by
  have hdf : ∀ᵐ x : ℝ, ∀ᵐ y : ℝ, DifferentiableAt ℝ f (x, y) :=
    Measure.ae_ae_of_ae_prod hf.ae_differentiableAt
  have hdg : ∀ᵐ x : ℝ, ∀ᵐ y : ℝ, DifferentiableAt ℝ g (x, y) :=
    Measure.ae_ae_of_ae_prod hg.ae_differentiableAt
  filter_upwards [hdf, hdg] with x hxf hxg
  intro a b
  have hsf : LipschitzWith K (fun y : ℝ => f (x, y)) :=
    fun a b => by simpa only [Prod.edist_eq, edist_self, zero_max] using hf (x, a) (x, b)
  have hsg : LipschitzWith L (fun y : ℝ => g (x, y)) :=
    fun a b => by simpa only [Prod.edist_eq, edist_self, zero_max] using hg (x, a) (x, b)
  have hacf : AbsolutelyContinuousOnInterval (fun y : ℝ => f (x, y)) a b :=
    hsf.lipschitzOnWith.absolutelyContinuousOnInterval
  have hacg : AbsolutelyContinuousOnInterval (fun y : ℝ => g (x, y)) a b :=
    hsg.lipschitzOnWith.absolutelyContinuousOnInterval
  rw [← hacf.integral_deriv_mul_eq_sub hacg]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hxf, hxg] with y hyf hyg _
  have hp : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have hfy : deriv (fun t : ℝ => f (x, t)) y = fderiv ℝ f (x, y) (0, 1) :=
    (hyf.hasFDerivAt.comp_hasDerivAt y hp).deriv
  have hgy : deriv (fun t : ℝ => g (x, t)) y = fderiv ℝ g (x, y) (0, 1) :=
    (hyg.hasFDerivAt.comp_hasDerivAt y hp).deriv
  rw [hfy, hgy]

theorem integral_chord_fderiv_snd_eq_boundary
    {K : ℝ≥0} {f : ℝ × ℝ → ℝ} (hf : LipschitzWith K f)
    (a b : ℝ → ℝ) (s : Set ℝ) :
    (∫ x in s, ∫ y in a x..b x, fderiv ℝ f (x, y) (0, 1)) =
      ∫ x in s, f (x, b x) - f (x, a x) := by
  apply integral_congr_ae
  filter_upwards [ae_mono Measure.restrict_le_self (LipschitzWith.ae_integral_fderiv_snd_eq_sub hf)] with x hx
  exact hx (a x) (b x)

end LipschitzWith

end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace LipschitzWith

theorem integral_mul_fderiv_snd_add_regionBetween
    {K L : ℝ≥0} {f g : ℝ × ℝ → ℝ} (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    {a b : ℝ → ℝ} {s : Set ℝ} (ha : Measurable a) (hb : Measurable b)
    (hs : MeasurableSet s) (hab : ∀ x ∈ s, a x ≤ b x)
    (hi : IntegrableOn (fun p => fderiv ℝ f p (0, 1) * g p +
      f p * fderiv ℝ g p (0, 1)) (regionBetween a b s)) :
    (∫ p in regionBetween a b s, fderiv ℝ f p (0, 1) * g p +
      f p * fderiv ℝ g p (0, 1)) =
      ∫ x in s, f (x, b x) * g (x, b x) - f (x, a x) * g (x, a x) := by
  rw [Measure.volume_eq_prod,
    integral_regionBetween_eq_integral_intervalIntegral ha hb hs hab hi]
  apply integral_congr_ae
  filter_upwards [ae_mono Measure.restrict_le_self
    (LipschitzWith.ae_integral_mul_fderiv_snd_add_eq_boundary hf hg)] with x hx
  exact hx (a x) (b x)

private theorem integrableOn_fderiv_snd_square
    {K : ℝ≥0} {f : ℝ × ℝ → ℝ} (hf : LipschitzWith K f) :
    IntegrableOn (fun p => fderiv ℝ f p (0, 1))
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := by
  apply (integrableOn_const (C := (K : ℝ))
    (isCompact_Icc.prod isCompact_Icc).measure_ne_top).mono'
      (measurable_fderiv_apply_const ℝ f (0, 1)).aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  have h := (fderiv ℝ f p).le_opNorm (0, 1)
  have hn : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp
  rw [hn, mul_one] at h
  exact h.trans (norm_fderiv_le_of_lipschitz ℝ hf)

private theorem regionBetween_sqrt_eq_unit_disk :
    regionBetween (fun x : ℝ => -Real.sqrt (1 - x ^ 2))
      (fun x : ℝ => Real.sqrt (1 - x ^ 2)) (Ioo (-1 : ℝ) 1) =
        {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1} := by
  ext p
  change (-1 < p.1 ∧ p.1 < 1) ∧
    (-Real.sqrt (1 - p.1 ^ 2) < p.2 ∧ p.2 < Real.sqrt (1 - p.1 ^ 2)) ↔
      p.1 ^ 2 + p.2 ^ 2 < 1
  constructor
  · intro hp
    have hx : 0 ≤ 1 - p.1 ^ 2 := by nlinarith [hp.1.1, hp.1.2]
    have hsq := Real.sq_sqrt hx
    have hy : p.2 ^ 2 < (Real.sqrt (1 - p.1 ^ 2)) ^ 2 := by
      nlinarith [hp.2.1, hp.2.2]
    nlinarith
  · intro hp
    have hx : 0 < 1 - p.1 ^ 2 := by nlinarith [sq_nonneg p.2]
    have hsqrt := Real.sqrt_nonneg (1 - p.1 ^ 2)
    have hsq := Real.sq_sqrt hx.le
    exact ⟨⟨by nlinarith [sq_nonneg p.2], by nlinarith [sq_nonneg p.2]⟩,
      ⟨by nlinarith, by nlinarith⟩⟩

theorem integral_mul_fderiv_snd_add_unit_disk
    {K L : ℝ≥0} {f g : ℝ × ℝ → ℝ} (hf : LipschitzWith K f) (hg : LipschitzWith L g) :
    (∫ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1},
      fderiv ℝ f p (0, 1) * g p + f p * fderiv ℝ g p (0, 1)) =
      ∫ x in Ioo (-1 : ℝ) 1,
        f (x, Real.sqrt (1 - x ^ 2)) * g (x, Real.sqrt (1 - x ^ 2)) -
        f (x, -Real.sqrt (1 - x ^ 2)) * g (x, -Real.sqrt (1 - x ^ 2)) := by
  rw [← regionBetween_sqrt_eq_unit_disk]
  have hsub : regionBetween (fun x : ℝ => -Real.sqrt (1 - x ^ 2))
        (fun x : ℝ => Real.sqrt (1 - x ^ 2)) (Ioo (-1 : ℝ) 1) ⊆
      Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    intro p hp
    have hroot : Real.sqrt (1 - p.1 ^ 2) ≤ 1 := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by norm_num, by nlinarith [sq_nonneg p.1]⟩
    exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  apply LipschitzWith.integral_mul_fderiv_snd_add_regionBetween hf hg
    (by fun_prop) (by fun_prop) measurableSet_Ioo
    (fun x _ => by linarith [Real.sqrt_nonneg (1 - x ^ 2)])
  have hfi := (integrableOn_fderiv_snd_square hf).mul_continuousOn
    hg.continuous.continuousOn (isCompact_Icc.prod isCompact_Icc)
  have hgi := (integrableOn_fderiv_snd_square hg).mul_continuousOn
    hf.continuous.continuousOn (isCompact_Icc.prod isCompact_Icc)
  apply (hfi.add (hgi.congr_fun (fun p _ => mul_comm _ _)
    (measurableSet_Icc.prod measurableSet_Icc))).mono_set hsub

end LipschitzWith

end
