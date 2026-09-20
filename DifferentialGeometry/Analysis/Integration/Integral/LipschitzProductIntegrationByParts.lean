import DifferentialGeometry.Analysis.Integration.Integral.Prod
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Compactness.LocallyCompact

open MeasureTheory Set Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ν : Measure ℝ} [IsFiniteMeasureOnCompacts ν]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

private theorem integral_fderiv_prod_eq_neg_of_lipschitzWith
    {f h : ℝ × E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h) (v : E) :
    Integrable (fun p => f p * fderiv ℝ h p (0, v)) (ν.prod μ) ∧
      Integrable (fun p => fderiv ℝ (fun x => f (p.1, x)) p.2 v * h p) (ν.prod μ) ∧
      (∫ p, f p * fderiv ℝ h p (0, v) ∂ν.prod μ) =
        -(∫ p, fderiv ℝ (fun x => f (p.1, x)) p.2 v * h p ∂ν.prod μ) := by
  have hf_slice (t : ℝ) : LipschitzWith L (fun x : E => f (t, x)) := by
    simpa only [Function.comp_def, mul_one] using
      hf.comp (LipschitzWith.prodMk_left t)
  have hd : Continuous (fun p => fderiv ℝ h p (0, v)) :=
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hleft : Integrable (fun p => f p * fderiv ℝ h p (0, v)) (ν.prod μ) :=
    (hf.continuous.mul hd).integrable_of_hasCompactSupport
      (hhc.fderiv_apply (𝕜 := ℝ) (0, v)).mul_left
  have hmeas : Measurable (fun p : ℝ × E =>
      fderiv ℝ (fun x => f (p.1, x)) p.2 v) :=
    measurable_fderiv_apply_const_with_param ℝ
      (f := fun t x => f (t, x)) hf.continuous v
  have hright : Integrable
      (fun p => fderiv ℝ (fun x => f (p.1, x)) p.2 v * h p) (ν.prod μ) := by
    apply ((hh.continuous.integrable_of_hasCompactSupport hhc).norm.const_mul
      ((L : ℝ) * ‖v‖)).mono'
        (hmeas.aestronglyMeasurable.mul hh.continuous.aestronglyMeasurable)
    filter_upwards with p
    change ‖fderiv ℝ (fun x => f (p.1, x)) p.2 v * h p‖ ≤
      (L : ℝ) * ‖v‖ * ‖h p‖
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact ((fderiv ℝ (fun x => f (p.1, x)) p.2).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right
        (norm_fderiv_le_of_lipschitz ℝ (hf_slice p.1)) (norm_nonneg v))
  refine ⟨hleft, hright, ?_⟩
  rw [hleft.integral_prod, hright.integral_prod, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with t
  have hs : ContDiff ℝ 1 (fun x : E => h (t, x)) :=
    hh.comp (contDiff_const.prodMk contDiff_id)
  have hsupport : tsupport (fun x : E => h (t, x)) ⊆ Prod.snd '' tsupport h := by
    intro x hx
    exact ⟨(t, x), tsupport_comp_subset_preimage
      (f := fun y : E => (t, y)) h (by fun_prop) hx, rfl⟩
  have hsc : HasCompactSupport (fun x : E => h (t, x)) :=
    IsCompact.of_isClosed_subset (hhc.image continuous_snd) (isClosed_tsupport _) hsupport
  obtain ⟨D, hsl⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsc hs one_ne_zero
  have hderiv (x : E) :
      fderiv ℝ (fun y : E => h (t, y)) x v = fderiv ℝ h (t, x) (0, v) := by
    have hcomp := (hh.differentiable one_ne_zero (t, x)).hasFDerivAt.comp x
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    exact congrArg (fun A => A v) hcomp.fderiv
  have hline (x : E) :
      lineDeriv ℝ (fun y : E => h (t, y)) x (-v) * f (t, x) =
        -(f (t, x) * fderiv ℝ h (t, x) (0, v)) := by
    rw [(hs.differentiable one_ne_zero x).lineDeriv_eq_fderiv, map_neg, hderiv]
    ring
  have hdf :
      (∫ x, fderiv ℝ (fun y => f (t, y)) x v * h (t, x) ∂μ) =
        ∫ x, lineDeriv ℝ (fun y => f (t, y)) x v * h (t, x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [(hf_slice t).ae_differentiableAt (μ := μ)] with x hx
    rw [hx.lineDeriv_eq_fderiv]
  have hibp := (hf_slice t).integral_lineDeriv_mul_eq (μ := μ) hsl hsc v
  simp_rw [hline] at hibp
  rw [integral_neg] at hibp
  have heq := hdf.trans hibp
  calc
    (∫ x, f (t, x) * fderiv ℝ h (t, x) (0, v) ∂μ) =
        -(-(∫ x, f (t, x) * fderiv ℝ h (t, x) (0, v) ∂μ)) := (neg_neg _).symm
    _ = -(∫ x, fderiv ℝ (fun y => f (t, y)) x v * h (t, x) ∂μ) :=
      congrArg Neg.neg heq.symm

namespace LocallyLipschitzOn

theorem integral_fderiv_prod_eq_neg
    {W : Set (ℝ × E)} {f h : ℝ × E → ℝ}
    (hf : LocallyLipschitzOn W f) (hW : IsOpen W)
    (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h)
    (hhs : tsupport h ⊆ W) (v : E) :
    Integrable (fun p => f p * fderiv ℝ h p (0, v)) (ν.prod μ) ∧
      Integrable (fun p => fderiv ℝ (fun x => f (p.1, x)) p.2 v * h p) (ν.prod μ) ∧
      (∫ p, f p * fderiv ℝ h p (0, v) ∂ν.prod μ) =
        -(∫ p, fderiv ℝ (fun x => f (p.1, x)) p.2 v * h p ∂ν.prod μ) := by
  obtain ⟨K, hK, hhK, hKW⟩ := exists_compact_between hhc hW hhs
  obtain ⟨L, hL⟩ := (hf.mono hKW).exists_lipschitzOnWith_of_compact hK
  obtain ⟨g, hg, hfg⟩ := hL.extend_real
  have heq {p : ℝ × E} (hp : p ∈ tsupport h) : f =ᶠ[𝓝 p] g :=
    hfg.eventuallyEq_of_mem (mem_interior_iff_mem_nhds.mp (hhK hp))
  have hleft_eq :
      (fun p => g p * fderiv ℝ h p (0, v)) =
        (fun p => f p * fderiv ℝ h p (0, v)) := by
    funext p
    by_cases hp : p ∈ tsupport h
    · rw [(heq hp).self_of_nhds]
    · rw [fderiv_of_notMem_tsupport ℝ hp]
      simp only [zero_apply, mul_zero]
  have hright_eq :
      (fun p => fderiv ℝ (fun x => g (p.1, x)) p.2 v * h p) =
        (fun p => fderiv ℝ (fun x => f (p.1, x)) p.2 v * h p) := by
    funext p
    by_cases hp : p ∈ tsupport h
    · have hslice : (fun x => f (p.1, x)) =ᶠ[𝓝 p.2] (fun x => g (p.1, x)) :=
        (heq hp).comp_tendsto (continuousAt_const.prodMk continuousAt_id)
      rw [hslice.fderiv_eq]
    · rw [image_eq_zero_of_notMem_tsupport hp]
      simp only [mul_zero]
  simpa only [hleft_eq, hright_eq] using
    integral_fderiv_prod_eq_neg_of_lipschitzWith (ν := ν) (μ := μ) hg hh hhc v

end LocallyLipschitzOn
