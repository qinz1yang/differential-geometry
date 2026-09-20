import DifferentialGeometry.Analysis.Calculus.Rademacher
import DifferentialGeometry.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_contDiffOn
    {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    {Ω : Set E} (hΩ : IsOpen Ω) {f φ : E → 𝕜}
    (hf : ContDiffOn ℝ 1 f Ω) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) (v : E) :
    (∫ x in Ω, f x * fderiv ℝ φ x v ∂μ) = -∫ x in Ω, fderiv ℝ f x v * φ x ∂μ := by
  have hdφs : tsupport (fun x => fderiv ℝ φ x v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφs
  have hdφc : HasCompactSupport (fun x => fderiv ℝ φ x v) := hφc.fderiv_apply (𝕜 := ℝ) v
  have hdc : ContinuousOn (fun x => fderiv ℝ f x v) Ω :=
    (hf.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint₁ : Integrable (fun x => fderiv ℝ f x v * φ x) μ :=
    ((hdc.mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport hφc.mul_left
  have hint₂ : Integrable (fun x => f x * fderiv ℝ φ x v) μ :=
    ((hf.continuousOn.mul hdφ.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hdφs)).integrable_of_hasCompactSupport hdφc.mul_left
  have hint₃ : Integrable (fun x => f x * φ x) μ :=
    ((hf.continuousOn.mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport hφc.mul_left
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hint₁ hint₂ hint₃
      (fun x hx => ((hf x (hφs hx)).contDiffAt (hΩ.mem_nhds (hφs hx))).differentiableAt
        one_ne_zero)
      (fun x _ => (hφ.differentiable one_ne_zero) x)
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := φ) (fun h => hx (hφs h)), mul_zero]
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport
      (f := fun x => fderiv ℝ φ x v) (fun h => hx (hdφs h)), mul_zero]

theorem integral_mul_fderiv_eq_neg_lineDeriv_mul_of_locallyLipschitzOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {f φ : E → ℝ} {Ω : Set E} (hf : LocallyLipschitzOn Ω f)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) (v : E) :
    (∫ x in Ω, f x * fderiv ℝ φ x v ∂μ) =
      -∫ x in Ω, lineDeriv ℝ f x v * φ x ∂μ := by
  obtain ⟨C, hC⟩ := (hf.mono hφs).exists_lipschitzOnWith_of_compact hφc
  obtain ⟨g, hg, hfg⟩ := hC.extend_real
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by simp)
  have hderiv_sub : tsupport (fun x => fderiv ℝ φ x v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφs
  have hleft (x : E) : f x * fderiv ℝ φ x v = g x * fderiv ℝ φ x v := by
    by_cases hx : fderiv ℝ φ x v = 0
    · rw [hx, mul_zero, mul_zero]
    · rw [hfg ((tsupport_fderiv_apply_subset ℝ v) (subset_tsupport _ hx))]
  have hright (x : E) : lineDeriv ℝ g x v * φ x = lineDeriv ℝ f x v * φ x := by
    by_cases hx : φ x = 0
    · rw [hx, mul_zero, mul_zero]
    · have heq : f =ᶠ[𝓝 x] g := by
        filter_upwards [hφ.continuous.continuousAt.eventually_ne hx] with y hy
        exact hfg (subset_tsupport φ hy)
      rw [heq.lineDeriv_eq]
  have hibp := LipschitzWith.integral_lineDeriv_mul_eq (μ := μ) hg hD hφc v
  have hdφ (x : E) : lineDeriv ℝ φ x (-v) = -fderiv ℝ φ x v := by
    rw [((hφ.differentiable one_ne_zero) x).lineDeriv_eq_fderiv, map_neg]
  simp_rw [hdφ, neg_mul, mul_comm _ (g _)] at hibp
  rw [integral_neg] at hibp
  have hz₁ (x : E) (hx : x ∉ Ω) : g x * fderiv ℝ φ x v = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ φ x v)
      (fun h => hx (hderiv_sub h)), mul_zero]
  have hz₂ (x : E) (hx : x ∉ Ω) : lineDeriv ℝ g x v * φ x = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (f := φ) (fun h => hx (hφs h)), mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz₁,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hz₂] at hibp
  calc
    _ = ∫ x in Ω, g x * fderiv ℝ φ x v ∂μ := integral_congr_ae (.of_forall hleft)
    _ = -∫ x in Ω, lineDeriv ℝ g x v * φ x ∂μ := by linarith [hibp]
    _ = _ := congrArg Neg.neg (integral_congr_ae (.of_forall hright))


theorem integral_fderiv_fderiv_mul_eq_of_locallyLipschitzOn_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {u φ : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hu : DifferentiableOn ℝ u Ω)
    (hdu : LocallyLipschitzOn Ω (fderiv ℝ u))
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) (v w : E) :
    (∫ x in Ω, fderiv ℝ (fderiv ℝ u) x v w * φ x ∂μ) =
      ∫ x in Ω, u x * fderiv ℝ (fderiv ℝ φ) x w v ∂μ := by
  have hu1 : ContDiffOn ℝ 1 u Ω := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hΩ).mpr
    exact ⟨hu, by norm_num, contDiffOn_zero.mpr hdu.continuousOn⟩
  have hw : LocallyLipschitzOn Ω (fun x => fderiv ℝ u x w) :=
    ((ContinuousLinearMap.apply ℝ ℝ w).lipschitz.locallyLipschitz.locallyLipschitzOn).comp
      hdu (Set.mapsTo_univ _ _)
  have hd : (fun x => lineDeriv ℝ (fun y => fderiv ℝ u y w) x v) =ᵐ[μ.restrict Ω]
      (fun x => fderiv ℝ (fderiv ℝ u) x v w) := by
    filter_upwards [hdu.ae_differentiableAt hΩ] with x hx
    rw [(hx.clm_apply (differentiableAt_const w)).lineDeriv_eq_fderiv,
      fderiv_clm_apply hx (differentiableAt_const w)]
    simp
  have h₁ := integral_mul_fderiv_eq_neg_lineDeriv_mul_of_locallyLipschitzOn
    (μ := μ) hw (hφ.of_le (by norm_num)) hφc hφs v
  have htest : ContDiff ℝ 1 (fun x => fderiv ℝ φ x v) :=
    (hφ.fderiv_right (by norm_num)).clm_apply contDiff_const
  have h₂ := integral_mul_fderiv_eq_neg_fderiv_mul_of_contDiffOn (μ := μ) hΩ hu1
    htest (hφc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hφs) w
  have heq (x : E) : fderiv ℝ (fun y => fderiv ℝ φ y v) x w =
      fderiv ℝ (fderiv ℝ φ) x w v := by
    rw [fderiv_clm_apply ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)
      (differentiableAt_const v)]
    simp
  simp_rw [heq] at h₂
  have hdint : (∫ x in Ω, lineDeriv ℝ (fun y => fderiv ℝ u y w) x v * φ x ∂μ) =
      ∫ x in Ω, fderiv ℝ (fderiv ℝ u) x v w * φ x ∂μ :=
    integral_congr_ae (hd.mul (.refl _ _))
  linarith

end DifferentialGeometry.Analysis
