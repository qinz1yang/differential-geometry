import DifferentialGeometry.Analysis.Elliptic.Planar.FirstOrderReduction
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.BoundedCoefficient

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ContDiff ComplexConjugate

namespace DifferentialGeometry.Analysis

private theorem fderiv_eq_planarComplexGradient_pair (v : ℂ → ℝ) (z B : ℂ) :
    (fderiv ℝ v z B : ℂ) =
      B * planarComplexGradient v z + conj B * conj (planarComplexGradient v z) := by
  have hB : B = B.re • (1 : ℂ) + B.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hB, map_add, map_smul, map_smul]
  apply Complex.ext <;>
    simp [planarComplexGradient, Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

/-- The literal weak right-hand side has the same linear-plus-conjugate
coefficients as the classical augmented equation. This is pointwise algebra and
does not differentiate the augmented section. -/
theorem planarGradientSection_weak_rhs_eq (v : ℂ → ℝ) (z B : ℂ) (q : ℝ) :
    (-((fderiv ℝ v z B + q * v z : ℝ) : ℂ) / 4,
      conj (planarComplexGradient v z)) =
      planarGradientLinearCoefficient B q (planarGradientSection v z) +
        planarGradientConjugateCoefficient B
          (conj (planarGradientSection v z).1, conj (planarGradientSection v z).2) := by
  apply Prod.ext
  · change -((fderiv ℝ v z B + q * v z : ℝ) : ℂ) / 4 =
      (-(1 / 4 : ℂ) * B * planarComplexGradient v z +
        -(1 / 4 : ℂ) * (q : ℂ) * (v z : ℂ)) +
      (-(1 / 4 : ℂ) * conj B * conj (planarComplexGradient v z) + 0)
    simp only [Complex.ofReal_add, Complex.ofReal_mul]
    rw [fderiv_eq_planarComplexGradient_pair v z B]
    ring
  · change conj (planarComplexGradient v z) =
      (-(1 / 4 : ℂ) * B * 0 + -(1 / 4 : ℂ) * (q : ℂ) * 0) +
      (-(1 / 4 : ℂ) * conj B * 0 + conj (planarComplexGradient v z))
    simp

/-- Uniform bounds for the original drift and potential bound the two actual
coefficient operators, without any regularity assumption on those fields. -/
theorem norm_planarGradientCoefficients_le (B : ℂ) (q : ℝ) :
    ‖planarGradientLinearCoefficient B q‖ + ‖planarGradientConjugateCoefficient B‖ ≤
      ‖B‖ / 2 + |q| / 4 + 1 := by
  let L₁ := (ContinuousLinearMap.inl ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ ℂ ℂ)
  let L₂ := (ContinuousLinearMap.inl ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ ℂ)
  let L₃ := (ContinuousLinearMap.inr ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ ℂ ℂ)
  have hL₁ : ‖L₁‖ ≤ 1 := by
    simpa only [L₁, ContinuousLinearMap.norm_inl, ContinuousLinearMap.norm_fst,
      one_mul] using
      (ContinuousLinearMap.inl ℂ ℂ ℂ).opNorm_comp_le (ContinuousLinearMap.fst ℂ ℂ ℂ)
  have hL₂ : ‖L₂‖ ≤ 1 := by
    simpa only [L₂, ContinuousLinearMap.norm_inl, ContinuousLinearMap.norm_snd,
      one_mul] using
      (ContinuousLinearMap.inl ℂ ℂ ℂ).opNorm_comp_le (ContinuousLinearMap.snd ℂ ℂ ℂ)
  have hL₃ : ‖L₃‖ ≤ 1 := by
    simpa only [L₃, ContinuousLinearMap.norm_inr, ContinuousLinearMap.norm_fst,
      one_mul] using
      (ContinuousLinearMap.inr ℂ ℂ ℂ).opNorm_comp_le (ContinuousLinearMap.fst ℂ ℂ ℂ)
  have hM : ‖planarGradientLinearCoefficient B q‖ ≤ ‖B‖ / 4 + |q| / 4 := by
    change ‖(-(1 / 4 : ℂ) * B) • L₁ + (-(1 / 4 : ℂ) * (q : ℂ)) • L₂‖ ≤ _
    calc
      _ ≤ ‖(-(1 / 4 : ℂ) * B) • L₁‖ +
          ‖(-(1 / 4 : ℂ) * (q : ℂ)) • L₂‖ := norm_add_le _ _
      _ = ‖-(1 / 4 : ℂ) * B‖ * ‖L₁‖ +
          ‖-(1 / 4 : ℂ) * (q : ℂ)‖ * ‖L₂‖ := by rw [norm_smul, norm_smul]
      _ ≤ ‖-(1 / 4 : ℂ) * B‖ * 1 +
          ‖-(1 / 4 : ℂ) * (q : ℂ)‖ * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hL₁ (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hL₂ (norm_nonneg _))
      _ = _ := by
        norm_num [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs] ; ring
  have hN : ‖planarGradientConjugateCoefficient B‖ ≤ ‖B‖ / 4 + 1 := by
    change ‖(-(1 / 4 : ℂ) * conj B) • L₁ + L₃‖ ≤ _
    calc
      _ ≤ ‖(-(1 / 4 : ℂ) * conj B) • L₁‖ + ‖L₃‖ := norm_add_le _ _
      _ = ‖-(1 / 4 : ℂ) * conj B‖ * ‖L₁‖ + ‖L₃‖ := by rw [norm_smul]
      _ ≤ ‖-(1 / 4 : ℂ) * conj B‖ * 1 + 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hL₁ (norm_nonneg _)) hL₃
      _ = _ := by norm_num [norm_mul, norm_div] ; ring
  calc
    _ ≤ (‖B‖ / 4 + |q| / 4) + (‖B‖ / 4 + 1) := add_le_add hM hN
    _ = _ := by ring

/-- The literal right-hand side is controlled by the same augmented section,
including at every zero of that section. -/
theorem planarGradientSection_weak_rhs_norm_le (v : ℂ → ℝ) (z B : ℂ) (q : ℝ) :
    ‖(-((fderiv ℝ v z B + q * v z : ℝ) : ℂ) / 4,
      conj (planarComplexGradient v z))‖ ≤
      (‖B‖ / 2 + |q| / 4 + 1) * ‖planarGradientSection v z‖ := by
  rw [planarGradientSection_weak_rhs_eq]
  have hc : ‖(conj (planarGradientSection v z).1,
      conj (planarGradientSection v z).2)‖ = ‖planarGradientSection v z‖ := by
    simp only [Prod.norm_def, Complex.norm_conj]
  calc
    _ ≤ ‖planarGradientLinearCoefficient B q (planarGradientSection v z)‖ +
        ‖planarGradientConjugateCoefficient B
          (conj (planarGradientSection v z).1, conj (planarGradientSection v z).2)‖ :=
      norm_add_le _ _
    _ ≤ ‖planarGradientLinearCoefficient B q‖ * ‖planarGradientSection v z‖ +
        ‖planarGradientConjugateCoefficient B‖ *
          ‖(conj (planarGradientSection v z).1, conj (planarGradientSection v z).2)‖ :=
      add_le_add ((planarGradientLinearCoefficient B q).le_opNorm _)
        ((planarGradientConjugateCoefficient B).le_opNorm _)
    _ = (‖planarGradientLinearCoefficient B q‖ +
        ‖planarGradientConjugateCoefficient B‖) * ‖planarGradientSection v z‖ := by
      rw [hc]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (norm_planarGradientCoefficients_le B q)
      (norm_nonneg _)

/-- A `C¹` scalar has a continuous literal augmented gradient. -/
theorem continuousOn_planarGradientSection_of_contDiffOn_one
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v Ω) :
    ContinuousOn (planarGradientSection v) Ω := by
  have hd := hv.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have ha := hd.clm_apply (continuousOn_const (c := (1 : ℂ)))
  have hb := hd.clm_apply (continuousOn_const (c := Complex.I))
  have hp := (ha.mul (continuousOn_const (c := (2 : ℝ)⁻¹))).prodMk
    (hb.neg.mul (continuousOn_const (c := (2 : ℝ)⁻¹)))
  have hg : ContinuousOn (planarComplexGradient v) Ω := by
    refine (Complex.equivRealProdCLM.symm.continuous.comp_continuousOn hp).congr ?_
    intro z _
    apply Complex.ext <;> simp [planarComplexGradient,
      Complex.equivRealProdCLM_symm_apply, div_eq_mul_inv]
  exact hg.prodMk (Complex.ofRealCLM.continuous.comp_continuousOn hv.continuousOn)

/-- Bounded measurable lower fields and the same `C¹` scalar give a globally
bounded measurable coefficient for its literal weak augmented right-hand side.
The equation is pointwise on the domain, and the coefficient is zero outside it. -/
theorem exists_measurable_planarGradientSection_weak_coefficient
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v Ω)
    {B : ℂ → ℂ} {q : ℂ → ℝ}
    (hB : Measurable (fun z : Ω => B z)) (hq : Measurable (fun z : Ω => q z))
    {b₀ q₀ : ℝ} (hb₀ : 0 ≤ b₀) (hq₀ : 0 ≤ q₀)
    (hBbound : ∀ z ∈ Ω, ‖B z‖ ≤ b₀) (hqbound : ∀ z ∈ Ω, |q z| ≤ q₀) :
    ∃ A : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ),
      Measurable A ∧
      (∀ z ∈ Ω, A z (planarGradientSection v z) =
        (-((fderiv ℝ v z (B z) + q z * v z : ℝ) : ℂ) / 4,
          conj (planarComplexGradient v z))) ∧
      (∀ z, ‖A z‖ ≤ b₀ / 2 + q₀ / 4 + 1) ∧ (∀ z ∉ Ω, A z = 0) := by
  have hξ : Measurable (fun z : Ω => planarGradientSection v z) :=
    (continuousOn_planarGradientSection_of_contDiffOn_one hΩ hv).domRestrict.measurable
  have hd : Measurable (fun z : Ω => fderiv ℝ v z) :=
    (hv.continuousOn_fderiv_of_isOpen hΩ le_rfl).domRestrict.measurable
  have heval : Continuous (fun p : (ℂ →L[ℝ] ℝ) × ℂ => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hS : Measurable (fun z : Ω => fderiv ℝ v z (B z) + q z * v z) :=
    (heval.measurable.comp (hd.prodMk hB)).add
      (hq.mul hv.continuousOn.domRestrict.measurable)
  have hF : Measurable (fun z : Ω =>
      (-((fderiv ℝ v z (B z) + q z * v z : ℝ) : ℂ) / 4,
        conj (planarComplexGradient v z))) :=
    ((Complex.ofRealCLM.measurable.comp hS).neg.div_const 4).prodMk
      (Complex.conjCLE.continuous.measurable.comp hξ.fst)
  apply exists_measurable_pair_coefficient_on hΩ.measurableSet hξ hF
    (by positivity)
  intro z hz
  exact (planarGradientSection_weak_rhs_norm_le v z (B z) (q z)).trans
    (mul_le_mul_of_nonneg_right (by linarith [hBbound z hz, hqbound z hz])
      (norm_nonneg _))

end DifferentialGeometry.Analysis
