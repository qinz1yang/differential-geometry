import DifferentialGeometry.Analysis.Integration.Lp.Product
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

open scoped ENNReal InnerProductSpace

namespace MeasureTheory

variable {A B E 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace A] [MeasurableSpace B]
variable {μ : Measure A} {ν : Measure B} [SFinite ν]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

private theorem uncurry_tensor_coeFn (η : Lp 𝕜 2 μ) (ψ : Lp E 2 ν) :
    (Lp.uncurry 𝕜 (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      ((ContinuousLinearMap.toSpanSingleton 𝕜 ψ).compLpL 2 μ η) : A × B → E)
        =ᵐ[μ.prod ν] fun z => η z.1 • ψ z.2 := by
  let F := Lp.uncurry 𝕜 (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    ((ContinuousLinearMap.toSpanSingleton 𝕜 ψ).compLpL 2 μ η)
  have hm : StronglyMeasurable (fun z : A × B => η z.1 • ψ z.2) :=
    ((Lp.stronglyMeasurable η).comp_measurable measurable_fst).smul
      ((Lp.stronglyMeasurable ψ).comp_measurable measurable_snd)
  apply (Measure.ae_prod_iff_ae_ae ((Lp.stronglyMeasurable F).measurableSet_eq_fun hm)).mpr
  filter_upwards [Lp.uncurry_compLpL_coeFn (𝕜 := 𝕜)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (ContinuousLinearMap.toSpanSingleton 𝕜 ψ) η]
    with a ha
  filter_upwards [ha, Lp.coeFn_smul (η a) ψ] with b hb hc
  change F (a, b) = ((η a) • ψ) b at hb
  exact hb.trans hc

omit [SFinite ν] [CompleteSpace E] in
private theorem inner_tensor_eq_integral (P : Lp (Lp E 2 ν) 2 μ)
    (η : Lp 𝕜 2 μ) (ψ : Lp E 2 ν) :
    inner 𝕜 P
      ((ContinuousLinearMap.toSpanSingleton 𝕜 ψ).compLpL 2 μ η) =
      ∫ a, η a * inner 𝕜 (P a) ψ ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.toSpanSingleton 𝕜 ψ).coeFn_compLpL η] with a ha
  rw [ha]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, inner_smul_right]

private theorem inner_uncurry_tensor_eq_integral (R : Lp E 2 (μ.prod ν))
    (η : Lp 𝕜 2 μ) (ψ : Lp E 2 ν) :
    inner 𝕜 R (Lp.uncurry 𝕜 (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      ((ContinuousLinearMap.toSpanSingleton 𝕜 ψ).compLpL 2 μ η)) =
      ∫ z, η z.1 * inner 𝕜 (R z) (ψ z.2) ∂μ.prod ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [uncurry_tensor_coeFn η ψ] with z hz
  rw [hz, inner_smul_right]

theorem Lp.integrable_mul_inner_tensor (R : Lp E 2 (μ.prod ν))
    (η : Lp 𝕜 2 μ) (ψ : Lp E 2 ν) :
    Integrable (fun z => η z.1 * inner 𝕜 (R z) (ψ z.2)) (μ.prod ν) := by
  let U := Lp.uncurry 𝕜 (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    ((ContinuousLinearMap.toSpanSingleton 𝕜 ψ).compLpL 2 μ η)
  have hU : Integrable (fun z => inner 𝕜 (R z) (U z)) (μ.prod ν) :=
    L2.integrable_inner R U
  apply hU.congr
  filter_upwards [uncurry_tensor_coeFn η ψ] with z hz
  rw [hz]
  simp only [inner_smul_right]

theorem MemLp.integrable_mul_tensor {F : A × B → ℝ}
    (hF : MemLp F 2 (μ.prod ν)) (η : Lp ℝ 2 μ) (ψ : Lp ℝ 2 ν) :
    Integrable (fun z => η z.1 * F z * ψ z.2) (μ.prod ν) := by
  apply (Lp.integrable_mul_inner_tensor (hF.toLp F) η ψ).congr
  filter_upwards [hF.coeFn_toLp] with z hz
  rw [hz]
  simp only [Real.inner_apply]
  ring

theorem Lp.integral_inner_eq_integral_uncurry_mul (P : Lp (Lp E 2 ν) 2 μ)
    (η : Lp 𝕜 2 μ) (ψ : Lp E 2 ν) :
    (∫ a, η a * inner 𝕜 (P a) ψ ∂μ) =
      ∫ z, η z.1 * inner 𝕜
        ((Lp.uncurry 𝕜 (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P) z) (ψ z.2) ∂μ.prod ν := by
  rw [← inner_tensor_eq_integral, ← inner_uncurry_tensor_eq_integral,
    LinearIsometry.inner_map_map]

theorem Lp.integral_inner_uncurryAdjoint_eq_integral_mul (R : Lp E 2 (μ.prod ν))
    (η : Lp 𝕜 2 μ) (ψ : Lp E 2 ν) :
    (∫ a, η a * inner 𝕜
      (((Lp.uncurry (μ := μ) (ν := ν) (E := E) 𝕜
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).toContinuousLinearMap.adjoint R) a) ψ ∂μ) =
      ∫ z, η z.1 * inner 𝕜 (R z) (ψ z.2) ∂μ.prod ν := by
  rw [← inner_tensor_eq_integral, ContinuousLinearMap.adjoint_inner_left]
  exact inner_uncurry_tensor_eq_integral R η ψ

theorem integral_mul_integral_lp_eq_integral_prod
    (P : Lp (Lp ℝ 2 ν) 2 μ) (F : Lp ℝ 2 (μ.prod ν))
    (hF : ∀ᵐ a ∂μ, (fun b => F (a, b)) =ᵐ[ν] (P a : B → ℝ))
    (τ : Lp ℝ 2 μ) {ψ : B → ℝ} (hψ : MemLp ψ 2 ν) :
    (∫ a, τ a * (∫ b, P a b * ψ b ∂ν) ∂μ) =
      ∫ p, τ p.1 * F p * ψ p.2 ∂μ.prod ν := by
  let Ψ := hψ.toLp ψ
  let U := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P
  have hUF : (U : A × B → ℝ) =ᵐ[μ.prod ν] F := by
    apply (Measure.ae_prod_iff_ae_ae
      ((Lp.stronglyMeasurable U).measurableSet_eq_fun (Lp.stronglyMeasurable F))).mpr
    filter_upwards [Lp.uncurry_coeFn (𝕜 := ℝ) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) P, hF]
      with a ha hFa
    exact ha.trans hFa.symm
  calc
    (∫ a, τ a * (∫ b, P a b * ψ b ∂ν) ∂μ) =
        ∫ a, τ a * inner ℝ (P a) Ψ ∂μ := by
      apply integral_congr_ae
      filter_upwards with a
      congr 1
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hψ.coeFn_toLp] with b hb
      simp only [Ψ, hb, Real.inner_apply]
    _ = ∫ p, τ p.1 * inner ℝ (U p) (Ψ p.2) ∂μ.prod ν :=
      Lp.integral_inner_eq_integral_uncurry_mul P τ Ψ
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hUF, (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hψ.coeFn_toLp]
        with p hp hψp
      simp only [Real.inner_apply, Ψ, hψp, hp]
      ring

end MeasureTheory
