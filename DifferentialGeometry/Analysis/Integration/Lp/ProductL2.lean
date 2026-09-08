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

end MeasureTheory
