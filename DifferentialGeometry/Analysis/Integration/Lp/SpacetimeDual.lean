import DifferentialGeometry.Analysis.Integration.Lp.ProductL2
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace MeasureTheory
variable {A B E V : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {μ : Measure A} {ν : Measure B} [SFinite ν]

theorem Lp.exists_lp_dual_integral_prod
    (J : V →L[ℝ] Lp E 2 ν) (F : Lp E 2 (μ.prod ν)) :
    ∃ ℓ : Lp (V →L[ℝ] ℝ) 2 μ, ∀ η : Lp ℝ 2 μ, ∀ v : V,
      (∫ t, η t * ℓ t v ∂μ) =
        ∫ p, η p.1 * inner ℝ (F p) (J v p.2) ∂μ.prod ν := by
  let Q := (Lp.uncurry (μ := μ) (ν := ν) (E := E) ℝ
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).toContinuousLinearMap.adjoint F
  let K : Lp E 2 ν →L[ℝ] V →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ (Lp E 2 ν)) J
  refine ⟨K.compLpL 2 μ Q, ?_⟩
  intro η v
  calc
    (∫ t, η t * (K.compLpL 2 μ Q) t v ∂μ) =
        ∫ t, η t * inner ℝ (Q t) (J v) ∂μ := by
      apply integral_congr_ae
      filter_upwards [K.coeFn_compLpL Q] with t ht
      rw [ht]
      rfl
    _ = _ := Lp.integral_inner_uncurryAdjoint_eq_integral_mul F η (J v)
end MeasureTheory
