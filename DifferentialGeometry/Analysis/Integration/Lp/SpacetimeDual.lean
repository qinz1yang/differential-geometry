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
theorem Lp.exists_lp_dual_integral_uncurry
    (J : V →L[ℝ] Lp E 2 ν) (F : Lp E 2 (μ.prod ν)) :
    ∃ ℓ : Lp (V →L[ℝ] ℝ) 2 μ,
      (∀ η : Lp ℝ 2 μ, ∀ v : V,
        (∫ t, η t * ℓ t v ∂μ) =
          ∫ p, η p.1 * inner ℝ (F p) (J v p.2) ∂μ.prod ν) ∧
      (∀ z : Lp V 2 μ, (∫ t, ℓ t (z t) ∂μ) =
        ∫ p, inner ℝ (F p) ((Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
          (J.compLpL 2 μ z)) p) ∂μ.prod ν) := by
  let Q := (Lp.uncurry (μ := μ) (ν := ν) (E := E) ℝ
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).toContinuousLinearMap.adjoint F
  let K : Lp E 2 ν →L[ℝ] V →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ (Lp E 2 ν)) J
  let ℓ := K.compLpL 2 μ Q
  have hvariable (z : Lp V 2 μ) : (∫ t, ℓ t (z t) ∂μ) =
      ∫ p, inner ℝ (F p) ((Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        (J.compLpL 2 μ z)) p) ∂μ.prod ν := by
    calc
      (∫ t, ℓ t (z t) ∂μ) = inner ℝ Q (J.compLpL 2 μ z) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [K.coeFn_compLpL Q, J.coeFn_compLpL z] with t hKt hJt
        change ℓ t = K (Q t) at hKt
        rw [hKt, hJt]
        rfl
      _ = inner ℝ F (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
          (J.compLpL 2 μ z)) :=
        ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = _ := L2.inner_def _ _
  refine ⟨ℓ, ?_, hvariable⟩
  intro η v
  calc
    (∫ t, η t * ℓ t v ∂μ) = ∫ t, η t * inner ℝ (Q t) (J v) ∂μ := by
      apply integral_congr_ae
      filter_upwards [K.coeFn_compLpL Q] with t ht
      change ℓ t = K (Q t) at ht
      rw [ht]
      rfl
    _ = _ := Lp.integral_inner_uncurryAdjoint_eq_integral_mul F η (J v)

theorem Lp.integral_inner_uncurry_compLpL_eq_integral_integral [SFinite μ]
    (J : V →L[ℝ] Lp E 2 ν) (F : Lp E 2 (μ.prod ν)) (z : Lp V 2 μ) :
    (∫ p, inner ℝ (F p) ((Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (J.compLpL 2 μ z)) p) ∂μ.prod ν) =
        ∫ t, ∫ x, inner ℝ (F (t, x)) (J (z t) x) ∂ν ∂μ := by
  let Z := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (J.compLpL 2 μ z)
  have hprod := integral_prod (fun p => inner ℝ (F p) (Z p)) (L2.integrable_inner F Z)
  apply hprod.trans
  apply integral_congr_ae
  filter_upwards [Lp.uncurry_compLpL_coeFn (𝕜 := ℝ)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) J z] with t ht
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  exact congrArg (fun y : E => inner ℝ (F (t, x)) y) hx

theorem Lp.exists_lp_scalar_dual_integral_uncurry
    (J : V →L[ℝ] Lp ℝ 2 ν) (F : Lp ℝ 2 (μ.prod ν)) :
    ∃ ℓ : Lp (V →L[ℝ] ℝ) 2 μ,
      (∀ τ : Lp ℝ 2 μ, ∀ v : V, (∫ t, τ t * ℓ t v ∂μ) =
        ∫ p, τ p.1 * F p * J v p.2 ∂μ.prod ν) ∧
      ∀ z : Lp V 2 μ, (∫ t, ℓ t (z t) ∂μ) =
        ∫ p, F p * (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
          (J.compLpL 2 μ z)) p ∂μ.prod ν := by
  obtain ⟨ℓ, hℓ, hv⟩ := Lp.exists_lp_dual_integral_uncurry J F
  refine ⟨ℓ, ?_, ?_⟩
  · intro τ v
    exact (hℓ τ v).trans (integral_congr_ae (Filter.Eventually.of_forall fun p => by
      simp only [Real.inner_apply]
      ring))
  · intro z
    exact (hv z).trans (integral_congr_ae (Filter.Eventually.of_forall fun p => by
      exact mul_comm _ _))

end MeasureTheory
