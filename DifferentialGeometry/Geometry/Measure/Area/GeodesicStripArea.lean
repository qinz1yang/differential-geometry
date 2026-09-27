import DifferentialGeometry.Geometry.Measure.Area.ExtendedGeodesicStrip
import DifferentialGeometry.Geometry.Metric.CurveLength
import DifferentialGeometry.Analysis.Integration.Integral.ComplexSquare



noncomputable section

open Bundle Manifold Set DifferentialGeometry Filter MeasureTheory
open DifferentialGeometry.Analysis
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M] [PreconnectedSpace M]





theorem exists_geodesicStrip_area_bound (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ ρ C : ℝ≥0, 0 < ρ ∧ 0 < C ∧ ∀ (γ₀ γ₁ : ℝ → M) (L₀ L₁ D : ℝ≥0),
      (∀ s t, riemannianEDistOf g (γ₀ s) (γ₀ t) ≤ (L₀ : ℝ≥0∞) * edist s t) →
      (∀ s t, riemannianEDistOf g (γ₁ s) (γ₁ t) ≤ (L₁ : ℝ≥0∞) * edist s t) →
      D ≤ ρ → (∀ t, riemannianEDistOf g (γ₀ t) (γ₁ t) ≤ (D : ℝ≥0∞)) →
      (∃ K : ℝ≥0, ∀ z w : ℂ,
        riemannianEDistOf g (extendedGeodesicStrip g γ₀ γ₁ z) (extendedGeodesicStrip g γ₀ γ₁ w) ≤
          (K : ℝ≥0∞) * edist z w) ∧
      riemannianArea g (extendedGeodesicStrip g γ₀ γ₁) unitSquare ≤
        C * D * (riemannianCurveLength g γ₀ 0 1 + riemannianCurveLength g γ₁ 0 1) := by
  obtain ⟨ρ₁, C, hρ₁, hC, hdensity⟩ := exists_geodesicStrip_density_bound g
  obtain ⟨ρ₂, hρ₂, hlip⟩ := exists_extendedGeodesicStrip_lipschitz_radius g
  refine ⟨min ρ₁ ρ₂, C, lt_min hρ₁ hρ₂, hC, fun γ₀ γ₁ L₀ L₁ D h₀ h₁ hD hnear => ?_⟩
  have hnear₁ (t : ℝ) : riemannianEDistOf g (γ₀ t) (γ₁ t) ≤ (ρ₁ : ℝ≥0∞) :=
    (hnear t).trans (by exact_mod_cast hD.trans (min_le_left ρ₁ ρ₂))
  have hnear₂ (t : ℝ) : riemannianEDistOf g (γ₀ t) (γ₁ t) ≤ (ρ₂ : ℝ≥0∞) :=
    (hnear t).trans (by exact_mod_cast hD.trans (min_le_right ρ₁ ρ₂))
  obtain ⟨K, hK⟩ := hlip γ₀ γ₁ L₀ L₁ h₀ h₁ hnear₂
  refine ⟨⟨K, hK⟩, ?_⟩
  let f : ℂ → ℝ := riemannianAreaDensity g (extendedGeodesicStrip g γ₀ γ₁)
  have hf : IntegrableOn f unitSquare := integrable_extendedGeodesicStrip_density g hK
  have hprod : Integrable (fun p : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm p))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact integrable_unitSquare_coordinates hf
  have hs₀ := integrableOn_riemannianCurveSpeed g h₀ (Icc (0 : ℝ) 1)
  have hs₁ := integrableOn_riemannianCurveSpeed g h₁ (Icc (0 : ℝ) 1)
  have htime : ∀ᵐ v ∂volume.restrict (Icc (0 : ℝ) 1), v ∈ Ioo (0 : ℝ) 1 := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hbound : ∀ᵐ v ∂volume.restrict (Icc (0 : ℝ) 1),
      (∫ θ in Icc (0 : ℝ) 1, f (Complex.measurableEquivRealProd.symm (v, θ))) ≤
        (C : ℝ) * D * (riemannianCurveLength g γ₀ 0 1 + riemannianCurveLength g γ₁ 0 1) := by
    filter_upwards [htime, hprod.prod_right_ae] with v hv hvint
    calc
      _ ≤ ∫ θ in Icc (0 : ℝ) 1, (C : ℝ) * D *
          (riemannianCurveSpeed g γ₀ θ + riemannianCurveSpeed g γ₁ θ) := by
        apply integral_mono_ae hvint ((hs₀.add hs₁).const_mul ((C : ℝ) * D))
        filter_upwards [ae_restrict_of_ae (ae_mdifferentiableAt_riemannian_curve g h₀),
          ae_restrict_of_ae (ae_mdifferentiableAt_riemannian_curve g h₁)] with θ hθ₀ hθ₁
        let z := Complex.measurableEquivRealProd.symm (v, θ)
        have hz : z.re ∈ Ioo (0 : ℝ) 1 := hv
        have h := hdensity γ₀ γ₁ z (Ioo_subset_Icc_self hz) (hnear₁ θ) hθ₀ hθ₁
        change riemannianAreaDensity g (extendedGeodesicStrip g γ₀ γ₁) z ≤ _
        rw [extendedGeodesicStrip_density_eq g γ₀ γ₁ hz]
        apply h.trans
        have hd : (riemannianEDistOf g (γ₀ θ) (γ₁ θ)).toReal ≤ D := by
          simpa only [ENNReal.coe_toReal] using ENNReal.toReal_mono ENNReal.coe_ne_top (hnear θ)
        change (C : ℝ) * (riemannianEDistOf g (γ₀ θ) (γ₁ θ)).toReal *
          (riemannianCurveSpeed g γ₀ θ + riemannianCurveSpeed g γ₁ θ) ≤ _
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd C.coe_nonneg)
          (add_nonneg (riemannianCurveSpeed_nonneg g γ₀ θ) (riemannianCurveSpeed_nonneg g γ₁ θ))
      _ = _ := by
        rw [integral_const_mul, integral_add hs₀ hs₁,
          ← riemannianCurveLength_eq_integral g h₀, ← riemannianCurveLength_eq_integral g h₁]
  unfold riemannianArea
  rw [integral_unitSquare_eq_iterated hf]
  calc
    _ ≤ ∫ _v in Icc (0 : ℝ) 1,
        (C : ℝ) * D * (riemannianCurveLength g γ₀ 0 1 + riemannianCurveLength g γ₁ 0 1) :=
      integral_mono_ae hprod.integral_prod_left (integrable_const _) hbound
    _ = _ := by simp



theorem extendedGeodesicStrip_self_area_zero (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {L : ℝ≥0}
    (hγ : ∀ s t, riemannianEDistOf g (γ s) (γ t) ≤ (L : ℝ≥0∞) * edist s t) :
    riemannianArea g (extendedGeodesicStrip g γ γ) unitSquare = 0 := by
  obtain ⟨ρ, C, _, _, h⟩ := exists_geodesicStrip_area_bound g
  have hb := (h γ γ L L 0 hγ hγ (bot_le : (0 : ℝ≥0) ≤ ρ) (fun t => by
    rw [riemannianEDistOf_self, ENNReal.coe_zero])).2
  apply le_antisymm _ (riemannianArea_nonneg g _ _)
  simpa only [NNReal.coe_zero, mul_zero, zero_mul] using hb

end DifferentialGeometry.Geometry
