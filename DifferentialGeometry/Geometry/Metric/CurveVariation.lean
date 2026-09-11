import DifferentialGeometry.Geometry.Metric.CurveDistance
import DifferentialGeometry.Analysis.Calculus.Variation.Comparison








noncomputable section

open Bundle Manifold Set DifferentialGeometry MeasureTheory Filter
open DifferentialGeometry.Analysis
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace



def riemannianCurveVariation (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  let cg := g.toContinuousRiemannianMetric
  letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  letI : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  eVariationOn γ (Icc a b)

variable [FiniteDimensional ℝ E] [CompactSpace M] [PreconnectedSpace M]



theorem riemannianCurveVariation_eq_elength (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y)
    (a b : ℝ) : riemannianCurveVariation g γ a b = riemannianCurveELength g γ a b := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : MetricSpace M := EMetricSpace.toMetricSpace edist_ne_top_of_preconnected
  have hγ' : LipschitzWith C γ := hγ
  change eVariationOn γ (Icc a b) = riemannianCurveELength g γ a b
  by_cases hab : a ≤ b
  · have hspeed (x y : ℝ) : IntervalIntegrable (riemannianCurveSpeed g γ) volume x y := by
      let : IsFiniteMeasure (volume.restrict (uIcc x y)) :=
        ⟨by simpa only [Measure.restrict_apply_univ] using
          ((isCompact_uIcc : IsCompact (uIcc x y)).measure_lt_top (μ := volume))⟩
      exact (integrableOn_riemannianCurveSpeed g hγ (uIcc x y)).intervalIntegrable
    have hlen (x y : ℝ) (hxy : x ≤ y) :
        (∫ t in x..y, riemannianCurveSpeed g γ t) = riemannianCurveLength g γ x y := by
      rw [riemannianCurveLength_eq_integral g hγ, intervalIntegral.integral_of_le hxy,
        integral_Icc_eq_integral_Ioc]
    apply le_antisymm
    · let F : ℝ → ℝ := fun x => ∫ t in a..x, riemannianCurveSpeed g γ t
      have hF (x y : ℝ) : F y - F x = ∫ t in x..y, riemannianCurveSpeed g γ t := by
        have h := intervalIntegral.integral_add_adjacent_intervals (hspeed a x) (hspeed x y)
        dsimp only [F]
        linarith
      have hm : Monotone F := by
        intro x y hxy
        have h := intervalIntegral.integral_nonneg_of_forall (μ := volume) hxy (riemannianCurveSpeed_nonneg g γ)
        rw [← hF] at h
        exact sub_nonneg.mp h
      have hbound (x y : ℝ) (hxy : x ≤ y) : dist (γ x) (γ y) ≤ F y - F x := by
        rw [hF, hlen x y hxy]
        have h := riemannianDistance_le_curveLength g hγ hxy
        change (edist (γ x) (γ y)).toReal ≤ _ at h
        simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h
      have hvar := eVariationOn_Icc_le_of_dist_le_sub hm hbound a b
      rw [hF, hlen a b hab, riemannianCurveLength,
        ENNReal.ofReal_toReal (riemannianCurveELength_ne_top_of_lipschitz g hγ a b)] at hvar
      exact hvar
    · let V := variationOnFromTo γ univ a
      have hV : LipschitzWith C V := lipschitz_variationOnFromTo hγ' a
      have hVac := hV.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
      have hae : ∀ᵐ t ∂volume, riemannianCurveSpeed g γ t ≤ deriv V t := by
        filter_upwards [ae_mdifferentiableAt_riemannian_curve g hγ, hV.ae_differentiableAt_real]
          with t ht hVt
        have hd := riemannianCurveSpeed_le_abs_deriv_of_distance_bound g ht hVt (fun y => by
          have h := dist_le_variationOnFromTo_dist hγ' a t y
          change edist (γ t) (γ y) ≤ _
          rw [edist_dist]
          apply ENNReal.ofReal_le_ofReal
          simpa only [V, Real.dist_eq, abs_sub_comm] using h)
        simpa only [V, abs_of_nonneg (deriv_variationOnFromTo_nonneg hγ' a t)] using hd
      have hle := intervalIntegral.integral_mono_ae hab (hspeed a b) hVac.intervalIntegrable_deriv hae
      rw [hlen a b hab, hVac.integral_deriv_eq_sub] at hle
      have hVvalue : V b - V a = (eVariationOn γ (Icc a b)).toReal := by
        dsimp only [V]
        rw [variationOnFromTo.self, sub_zero, variationOnFromTo.eq_of_le γ univ hab,
          univ_inter]
      rw [hVvalue] at hle
      exact (ENNReal.toReal_le_toReal (riemannianCurveELength_ne_top_of_lipschitz g hγ a b)
        (eVariationOn_Icc_ne_top_of_lipschitz hγ' a b)).mp hle
  · simp only [riemannianCurveELength, Icc_eq_empty_of_lt (lt_of_not_ge hab),
      eVariationOn.subsingleton γ Set.subsingleton_empty, Measure.restrict_empty, lintegral_zero_measure]


theorem riemannianCurveLength_eq_variation (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y)
    (a b : ℝ) : riemannianCurveLength g γ a b = (riemannianCurveVariation g γ a b).toReal := by
  rw [riemannianCurveVariation_eq_elength g hγ, riemannianCurveLength]

end DifferentialGeometry.Geometry
