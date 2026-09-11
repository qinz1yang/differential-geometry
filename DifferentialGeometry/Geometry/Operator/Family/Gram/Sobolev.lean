import DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Regularity.AbsolutelyContinuous
import DifferentialGeometry.Geometry.Operator.Family.Gram.Curve

noncomputable section

open Filter Function MeasureTheory Set
open scoped Manifold ContDiff Interval Topology

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem MetricConnectionFamilyOn.exists_timeH1_extChartAt
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (p : M) {L : ℝ} (gamma : ℝ → M) (tau : ℝ → ℝ)
    (hAC : AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ gamma) 0 L)
    (hsrc : MapsTo gamma (uIcc 0 L) (chartAt H p).source)
    (hchart : MapsTo ((extChartAt I p) ∘ gamma) (Icc 0 L)
      (interior (extChartAt I p).target))
    (htau : ContinuousOn tau (Icc 0 L))
    (hreg : MapsTo tau (Icc 0 L) D.regular)
    (hInt : Integrable (fun r ↦ (G.metric (tau r)).inner (gamma r)
      ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ))
      ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ))) (timeMeasure L)) :
    ∃ u : timeH1 E L,
      EqOn u.toFun ((extChartAt I p) ∘ gamma) (Icc 0 L) ∧
        u.deriv =ᵐ[timeMeasure L] deriv ((extChartAt I p) ∘ gamma) := by
  let f := (extChartAt I p) ∘ gamma
  have hmdiff : ∀ᵐ r ∂timeMeasure L, MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r :=
    ae_mono (Measure.restrict_mono Icc_subset_uIcc le_rfl)
      (hAC.ae_mdifferentiableAt_of_extChartAt p hsrc)
  obtain ⟨c, hc, hcLower⟩ := chartGramOp_lower hG (mapsTo_iff_image_subset.mp hreg)
    (isCompact_Icc.image_of_continuousOn htau) p (mapsTo_iff_image_subset.mp hchart)
    (isCompact_Icc.image_of_continuousOn (hAC.continuousOn.mono Icc_subset_uIcc))
  have hsqBound : ∀ᵐ r ∂timeMeasure L,
      ‖deriv f r‖ ^ 2 ≤ |(G.metric (tau r)).inner (gamma r)
        ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ))
        ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ))| / c := by
    filter_upwards [hmdiff, ae_restrict_mem measurableSet_Icc] with r hmd hr
    apply (le_div_iff₀' hc).2
    have hgram := hcLower (tau r, f r) ⟨⟨r, hr, rfl⟩, ⟨r, hr, rfl⟩⟩ (deriv f r)
    dsimp only [f, Function.comp_apply] at hgram
    rw [chartGramOp_inner_deriv G p (tau r) hmd (hsrc (Icc_subset_uIcc hr))] at hgram
    exact hgram.trans (le_abs_self _)
  have hdmeas := aestronglyMeasurable_deriv f (timeMeasure L)
  have hsqInt : Integrable (fun r ↦ ‖deriv f r‖ ^ 2) (timeMeasure L) :=
    (hInt.abs.div_const c).mono_nonneg (hdmeas.norm.pow 2)
      (Eventually.of_forall fun r ↦ sq_nonneg ‖deriv f r‖) hsqBound
  exact timeH1.exists_of_absolutelyContinuousOnInterval f hAC
    ((memLp_two_iff_integrable_sq_norm hdmeas).2 hsqInt)

end DifferentialGeometry.Geometry.Curvature
