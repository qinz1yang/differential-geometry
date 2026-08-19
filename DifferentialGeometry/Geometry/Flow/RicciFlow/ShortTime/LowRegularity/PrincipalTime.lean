import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.TimeDependentPrincipalOperatorH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.DuhamelBootstrap

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private abbrev metricH1 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricThirdOrderSobolev (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)

private abbrev metricH4 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)

def orderOneH2Iso (g : SmoothRiemannianMetric I M) :
    tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 1) ≃ₗᵢ[ℝ]
      metricH2 (I := I) (M := M) g := by
  rw [show (1 : ℝ) + 1 = 2 by norm_num]
  exact LinearIsometryEquiv.refl ℝ _

def lowRegularityStateL2
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t)‖ ≤ R) :
    timeL2 (metricH2 (I := I) (M := M) g) T :=
  (orderOneH2Iso (I := I) (M := M) g).toLinearIsometry.toContinuousLinearMap.compLpL
    2 (timeMeasure T)
      (duhReprL2 (I := I) (M := M)
        g 0 2 (1 : ℝ) hT hT1 0 f hR hball)

omit [BoundarylessManifold I M] in
theorem lowRegularityState_ae
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t)‖ ≤ R) :
    lowRegularityStateL2 (I := I) (M := M)
        g hT hT1 f hR hball =ᵐ[timeMeasure T]
      fun t => orderOneH2Iso (I := I) (M := M) g
        (tensorHsInclusion (I := I) (M := M)
          (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
          (maxRegDuhamelSolField (I := I) (M := M)
            (1 : ℝ) hT hT1
            (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t)) := by
  have hmap :=
    (orderOneH2Iso (I := I) (M := M) g).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL
      (p := 2) (μ := timeMeasure T)
      (duhReprL2 (I := I) (M := M)
        g 0 2 (1 : ℝ) hT hT1 0 f hR hball)
  have hcoe := duhReprL2_ae (I := I) (M := M)
    g 0 2 (1 : ℝ) hT hT1 0 f hR hball
  have hfield := duhRepr_field_ae (I := I) (M := M)
    g 0 2 (1 : ℝ) hT hT1 0 f
  filter_upwards [hmap, hcoe, hfield] with t hm hc hf
  simpa only [lowRegularityStateL2] using
    hm.trans (congrArg
      (orderOneH2Iso (I := I) (M := M) g) (hc.trans hf))

omit [BoundarylessManifold I M] in
theorem lowRegularityState_ae_le
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t)‖ ≤ R) :
    ∀ᵐ t ∂timeMeasure T,
      ‖lowRegularityStateL2 (I := I) (M := M)
        g hT hT1 f hR hball t‖ ≤ R := by
  filter_upwards [
    lowRegularityState_ae (I := I) (M := M)
      g hT hT1 f hR hball,
    hball] with t ht hbound
  rw [ht, LinearIsometryEquiv.norm_map]
  exact hbound

def lowRegularityPrincipalSecondOrderActionTime
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t)‖ ≤ R) :
    ℝ → (metricH4 (I := I) (M := M) g →L[ℝ]
      metricH2 (I := I) (M := M) g) :=
  timeDependentPrincipalOperatorH2 (I := I) (M := M) g hR
    (lowRegularityStateL2 (I := I) (M := M)
      g hT hT1 f hR hball)

theorem lowRegularityPrincipalSecondOrderActionTime_ae
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t)‖ ≤ R) :
    lowRegularityPrincipalSecondOrderActionTime (I := I) (M := M)
        g hT hT1 f hR hball =ᵐ[timeMeasure T]
      fun t => lowRegularityPrincipalOperatorH2 (I := I) (M := M) g
        (orderOneH2Iso (I := I) (M := M) g
          (tensorHsInclusion (I := I) (M := M)
            (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
            (maxRegDuhamelSolField (I := I) (M := M)
              (1 : ℝ) hT hT1
              (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t))) := by
  have hstate := lowRegularityState_ae_le (I := I) (M := M)
    g hT hT1 f hR hball
  have hprincipal := timeDependentPrincipalOperatorH2_ae_eq (I := I) (M := M)
    g hR
      (lowRegularityStateL2 (I := I) (M := M)
        g hT hT1 f hR hball) hstate
  have hfield := lowRegularityState_ae (I := I) (M := M)
    g hT hT1 f hR hball
  filter_upwards [hprincipal, hfield] with t hp hf
  simpa only [lowRegularityPrincipalSecondOrderActionTime] using hp.trans (congrArg
    (lowRegularityPrincipalOperatorH2 (I := I) (M := M) g) hf)

theorem lowRegularityPrincipalSecondOrderActionTime_data
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ (ρ : ℝ) (C : NNReal), 0 < ρ ∧
      ∀ {R : ℝ} (hR : 0 ≤ R), R ≤ ρ →
        ∀ {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
          (f : timeL2 (metricH1 (I := I) (M := M) g) T)
          (hball : ∀ᵐ t ∂timeMeasure T,
            ‖tensorHsInclusion (I := I) (M := M)
              (g := g) (r := 0) (s := 2)
              (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
              (maxRegDuhamelSolField (I := I) (M := M)
                (1 : ℝ) hT hT1
                (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t)‖ ≤ R),
          AEStronglyMeasurable
              (lowRegularityPrincipalSecondOrderActionTime (I := I) (M := M)
                g hT hT1 f hR hball)
              (timeMeasure T) ∧
            (∀ᵐ t ∂timeMeasure T,
              ‖lowRegularityPrincipalSecondOrderActionTime (I := I) (M := M)
                g hT hT1 f hR hball t‖ ≤ (C : ℝ) * R) ∧
            lowRegularityPrincipalSecondOrderActionTime (I := I) (M := M)
                g hT hT1 f hR hball =ᵐ[timeMeasure T]
              fun t => lowRegularityPrincipalOperatorH2 (I := I) (M := M) g
                (orderOneH2Iso (I := I) (M := M) g
                  (tensorHsInclusion (I := I) (M := M)
                    (g := g) (r := 0) (s := 2)
                    (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
                    (maxRegDuhamelSolField (I := I) (M := M)
                      (1 : ℝ) hT hT1
                      (0 : metricThirdOrderSobolev (I := I) (M := M) g) f t))) := by
  obtain ⟨ρ, C, hρ, hdata⟩ :=
    exists_timeDependentPrincipalOperatorH2_bounds (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, ?_⟩
  intro R hR hRρ T hT hT1 f hball
  have hstate := lowRegularityState_ae_le (I := I) (M := M)
    g hT hT1 f hR hball
  obtain ⟨hmeas, hbound, _⟩ := hdata hR hRρ
    (lowRegularityStateL2 (I := I) (M := M)
      g hT hT1 f hR hball) hstate
  exact ⟨by
      simpa only [lowRegularityPrincipalSecondOrderActionTime] using hmeas,
    by
      simpa only [lowRegularityPrincipalSecondOrderActionTime] using hbound,
    lowRegularityPrincipalSecondOrderActionTime_ae (I := I) (M := M)
      g hT hT1 f hR hball⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
