import RicciFlower.Analysis.Measure
import RicciFlower.Analysis.Volume.Family

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RicciFlower
namespace Analysis
namespace VolumeVariation

noncomputable section

open MeasureTheory
open RicciFlower.Analysis.Volume
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The measure-layer metric family associated to a realized metric family. -/
abbrev metricFamilyForMeasure
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real) :
    Real → Volume.SmoothRiemannianMetric I M :=
  fun t => G.metric t

/-- The measure-layer metric family associated to an interval realized metric family. -/
abbrev metricFamilyForMeasureOn
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamilyOn (I := I) (M := M) D) :
    Real → Volume.SmoothRiemannianMetric I M :=
  fun t => G.metric t

/-- The time-dependent Riemannian measure family for a realized metric family. -/
abbrev volumeMeasureFamily [T2Space M] [SigmaCompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real) :
    Real → MeasureTheory.Measure M :=
  riemannianMeasureFamily (I := I) (M := M) (metricFamilyForMeasure (I := I) (M := M) G)

@[simp]
theorem volumeMeasureFamily_eq [T2Space M] [SigmaCompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real) (t : Real) :
    volumeMeasureFamily (I := I) (M := M) G t =
      Measure.volumeMeasureAt (I := I) (M := M) G t := rfl

/-- The time-dependent Riemannian measure family for an interval realized metric family. -/
abbrev volumeMeasureFamilyOn [T2Space M] [SigmaCompactSpace M]
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamilyOn (I := I) (M := M) D) :
    Real → MeasureTheory.Measure M :=
  riemannianMeasureFamily (I := I) (M := M) (metricFamilyForMeasureOn (I := I) (M := M) G)

@[simp]
theorem volumeMeasureFamilyOn_eq [T2Space M] [SigmaCompactSpace M]
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamilyOn (I := I) (M := M) D) (t : Real) :
    volumeMeasureFamilyOn (I := I) (M := M) G t =
      riemannianVolumeMeasure (I := I) (M := M)
        (G.metric t) := rfl

@[simp]
theorem volumeMeasureFamilyOn_eq_volumeMeasureOn [T2Space M] [SigmaCompactSpace M]
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : Realized.RealTimeInterval.FlowTime D) :
    volumeMeasureFamilyOn (I := I) (M := M) G (t : Real) =
      Measure.volumeMeasureOn (I := I) (M := M) G t := rfl

/-- The trace of the time derivative of the metric in the existing measure API. -/
abbrev traceTimeDerivMetricAt
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real) (t : Real) (x : M) :
    Real :=
  traceTimeDerivMetric (I := I) (metricFamilyForMeasure (I := I) (M := M) G) t x

@[simp]
theorem traceTimeDerivMetricAt_eq
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real) (t : Real) (x : M) :
    traceTimeDerivMetricAt (I := I) G t x =
      traceTimeDerivMetric (I := I) (metricFamilyForMeasure (I := I) (M := M) G) t x := rfl

/-- The trace of the time derivative of an interval-indexed realized metric family. -/
abbrev traceTimeDerivMetricOn
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamilyOn (I := I) (M := M) D) (t : Real) (x : M) :
    Real :=
  traceTimeDerivMetric (I := I) (metricFamilyForMeasureOn (I := I) (M := M) G) t x

@[simp]
theorem traceTimeDerivMetricOn_eq
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamilyOn (I := I) (M := M) D) (t : Real) (x : M) :
    traceTimeDerivMetricOn (I := I) G t x =
      traceTimeDerivMetric (I := I) (metricFamilyForMeasureOn (I := I) (M := M) G) t x := rfl

theorem volume_variation_formula_clean_at
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {f : Real → M → Real} {t₀ : Real}
    (hg : MetricFamilyRegularAt (I := I) (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀
            + (1 / 2 : Real) * traceTimeDerivMetricAt (I := I) G t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  simpa [volumeMeasureFamily, traceTimeDerivMetricAt] using
    (volume_variation_formula_clean (I := I) (M := M)
      (g_fam := metricFamilyForMeasure (I := I) (M := M) G)
      (f := f) (t₀ := t₀) hg hf)

theorem volume_variation_formula_clean_on
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamilyOn (I := I) (M := M) D)
    {f : Real → M → Real} {t₀ : Real}
    (hg : MetricFamilyRegularAt (I := I) (metricFamilyForMeasureOn (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamilyOn (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀
            + (1 / 2 : Real) * traceTimeDerivMetricOn (I := I) G t₀ x * f t₀ x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M) G t₀))
      t₀ := by
  simpa [volumeMeasureFamilyOn, traceTimeDerivMetricOn] using
    (volume_variation_formula_clean (I := I) (M := M)
      (g_fam := metricFamilyForMeasureOn (I := I) (M := M) G)
      (f := f) (t₀ := t₀) hg hf)

end

end VolumeVariation
end Analysis
end RicciFlower
