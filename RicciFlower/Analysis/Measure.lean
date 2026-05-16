import RicciFlower.Realized.MetricFamily
import RicciFlower.Analysis.Volume.Properties

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RicciFlower
namespace Analysis
namespace Measure

noncomputable section

open MeasureTheory
open RicciFlower.Analysis.Volume
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Compatibility spelling for the metric type used by the local volume layer.
This is now the identity on RicciFlower analytic metrics, not a forgetful map. -/
abbrev metricForMeasure (g : SmoothRiemannianMetric I M) :
    Volume.SmoothRiemannianMetric I M :=
  g

@[simp]
theorem metricForMeasure_inner (g : SmoothRiemannianMetric I M) (x : M) :
    (metricForMeasure (I := I) (M := M) g).inner x = g.inner x := rfl

/-- The Riemannian volume measure attached to a realized metric family at a time. -/
abbrev volumeMeasureAt [T2Space M] [SigmaCompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Time) (t : Time) :
    MeasureTheory.Measure M :=
  riemannianVolumeMeasure (I := I) (M := M) (G.metric t)

@[simp]
theorem volumeMeasureAt_eq [T2Space M] [SigmaCompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Time) (t : Time) :
    volumeMeasureAt (I := I) (M := M) G t =
      riemannianVolumeMeasure (I := I) (M := M) (G.metric t) := rfl

/-- The Riemannian volume measure attached to an interval-indexed realized family. -/
abbrev volumeMeasureOn [T2Space M] [SigmaCompactSpace M]
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : Realized.RealTimeInterval.FlowTime D) :
  MeasureTheory.Measure M :=
  riemannianVolumeMeasure (I := I) (M := M) (G.metricAt t)

@[simp]
theorem volumeMeasureOn_eq [T2Space M] [SigmaCompactSpace M]
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : Realized.RealTimeInterval.FlowTime D) :
    volumeMeasureOn (I := I) (M := M) G t =
      riemannianVolumeMeasure (I := I) (M := M) (G.metricAt t) := rfl

@[simp]
theorem volumeMeasureOn_eq_metric [T2Space M] [SigmaCompactSpace M]
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : Realized.RealTimeInterval.FlowTime D) :
    volumeMeasureOn (I := I) (M := M) G t =
      riemannianVolumeMeasure (I := I) (M := M) (G.metric (t : Real)) := rfl

theorem volumeMeasureAt_isLocallyFiniteMeasure [T2Space M] [SigmaCompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Time) (t : Time) :
    IsLocallyFiniteMeasure (volumeMeasureAt (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M)
    (G.metric t)

theorem volumeMeasureAt_sigmaFinite [T2Space M] [SigmaCompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Time) (t : Time) :
    SigmaFinite (volumeMeasureAt (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_sigmaFinite (I := I) (M := M)
    (G.metric t)

theorem volumeMeasureAt_isFiniteMeasure_of_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Time) (t : Time) :
    IsFiniteMeasure (volumeMeasureAt (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
    (I := I) (M := M) (G.metric t)

theorem volumeMeasureOn_isLocallyFiniteMeasure [T2Space M] [SigmaCompactSpace M]
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : Realized.RealTimeInterval.FlowTime D) :
    IsLocallyFiniteMeasure (volumeMeasureOn (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M)
    (G.metricAt t)

theorem volumeMeasureOn_sigmaFinite [T2Space M] [SigmaCompactSpace M]
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : Realized.RealTimeInterval.FlowTime D) :
    SigmaFinite (volumeMeasureOn (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_sigmaFinite (I := I) (M := M)
    (G.metricAt t)

theorem volumeMeasureOn_isFiniteMeasure_of_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : Realized.RealTimeInterval}
    (G : Realized.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : Realized.RealTimeInterval.FlowTime D) :
    IsFiniteMeasure (volumeMeasureOn (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
    (I := I) (M := M) (G.metricAt t)

end

end Measure
end Analysis
end RicciFlower
