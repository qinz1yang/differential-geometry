import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory
open Integral.Measure (riemannianVolumeMeasure)
open scoped ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable {D : Geometry.Curvature.RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def redDensityMeasure (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (tau : ℝ) :
    Measure M :=
  (riemannianVolumeMeasure I M (S.base.metric (T - tau))).withDensity
    (fun y => ENNReal.ofReal (redDensity S T x y tau))

@[simp]
theorem redDensityMeasure_apply (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ) {A : Set M} (hA : MeasurableSet A) :
    redDensityMeasure S T x tau A =
      ∫⁻ y in A, ENNReal.ofReal (redDensity S T x y tau)
        ∂riemannianVolumeMeasure I M (S.base.metric (T - tau)) :=
  withDensity_apply _ hA

end DifferentialGeometry.PDE.RicciFlow.Perelman
