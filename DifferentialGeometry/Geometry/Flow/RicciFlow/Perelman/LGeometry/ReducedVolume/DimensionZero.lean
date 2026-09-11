import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.DimensionZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measure

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

omit [T2Space M] in
theorem redDensity_eq_one_of_finrank_eq_zero
    (hdim : Module.finrank ℝ E = 0)
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x y : M) (tau : ℝ) :
    redDensity S T x y tau = 1 := by
  simp [redDensity, redLength, lCost_eq_zero_of_finrank_eq_zero hdim, hdim]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [SigmaCompactSpace M]

theorem redVolume_eq_volume_of_finrank_eq_zero
    (hdim : Module.finrank ℝ E = 0)
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (tau : ℝ) :
    redVolume S T x tau =
      riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) Set.univ := by
  simp only [redVolume, redDensity_eq_one_of_finrank_eq_zero hdim,
    ENNReal.ofReal_one, lintegral_const, one_mul]

end DifferentialGeometry.PDE.RicciFlow.Perelman
