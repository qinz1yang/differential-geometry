import DifferentialGeometry.Analysis.Integration.Measure.LocalRestriction
import DifferentialGeometry.Analysis.Integration.Measure.Family.Decomposition

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_riemannianVolumeMeasure_eq_chartLocalMeasure_of_tsupport_subset
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M) (alpha : M)
    {f : M → F} (hf : HasCompactSupport f) (hs : tsupport f ⊆ (chartAt H alpha).source) :
    ∫ x, f x ∂riemannianVolumeMeasure (I := I) (M := M) g =
      ∫ x, f x ∂chartLocalMeasure g alpha := by
  have hzero (x : M) (hx : x ∉ tsupport f) : f x = 0 := image_eq_zero_of_notMem_tsupport hx
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    riemannianVolumeMeasure_restrict_eq_chartLocalMeasure_restrict g alpha hf hs,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero]

theorem integral_riemannianVolumeMeasure_eq_chartDensity_of_tsupport_subset
    [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M) (alpha : M)
    {f : M → Real} (hf : HasCompactSupport f) (hs : tsupport f ⊆ (chartAt H alpha).source)
    (hm : AEStronglyMeasurable f (chartLocalMeasure g alpha)) :
    ∫ x, f x ∂riemannianVolumeMeasure (I := I) (M := M) g =
      ∫ y in (extChartAt I alpha).target,
        chartDensity g alpha ((extChartAt I alpha).symm y) * f ((extChartAt I alpha).symm y)
        ∂modelHaar := by
  rw [integral_riemannianVolumeMeasure_eq_chartLocalMeasure_of_tsupport_subset g alpha hf hs]
  exact integral_chart_ae g alpha f hm

end DifferentialGeometry.Integral.Measure
