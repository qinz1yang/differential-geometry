import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Conjugate.Sard
import DifferentialGeometry.Geometry.Measure.ChartNull

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem lConjugateImage_null
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      {y : M | ∃ Z : TangentSpace I x,
        IsLConjugate S T x Z tau ∧ lExp S T x Z tau = y} = 0 := by
  classical
  change riemannianMeasure (I := I) g (chartAtlasPOU I M)
    {y : M | ∃ Z : TangentSpace I x,
      IsLConjugate S T x Z tau ∧ lExp S T x Z tau = y} = 0
  apply DifferentialGeometry.Geometry.Measure.riemannianMeasure_null_of_chartLocalMeasure
  intro alpha
  apply DifferentialGeometry.Geometry.Measure.chartLocalMeasure_null_of_chart_image_null
  apply measure_mono_null _ (lConjugateChart_null S hS T x tau alpha)
  rintro _ ⟨y, ⟨hy, hysource⟩, rfl⟩
  rcases hy with ⟨Z, hconj, hend⟩
  refine ⟨(Z : E), ⟨hconj, ?_⟩, ?_⟩
  · simpa only [hend] using hysource
  · simp only [hend]

omit [NeZero (Module.finrank ℝ E)] in
theorem lCutConj_null
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      (lCutConj S T x tau) = 0 := by
  apply measure_mono_null _ (lConjugateImage_null S hS T x tau g)
  rintro y ⟨Z, _hcut, hconj, hend⟩
  exact ⟨Z, hconj, hend⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
