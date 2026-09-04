import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Conjugate.Sard
import DifferentialGeometry.Analysis.Integration.Measure.Chart.NullSets

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
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem lCutConj_null
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      (lCutConj S T x tau) = 0 := by
  classical
  obtain ⟨c, hc⟩ := finite_chart_cover (H := H) (M := M)
  apply null_of_chart_cover
    (H := H)
    (μ := riemannianVolumeMeasure (I := I) (M := M) g)
    (A := lCutConj S T x tau) (s := c)
  · rw [hc]
    exact subset_univ _
  · intro alpha halpha
    let N : Set E :=
      (fun Z : E => (extChartAt I alpha) (lExp S T x Z tau)) ''
        {Z : E | IsLConjugate S T x Z tau ∧
          lExp S T x Z tau ∈ (chartAt H alpha).source}
    have hN0 : modelHaar (E := E) N = 0 := by
      simpa only [N] using lConjugateChart_null S hS T x tau alpha
    have hNT0 : modelHaar (E := E)
        (N ∩ (extChartAt I alpha).target) = 0 :=
      measure_mono_null inter_subset_left hN0
    have hpull := chart_model_null (I := I) (M := M) g alpha hNT0
    apply measure_mono_null _ hpull
    intro y hy
    rcases hy.1 with ⟨Z, hcut, hconj, hend⟩
    refine ⟨hy.2, ?_⟩
    change (extChartAt I alpha) y ∈ N
    refine ⟨Z, ⟨hconj, ?_⟩, ?_⟩
    · simpa only [hend] using hy.2
    · simp only [hend]

end DifferentialGeometry.PDE.RicciFlow.Perelman
