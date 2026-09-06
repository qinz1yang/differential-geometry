import DifferentialGeometry.Analysis.Integration.Measure.ParamDensitySmoothness
import DifferentialGeometry.Geometry.Comparison.Volume.NormalChartMeasure
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback

noncomputable section

open Manifold Set
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open NormalCoordinates
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

private theorem expMapDiffeo_contMDiffOn_ball
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContMDiffOn 𝓘(ℝ, E) I ∞ (expMapDiffeo g p)
      (Metric.ball 0 (expMapC2Radius g p)) := by
  intro w hw
  have hnorm : ‖w‖ < expMapC2Radius g p := by simpa using hw
  have hsource := mem_expMapDiffeo_source_of_norm_lt_radius g p hnorm
  apply ContMDiffAt.contMDiffWithinAt
  apply (expMap_contMDiffAt_infty_of_norm_lt_radius g p hnorm).congr_of_eventuallyEq
  filter_upwards [(expMapDiffeo g p).open_source.mem_nhds hsource] with z hz
  exact expMapDiffeo_apply_eq g p hz

theorem contDiffOn_normalGramMatrix
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffOn ℝ ∞ (normalGramMatrix g p) (Metric.ball 0 (expMapC2Radius g p)) := by
  apply contDiffOn_paramGramMatrix g (expMapDiffeo g p) Metric.isOpen_ball
    (fun w hw => mem_expMapDiffeo_source_of_norm_lt_radius g p (by simpa using hw))
  simpa using expMapDiffeo_contMDiffOn_ball g p

theorem contDiffOn_normalChartDensity
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffOn ℝ ∞ (normalChartDensity g p) (Metric.ball 0 (expMapC2Radius g p)) := by
  apply contDiffOn_paramDensity g (expMapDiffeo g p) Metric.isOpen_ball
    (fun w hw => mem_expMapDiffeo_source_of_norm_lt_radius g p (by simpa using hw))
  simpa using expMapDiffeo_contMDiffOn_ball g p

theorem contDiffAt_normalGramMatrix_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffAt ℝ ∞ (normalGramMatrix g p) 0 :=
  (contDiffOn_normalGramMatrix g p).contDiffAt
    (Metric.ball_mem_nhds 0 (expMapC2Radius_pos g p))

theorem contDiffAt_normalChartDensity_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffAt ℝ ∞ (normalChartDensity g p) 0 :=
  (contDiffOn_normalChartDensity g p).contDiffAt
    (Metric.ball_mem_nhds 0 (expMapC2Radius_pos g p))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
