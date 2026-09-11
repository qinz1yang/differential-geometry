import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Ball
import DifferentialGeometry.Geometry.Metric.Distance.Ball


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure MeasureTheory
open scoped Manifold ContDiff ENNReal


def localDoublingFactor (n : ℕ) (a : ℝ) : ℝ :=
  hyperbolicRadialVolume (Real.sqrt (a / ((n - 1 : ℕ) : ℝ))) (n - 1) 1 /
    hyperbolicRadialVolume (Real.sqrt (a / ((n - 1 : ℕ) : ℝ))) (n - 1) (1 / 2)

theorem one_le_localDoublingFactor (n : ℕ) (a : ℝ) :
    1 ≤ localDoublingFactor n a := by
  let q := Real.sqrt (a / ((n - 1 : ℕ) : ℝ))
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hden : 0 < hyperbolicRadialVolume q (n - 1) (1 / 2) :=
    hyperbolicRadialVolume_pos hq (by norm_num)
  apply (one_le_div hden).2
  change (∫ t in (0 : ℝ)..(1 / 2 : ℝ), hyperbolicDensity q (n - 1) t) ≤
    ∫ t in (0 : ℝ)..(1 : ℝ), hyperbolicDensity q (n - 1) t
  apply intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hyperbolicDensity_pos hq ht.1).le
  · exact (hyperbolicDen_continuous q (n - 1)).intervalIntegrable _ _

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]


theorem local_volume_doubling [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : 2 ≤ Module.finrank ℝ E)
    (x : M) {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r)
    (hRic : ∀ y ∈ riemannianBallOf (I := I) g x r, ∀ v : TangentSpace I y,
      -a * r⁻¹ ^ 2 * g.inner y v v ≤ metricRicciAt g y (fun _ => v)) :
    (riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x r)).toReal ≤
      localDoublingFactor (Module.finrank ℝ E) a *
        (riemannianVolumeMeasure I M g (riemannianBallOf (I := I) g x (r / 2))).toReal := by
  sorry


end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
