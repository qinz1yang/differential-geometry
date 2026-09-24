import DifferentialGeometry.Geometry.Metric.Distance.MetricLocality
import DifferentialGeometry.Geometry.Comparison.Volume.VolumeNaturality
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem riemannianVolumeMeasure_ball_eq_of_eqOn_outer_closedBall
    (g g' : SmoothRiemannianMetric I M) {p x : M} {r ρ R : ℝ}
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hR : r + ρ ≤ R)
    (hx : x ∈ riemannianClosedBallOf g p r)
    (heq : ∀ z ∈ riemannianClosedBallOf g p R, g'.inner z = g.inner z)
    (hle : ∀ z (v : TangentSpace I z), g.inner z v v ≤ g'.inner z v v) :
    riemannianVolumeMeasure I M g' (riemannianBallOf g' x ρ) =
      riemannianVolumeMeasure I M g (riemannianBallOf g x ρ) := by
  rw [riemannianBallOf_eq_of_eqOn_outer_closedBall g g' hr hρ hR hx heq hle]
  have hopen : IsOpen (riemannianBallOf g x ρ) :=
    isOpen_lt (by
      unfold riemannianEDistOf
      exact Riemannian.continuous_riemannianEDist g x) continuous_const
  apply Riemannian.VolumeComparison.riemannianVolumeMeasure_apply_eq_of_inner_eqOn
    g' g hopen.measurableSet
  intro z hz v
  change riemannianEDistOf g x z < ENNReal.ofReal ρ at hz
  have hzR := riemannianClosedBallOf_subset_of_add_radius_le g hr hρ hR hx (le_of_lt hz)
  exact congrArg (fun A => A v v) (heq z hzR)

end DifferentialGeometry.Geometry.Measure
