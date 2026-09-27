import DifferentialGeometry.Geometry.Metric.PointPickingSequence
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Topology.Manifold.LocalCompactness

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

theorem exists_scalar_point_selection_of_tendsto_atTop_on_compact_balls
    {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]
    [∀ n, IsManifold I ∞ (M n)] [∀ n, T2Space (M n)] [∀ n, PreconnectedSpace (M n)]
    (g : ∀ n, SmoothRiemannianMetric I (M n)) (p y : ∀ n, M n)
    {D : ℝ} (hD : 0 ≤ D)
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf (g n) (p n) (D + 1)))
    (hy : ∀ n, riemannianEDistOf (g n) (p n) (y n) ≤ ENNReal.ofReal D)
    (hfy : ∀ n, 0 < metricScalarAt (g n) (y n))
    (hlim : Tendsto (fun n => metricScalarAt (g n) (y n)) atTop atTop) :
    ∃ (x : ∀ n, M n) (r : ℕ → ℝ),
      (∀ n, 0 < r n ∧ r n < D + 1 ∧
        (riemannianEDistOf (g n) (p n) (x n)).toReal < D + 1 ∧ 0 < metricScalarAt (g n) (x n)) ∧
      Tendsto (fun n => metricScalarAt (g n) (x n)) atTop atTop ∧
      Tendsto (fun n => metricScalarAt (g n) (x n) * r n ^ 2) atTop atTop ∧
      (∀ n, r n = (D + 1-(riemannianEDistOf (g n) (p n) (x n)).toReal)/4) ∧
      (∀ n, metricScalarAt (g n) (y n)/16 ≤ metricScalarAt (g n) (x n) * r n ^ 2) ∧
      (∀ n, IsCompact (riemannianClosedBallOf (g n) (x n) (r n))) ∧
      ∀ n z, (riemannianEDistOf (g n) (x n) z).toReal ≤ r n →
        (riemannianEDistOf (g n) (p n) z).toReal < D + 1 ∧
          metricScalarAt (g n) z ≤ (16/9 : ℝ) * metricScalarAt (g n) (x n) := by
  let _ : ∀ n, RegularSpace (M n) := fun n => DifferentialGeometry.Topology.Manifold.regularSpace_of_chartedSpace I
  exact SmoothRiemannianMetric.exists_point_selection_of_tendsto_atTop_on_compact_balls
    g p y (fun n => metricScalarAt (g n)) hD hcompact
    (fun n => (metricScalar_smooth (g n)).continuous.continuousOn) hy hfy hlim

end DifferentialGeometry.Geometry.Curvature
