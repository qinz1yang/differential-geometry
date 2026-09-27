import DifferentialGeometry.Topology.Manifold.ClosedCellChart
import DifferentialGeometry.Geometry.Metric.Family.Pullback
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula

noncomputable section

open Bundle Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Connection

private local instance (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  Handle.closedCellChartedSpaceSucc m

private local instance (m : ℕ) :
    IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  Handle.closedCellIsManifold m

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
  (Φ : PartialDiffeomorph (𝓡 (m + 1)) I
    (EuclideanSpace ℝ (Fin (m + 1))) M ∞)
  (c : EuclideanSpace ℝ (Fin (m + 1))) {r : ℝ} (hr : 0 < r)
  (hsource : Metric.closedBall c r ⊆ Φ.source)

def closedCellPullbackMetricFamily :
    MetricConnectionFamilyOn (I := 𝓡∂ (m + 1)) (M := ClosedCell (m + 1)) D where
  metric t := (g t).pullback (closedCellChartMap Φ c r)
    (contMDiff_closedCellChartMap Φ c hr.le hsource)
    (injective_mfderiv_closedCellChartMap Φ c hr hsource)
  connection t := leviCivitaConnectionOfMetric
    ((g t).pullback (closedCellChartMap Φ c r)
      (contMDiff_closedCellChartMap Φ c hr.le hsource)
      (injective_mfderiv_closedCellChartMap Φ c hr hsource))
  metricCompatible _ := leviCivitaConnectionOfMetric_isMetricCompatible _

omit [FiniteDimensional ℝ E] in
@[simp]
theorem closedCellPullbackMetricFamily_inner (t : ℝ) (x : ClosedCell (m + 1))
    (v w : TangentSpace (𝓡∂ (m + 1)) x) :
    ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t).inner x v w =
      (g t).inner (Φ (c + r • x.val))
        (mfderiv (𝓡∂ (m + 1)) I (closedCellChartMap Φ c r) x v)
        (mfderiv (𝓡∂ (m + 1)) I (closedCellChartMap Φ c r) x w) := rfl

theorem metricFamilySmoothOn_closedCellPullbackMetricFamily
    (hg : MetricFamilySmoothOn D g) :
    MetricFamilySmoothOn D (closedCellPullbackMetricFamily D g Φ c hr hsource).metric :=
  hg.of_pullback (closedCellPullbackMetricFamily D g Φ c hr hsource).metric
    (closedCellChartMap Φ c r) (contMDiff_closedCellChartMap Φ c hr.le hsource)
    (fun _ _ _ _ => rfl)

end DifferentialGeometry.Geometry.Curvature
