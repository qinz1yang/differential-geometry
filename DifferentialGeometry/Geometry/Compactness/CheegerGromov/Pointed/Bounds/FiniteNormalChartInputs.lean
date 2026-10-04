import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.VolumeInjectivity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm







set_option autoImplicit false
noncomputable section
open Bundle Set Manifold Metric MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
namespace DifferentialGeometry.CheegerGromovCompactness
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem uniform_injectivity_and_unit_ball_curvature (n K : ℕ) (hn : 2 ≤ n) {r v S A : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hS : 0 < S) (hA : 0 < A) :
    let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
      ⟨by simpa using (show n ≠ 0 by omega)⟩
    ∃ ι > 0, ∀ P : PointedRiemannianManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))),
      MetricComplete P →
      ENNReal.ofReal v ≤ riemannianVolumeMeasure _ P.M P.metric
        (riemannianBallOf P.metric P.basepoint r) →
      (∀ j ≤ K, ∀ y ∈ riemannianBallOf P.metric P.basepoint (2*S+r+4),
        curvDerivNorm j P.metric y ≤ A) →
      ∀ z ∈ riemannianBallOf P.metric P.basepoint (S+1),
        HasInjRadiusAt P z ι ∧ ∀ j ≤ K, ∀ y,
          riemannianEDistOf P.metric z y < ENNReal.ofReal 1 →
          curvDerivNorm j P.metric y ≤ A := by
  let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
      ⟨by simpa using (show n ≠ 0 by omega)⟩
  obtain ⟨ι, hι, hi⟩ := exists_uniform_injRadius_of_base_volume n hn hr hv
    (show 0 < S+1 by linarith) hA
  refine ⟨ι, hι, ?_⟩
  intro P hcomplete hvol hcurv z hz
  have hRm : ∀ y ∈ riemannianBallOf P.metric P.basepoint (2*(S+1)+r+2),
      Real.sqrt (Tensor0SBundle.normSq0S P.metric y 4 (metricRm04At P.metric y)) ≤ A := by
    intro y hy
    have hy' : y ∈ riemannianBallOf P.metric P.basepoint (2*S+r+4) := by
      simpa only [show 2*(S+1)+r+2 = 2*S+r+4 by ring] using hy
    exact hcurv 0 (Nat.zero_le K) y hy'
  refine ⟨hi P hcomplete hvol hRm z hz, ?_⟩
  intro j hj y hy
  apply hcurv j hj y
  change riemannianEDistOf P.metric P.basepoint y < ENNReal.ofReal (2*S+r+4)
  have hz' : riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal (S+1) := hz
  calc
    riemannianEDistOf P.metric P.basepoint y ≤
        riemannianEDistOf P.metric P.basepoint z + riemannianEDistOf P.metric z y :=
      riemannianEDistOf_triangle P.metric _ _ _
    _ < ENNReal.ofReal (S+1) + ENNReal.ofReal 1 := ENNReal.add_lt_add hz' hy
    _ = ENNReal.ofReal (S+2) := by rw [← ENNReal.ofReal_add (by linarith) (by norm_num)]; congr 1; ring
    _ ≤ ENNReal.ofReal (2*S+r+4) := ENNReal.ofReal_le_ofReal (by linarith)

end DifferentialGeometry.CheegerGromovCompactness
