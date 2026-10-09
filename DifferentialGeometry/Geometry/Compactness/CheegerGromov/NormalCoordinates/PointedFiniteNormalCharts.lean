import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.FiniteNormalChartInputs
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.FiniteNormalCharts





set_option autoImplicit false
noncomputable section
open Bundle Set Manifold
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
namespace DifferentialGeometry.CheegerGromovCompactness
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
universe u

theorem exists_uniform_complete_normal_charts_of_pointed_bounds (n K : ℕ) (hn : 2 ≤ n)
    {r v S A : ℝ} (hr : 0 < r) (hv : 0 < v) (hS : 0 < S) (hA : 0 < A) :
    letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := ⟨by simpa using (show n ≠ 0 by omega)⟩
    letI : NormedAddCommGroup ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ 2 * a < 1 ∧
      ∀ (P : PointedRiemannianManifold.{u} (𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))))
        (hcomplete : MetricComplete P)
        (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M) (p : P.M),
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) P.M := P.charted
    letI : IsManifold 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) ∞ P.M := P.smooth
    letI : IsManifold 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 1 P.M :=
      IsManifold.of_le (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) (M := P.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x) :=
      P.riemBundle (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
    letI : (x : P.M) → InnerProductSpace Real (TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x) :=
      P.riemInner (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (fun x : P.M => TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x) :=
      P.riemBundle_cont (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
    letI : EMetricSpace P.M := P.emetricSpace (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) P hcomplete
    letI : ConnectedSpace P.M := hconn
    let hEnorm : ∀ (x : P.M) (v : TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) x),
        ‖v‖ₑ = ENNReal.ofReal
          (Real.sqrt (P.metric.inner x v v)) := by
      intro x v
      with_unfolding_all
        exact
          Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) P.metric x v
    ENNReal.ofReal v ≤ riemannianVolumeMeasure _ P.M P.metric
      (riemannianBallOf P.metric P.basepoint r) →
    (∀ q : ℕ, q ≤ K → ∀ y ∈ riemannianBallOf P.metric P.basepoint (2 * S + r + 4),
      curvDerivNorm q P.metric y ≤ A) →
    p ∈ riemannianBallOf P.metric P.basepoint (S + 1) →
    ∀ Q : (EuclideanSpace ℝ (Fin n)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin n)), ∃ Φ : PartialDiffeomorph 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) (EuclideanSpace ℝ (Fin n)) P.M ∞,
      Φ.source = Metric.ball (0 : (EuclideanSpace ℝ (Fin n))) (2 * a) ∧
      Φ.target = (intrinsicFramedExp P.metric hEnorm p ∘ Q) ''
        Metric.ball (0 : (EuclideanSpace ℝ (Fin n))) (2 * a) ∧
      EqOn Φ (intrinsicFramedExp P.metric hEnorm p ∘ Q) (Metric.ball (0 : (EuclideanSpace ℝ (Fin n))) (2 * a)) ∧
      Φ 0 = p ∧
      ContDiffOn ℝ ∞ (pullbackMetricCoefficients P.metric Φ) (Metric.ball (0 : (EuclideanSpace ℝ (Fin n))) (2 * a)) ∧
      ContDiffOn ℝ K (fun z => Ring.inverse
        (IsCoercive.gramCLM (pullbackMetricCoefficients P.metric Φ z)))
        (Metric.ball (0 : (EuclideanSpace ℝ (Fin n))) (2 * a)) ∧
      ∀ z ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin n))) a,
        (∀ v : (EuclideanSpace ℝ (Fin n)), (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients P.metric Φ z v v ∧
          pullbackMetricCoefficients P.metric Φ z v v ≤ 2 * ‖v‖ ^ 2) ∧
        ∀ q : ℕ, q ≤ K →
          ‖iteratedFDeriv ℝ q (pullbackMetricCoefficients P.metric Φ) z‖ +
            ‖iteratedFDeriv ℝ q (fun y => Ring.inverse
              (IsCoercive.gramCLM (pullbackMetricCoefficients P.metric Φ y))) z‖ ≤ C := by
  let E := EuclideanSpace ℝ (Fin n)
  let _ : NeZero (Module.finrank ℝ E) := ⟨by simpa [E] using (show n ≠ 0 by omega)⟩
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  dsimp only
  obtain ⟨ι, hι, hi⟩ := DifferentialGeometry.CheegerGromovCompactness.uniform_injectivity_and_unit_ball_curvature
    n K hn hr hv hS hA
  obtain ⟨a, C, ha, hC, hsmall, hcharts⟩ :=
    exists_uniform_complete_normal_charts n K (by omega) hA hι
  refine ⟨a, C, ha, hC, hsmall.trans_le (min_le_left _ _), ?_⟩
  intro P hcomplete hconn p
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace E P.M := P.charted
  let _ : IsManifold 𝓘(ℝ, E) ∞ P.M := P.smooth
  let _ : IsManifold 𝓘(ℝ, E) 1 P.M :=
    IsManifold.of_le (I := 𝓘(ℝ, E)) (M := P.M) (n := ∞) (by decide)
  let _ : SigmaCompactSpace P.M := P.sigmaCompact
  let _ : T2Space P.M := P.t2
  let _ : T2Space (TangentBundle 𝓘(ℝ, E) P.M) := P.t2TangentBundle
  let _ : RiemannianBundle (fun x : P.M => TangentSpace 𝓘(ℝ, E) x) :=
    P.riemBundle (I := 𝓘(ℝ, E))
  let _ : (x : P.M) → InnerProductSpace Real (TangentSpace 𝓘(ℝ, E) x) :=
    P.riemInner (I := 𝓘(ℝ, E))
  let _ : IsContinuousRiemannianBundle E
      (fun x : P.M => TangentSpace 𝓘(ℝ, E) x) :=
    P.riemBundle_cont (I := 𝓘(ℝ, E))
  let _ : EMetricSpace P.M := P.emetricSpace (I := 𝓘(ℝ, E))
  let _ : CompleteSpace P.M :=
    MetricComplete.complete (I := 𝓘(ℝ, E)) P hcomplete
  let _ : ConnectedSpace P.M := hconn
  intro hvol hcurv hp Q
  obtain ⟨hinj, hjets⟩ := hi P hcomplete hvol hcurv p hp
  exact hcharts P hcomplete hconn p hjets hinj Q

end DifferentialGeometry.CheegerGromovCompactness
