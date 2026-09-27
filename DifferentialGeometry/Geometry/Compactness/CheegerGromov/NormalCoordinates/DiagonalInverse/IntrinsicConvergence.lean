import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.DiagonalInverse.ChartConvergence
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallChartMetric

set_option autoImplicit false

noncomputable section
open Set Bundle Manifold Filter
open scoped ContDiff Manifold Topology
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, PseudoEMetricSpace (M k)] [∀ k, IsRiemannianManifold I (M k)]
  [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem IntrinsicBallChart.exists_recentered_diagonal_inverse_convergence
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k, IsMetricNorm (I := I) (g k))
    {p : ∀ k, M k} {ρ : ℝ} (hρ : 0 < ρ)
    (c : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (p k) ρ)
    {a : E} (ha : a ∈ Metric.ball (0 : E) (ρ / 8))
    (hell : ∀ k z, z ∈ Metric.ball (0 : E) ρ → ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I) (g k) (hEnorm k) (p k) z v v ∧
      intrinsicFrameMetric (I := I) (g k) (hEnorm k) (p k) z v v ≤ 2 * ‖v‖ ^ 2)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiffOn ℝ ∞ B (Metric.ball (0 : E) ρ))
    (hconv : MapCInfConvergenceOnCompacts (Metric.ball (0 : E) ρ)
      (fun k => intrinsicFrameMetric (I := I) (g k) (hEnorm k) (p k)) B) :
    let nc := fun k => (c k).toNormalBallChart (g k) (hEnorm k) (p k) hρ
    let hr8 : 0 < 8 * (ρ / 32) := by positivity
    let hball : ∀ k, Metric.ball a (8 * (ρ / 32)) ⊆ Metric.ball (0 : E) (nc k).radius := by
      intro k z hz
      change dist z 0 < ρ
      have ha' : dist a 0 < ρ / 8 := ha
      have hz' : dist z a < 8 * (ρ / 32) := hz
      have htri := dist_triangle z a 0
      linarith
    let cc := fun k => (nc k).recenter a hr8 (hball k)
    ∃ (q : NNReal) (δ : ℝ) (η : NNReal)
        (Φ : ℕ → (E × E) → ℝ → E × E)
        (e : ℕ → OpenPartialHomeomorph (E × E) (E × E))
        (qInf : NNReal) (δInf : ℝ) (etaInf : NNReal)
        (eInf : OpenPartialHomeomorph (E × E) (E × E)),
      0 < q ∧ 6 * (q : ℝ) < ρ / 32 ∧ 0 < δ ∧ η < 1 / 24 ∧
      (∀ k,
        (e k).source = Metric.ball (0 : E × E) q ∧
        (e k : E × E → E × E) = (fun z => (z.1, (Φ k z 1).1)) ∧
        e k 0 = 0 ∧
        Metric.closedBall (0 : E × E) δ ⊆ (e k).target ∧
        ContDiffOn ℝ ∞ (e k : E × E → E × E) (e k).source ∧
        ContDiffOn ℝ ∞ ((e k).symm : E × E → E × E) (e k).target ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q,
          (cc k).pair (e k z) = diagExp (g k) (hEnorm k) ((cc k).tangent z)) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q,
          z.1 ∈ Metric.ball (0 : E) (cc k).radius ∧
          (e k z).1 ∈ Metric.ball (0 : E) (cc k).radius ∧
          (e k z).2 ∈ Metric.ball (0 : E) (cc k).radius) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ k z 0 = z) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q,
          IsIntegralCurveOn (Φ k z) (fun _ => MetricKoszul.metricSpray ((cc k).metric (g k)))
            (Icc 0 1)) ∧
        (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (0 : ℝ) 1,
          (Φ k z t).1 ∈ Metric.ball (0 : E) (ρ / 32)) ∧
        ApproximatesLinearOn ((e k).symm : E × E → E × E)
          ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E))
          (e k).target η) ∧
      0 < qInf ∧ qInf < q ∧ 0 < δInf ∧ etaInf < 1 / 24 ∧
      eInf.source = Metric.ball (0 : E × E) qInf ∧
      Metric.closedBall (0 : E × E) δInf ⊆ eInf.target ∧
      ContDiffOn ℝ ∞ (eInf : E × E → E × E) eInf.source ∧
      ContDiffOn ℝ ∞ (eInf.symm : E × E → E × E) eInf.target ∧
      (∀ x ∈ Metric.ball (0 : E) qInf,
        (x, x) ∈ eInf.target ∧ eInf.symm (x, x) = (x, 0)) ∧
      ApproximatesLinearOn (eInf.symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E)) eInf.target etaInf ∧
      MapCInfConvergenceOnCompacts (Metric.ball (0 : E × E) qInf)
        (fun k => (e k : E × E → E × E)) eInf ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < min δ δInf ∧
        eInf.symm '' Metric.closedBall (0 : E × E) ε ⊆ Metric.ball 0 qInf ∧
        (∀ᶠ k in Filter.atTop, MapsTo (e k).symm (Metric.closedBall 0 ε) (Metric.ball 0 qInf)) ∧
        MapCInfConvergenceOnCompacts (Metric.ball (0 : E × E) ε)
          (fun k => ((e k).symm : E × E → E × E)) eInf.symm := by
  intro nc hr8 hball cc
  have hnormal : ∀ k, (nc k).MetricEquivOn (g k) (Metric.ball (0 : E) ρ) := by
    intro k
    exact (c k).metricEquivOn_of_intrinsicFrameMetric (g k) (hEnorm k) (p k) hρ (hell k)
  have hnormalConv : MapCInfConvergenceOnCompacts (Metric.ball (0 : E) ρ)
      (fun k => (nc k).metric (g k)) B :=
    hconv.congr Metric.isOpen_ball
      (fun k z hz => (c k).metric_eq_intrinsicFrameMetric (g k) (hEnorm k) (p k) hρ hz)
      (fun _ _ => rfl)
  exact exists_recentered_diagonal_inverse_convergence_of_metric_convergence g hEnorm nc a
    (by positivity : 0 < ρ / 32) (fun _ => le_rfl) (hball 0) hnormal hB hnormalConv

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
end
