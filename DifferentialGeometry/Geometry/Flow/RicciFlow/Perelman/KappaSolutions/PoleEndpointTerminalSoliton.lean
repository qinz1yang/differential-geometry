import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointTerminalPotentialDerivatives
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ChartEquation


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

local notation "θ" => (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1))

namespace HalfLineMetricConvergenceData

theorem poleEndpoint_redLength_limit_exists_terminal_gradientRicciSoliton
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps
      (poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma) P phi)
    (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i)
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ᶠ k in atTop, redLength
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term (phi (co.φ k))).S
      0 p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y : P.M, ∀ t ∈ Icc 1 2,
      Tendsto (fun k => redLength
        ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term
          (phi (co.φ (rho k)))).S 0 p (Phi.map (co.φ (rho k)) y) t)
        atTop (𝓝 (ell (y, t))))
    (hsmooth : ∀ n : ℕ, ContMDiff I 𝓘(ℝ) ∞ (fun x => ell (x, θ n)))
    (hsol : ∀ n : ℕ, gradientRicciSoliton (co.gInf (1 - θ n))
      (⟨fun x => ell (x, θ n), hsmooth n⟩ : C^∞⟮I, P.M; ℝ⟯) (1 / θ n))
    : ∃ hf : ContMDiff I 𝓘(ℝ) ∞ (fun x => ell (x, 1)),
      gradientRicciSoliton (co.gInf 0)
        (⟨fun x => ell (x, 1), hf⟩ : C^∞⟮I, P.M; ℝ⟯) 1 := by
  classical
  apply exists_gradientRicciSoliton_of_local_chart_equation
    (co.gInf 0) (fun x => ell (x, 1)) 1
  intro α
  let center : E := extChartAt I α α
  obtain ⟨rOut, hrOut, hWt⟩ := Metric.mem_nhds_iff.mp
    (extChartAt_target_mem_nhds (I := I) α)
  let a : ℝ := rOut / 4
  have ha : 0 < a := by dsimp only [a]; positivity
  have hclosed : Metric.closedBall center (3 * a) ⊆ (extChartAt I α).target := by
    intro y hy
    apply hWt
    exact (Metric.mem_closedBall.mp hy).trans_lt (by dsimp only [a]; linarith)
  let J : Set P.M := (extChartAt I α).symm '' Metric.closedBall center (3 * a)
  have hJ : IsCompact J := (isCompact_closedBall center (3 * a)).image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := I) α).mono hclosed)
  have hmaps : MapsTo (extChartAt I α).symm (Metric.closedBall center (3 * a)) J :=
    fun y hy => ⟨y, hy, rfl⟩
  have hderiv := poleEndpoint_redLength_limit_chart_terminal_derivatives
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ hbase
    rho hrho ell (fun y _ t ht => hconv y t ht) hsmooth hsol α center
    (r := a) (rMid := 2 * a) (rOut := 3 * a)
    (by linarith) (by linarith) hclosed hmaps
  refine ⟨Metric.ball center a, Metric.isOpen_ball, Metric.mem_ball_self ha, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact hclosed (Metric.mem_closedBall.mpr ((Metric.mem_ball.mp hy).le.trans
      (by linarith)))
  · exact fun y hy => (hderiv y hy).1.differentiableWithinAt
  · exact fun y hy => (hderiv y hy).2.1.differentiableWithinAt
  · exact fun y hy => (hderiv y hy).2.2

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
