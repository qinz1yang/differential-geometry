import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointTerminalFirstDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointTerminalHessian


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter _root_.Manifold Set
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Analysis.Schauder
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal BigOperators

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

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "θ" => (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1))

namespace HalfLineMetricConvergenceData

theorem poleEndpoint_redLength_limit_chart_terminal_derivatives
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A : ℝ}
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc 1 2,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (hsmooth : ∀ n : ℕ, ContMDiff I 𝓘(ℝ) ∞ (fun x => ell (x, θ n)))
    (hsol : ∀ n : ℕ, gradientRicciSoliton (co.gInf (1 - θ n))
      (⟨fun x => ell (x, θ n), hsmooth n⟩ : C^∞⟮I, P.M; ℝ⟯) (1 / θ n))
    (α : P.M) (center : E) {r rMid rOut : ℝ}
    (hr : r < rMid) (hMid : rMid < rOut)
    (hWt : Metric.closedBall center rOut ⊆ (extChartAt I α).target)
    (hWJ : MapsTo (extChartAt I α).symm (Metric.closedBall center rOut) J) :
    ∀ y ∈ Metric.ball center r,
      DifferentiableAt ℝ (fun w : E => ell ((extChartAt I α).symm w, 1)) y ∧
      DifferentiableAt ℝ (fderiv ℝ (fun w : E => ell ((extChartAt I α).symm w, 1))) y ∧
      ∀ i j : Fin (Module.finrank ℝ E),
        fderiv ℝ (fderiv ℝ (fun w : E => ell ((extChartAt I α).symm w, 1))) y
          (chartModelBasis E i) (chartModelBasis E j) =
        (1 / 2 : ℝ) * chartGramOnE (co.gInf 0) α i j y -
          chartRicciTensor (co.gInf 0) α i j y +
          ∑ k : Fin (Module.finrank ℝ E), chartChristoffel (co.gInf 0) α i j k y *
            fderiv ℝ (fun w : E => ell ((extChartAt I α).symm w, 1)) y
              (chartModelBasis E k) := by
  obtain ⟨hd, hgrad⟩ := poleEndpoint_redLength_limit_chart_terminal_fderiv
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ hbase
      rho hrho ell hconv hsmooth hsol α center hr hMid hWt hWJ
  have hWK : Metric.ball center r ⊆ Metric.closedBall center rOut := by
    intro y hy
    exact Metric.mem_closedBall.mpr ((Metric.mem_ball.mp hy).trans (hr.trans hMid)).le
  have hsecond := co.poleEndpoint_chart_hessian_of_gradient_convergence Phi
    (by rfl : (Y).D.carrier = Iic 0) (by intro t ht; exact ht)
    ell hsmooth hsol α (isCompact_closedBall center rOut) hWt Metric.isOpen_ball hWK hgrad
  intro y hy
  exact ⟨hd y (Metric.mem_ball.mpr ((Metric.mem_ball.mp hy).trans hr)), hsecond y hy⟩

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
