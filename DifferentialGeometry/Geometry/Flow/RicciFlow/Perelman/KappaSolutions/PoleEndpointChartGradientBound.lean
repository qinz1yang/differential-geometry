import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointJointLipschitz
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter _root_.Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal NNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

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

namespace HalfLineMetricConvergenceData

theorem exists_poleEndpoint_redLength_limit_chart_fderiv_bound
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) (z : E) {r rOut : ℝ} (hr : r < rOut)
    (hWt : Metric.closedBall z rOut ⊆ (extChartAt I x).target)
    (hWJ : MapsTo (extChartAt I x).symm (Metric.closedBall z rOut) J) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc a c, ∀ y ∈ Metric.closedBall z r,
      ‖fderiv ℝ (fun w : E => ell ((extChartAt I x).symm w, t)) y‖ ≤ K := by
  have hLL : LocallyLipschitzOn (Metric.closedBall z rOut ×ˢ Icc a c)
      (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) :=
    locallyLipschitzOn_poleEndpoint_redLength_limit_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
      rho hrho ell hconv x hWt hWJ
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    ((isCompact_closedBall z rOut).prod isCompact_Icc) hLL
  refine ⟨K, ?_⟩
  intro t ht y hy
  have hslice : LipschitzOnWith K
      (fun w : E => ell ((extChartAt I x).symm w, t)) (Metric.closedBall z rOut) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro w hw w' hw'
    simpa only [dist_prod_same_right] using
      hK.dist_le_mul (w, t) ⟨hw, ht⟩ (w', t) ⟨hw', ht⟩
  have hyOut : y ∈ Metric.ball z rOut :=
    Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hy).trans_lt hr)
  exact norm_fderiv_le_of_lipschitzOn ℝ
    (Metric.closedBall_mem_nhds_of_mem hyOut) hslice

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
