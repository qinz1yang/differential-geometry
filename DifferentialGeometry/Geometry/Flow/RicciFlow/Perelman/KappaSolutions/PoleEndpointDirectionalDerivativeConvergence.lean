import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HalfLinePoleEndpointSemiconcavity
import DifferentialGeometry.Analysis.Calculus.Derivative.IntrinsicLimit

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

namespace HalfLineMetricConvergenceData

theorem tendsto_mvfderiv_poleEndpoint_redLength_along_of_geodesic
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {δ T A B : ℝ}
    (hδ : 1 < δ)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (lag : ℕ → ℝ) (hlag : ∀ᶠ k in atTop, lag k ∈ Icc δ T)
    (beta : ℝ → P.M) {a c r : ℝ} (hr : r ∈ interior (Icc a c))
    (hbeta : ∀ s ∈ Icc a c, IsGeodesicAt R beta s)
    (hbetaJ : MapsTo beta (Icc a c) J)
    (hspeed : ∀ s ∈ Icc a c, Real.sqrt (R.inner (beta s)
      (lVelocity (I := I) beta s) (lVelocity (I := I) beta s)) ≤ B)
    (f : P.M → ℝ)
    (hlim : ∀ s ∈ Icc a c, Tendsto
      (fun k ↦ redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) (beta s)) (lag k)) atTop (𝓝 (f (beta s))))
    (hsourceDiff : ∀ᶠ k in atTop, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y ↦ redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) (lag k)) (beta r))
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (beta r)) :
    Tendsto (fun k ↦ mvfderiv (I := I)
        (fun y ↦ redLength ((U).term (phi (co.φ (rho k)))).S 0 p
          (Phi.map (co.φ (rho k)) y) (lag k)) (beta r) (lVelocity (I := I) beta r))
      atTop (𝓝 (mvfderiv (I := I) f (beta r) (lVelocity (I := I) beta r))) := by
  obtain ⟨D, _hD, n, hconcave⟩ :=
    exists_eventually_concaveOn_poleEndpoint_redLength_sub_quadratic_on_time_interval
      F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
      kappa hF p hJ hδ hbase
  have hconcaveEv : ∀ᶠ k in atTop, ConcaveOn ℝ (Icc a c)
      (fun s ↦ redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) (beta s)) (lag k) - D / 2 * s ^ 2) := by
    filter_upwards [hrho.eventually (eventually_ge_atTop n), hlag] with k hk ht
    exact hconcave (rho k) hk (lag k) ht beta a c hbeta hbetaJ hspeed
  have hbetaDiff : MDifferentiableAt 𝓘(ℝ, ℝ) I beta r :=
    (DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt
      (hbeta r (interior_subset hr))).mdifferentiableAt (by simp)
  exact tendsto_mvfderiv_along_of_concaveOn_sub hr hbetaDiff hconcaveEv hsourceDiff hlim hf
    (by fun_prop)

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
