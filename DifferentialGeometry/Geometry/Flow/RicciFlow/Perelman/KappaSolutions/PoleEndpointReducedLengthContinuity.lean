import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthEquicontinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostContinuity
import Mathlib.Topology.EMetricSpace.Lipschitz


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter _root_.Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

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

theorem eventually_continuousOn_poleEndpoint_redLength_on_compact_time_interval
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 0 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A) :
    ∀ᶠ k in atTop, ContinuousOn
      (fun z : P.M × ℝ => redLength ((U).term (phi (co.φ k))).S 0 p
        (Phi.map (co.φ k) z.1) z.2) (J ×ˢ Icc a c) := by
  obtain ⟨C, _hC, htime⟩ :=
    exists_eventually_abs_poleEndpoint_redLength_sub_le_on_compact_time_interval
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) ha hbase
  obtain ⟨m, hm⟩ := Phi.source_subset hJ
  filter_upwards [htime,
    co.strictMono.tendsto_atTop.eventually (eventually_ge_atTop m)] with k htimek hk
  have hmap : ContinuousOn (Phi.map (co.φ k)) J :=
    (Phi.partialDiffeomorph (co.φ k)).contMDiffOn_toFun.continuousOn.mono
      (hm (co.φ k) hk)
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith'
    (fun z : P.M × ℝ => redLength ((U).term (phi (co.φ k))).S 0 p
      (Phi.map (co.φ k) z.1) z.2) (Real.toNNReal C)
  · intro y hy
    apply LipschitzOnWith.of_dist_le'
    intro s hs t ht
    simpa only [Real.dist_eq] using htimek y hy s hs t ht
  · intro t ht
    exact (continuous_redLength_of_ancient ((U).term (phi (co.φ k)))
      (hancient (phi (co.φ k))) p (ha.trans_le ht.1)).comp_continuousOn hmap

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
