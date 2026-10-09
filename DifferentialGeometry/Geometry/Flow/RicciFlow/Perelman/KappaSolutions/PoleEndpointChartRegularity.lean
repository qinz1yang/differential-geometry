import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointChartSemiconcavity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointJointLipschitz
import DifferentialGeometry.Topology.LipschitzSwap
import Mathlib.Analysis.InnerProductSpace.LinearMap


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter _root_.Manifold Set TopologicalSpace
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
  (b : ℝ) (hbmem : b ∈ D.carrier) (times : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < times i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem times q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem times q hsigma

namespace HalfLineMetricConvergenceData

theorem exists_eventually_locallyLipschitzOn_concaveOn_poleEndpoint_redLength_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) (a : P.M) {J : Set P.M} (hJ : IsCompact J)
    (hchart : J ⊆ (chartAt H a).source) {δ T A : ℝ} (hδ : 1 < δ)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    {W : Set E} (hWconv : Convex ℝ W) (hWJ : W ⊆ (extChartAt I a) '' J)
    {S : Set ℝ} (hST : S ⊆ Icc δ T) :
    ∃ B : E →L[ℝ] E →L[ℝ] ℝ, ∀ᶠ k in atTop,
      let f : ℝ × E → ℝ := fun z => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I a).symm z.2)) z.1
      LocallyLipschitzOn (S ×ˢ W) f ∧
        ∀ t ∈ S, ConcaveOn ℝ W (fun z => f (t, z) - B z z / 2) := by
  have hWt : W ⊆ (extChartAt I a).target := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hWJ hz
    exact (extChartAt I a).map_source (by simpa only [extChartAt_source] using hchart hy)
  have hWInv : MapsTo (extChartAt I a).symm W J := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hWJ hz
    rw [(extChartAt I a).left_inv (by simpa only [extChartAt_source] using hchart hy)]
    exact hy
  obtain ⟨D₀, _, n, hconcave⟩ :=
    exists_eventually_concaveOn_poleEndpoint_redLength_on_convex_chart_subset_sub_norm_sq
      F hcar hreg b hbmem times q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
      kappa hF p a hJ hchart (T := T) hδ hbase
  let B : E →L[ℝ] E →L[ℝ] ℝ := D₀ • innerSL ℝ
  have hB (z : E) : B z z = D₀ * ‖z‖ ^ 2 := by
    change D₀ * inner ℝ z z = D₀ * ‖z‖ ^ 2
    rw [real_inner_self_eq_norm_sq]
  refine ⟨B, ?_⟩
  have hLip := eventually_locallyLipschitzOn_poleEndpoint_redLength_chart
    F hcar hreg b hbmem times q hsigma Phi R hR co kappa hF p hJ (c := T) hδ.le hbase a hWt hWInv
  filter_upwards [hrho.eventually hLip, hrho.eventually (eventually_ge_atTop n)] with k hk hn
  dsimp only
  constructor
  · exact hk.comp_swap.mono (Set.prod_mono hST Subset.rfl)
  · intro t ht
    apply (hconcave (rho k) hn t (hST ht) W hWconv hWJ).congr
    intro z _
    change _ - D₀ / 2 * ‖z‖ ^ 2 = _ - B z z / 2
    erw [hB]
    ring

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
