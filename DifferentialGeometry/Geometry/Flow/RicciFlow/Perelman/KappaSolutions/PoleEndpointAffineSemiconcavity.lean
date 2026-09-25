import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HalfLinePoleEndpointAffineSupport
import DifferentialGeometry.Analysis.Convex.CenteredUpperSupport


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

theorem exists_eventually_concaveOn_poleEndpoint_redLength_in_chart_sub_quadratic
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
      p (q (phi (co.φ k))) 1 ≤ A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ n : ℕ, ∀ k ≥ n, ∀ t ∈ Icc δ T,
      ∀ (v w : E) (r₀ r₁ : ℝ),
        MapsTo (fun r : ℝ => v + r • w) (Icc r₀ r₁) ((extChartAt I a) '' J) →
        ConcaveOn ℝ (Icc r₀ r₁)
          (fun r => redLength ((U).term (phi (co.φ k))).S 0 p
            (Phi.map (co.φ k) ((extChartAt I a).symm (v + r • w))) t -
            (D * ‖w‖ ^ 2) / 2 * r ^ 2) := by
  obtain ⟨D₀, hD₀, n₁, hsupport⟩ :=
    exists_eventually_poleEndpoint_redLength_affine_upper_support_on_compact
      F hcar hreg b hbmem times q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
      kappa hF p a hJ hchart (T := T) hδ hbase
  obtain ⟨L, hLip⟩ := exists_eventually_lipschitzOnWith_poleEndpoint_redLength_in_chart
    F hcar hreg b hbmem times q hsigma Phi R hR co kappa hF p a hJ hchart hδ.le hbase
  obtain ⟨n₂, hLip₂⟩ := eventually_atTop.mp hLip
  refine ⟨D₀, hD₀, max n₁ n₂, ?_⟩
  intro k hk t ht v w r₀ r₁ hline
  have hk₁ : n₁ ≤ k := (le_max_left _ _).trans hk
  have hk₂ : n₂ ≤ k := (le_max_right _ _).trans hk
  let f : E → ℝ := fun z => redLength ((U).term (phi (co.φ k))).S 0 p
    (Phi.map (co.φ k) ((extChartAt I a).symm z)) t
  change ConcaveOn ℝ (Icc r₀ r₁) (fun r => f (v + r • w) - (D₀ * ‖w‖ ^ 2) / 2 * r ^ 2)
  apply DifferentialGeometry.Analysis.concaveOn_sub_quadratic_of_centered_upper_support
    (convex_Icc r₀ r₁)
  · intro r hr
    obtain ⟨y, hy, hcoord⟩ := hline hr
    change extChartAt I a y = v + r • w at hcoord
    obtain ⟨s, hs, hfs⟩ := hLip₂ k hk₂ t ht y hy
    rw [hcoord] at hs
    have hfc : ContinuousAt f (v + r • w) := hfs.continuousOn.continuousAt hs
    have hlinear : ContinuousAt (fun s : ℝ => v + s • w) r := by fun_prop
    exact (hfc.comp (f := fun s : ℝ => v + s • w) hlinear).continuousWithinAt
  · intro x hx
    obtain ⟨y, hy, hcoord⟩ := hline (interior_subset hx)
    change extChartAt I a y = v + x • w at hcoord
    have hinv : (extChartAt I a).symm (v + x • w) = y := by
      rw [← hcoord]
      exact (extChartAt I a).left_inv (by simpa only [extChartAt_source] using hchart hy)
    obtain ⟨ψ, hψ, htouch, hupper, hsecond⟩ := hsupport k hk₁ t ht y hy w
    refine ⟨ψ, hψ, ?_, ?_, hsecond⟩
    · simpa only [f, hinv] using htouch
    · filter_upwards [hupper] with r hr
      have hshift : v + (x + r) • w = (v + x • w) + r • w := by
        rw [add_smul, add_assoc]
      simpa only [f, hcoord, hshift] using hr

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
