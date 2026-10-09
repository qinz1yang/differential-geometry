import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointUpperSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostContinuity
import DifferentialGeometry.Analysis.Convex.CenteredUpperSupport

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
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

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

namespace FlowMetricConvergenceData

theorem exists_eventually_concaveOn_poleEndpoint_redLength_sub_quadratic_on_time_interval
    (Φ : PointedCGHMaps (I := I) Y P phi)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ)
    {δ T : ℝ} (hδ : 1 < δ)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt (1 - T) (-(δ - 1) / 2))
    (hG : MetricFamilySmoothOn (Y).D co.gInf)
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J K : Set P.M} (hK : IsCompact K) (hJK : J ⊆ K)
    {B W : ℝ}
    (hcost : ∀ᶠ k in atTop, ∀ t ∈ Icc δ T, ∀ y ∈ J,
      @redLength E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 p
        (Φ.map (co.φ k) y) t ≤ W)
    (hcapture : ∀ᶠ k in atTop, ∀ t ∈ Icc δ T, ∀ y ∈ J,
      ∀ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
      @IsLRegularizedGeodesicOn E _ _ _ H _ I _ F.M F.topology F.charted F.smooth F.t2 _
        ((U).term (phi (co.φ k))).S 0 alpha (Ioc 0 (Real.sqrt t)) →
      alpha 0 = p → alpha (Real.sqrt t) = Φ.map (co.φ k) y →
      @lRegularizedAction E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 alpha 0 (Real.sqrt t) =
        @lCost E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 p (Φ.map (co.φ k) y) t →
      alpha '' Icc (max (Real.sqrt ((1 + δ) / 2)) (Real.sqrt t / 2))
        (Real.sqrt t) ⊆ Φ.map (co.φ k) '' K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ n : ℕ, ∀ k ≥ n, ∀ t ∈ Icc δ T, ∀ (beta : ℝ → P.M) (a b : ℝ),
      (∀ r ∈ Icc a b, IsGeodesicAt R beta r) → MapsTo beta (Icc a b) J →
      (∀ r ∈ Icc a b, Real.sqrt (R.inner (beta r)
        (lVelocity (I := I) beta r) (lVelocity (I := I) beta r)) ≤ B) →
      ConcaveOn ℝ (Icc a b)
        (fun r ↦ @redLength E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 p
          (Φ.map (co.φ k) (beta r)) t - D / 2 * r ^ 2) := by
  obtain ⟨D, hD, n₁, hsupport⟩ :=
    exists_eventually_poleEndpoint_redLength_upper_support_on_time_interval_of_geodesic_capture
      F hcar hreg b hbmem tau q hsigma Φ R bf hsrc htgt hδ co hG hboundary
        kappa hF p hK hJK hcost hcapture
  obtain ⟨m, hm⟩ := Φ.source_subset hK
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.mp
    (co.strictMono.tendsto_atTop.eventually (eventually_ge_atTop m))
  refine ⟨D, hD, max n₁ n₂, ?_⟩
  intro k hk t htau beta a b hbeta hbetaJ hspeed
  have hk₁ : n₁ ≤ k := (le_max_left _ _).trans hk
  have hk₂ : n₂ ≤ k := (le_max_right _ _).trans hk
  have hsource : K ⊆ Φ.source (co.φ k) := hm (co.φ k) (hn₂ k hk₂)
  apply DifferentialGeometry.Analysis.concaveOn_sub_quadratic_of_centered_upper_support
    (convex_Icc a b)
  · apply (continuous_redLength_of_ancient ((U).term (phi (co.φ k)))
      (hF (phi (co.φ k))) p ((zero_lt_one.trans hδ).trans_le htau.1)).comp_continuousOn
    intro r hr
    have hmap := (Φ.partialDiffeomorph (co.φ k)).isLocalDiffeomorphAt I I ∞
      (hsource (hJK (hbetaJ hr)))
    exact (hmap.contMDiffAt.continuousAt.comp (hbeta r hr).continuousAt).continuousWithinAt
  · intro x hx
    have hxi : x ∈ Icc a b := interior_subset hx
    let gamma : ℝ → P.M := fun r ↦ beta (r + x)
    have hgamma : IsGeodesicAt R gamma 0 := by
      simpa only [sub_self] using
        DifferentialGeometry.Geometry.isGeodesicAt_comp_add (hbeta x hxi) x
    have hvel : lVelocity (I := I) gamma 0 = lVelocity (I := I) beta x := by
      have hdiff := (DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt
        (hbeta x hxi)).mdifferentiableAt (by simp)
      have hh := DifferentialGeometry.Geometry.mfderiv_comp_add_apply_one
        (I := I) (γ := beta) 0 x (by simpa only [zero_add] using hdiff)
      unfold lVelocity
      rw [zero_add] at hh
      exact hh
    have hgammaSpeed : Real.sqrt (R.inner (gamma 0)
        (lVelocity (I := I) gamma 0) (lVelocity (I := I) gamma 0)) ≤ B := by
      rw [hvel]
      change Real.sqrt (R.inner (beta (0 + x))
        (lVelocity (I := I) beta x) (lVelocity (I := I) beta x)) ≤ B
      rw [zero_add]
      exact hspeed x hxi
    obtain ⟨ψ, hψ, htouch, hupper, hsecond⟩ := hsupport k hk₁ t htau gamma hgamma
      (by simpa only [gamma, zero_add] using hbetaJ hxi) hgammaSpeed
    refine ⟨ψ, hψ.contDiffAt, ?_, ?_, hsecond⟩
    · simpa only [gamma, zero_add] using htouch
    · filter_upwards [hupper] with r hr
      simpa only [gamma, add_comm] using hr


end FlowMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
