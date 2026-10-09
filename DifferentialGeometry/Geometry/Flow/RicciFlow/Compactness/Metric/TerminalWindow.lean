import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardExtension
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Subsequence

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def _root_.DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.staticTerminalLimitOfWindow
    {X : FlowSequence.{u}} (P : MetricCompactLimit (X.atTime 0))
    (hcanonical : ∀ k, P.convergence.metrics.domain k =
      CanonicalMetricCompactness.canonicalSourceData P.maps k)
    (hconnected : ConnectedSpace P.limit.M)
    (hprecompact : ∀ i, IsCompact (closure (P.maps.source i)))
    (hsourceconn : ∀ i, IsConnected (P.maps.source i))
    (hnested : ∀ i, closure (P.maps.source i) ⊆ P.maps.source (i + 1))
    (hcapture : MetricSourceCapture P.maps)
    (hnonnegative : SecLower P.limit.metric 0 Set.univ)
    {A C : ℝ} (rho : ℕ → ℕ) (hrho : StrictMono rho)
    (hcarrier : ∀ i, Icc (-A) 0 ⊆ (X.interval (P.subseq (rho i))).carrier)
    (hregular : ∀ i, Ioo (-A) 0 ⊆ (X.interval (P.subseq (rho i))).regular)
    (hcurv : ∀ᶠ i in atTop, ∀ t ∈ (X.interval i).carrier,
      ∀ y, PointedFlowData.rmNormSq (X.term i) t y ≤ C) :
    StaticTerminalLimit
      { interval := fun i => X.interval (P.subseq (rho i))
        term := fun i => X.term (P.subseq (rho i)) } A := by
  let Y : FlowSequence :=
    { interval := fun i => X.interval (P.subseq (rho i))
      term := fun i => X.term (P.subseq (rho i)) }
  let F : PointedRiemannianConvergenceMaps (Y.atTime 0) P.limit id :=
    { partialDiffeomorph := fun i => P.maps.partialDiffeomorph (rho i)
      source_exhausts := P.maps.source_exhausts.comp_subseq hrho
      base_mem := fun i => P.maps.base_mem (rho i)
      basepoint_map := fun i => P.maps.basepoint_map (rho i) }
  let hconv : MetricConvergenceData F := {
    domain := CanonicalMetricCompactness.canonicalSourceData F
    converges := by
      intro K hK p epsilon hepsilon
      obtain ⟨N, hN⟩ := P.convergence.metrics.converges K hK p epsilon hepsilon
      refine ⟨N, fun i hi => ?_⟩
      have h := hN (rho i) (hi.trans (hrho.id_le i))
      rw [hcanonical] at h
      exact h }
  refine {
    carrier_window := hcarrier
    regular_window := hregular
    space := P.limit
    subseq := id
    strictMono := strictMono_id
    maps := F
    converges := hconv
    canonical_domains := fun _ => rfl
    capture := fun r hr => hrho.tendsto_atTop.eventually (hcapture r hr)
    precompact := fun i => hprecompact (rho i)
    connected_domains := fun i => hsourceconn (rho i)
    nested := ?_
    connected := hconnected
    complete := P.limit_complete
    nonnegative := hnonnegative
    slab_bounds := ?_ }
  · intro i
    exact (hnested (rho i)).trans (P.maps.source_exhausts.monotone
      (Nat.succ_le_iff.mpr (hrho (Nat.lt_succ_self i))))
  · intro K _hK width _hw hwd
    refine ⟨C, ?_⟩
    filter_upwards [(P.strictMono.comp hrho).tendsto_atTop.eventually hcurv] with i hi
    intro t ht y _hy
    exact hi t (hcarrier i ⟨(neg_le_neg hwd.le).trans ht.1, ht.2⟩) (F.map i y)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
