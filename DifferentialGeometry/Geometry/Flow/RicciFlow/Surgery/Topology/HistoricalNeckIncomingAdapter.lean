import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncoming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Neck.NormalizedLift
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.EqualDimensionImmersion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.ClosedWindow

set_option autoImplicit false
noncomputable section
open Set Manifold Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private local instance survivor_domain_sigmaCompact (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) :
    SigmaCompactSpace (H.backwardSurvivorDomain first last hle) := by
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorDomain first last hle).isOpen)

private local instance incoming_domain_sigmaCompact (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) :
    SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) := by
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingDomain first last hle G).isOpen)

private local instance incoming_footprint_sigmaCompact (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s) (K : Set G.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorIncomingFootprint first last hle G K) := by
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K).isOpen)

private theorem incoming_footprint_point_smoothEmbedding
    {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {s : ℝ} {G : (H.stage last).IncomingSlab (H.time last) s}
    {K : Set G.terminalRegularOpen}
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val))
    {L : G.TerminalLimitMetric} {δ : ℝ} {k : ℕ} (N : NormalizedNeck L.metric δ k)
    (hinside : range N.chart ⊆ interior K) :
    IsSmoothEmbedding NeckCylinderModel ThreeModel ∞
      (fun x : neckBuffer δ =>
        H.backwardSurvivorIncomingFootprintPoint first last hle G K htrace (N.chart x)
          (hinside (mem_range_self x))) := by
  apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen
    NeckCylinderModel ThreeModel
    (H.backwardSurvivorIncomingFootprint first last hle G K)
  apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen
    NeckCylinderModel ThreeModel
    (H.backwardSurvivorIncomingDomain first last hle G)
  apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen
    NeckCylinderModel ThreeModel (H.backwardSurvivorDomain first last hle)
  apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen
    NeckCylinderModel ThreeModel G.terminalRegularOpen
  exact N.chart_smooth

theorem exists_historical_pullback_solution_from_incoming_slab
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck L.metric δ k)
    (K : Set G.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val))
    (hinside : range N.chart ⊆ interior K)
    {θ : ℝ} (hθ : 0 ≤ θ) (hstart : H.time first ≤ s - θ / N.scale) :
    ∃ (Φ : neckBuffer δ → H.backwardSurvivorIncomingFootprint first last hle G K)
      (hΦ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ)
      (gflow : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorIncomingFootprint first last hle G K))
      (S : SolutionOn (I := NeckCylinderModel)
        (M := neckBuffer δ) (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ))),
      H.backwardSurvivorIncomingFootprintMap first last hle G K ∘ Φ = N.chart ∧
      IsSolutionOn S ∧ S.base.metric 0 = N.normalizedMetric ∧
      (∀ t, S.base.metric t = localPullMetric
        (scaleMetric N.scale N.scale_pos (gflow (s + t / N.scale))) Φ hΦ) ∧
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
              (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      ∀ t ∈ Icc (H.time last) s,
        gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K) := by
  obtain ⟨gflow, hslabs, hlast, hterminal, hjoint, hsol⟩ :=
    H.exists_backwardSurvivorIncomingFootprint_isSolutionOn first last hle G L hinit K
  let Φ : neckBuffer δ → H.backwardSurvivorIncomingFootprint first last hle G K := fun x =>
    H.backwardSurvivorIncomingFootprintPoint first last hle G K htrace (N.chart x)
      (hinside (mem_range_self x))
  have hΦs : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Φ := by
    exact incoming_footprint_point_smoothEmbedding htrace N hinside
  have hΦ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ := fun x =>
    Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq
      (by simp [ThreeSpace, Module.finrank_prod]) (hΦs.isImmersion.isImmersionAt x)
  have hmap : H.backwardSurvivorIncomingFootprintMap first last hle G K ∘ Φ = N.chart := by
    funext x
    exact H.backwardSurvivorIncomingFootprintMap_point first last hle G K htrace (N.chart x)
      (hinside (mem_range_self x))
  let D := RealTimeInterval.closed (H.time first) s
    ((H.time_strictMono.monotone hle).trans G.lt.le)
  let T : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingFootprint first last hle G K) D := { base.metric := gflow }
  let U := T.parabolicClosedWindow s N.scale θ N.scale_pos hθ
  have hU : IsSolutionOn U := isSolutionOn_parabolicClosedWindow T hsol N.scale_pos hθ
    (fun t ht => ⟨hstart.trans ht.1, ht.2⟩)
    (fun t ht => ⟨hstart.trans_lt ht.1, ht.2⟩)
  let S := U.localPullback Φ hΦ
  refine ⟨Φ, hΦ, gflow, S, hmap, hU.localPullback Φ hΦ, ?_, ?_, hslabs, hlast⟩
  · change localPullMetric (scaleMetric N.scale N.scale_pos
      (gflow (s + 0 / N.scale))) Φ hΦ = N.normalizedMetric
    rw [zero_div, add_zero]
    calc
      localPullMetric (scaleMetric N.scale N.scale_pos (gflow s)) Φ hΦ =
          localPullMetric (scaleMetric N.scale N.scale_pos
            (localPullMetric L.metric
              (H.backwardSurvivorIncomingFootprintMap first last hle G K)
              (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K))) Φ hΦ := by
        rw [hterminal]
      _ = N.normalizedMetric := by
        let f : H.backwardSurvivorIncomingFootprint first last hle G K → G.terminalRegularOpen :=
          H.backwardSurvivorIncomingFootprintMap first last hle G K
        have hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
          H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K
        have hmapf : f ∘ Φ = N.chart := by simpa only [f] using hmap
        exact N.pullback_normalizedMetric f hf Φ hΦ hmapf
  · intro t
    rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
