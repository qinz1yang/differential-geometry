import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalScalarDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorNormalizedPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckCurvature
import DifferentialGeometry.Geometry.Neck.NormalizedLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.ClosedWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.EqualDimensionImmersion


noncomputable section
open Set Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}
  {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}

private local instance : SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.event i).incoming.terminalRegularOpen.isOpen)

theorem NormalizedNeck.exists_historical_footprint_isSolutionOn_curvature_bound
    {δ₀ δ eps : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ₀ k)
    (hδ : δ₀ ≤ δ) (hδ1 : δ < 1) (hprecision : δ₀ ≤ eps)
    (hsmall : eps ≤ 1 / 8646) (hk : ⌈eps⁻¹⌉₊ ≤ k)
    (a : ℝ) (ha : 24 < a) (hpublic : δ⁻¹ + 1 ≤ a) (hfit : 4 * a < eps⁻¹)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ N.scale)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t x →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t x ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (htrace : ∀ x ∈ N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a},
      Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    {c : ℝ} (hc : H.time first ≤ c) (hcs : c ≤ H.time i.succ)
    (htime : 6 * C * (H.time i.succ - c) * N.scale ≤ 1) :
    ∃ K : Set (H.event i).incoming.terminalRegularOpen,
      K = N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a} ∧
      IsCompact K ∧ IsConnected K ∧ N.center ∈ K ∧
      range (N.monoDelta hδ hδ1).chart ⊆ interior K ∧
      IsCompact (riemannianClosedBallOf (H.event i).terminal.metric N.center
        (2*a / Real.sqrt N.scale)) ∧
      riemannianClosedBallOf (H.event i).terminal.metric N.center
        (2*a / Real.sqrt N.scale) ⊆ interior K ∧
      range (H.backwardSurvivorFootprintMap first i hle K) = interior K ∧
      ∃ G : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorFootprintInterior first i hle K),
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
          ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
            (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
              (H.backwardSurvivorFootprintInterior first i hle K)) ∧
        (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
          G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
            (H.backwardSurvivorFootprintInterior first i hle K)) ∧
        G (H.time i.succ) = localPullMetric (H.event i).terminal.metric
          (H.backwardSurvivorFootprintMap first i hle K)
          (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K) ∧
        IsSolutionOn ({ base := { metric := G } } :
          SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K)
            (RealTimeInterval.closed c (H.time i.succ) hcs)) ∧
        ∀ t ∈ Icc c (H.time i.succ), ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
          normSq0S (G t) x 4 (metricRm04At (G t) x) ≤
            (4 * Real.sqrt 3 * (N.scale + Phi (4*N.scale) + Phi 0)) ^ 2 := by
  obtain ⟨K,hK,hcompact,hconn,hcenter,hchart,hball,hballsub,hscalar,_,_⟩ :=
    N.exists_compact_footprint_historical_curvature_bound hδ hδ1 hprecision hsmall hk
      a ha hpublic hfit hq hqQ hPhi first hle hbound hpinch
  have htraceK : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val) := by
    intro x hx
    exact htrace x (hK ▸ hx)
  obtain ⟨hrange,G,hslabs,hlast,hterminal,hsol,hRm⟩ :=
    H.exists_backwardSurvivorFootprint_curvature_bound first i hle K hq hqQ hPhi hbound hpinch
      (fun x hx => (hscalar x hx).trans (by nlinarith [N.scale_pos])) htraceK hc hcs htime
  exact ⟨K,hK,hcompact,hconn,hcenter,hchart,hball,hballsub,hrange,G,hslabs,hlast,hterminal,hsol,hRm⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

set_option autoImplicit false
noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {first : Fin (H.eventCount + 1)}
  {i : Fin H.eventCount} {hle : first ≤ i.castSucc}

private local instance (K : Set (H.event i).incoming.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorFootprintInterior first i hle K) := by
  let _ : SigmaCompactSpace (H.backwardSurvivorDomain first i.castSucc hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorDomain first i.castSucc hle).isOpen)
  let _ : SigmaCompactSpace (H.backwardSurvivorTerminalFace first i hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorTerminalFace first i hle).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorFootprintInterior first i hle K).isOpen)

theorem NormalizedNeck.exists_historical_pullback_solution
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ k)
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (hinside : range N.chart ⊆ interior K)
    {θ : ℝ} (hθ : 0 ≤ θ) (hstart : H.time first ≤ H.time i.succ - θ / N.scale) :
    ∃ (Φ : neckBuffer δ → H.backwardSurvivorFootprintInterior first i hle K)
      (hΦ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ)
      (G : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorFootprintInterior first i hle K))
      (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
        (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ))),
      H.backwardSurvivorFootprintMap first i hle K ∘ Φ = N.chart ∧
      IsSolutionOn S ∧ S.base.metric 0 = N.normalizedMetric ∧
      (∀ t, S.base.metric t = localPullMetric
        (scaleMetric N.scale N.scale_pos (G (H.time i.succ + t / N.scale))) Φ hΦ) ∧
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
            (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
              (H.backwardSurvivorFootprintInterior first i hle K)) ∧
      ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
        G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
          (H.backwardSurvivorFootprintInterior first i hle K) := by
  let Φ := H.backwardSurvivorFootprintLift first i hle K htrace N.chart hinside
  have hsm : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ Φ :=
    H.backwardSurvivorFootprintLift_isSmoothEmbedding first i hle K htrace N.chart hinside N.chart_smooth
  have hΦ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ := fun x =>
    Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq
      (by simp [ThreeSpace, Module.finrank_prod]) (hsm.isImmersion.isImmersionAt x)
  have hmap : H.backwardSurvivorFootprintMap first i hle K ∘ Φ = N.chart := rfl
  obtain ⟨G, hslabs, hlast, hterminal, _, hsol⟩ :=
    H.exists_backwardSurvivorFootprint_isSolutionOn first i hle K
  let D := RealTimeInterval.closed (H.time first) (H.time i.succ)
    (H.time_strictMono.monotone (hle.trans i.castSucc_lt_succ.le))
  let T : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorFootprintInterior first i hle K) D := { base.metric := G }
  let U := T.parabolicClosedWindow (H.time i.succ) N.scale θ N.scale_pos hθ
  have hU : IsSolutionOn U := isSolutionOn_parabolicClosedWindow T hsol N.scale_pos hθ
    (fun t ht => ⟨hstart.trans ht.1, ht.2⟩)
    (fun t ht => ⟨hstart.trans_lt ht.1, ht.2⟩)
  let S := U.localPullback Φ hΦ
  refine ⟨Φ, hΦ, G, S, hmap, hU.localPullback Φ hΦ, ?_, fun _ => rfl, hslabs, hlast⟩
  change localPullMetric (scaleMetric N.scale N.scale_pos
    (G (H.time i.succ + 0 / N.scale))) Φ hΦ = N.normalizedMetric
  rw [zero_div, add_zero, hterminal]
  exact N.pullback_normalizedMetric _ _ Φ hΦ hmap

theorem NormalizedNeck.exists_historical_pullback_solution_with_scalar_bounds
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ k)
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (hinside : range N.chart ⊆ interior K)
    {θ : ℝ} (hθ : 0 ≤ θ) (hstart : H.time first ≤ H.time i.succ - θ / N.scale)
    {q : ℝ} {C : ℝ≥0}
    (hbound : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t x →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi) :
    ∃ (Φ : neckBuffer δ → H.backwardSurvivorFootprintInterior first i hle K)
      (hΦ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Φ)
      (G : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorFootprintInterior first i hle K))
      (S : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
        (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ))),
      H.backwardSurvivorFootprintMap first i hle K ∘ Φ = N.chart ∧
      IsSolutionOn S ∧ S.base.metric 0 = N.normalizedMetric ∧
      (∀ t, S.base.metric t = localPullMetric
        (scaleMetric N.scale N.scale_pos (G (H.time i.succ + t / N.scale))) Φ hΦ) ∧
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
            (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
              (H.backwardSurvivorFootprintInterior first i hle K)) ∧
      (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
        G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
          (H.backwardSurvivorFootprintInterior first i hle K)) ∧
      (∀ s ∈ Ioo (-θ) 0, ∀ x : neckBuffer δ, q / N.scale < S.scalar s x →
        |derivWithin (fun v => S.scalar v x) (Iic s) s| ≤ C * S.scalar s x ^ 2) ∧
      Perelman.PhiAlmostNonnegative S (Icc (-θ) 0)
        (Perelman.rescalePinchingFunction N.scale Phi) := by
  obtain ⟨F,hF,G,S,hmap,hS,hzero,hmetric,hslabs,hlast⟩ :=
    N.exists_historical_pullback_solution K htrace hinside hθ hstart
  refine ⟨F,hF,G,S,hmap,hS,hzero,hmetric,hslabs,hlast,?_,?_⟩
  · intro s hs x hhigh
    exact H.abs_derivWithin_scalar_parabolic_backwardSurvivorFootprint_le first i hle
      K G hslabs hlast F hF S N.scale_pos (fun t _ => hmetric t) hS
      Ioo_subset_Icc_self hstart hbound hs x hhigh
  · exact H.phiAlmostNonnegative_parabolic_backwardSurvivorFootprint_localPullback
      first i hle K G hslabs hlast hPhi hpinch N.scale_pos hstart
      F hF S (fun t _ => hmetric t)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
