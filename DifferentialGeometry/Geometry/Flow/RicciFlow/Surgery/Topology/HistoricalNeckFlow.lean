import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckCurvature

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
