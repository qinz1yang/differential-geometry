import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorDistance

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}
  {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}

theorem NormalizedNeck.exists_historical_footprint_distance_bounds
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
    let K := N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}
    let B := 4 * Real.sqrt 3 * (N.scale + Phi (4*N.scale) + Phi 0)
    ∃ (p : H.backwardSurvivorFootprintInterior first i hle K)
      (G : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorFootprintInterior first i hle K)),
      H.backwardSurvivorFootprintMap first i hle K p = N.center ∧
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
      (∀ t ∈ Icc c (H.time i.succ), ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
        normSq0S (G t) x 4 (metricRm04At (G t) x) ≤ B ^ 2) ∧
      (∀ t ∈ Icc c (H.time i.succ), ∀ r : ℝ≥0,
        ENNReal.ofReal (Real.exp (9 * Real.sqrt (B ^ 2) * |t - H.time i.succ|)) * r ≤
            ENNReal.ofReal (2*a / Real.sqrt N.scale) →
          IsCompact {x | riemannianEDistOf (G t) p x ≤ r}) ∧
      ∀ t ∈ Icc c (H.time i.succ), ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
        riemannianEDistOf (H.event i).terminal.metric N.center
            (H.backwardSurvivorFootprintMap first i hle K x) <
          ENNReal.ofReal (2*a / Real.sqrt N.scale / 3) →
        ENNReal.ofReal (Real.exp (-(9 * Real.sqrt (B ^ 2) * |t - H.time i.succ|))) *
            riemannianEDistOf (H.event i).terminal.metric N.center
              (H.backwardSurvivorFootprintMap first i hle K x) ≤
            riemannianEDistOf (G t) p x ∧
          riemannianEDistOf (G t) p x ≤
            ENNReal.ofReal (Real.exp (9 * Real.sqrt (B ^ 2) * |t - H.time i.succ|)) *
              riemannianEDistOf (H.event i).terminal.metric N.center
                (H.backwardSurvivorFootprintMap first i hle K x) := by
  obtain ⟨K,hK,hcompact,hconn,hcenter,hchart,hball,hballsub,hrange,
    G,hslabs,hlast,hterminal,hsol,hRm⟩ :=
    N.exists_historical_footprint_isSolutionOn_curvature_bound hδ hδ1 hprecision hsmall hk
      a ha hpublic hfit hq hqQ hPhi hbound hpinch htrace hc hcs htime
  subst K
  dsimp only
  let K := N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}
  have hp : N.center ∈ interior K := by
    apply hballsub
    simp only [riemannianClosedBallOf, mem_ofPred_eq, riemannianEDistOf_self, zero_le]
  let p := H.backwardSurvivorFootprintPoint first i hle K htrace N.center hp
  let S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K)
      (RealTimeInterval.closed c (H.time i.succ) hcs) := { base := { metric := G } }
  let R : ℝ≥0 := ⟨2*a / Real.sqrt N.scale, by
    have := Real.sqrt_pos.mpr N.scale_pos
    positivity⟩
  have hR : 0 < R := by
    change 0 < 2*a / Real.sqrt N.scale
    exact div_pos (by linarith) (Real.sqrt_pos.mpr N.scale_pos)
  have hRcoe : (R : ℝ≥0∞) = ENNReal.ofReal (2*a / Real.sqrt N.scale) := by
    exact (ENNReal.ofReal_coe_nnreal (p := R)).symm
  have hcompactR :
      IsCompact {x | riemannianEDistOf (H.event i).terminal.metric N.center x ≤ R} := by
    simpa only [riemannianClosedBallOf, hRcoe] using hball
  have hballR : {x | riemannianEDistOf (H.event i).terminal.metric N.center x ≤ R} ⊆
      interior K := by
    simpa only [riemannianClosedBallOf, hRcoe] using hballsub
  refine ⟨p,G,rfl,hslabs,hlast,hterminal,hsol,hRm,?_,?_⟩
  · intro t ht r hfitR
    apply H.isCompact_intrinsic_closedBall_backwardSurvivorFootprint first i hle K htrace
      N.center hp hcs S hsol hterminal hRm ht hcompactR hballR
    simpa only [hRcoe] using hfitR
  · intro t ht x hx
    apply H.riemannianEDistOf_exp_bounds_backwardSurvivorFootprint first i hle K htrace
      N.center hp hcs S hsol hterminal hRm ht hR
      (fun y hy => hballR (show riemannianEDistOf (H.event i).terminal.metric N.center y ≤ R
        from le_of_lt hy)) x
    have hd : ((R / 3 : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (2*a / Real.sqrt N.scale / 3) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      rfl
    simpa only [hd] using hx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
