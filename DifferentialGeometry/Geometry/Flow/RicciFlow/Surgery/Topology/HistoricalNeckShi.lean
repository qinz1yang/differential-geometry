import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall

noncomputable section
open Set Bundle Manifold
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}
  {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}

private local instance (K : Set (H.event i).incoming.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorFootprintInterior first i hle K) := by
  let : SigmaCompactSpace (H.backwardSurvivorDomain first i.castSucc hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first i.castSucc hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorTerminalFace first i hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorTerminalFace first i hle).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K).isOpen)

theorem NormalizedNeck.exists_historical_footprint_curvature_derivative_bounds
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
    {c : ℝ} (hc : H.time first ≤ c) (hcs : c < H.time i.succ)
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
          (RealTimeInterval.closed c (H.time i.succ) hcs.le)) ∧
      (∀ t ∈ Icc c (H.time i.succ), ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
        normSq0S (G t) x 4 (metricRm04At (G t) x) ≤ B ^ 2) ∧
      IsCompact (riemannianClosedBallOf (G (H.time i.succ)) p
        (2*a / Real.sqrt N.scale)) ∧
      ∀ m : ℕ, ∀ t ∈ Icc ((c + H.time i.succ) / 2) (H.time i.succ),
        ∀ x ∈ riemannianClosedBallOf (G (H.time i.succ)) p
            ((2*a / Real.sqrt N.scale) / 4),
          curvDerivNorm m (G t) x ≤
            shiLocalUniformBound 3 m (B * ((H.time i.succ - c) / 4))
              (((2*a / Real.sqrt N.scale) /
                (4 * Real.exp (9 * B * (H.time i.succ - c)))) * Real.sqrt B /
                  (4 * Real.exp (9 * B * ((H.time i.succ - c) / 4)))) *
              B / Real.sqrt ((H.time i.succ - c) / 4) ^ m := by
  obtain ⟨p,G,hp,hslabs,hlast,hterminal,hsol,hRm,hcompact,hdistance⟩ :=
    N.exists_historical_footprint_distance_bounds hδ hδ1 hprecision hsmall hk
      a ha hpublic hfit hq hqQ hPhi hbound hpinch htrace hc hcs.le htime
  dsimp only
  let K := N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}
  let B := 4 * Real.sqrt 3 * (N.scale + Phi (4*N.scale) + Phi 0)
  let R := 2*a / Real.sqrt N.scale
  have hB : 0 < B := by
    have hp4 := hPhi.pos (4*N.scale)
    have hp0 := hPhi.pos 0
    dsimp only [B]
    exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num)))
      (by linarith [N.scale_pos])
  have hR : 0 < R := div_pos (by linarith) (Real.sqrt_pos.mpr N.scale_pos)
  let r : ℝ≥0 := ⟨R, hR.le⟩
  have hcpt : IsCompact (riemannianClosedBallOf (G (H.time i.succ)) p R) := by
    have hh := hcompact (H.time i.succ) ⟨hcs.le,le_rfl⟩ r
    have heq : (r : ℝ≥0∞) = ENNReal.ofReal R := (ENNReal.ofReal_coe_nnreal (p := r)).symm
    rw [heq] at hh
    apply hh
    simp only [sub_self, abs_zero, mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    exact le_rfl
  refine ⟨p,G,hp,hslabs,hlast,hterminal,hsol,hRm,hcpt,?_⟩
  let S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K)
      (RealTimeInterval.closed c (H.time i.succ) hcs.le) := { base := { metric := G } }
  have hshi := shi_curvDerivNorm_on_terminal_ball S hsol hcs hB hR
    Subset.rfl Subset.rfl p hcpt (fun t ht x _ => hRm t ht x)
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  simpa only [hdim, Nat.cast_ofNat, show (3 : ℝ)^2 = 9 by norm_num] using hshi

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
