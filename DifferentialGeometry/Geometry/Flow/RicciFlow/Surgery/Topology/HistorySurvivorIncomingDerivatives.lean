import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.LocalPullTerminalBall

noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)

private local instance (K : Set G.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorIncomingFootprint first last hle G K) := by
  let : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorDomain first last hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K).isOpen)

theorem curvDerivNorm_scaleMetric_terminal_le_of_backwardPointTrace
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) {r q Q θ : ℝ} {C : ℝ≥0}
    (hr : 0 < r) (hq : 0 < q) (hqQ : q ≤ Q) (hQ : 1 ≤ Q) (hθ : 0 < θ)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric x (r / Real.sqrt Q)))
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ y ∈ riemannianClosedBallOf L.metric x (r / Real.sqrt Q),
      ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi)
    (hscalar : ∀ y ∈ riemannianClosedBallOf L.metric x (r / Real.sqrt Q),
      metricScalarAt L.metric y ≤ 2 * Q)
    (htrace : ∀ y ∈ riemannianClosedBallOf L.metric x (r / Real.sqrt Q),
      Nonempty (BackwardPointTrace H first last hle y.val))
    (hc : H.time first ≤ s - θ / Q) (htime : 6 * C * θ ≤ 1) :
    let B := 4 * Real.sqrt 3 * (1 + Phi 4 + Phi 0)
    ∀ m : ℕ, curvDerivNorm m (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) x ≤
      shiLocalUniformBound 3 m (B * (θ / 4))
        (((r / 2) / (4 * Real.exp (9 * B * θ))) * Real.sqrt B /
          (4 * Real.exp (9 * B * (θ / 4)))) * B / Real.sqrt (θ / 4) ^ m := by
  let B := 4 * Real.sqrt 3 * (1 + Phi 4 + Phi 0)
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hB : 0 < B := by dsimp only [B]; positivity [hPhi.pos 4, hPhi.pos 0]
  let K := riemannianClosedBallOf L.metric x (r / Real.sqrt Q)
  have hcs : s - θ / Q ≤ s := sub_le_self _ (div_nonneg hθ.le hQpos.le)
  have htime' : 6 * C * (s - (s - θ / Q)) * Q ≤ 1 := by
    have heq : 6 * C * (s - (s - θ / Q)) * Q = 6 * C * θ := by field_simp; ring
    rwa [heq]
  obtain ⟨hrange, gflow, _, _, hterminal, hsol, hRm⟩ :=
    H.exists_backwardSurvivorIncomingFootprint_curvature_bound first last hle G L hinit K
      hq hqQ hPhi hbound hfinal hpinch hpinchFinal hscalar htrace hc hcs htime'
  let S : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingFootprint first last hle G K)
      (RealTimeInterval.closed (s - θ / Q) s hcs) := { base := { metric := gflow } }
  let f := H.backwardSurvivorIncomingFootprintMap first last hle G K
  have hf := H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K
  have hball : riemannianBallOf L.metric x (r / Real.sqrt Q) ⊆ range f := by
    rw [hrange]
    apply interior_maximal
    · intro y hy
      exact (show riemannianEDistOf L.metric x y < ENNReal.ofReal (r / Real.sqrt Q) from hy).le
    · exact isOpen_lt (by unfold riemannianEDistOf; exact Geometry.Riemannian.continuous_riemannianEDist _ x)
        continuous_const
  have hpinchBound : 4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0) ≤ B * Q := by
    have hfour := hPhi.rescale_le hQ 4
    change Q⁻¹ * Phi (Q * 4) ≤ Phi 4 at hfour
    have hfour' := (inv_mul_le_iff₀ hQpos).mp hfour
    have hzero : Phi 0 ≤ Q * Phi 0 := by nlinarith [hPhi.pos 0]
    have hin : Q + Phi (4 * Q) + Phi 0 ≤ Q * (1 + Phi 4 + Phi 0) := by
      rw [mul_comm Q 4] at hfour'
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hin (by positivity : 0 ≤ 4 * Real.sqrt 3)
    dsimp only [B]
    nlinarith
  have hcurv : ∀ t ∈ Icc (s - θ / Q) s,
      ∀ y : H.backwardSurvivorIncomingFootprint first last hle G K,
        f y ∈ K → curvDerivNormSq 0 (S.base.metric t) y ≤ (B * Q) ^ 2 := by
    intro t ht y _
    apply (hRm t ht y).trans
    exact pow_le_pow_left₀ (by positivity [hPhi.pos (4 * Q), hPhi.pos 0]) hpinchBound 2
  have hh := shi_curvDerivNorm_scaleMetric_of_localPullMetric_terminal S hsol L.metric f hf
    (H.backwardSurvivorIncomingFootprintMap_injective first last hle G K)
    hQpos hθ hB hr Subset.rfl Subset.rfl hterminal x hcompact hball hcurv
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  simpa only [hdim, Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] using hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
