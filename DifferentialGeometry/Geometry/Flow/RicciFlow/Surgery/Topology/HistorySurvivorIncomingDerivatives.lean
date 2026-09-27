import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.LocalPullTerminalBall
import DifferentialGeometry.Geometry.Metric.PullbackScaling

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

variable {E XH M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH}
  [TopologicalSpace M] [ChartedSpace XH M] [IsManifold I ∞ M] [T2Space M]

theorem curvDerivNorm_historical_localPullback_le_of_backwardPointTrace
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (K : Set G.terminalRegularOpen)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K))
    (hlast : ∀ t ∈ Icc (H.time last) s,
      gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
        (H.backwardSurvivorIncomingFootprint first last hle G K))
    (Ψ : M → H.backwardSurvivorIncomingFootprint first last hle G K)
    (hΨ : IsLocalDiffeomorph I ThreeModel ∞ Ψ)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {r q Q θ A : ℝ} {C : ℝ≥0}
    (hr : 0 < r) (hq : 0 < q) (hqQ : q ≤ A * Q) (hQ : 1 ≤ Q) (hA : 1 ≤ A) (hθ : 0 < θ)
    (hmetric : ∀ t ∈ Icc (-(θ / 2)) 0, S.base.metric t =
      localPullMetric (scaleMetric Q (zero_lt_one.trans_le hQ) (gflow (s + t / Q))) Ψ hΨ)
    (z : M)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric
      (H.backwardSurvivorIncomingFootprintMap first last hle G K (Ψ z)) (r / Real.sqrt Q)))
    (hball : riemannianBallOf L.metric
      (H.backwardSurvivorIncomingFootprintMap first last hle G K (Ψ z)) (r / Real.sqrt Q) ⊆ interior K)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ y ∈ K,
      ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi)
    (hscalar : ∀ y ∈ K,
      metricScalarAt L.metric y ≤ 2 * (A * Q))
    (htrace : ∀ y ∈ K,
      Nonempty (BackwardPointTrace H first last hle y.val))
    (hc : H.time first ≤ s - θ / Q) (htime : 6 * C * θ * A ≤ 1) :
    let B := 4 * Real.sqrt 3 * A * (1 + Phi 4 + Phi 0)
    ∀ m : ℕ, ∀ t ∈ Icc (-(θ / 2)) 0, curvDerivNorm m (S.base.metric t) z ≤
      shiLocalUniformBound 3 m (B * (θ / 4))
        (((r / 2) / (4 * Real.exp (9 * B * θ))) * Real.sqrt B /
          (4 * Real.exp (9 * B * (θ / 4)))) * B / Real.sqrt (θ / 4) ^ m := by
  let B := 4 * Real.sqrt 3 * A * (1 + Phi 4 + Phi 0)
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hAQ : 1 ≤ A * Q := by nlinarith
  have hAQpos : 0 < A * Q := mul_pos hApos hQpos
  have hB : 0 < B := by dsimp only [B]; positivity [hPhi.pos 4, hPhi.pos 0]
  have hcs : s - θ / Q ≤ s := sub_le_self _ (div_nonneg hθ.le hQpos.le)
  have htime' : 6 * C * (s - (s - θ / Q)) * (A * Q) ≤ 1 := by
    have heq : 6 * C * (s - (s - θ / Q)) * (A * Q) = 6 * C * θ * A := by field_simp; ring
    rwa [heq]
  obtain ⟨hrange, gBound, hBoundSlabs, hBoundLast, hterminal, hsol, hRm⟩ :=
    H.exists_backwardSurvivorIncomingFootprint_curvature_bound first last hle G L hinit K
      hq hqQ hPhi hbound hfinal hpinch hpinchFinal hscalar htrace hc hcs htime'
  let T : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingFootprint first last hle G K)
      (RealTimeInterval.closed (s - θ / Q) s hcs) := { base := { metric := gBound } }
  let f := H.backwardSurvivorIncomingFootprintMap first last hle G K
  have hf := H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K
  have hrangeball : riemannianBallOf L.metric (f (Ψ z)) (r / Real.sqrt Q) ⊆ range f := by
    rw [hrange]
    exact hball
  have hpinchBound : 4 * Real.sqrt 3 * (A * Q + Phi (4 * (A * Q)) + Phi 0) ≤ B * Q := by
    have hfour := hPhi.rescale_le hAQ 4
    change (A * Q)⁻¹ * Phi ((A * Q) * 4) ≤ Phi 4 at hfour
    have hfour' := (inv_mul_le_iff₀ hAQpos).mp hfour
    have hzero : Phi 0 ≤ (A * Q) * Phi 0 := by nlinarith [hPhi.pos 0]
    have hin : A * Q + Phi (4 * (A * Q)) + Phi 0 ≤ (A * Q) * (1 + Phi 4 + Phi 0) := by
      rw [mul_comm (A * Q) 4] at hfour'
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hin (by positivity : 0 ≤ 4 * Real.sqrt 3)
    dsimp only [B]
    nlinarith
  have hcurv : ∀ t ∈ Icc (s - θ / Q) s,
      ∀ y : H.backwardSurvivorIncomingFootprint first last hle G K,
        f y ∈ riemannianClosedBallOf L.metric (f (Ψ z)) (r / Real.sqrt Q) → curvDerivNormSq 0 (T.base.metric t) y ≤ (B * Q) ^ 2 := by
    intro t ht y _
    apply (hRm t ht y).trans
    exact pow_le_pow_left₀ (by positivity [hPhi.pos (4 * (A * Q)), hPhi.pos 0]) hpinchBound 2
  have hshi := shi_curvDerivNorm_scaleMetric_of_localPullMetric_on_time_window T hsol L.metric f hf
    (H.backwardSurvivorIncomingFootprintMap_injective first last hle G K)
    hQpos hθ hB hr Subset.rfl Subset.rfl hterminal (Ψ z) hcompact hrangeball hcurv
  dsimp only
  intro m t ht
  have hclock : s + t / Q ∈ Icc (H.time first) s := by
    have hlo := div_le_div_of_nonneg_right ht.1 hQpos.le
    have hhi := div_le_div_of_nonneg_right ht.2 hQpos.le
    simp only [neg_div, zero_div] at hlo hhi
    constructor
    · have hhalf : θ / 2 / Q ≤ θ / Q :=
        div_le_div_of_nonneg_right (by linarith : θ / 2 ≤ θ) hQpos.le
      linarith
    · linarith
  have hpull := H.localPullMetric_backwardSurvivorIncomingFootprint_eq
    (first := first) (last := last) (hle := hle) (G := G) (L := L)
    K K gflow gBound hslabs hBoundSlabs hlast hBoundLast Ψ Ψ hΨ hΨ rfl hclock
  rw [hmetric t ht, localPullMetric_scaleMetric, hpull,
    ← localPullMetric_scaleMetric, curvDerivNorm_localPullMetric]
  have hh := hshi m t ht
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  simpa only [hdim, Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] using hh


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
