import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HistorySurvivorIncomingDerivatives_P6L

/-!
# L6-B 叶子：`curvDerivNorm_historical_localPullback_le_of_backwardPointTrace` 的足迹局部化（`_P6L`）

局部化合同 §2 (D-event)：原 `ST/HistorySurvivorIncomingDerivatives.lean:107` 的 `hbound`（stage 全局）
只整体传给 `HSIC:198`（同一 `K`）；这里改 footprint 形，加 `U`、`hKU : ∀ y ∈ K, y.val ∈ U`，
调 `exists_backwardSurvivorIncomingFootprint_curvature_bound_P6L`。证明体照抄（局部实例一并复制）。
-/

set_option autoImplicit false


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
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first last hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K).isOpen)

variable {E XH M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace XH] {I : ModelWithCorners ℝ E XH}
  [TopologicalSpace M] [ChartedSpace XH M] [IsManifold I ∞ M] [T2Space M]

/-- **`_P6L`**：原 `ObservedHistory.curvDerivNorm_historical_localPullback_le_of_backwardPointTrace`
（`HistorySurvivorIncomingDerivatives:107`）。改动：`hbound` 改 footprint 形，加 `U`、
`hKU : ∀ y ∈ K, y.val ∈ U`（在 `hPhi` 之后）。结论逐字。 -/
theorem curvDerivNorm_historical_localPullback_le_of_backwardPointTrace_P6L
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
    (U : Set (H.stage last).Carrier) (hKU : ∀ y ∈ K, y.val ∈ U)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H first last hle z,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
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
    H.exists_backwardSurvivorIncomingFootprint_curvature_bound_P6L first last hle G L hinit K
      U hKU hq hqQ hPhi hbound hfinal hpinch hpinchFinal hscalar htrace hc hcs htime'
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
