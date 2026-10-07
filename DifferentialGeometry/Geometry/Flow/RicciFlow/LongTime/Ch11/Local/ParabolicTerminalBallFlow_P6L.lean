import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ParabolicTerminalBallFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HistorySurvivorIncomingCurvature_P6L

/-!
# L6-B 叶子：`ParabolicTerminalBallFlow:461/561` 的足迹局部化（`_P6L`）

局部化合同 §2 (D-event)：原 `ST/ParabolicTerminalBallFlow.lean:461`
（`exists_parabolically_controlled_incoming_terminal_ball`）与 `:561`
（`exists_uniform_parabolically_controlled_incoming_terminal_ball_radius`）的 `hbound`（stage 全局）
只整体传给 `HSIC:198`（唯一求值点 `HSIC:271`，trace 点）；这里改 footprint 形，加 `U`、
`hKU : ∀ y ∈ B(x, r), y.val ∈ U`，调 `exists_backwardSurvivorIncomingFootprint_curvature_bound_P6L`。
私有引理 `Perelman.exists_uniform_pinching_test_radius`（`:186`）与 footprint 局部实例一并复制。证明体照抄。
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

/-- **`_P6L` 私有副本**：原 private `Perelman.exists_uniform_pinching_test_radius`
（`ParabolicTerminalBallFlow:186`），陈述与证明逐字。 -/
private theorem exists_uniform_pinching_test_radius_P6L {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi) {θ : ℝ} (hθ : 0 < θ) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α ^ 2 ≤ θ ∧
      ∀ Q : ℝ, 1 ≤ Q →
        (α / Real.sqrt Q) ^ 2 ≤ θ / Q ∧
        (α / Real.sqrt Q) ^ 4 * (4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0)) ^ 2 ≤ 1 := by
  let B := 4 * Real.sqrt 3 * (1 + Phi 4 + Phi 0)
  have hB : 0 < B := by dsimp only [B]; positivity [hPhi.pos 4, hPhi.pos 0]
  let α := min 1 (min θ (1 / B))
  have hα : 0 < α := lt_min zero_lt_one (lt_min hθ (one_div_pos.mpr hB))
  have hα1 : α ≤ 1 := min_le_left _ _
  have hαθ : α ≤ θ := (min_le_right _ _).trans (min_le_left _ _)
  have hαB : α ≤ 1 / B := (min_le_right _ _).trans (min_le_right _ _)
  have hαsq : α ^ 2 ≤ α := by nlinarith
  have hαsqB : α ^ 2 * B ≤ 1 :=
    (mul_le_mul_of_nonneg_right hαsq hB.le).trans ((le_div_iff₀ hB).mp hαB)
  refine ⟨α, hα, hα1, hαsq.trans hαθ, ?_⟩
  intro Q hQ
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  have hradsq : (α / Real.sqrt Q) ^ 2 = α ^ 2 / Q := by
    rw [div_pow, Real.sq_sqrt hQpos.le]
  constructor
  · rw [hradsq]
    exact div_le_div_of_nonneg_right (hαsq.trans hαθ) hQpos.le
  have hfour := hPhi.rescale_le hQ 4
  change Q⁻¹ * Phi (Q * 4) ≤ Phi 4 at hfour
  have hfour' := (inv_mul_le_iff₀ hQpos).mp hfour
  have hzero : Phi 0 ≤ Q * Phi 0 := by nlinarith [hPhi.pos 0]
  have hin : Q + Phi (4 * Q) + Phi 0 ≤ Q * (1 + Phi 4 + Phi 0) := by
    rw [mul_comm Q 4] at hfour'
    nlinarith
  have hbound : 4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0) ≤ B * Q := by
    have hh := mul_le_mul_of_nonneg_left hin (by positivity : 0 ≤ 4 * Real.sqrt 3)
    dsimp only [B]
    nlinarith
  have hcurv : 0 ≤ 4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0) := by
    positivity [hPhi.pos (4 * Q), hPhi.pos 0]
  have hb2 := pow_le_pow_left₀ hcurv hbound 2
  have heq : (α / Real.sqrt Q) ^ 4 * (B * Q) ^ 2 = (α ^ 2 * B) ^ 2 := by
    have hs := Real.sq_sqrt hQpos.le
    field_simp
    nlinarith [sq_nonneg (Real.sqrt Q)]
  calc
    (α / Real.sqrt Q) ^ 4 * (4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0)) ^ 2
      ≤ (α / Real.sqrt Q) ^ 4 * (B * Q) ^ 2 := mul_le_mul_of_nonneg_left hb2 (by positivity)
    _ = (α ^ 2 * B) ^ 2 := heq
    _ ≤ 1 := by nlinarith [mul_nonneg (sq_nonneg α) hB.le]

end DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)

private local instance : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
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

/-- **`_P6L`**：原 `ObservedHistory.exists_parabolically_controlled_incoming_terminal_ball`
（`ParabolicTerminalBallFlow:461`）。改动：`hbound` 改 footprint 形，加 `U`、`hKU`。结论逐字。 -/
theorem exists_parabolically_controlled_incoming_terminal_ball_P6L
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric x r))
    (U : Set (H.stage last).Carrier)
    (hKU : ∀ y ∈ riemannianClosedBallOf L.metric x r, y.val ∈ U)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H first last hle z,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ y ∈ riemannianClosedBallOf L.metric x r, ∀ t ∈ Ioo (H.time last) s,
      q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi)
    (hscalar : ∀ y ∈ riemannianClosedBallOf L.metric x r, metricScalarAt L.metric y ≤ 2 * Q)
    (htrace : ∀ y ∈ riemannianClosedBallOf L.metric x r,
      Nonempty (BackwardPointTrace H first last hle y.val))
    {c : ℝ} (hc : H.time first ≤ c) (hcs : c ≤ s)
    (htime : 6 * C * (s - c) * Q ≤ 1)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hwindow : ρ ^ 2 ≤ s - c)
    (hscale : ρ ^ 4 * (4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0)) ^ 2 ≤ 1) :
    let K := riemannianClosedBallOf L.metric x r
    ∃ (p : H.backwardSurvivorIncomingFootprint first last hle G K)
      (S : SolutionOn (I := ThreeModel)
        (M := H.backwardSurvivorIncomingFootprint first last hle G K)
        (RealTimeInterval.closed c s hcs)),
      H.backwardSurvivorIncomingFootprintMap first last hle G K p = x ∧
      range (H.backwardSurvivorIncomingFootprintMap first last hle G K) = interior K ∧
      IsSolutionOn S ∧
      S.base.metric s = localPullMetric L.metric
        (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          S.base.metric t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
              (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      (∀ t ∈ Icc (H.time last) s,
        S.base.metric t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      ∃ B : Perelman.FlowMetricBall S ⟨s, hcs, le_rfl⟩,
        B.center = p ∧ B.radius = ρ ∧ B.IsParabolicallyRmControlled ∧
        B.set = riemannianBallOf (S.base.metric s) p ρ ∧
        H.backwardSurvivorIncomingFootprintMap first last hle G K '' B.set =
          riemannianBallOf L.metric x ρ ∧
        B.volume = riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
          (riemannianBallOf L.metric x ρ) ∧
        IsCompact (riemannianClosedBallOf (S.base.metric s) p ρ) := by
  intro K
  obtain ⟨hrange, gflow, hslabs, hlast, hterminal, hsol, hRm⟩ :=
    H.exists_backwardSurvivorIncomingFootprint_curvature_bound_P6L first last hle G L hinit K
      U hKU hq hqQ hPhi hbound hfinal hpinch hpinchFinal hscalar htrace hc hcs htime
  obtain ⟨p, hp, hcompact'⟩ := H.exists_incomingFootprint_point_isCompact_terminal_closedBall
    first last hle G L x hr hcompact hrange (gflow s) hterminal
  let S : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingFootprint first last hle G K)
      (RealTimeInterval.closed c s hcs) := { base := { metric := gflow } }
  let B : Perelman.FlowMetricBall S ⟨s, hcs, le_rfl⟩ := ⟨p, ρ, hρ⟩
  have hinterval : Icc (s - ρ ^ 2) s ⊆ Icc c s := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have htest : B.IsParabolicallyRmControlled := by
    refine ⟨hinterval, ?_⟩
    intro t ht z hz
    exact (mul_le_mul_of_nonneg_left (hRm t (hinterval ht) z) (by positivity)).trans hscale
  have hmid : ρ < (ρ + r) / 2 := by linarith
  have hmidr : (ρ + r) / 2 < r := by linarith
  have hcompactmid : IsCompact (riemannianClosedBallOf
      (localPullMetric L.metric (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K)) p
        ((ρ + r) / 2)) :=
    hterminal ▸ hcompact' ((ρ + r) / 2) hmidr
  have himage : H.backwardSurvivorIncomingFootprintMap first last hle G K '' B.set =
      riemannianBallOf L.metric x ρ := by
    change _ '' riemannianBallOf (gflow s) p ρ = _
    rw [hterminal]
    have h := Geometry.Metric.image_riemannianBallOf_localPullMetric L.metric
      (H.backwardSurvivorIncomingFootprintMap first last hle G K)
      (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K)
      (H.backwardSurvivorIncomingFootprintMap_injective first last hle G K)
      p hρ hmid hcompactmid
    exact h.trans (congrArg (fun y => riemannianBallOf L.metric y ρ) hp)
  have hvolume : B.volume = riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
      (riemannianBallOf L.metric x ρ) := by
    rw [Perelman.FlowMetricBall.volume_eq_riemannianVolumeMeasure]
    change riemannianVolumeMeasure _ _ (gflow s) (riemannianBallOf (gflow s) p ρ) = _
    rw [hterminal]
    have h := Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_localPullMetric L.metric
      (H.backwardSurvivorIncomingFootprintMap first last hle G K)
      (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K)
      (H.backwardSurvivorIncomingFootprintMap_injective first last hle G K)
      p hρ hmid hcompactmid
    exact h.trans (congrArg (fun y =>
      riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
      (riemannianBallOf L.metric y ρ)) hp)
  exact ⟨p, S, hp, hrange, hsol, hterminal, hslabs, hlast,
    B, rfl, rfl, htest, rfl, himage, hvolume, hcompact' ρ hρr⟩


/-- **`_P6L`**：原
`ObservedHistory.exists_uniform_parabolically_controlled_incoming_terminal_ball_radius`
（`ParabolicTerminalBallFlow:561`）。改动：在 `IsCompact …` 之后加 `∀ U, (B(x, r) ⊆ U) →`，
`hbound` 改 footprint 形。常数 `α` 仍在历史之前取。结论逐字。 -/
theorem exists_uniform_parabolically_controlled_incoming_terminal_ball_radius_P6L
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α ^ 2 ≤ θ ∧
    ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
      {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
      (x : G.terminalRegularOpen) {r q Q : ℝ} {C : ℝ≥0} (hQ : 1 ≤ Q),
    G.flow.base.metric (H.time last) = H.initialMetric last →
    0 < r → IsCompact (riemannianClosedBallOf L.metric x r) →
    ∀ U : Set (H.stage last).Carrier, (∀ y ∈ riemannianClosedBallOf L.metric x r, y.val ∈ U) →
    0 < q → q ≤ Q →
    (∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H first last hle z,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2) →
    (∀ y ∈ riemannianClosedBallOf L.metric x r, ∀ t ∈ Ioo (H.time last) s,
      q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2) →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi) →
    (Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi) →
    (∀ y ∈ riemannianClosedBallOf L.metric x r, metricScalarAt L.metric y ≤ 2 * Q) →
    (∀ y ∈ riemannianClosedBallOf L.metric x r,
      Nonempty (BackwardPointTrace H first last hle y.val)) →
    H.time first ≤ s - θ / Q →
    6 * C * θ ≤ 1 →
    α / Real.sqrt Q < r →
    let K := riemannianClosedBallOf L.metric x r
    ∃ (p : H.backwardSurvivorIncomingFootprint first last hle G K)
      (S : SolutionOn (I := ThreeModel)
        (M := H.backwardSurvivorIncomingFootprint first last hle G K)
        (RealTimeInterval.closed (s - θ / Q) s
          (sub_le_self s (div_nonneg hθ.le (zero_le_one.trans hQ))))),
      H.backwardSurvivorIncomingFootprintMap first last hle G K p = x ∧
      range (H.backwardSurvivorIncomingFootprintMap first last hle G K) = interior K ∧
      IsSolutionOn S ∧
      S.base.metric s = localPullMetric L.metric
        (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          S.base.metric t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
              (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      (∀ t ∈ Icc (H.time last) s,
        S.base.metric t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      ∃ B : Perelman.FlowMetricBall S
          ⟨s, sub_le_self s (div_nonneg hθ.le (zero_le_one.trans hQ)), le_rfl⟩,
        B.center = p ∧ B.radius = α / Real.sqrt Q ∧ B.IsParabolicallyRmControlled ∧
        B.set = riemannianBallOf (S.base.metric s) p (α / Real.sqrt Q) ∧
        H.backwardSurvivorIncomingFootprintMap first last hle G K '' B.set =
          riemannianBallOf L.metric x (α / Real.sqrt Q) ∧
        B.volume = riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
          (riemannianBallOf L.metric x (α / Real.sqrt Q)) ∧
        IsCompact (riemannianClosedBallOf (S.base.metric s) p (α / Real.sqrt Q)) := by
  obtain ⟨α, hα, hα1, hαθ, hchoice⟩ := Perelman.exists_uniform_pinching_test_radius_P6L hPhi hθ
  refine ⟨α, hα, hα1, hαθ, ?_⟩
  intro H first last hle s G L x r q Q C hQ hinit hr hcompact U hKU hq hqQ
    hbound hfinal hpinch hpinchFinal hscalar htrace hc htime hradius
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hrho : 0 < α / Real.sqrt Q := div_pos hα (Real.sqrt_pos.mpr hQpos)
  have hcs : s - θ / Q ≤ s := sub_le_self s (div_nonneg hθ.le hQpos.le)
  have htime' : 6 * C * (s - (s - θ / Q)) * Q ≤ 1 := by
    have heq : 6 * C * (s - (s - θ / Q)) * Q = 6 * C * θ := by field_simp; ring
    rwa [heq]
  have hwindow : (α / Real.sqrt Q) ^ 2 ≤ s - (s - θ / Q) := by
    simpa only [sub_sub_cancel] using (hchoice Q hQ).1
  exact H.exists_parabolically_controlled_incoming_terminal_ball_P6L first last hle G L hinit x hr
    hcompact U hKU hq hqQ hPhi hbound hfinal hpinch hpinchFinal hscalar htrace hc hcs htime' hrho
    hradius
    hwindow (hchoice Q hQ).2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
