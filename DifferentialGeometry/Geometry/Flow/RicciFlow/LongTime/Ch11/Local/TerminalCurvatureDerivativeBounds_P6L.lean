import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HistorySurvivorIncomingDerivatives_P6L

/-!
# L6-B 叶子：`curvDerivNorm_scaleMetric_terminal_le_on_closedBall_of_backwardPointTrace`（`_P6L`）

局部化合同 §2 (D-event)：原 `ST/TerminalCurvatureDerivativeBounds.lean:21` 的 `hbound`（stage 全局）
只整体传给 `HistorySurvivorIncomingDerivatives:29`（球 `B(y, r/√Q) ⊆ B(x, (a+r)/√Q)`）；这里改
footprint 形，加 `U`、`hKU : ∀ y ∈ B(x, (a+r)/√Q), y.val ∈ U`，调 `…_P6L`。证明体照抄。
-/

set_option autoImplicit false

noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)

/-- **`_P6L`**：原
`ObservedHistory.curvDerivNorm_scaleMetric_terminal_le_on_closedBall_of_backwardPointTrace`
（`TerminalCurvatureDerivativeBounds:21`）。改动：`hbound` 改 footprint 形，加 `U`、
`hKU : ∀ y ∈ B(x, (a+r)/√Q), y.val ∈ U`。结论逐字。 -/
theorem curvDerivNorm_scaleMetric_terminal_le_on_closedBall_of_backwardPointTrace_P6L
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) {a r q Q θ : ℝ} {C : ℝ≥0}
    (ha : 0 ≤ a) (hr : 0 < r) (hq : 0 < q) (hqQ : q ≤ Q) (hQ : 1 ≤ Q) (hθ : 0 < θ)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q)))
    (U : Set (H.stage last).Carrier)
    (hKU : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q), y.val ∈ U)
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
    (hfinal : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi)
    (hscalar : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      metricScalarAt L.metric y ≤ 2 * Q)
    (htrace : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      Nonempty (BackwardPointTrace H first last hle y.val))
    (hc : H.time first ≤ s - θ / Q) (htime : 6 * C * θ ≤ 1) :
    let B := 4 * Real.sqrt 3 * (1 + Phi 4 + Phi 0)
    ∀ y ∈ riemannianClosedBallOf L.metric x (a / Real.sqrt Q),
    ∀ m : ℕ, curvDerivNorm m (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) y ≤
      shiLocalUniformBound 3 m (B * (θ / 4))
        (((r / 2) / (4 * Real.exp (9 * B * θ))) * Real.sqrt B /
          (4 * Real.exp (9 * B * (θ / 4)))) * B / Real.sqrt (θ / 4) ^ m := by
  dsimp only
  intro y hy m
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hsub : riemannianClosedBallOf L.metric y (r / Real.sqrt Q) ⊆
      riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q) :=
    riemannianClosedBallOf_subset_of_add_radius_le L.metric
      (div_nonneg ha (Real.sqrt_nonneg _)) (div_nonneg hr.le (Real.sqrt_nonneg _))
      (by rw [add_div]) hy
  exact H.curvDerivNorm_scaleMetric_terminal_le_of_backwardPointTrace_P6L first last hle G L
    hinit y hr hq hqQ hQ hθ
    (hcompact.of_isClosed_subset
      (Geometry.Metric.isClosed_riemannianClosedBallOf L.metric y _) hsub)
    U (fun z hz => hKU z (hsub hz)) hPhi hbound (fun z hz => hfinal z (hsub hz)) hpinch
    hpinchFinal
    (fun z hz => hscalar z (hsub hz)) (fun z hz => htrace z (hsub hz)) hc htime m

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
