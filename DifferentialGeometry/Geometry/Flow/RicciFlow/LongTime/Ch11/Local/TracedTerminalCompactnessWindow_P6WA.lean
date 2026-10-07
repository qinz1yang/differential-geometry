import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedTerminalCompactness_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TerminalCurvatureDerivativeBoundsWindow_P6WA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BackwardTraceChainCaptureLateRecords_P6N

/-!
# L6-B 第 1 层窗口版：`TracedTerminalCompactness:54p/149/226`（`_P6WA`）

P6WIN 接口约定（`state-O-CH11-P6CON.md` 02:3x）：
* 私有 `TTC:54p`：窗口起点即 `s - θ / Q`（guard `s - θ / Q ≤ t`，pinching `Ici (s - θ / Q)`），调
  `TCDB:27` 窗口版；
* 序列层 `TTC:149/226`：加 `(a : ℕ → ℝ)`（窗口起点）紧随 `U`，`hderiv` / `hfinal` guard `a n ≤ t →`，
  pinching 取 `Ico … ∩ Ici (a n)`；`hbuffer` 的 `θ` 是存在量，故加 `hQa : Tendsto (Q n * (s n - a n))`
  （坑 F5：给 `∀ᶠ n, a n ≤ s n - θ / Q n`），内部 `phiAlmostNonnegative_mono_P6N` 降到 `s - θ / Q`。
结论逐字，证明体照抄 `_P6L`。consumer：`_P6L`（无 guard）由窗口版推回（取 `a n = s n - (n + 1) / Q n`）。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

noncomputable section
open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- **`_window_P6WA` 私有副本**：`_P6L` 的时间窗版；原 private
`exists_normalized_curvature_derivative_bounds_of_buffered_backward_traces`
（`TracedTerminalCompactness:30`）。改动：窗口 guard `s - θ / Q ≤ t`，pinching 取
`Ici (s - θ / Q)`。常数 `B` 仍在历史之前取。 -/
private theorem
    exists_normalized_curvature_derivative_bounds_of_buffered_backward_traces_window_P6WA
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    {a r A θ : ℝ} {C : ℝ≥0} (ha : 0 ≤ a) (hr : 0 < r) (hA : 1 ≤ A)
    (hθ : 0 < θ) (htime : 6 * C * (A * θ) ≤ 1) :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
    ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
      {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
    G.flow.base.metric (H.time last) = H.initialMetric last →
    ∀ (x : G.terminalRegularOpen) {q Q : ℝ}, 0 < q → q ≤ Q → ∀ hQ : 1 ≤ Q,
    IsCompact
      (riemannianClosedBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) x (a + r)) →
    ∀ U : Set (H.stage last).Carrier,
    (∀ y ∈ riemannianClosedBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) x (a + r),
      y.val ∈ U) →
    (∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H first last hle z,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ), s - θ / Q ≤ t →
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2) →
    (∀ y ∈ U, ∀ t ∈ Ioo (H.time last) s, s - θ / Q ≤ t → q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (s - θ / Q)) Phi) →
    Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s ∩ Ici (s - θ / Q)) Phi →
    (∀ y ∈ riemannianClosedBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) x (a + r),
      metricScalarAt L.metric y ≤ 2 * (A * Q)) →
    (∀ y ∈ riemannianClosedBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) x (a + r),
      Nonempty (BackwardPointTrace H first last hle y.val)) →
    H.time first ≤ s - θ / Q →
    ∀ m : ℕ, ∀ y ∈ riemannianClosedBallOf (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) x a,
      curvDerivNorm m (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) y ≤ B m := by
  let K := 4 * Real.sqrt 3 * (1 + Phi 4 + Phi 0)
  let B := fun m => (shiLocalUniformBound 3 m (K * (A * θ / 4))
    (((r * Real.sqrt A / 2) / (4 * Real.exp (9 * K * (A * θ)))) * Real.sqrt K /
      (4 * Real.exp (9 * K * (A * θ / 4)))) * K / Real.sqrt (A * θ / 4) ^ m) *
        (A * Real.sqrt A ^ m)
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hK : 0 < K := by dsimp only [K]; positivity [hPhi.pos 4, hPhi.pos 0]
  refine ⟨B, ?_, ?_⟩
  · intro m
    exact mul_nonneg (div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK.le)
      (by positivity)) (by positivity)
  intro H first last hle s G L hinit x q Q hq hqQ hQ hcompact U hKU hderiv hfinal hpinch hpinchFinal
    hscalar htrace hstart m y hy
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hAQ : 1 ≤ A * Q := hQ.trans (le_mul_of_one_le_left hQp.le hA)
  have hqAQ : q ≤ A * Q := hqQ.trans (le_mul_of_one_le_left hQp.le hA)
  have hradius (b : ℝ) : b * Real.sqrt A / Real.sqrt (A * Q) = b / Real.sqrt Q := by
    rw [Real.sqrt_mul hAp.le]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hAp)]
  have hball (b : ℝ) : riemannianClosedBallOf (scaleMetric Q hQp L.metric) x b =
      riemannianClosedBallOf L.metric x (b / Real.sqrt Q) := by
    conv_lhs => rw [show b = Real.sqrt Q * (b / Real.sqrt Q) by field_simp]
    exact riemannianClosedBallOf_scaleMetric Q hQp L.metric x _
  have houter :
      (a * Real.sqrt A + r * Real.sqrt A) / Real.sqrt (A * Q) = (a + r) / Real.sqrt Q := by
    rw [← add_mul, hradius]
  have ht : A * θ / (A * Q) = θ / Q := by field_simp
  have hKUL : ∀ y ∈ riemannianClosedBallOf L.metric x
      ((a * Real.sqrt A + r * Real.sqrt A) / Real.sqrt (A * Q)), y.val ∈ U := by
    rw [houter, ← hball]; exact hKU
  have hbound :=
    H.curvDerivNorm_scaleMetric_terminal_le_on_closedBall_of_backwardPointTrace_window_P6WA
    first last hle G L hinit x (mul_nonneg ha (Real.sqrt_nonneg _))
    (mul_pos hr (Real.sqrt_pos.mpr hAp)) hq hqAQ hAQ (mul_pos hAp hθ)
    (by rw [houter, ← hball]; exact hcompact) U hKUL hPhi
    (fun j hf hl z hz A' t ht' hct => hderiv j hf hl z hz A' t ht' (by rw [ht] at hct; exact hct))
    (fun y hy t ht' hct => hfinal y.val (hKUL y hy) t ht' (by rw [ht] at hct; exact hct))
    (fun j hf hl => by rw [ht]; exact hpinch j hf hl) (by rw [ht]; exact hpinchFinal)
    (by simpa only [houter, ← hball] using hscalar)
    (by simpa only [houter, ← hball] using htrace) (by simpa only [ht] using hstart) htime y
      (by rw [hradius, ← hball]; exact hy) m
  have hmetric : scaleMetric (A * Q) (zero_lt_one.trans_le hAQ) L.metric =
      scaleMetric A hAp (scaleMetric Q hQp L.metric) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    simp only [scaleMetric_inner]
    ring
  rw [hmetric, curvDerivNorm_scaleMetric] at hbound
  exact (div_le_iff₀ (by positivity : 0 < A * Real.sqrt A ^ m)).mp hbound

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

/-- **`_window_P6WA`**：`_P6L` 的时间窗版；原
`exists_terminal_normalized_inner_ball_curvature_derivative_bounds_of_backward_traces`
（`TracedTerminalCompactness:110`）。改动：加 `a`、`hQa`；guard `a n ≤ t`，pinching 取
`Ici (a n)`。结论逐字。 -/
theorem
    exists_terminal_normalized_inner_ball_curvature_derivative_bounds_of_backward_traces_window_P6WA
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → ObservedHistory.{u})
    (last : ∀ n, Fin ((H n).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (last n)).IncomingSlab ((H n).time (last n)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (last n)) = (H n).initialMetric (last n))
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (U : ∀ n, Set ((H n).stage (last n)).Carrier) (a : ℕ → ℝ)
    (hQa : Tendsto (fun n => Q n * (s n - a n)) atTop atTop)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ last n),
      ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last n,
      ∀ z ∈ U n, ∀ A : BackwardPointTrace (H n) first (last n) hle z,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ), a n ≤ t →
      q n < ((H n).event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => ((H n).event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * ((H n).event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ n, ∀ y ∈ U n,
      ∀ t ∈ Ioo ((H n).time (last n)) (s n), a n ≤ t → q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      Perelman.PhiAlmostNonnegative ((H n).event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (a n)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (last n)) (s n) ∩ Ici (a n)) Phi)
    {rho : ℝ}
    (hU : ∀ n, ∀ y ∈ riemannianBallOf
      (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) rho, y.val ∈ U n)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ last n),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n) first (last n) hle y.val)) ∧
          (H n).time first ≤ s n - θ / Q n) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } }
    ∀ R : ℝ, 0 < R → R < rho → ∀ p : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint R p B := by
  dsimp only
  intro R hR hRrho p
  obtain ⟨r, A, θ, hr, hRr, hA, hθ, htime, hbuf⟩ := hbuffer R hR hRrho
  obtain ⟨B, hB, hbound⟩ :=
    exists_normalized_curvature_derivative_bounds_of_buffered_backward_traces_window_P6WA
    Phi hPhi hR.le hr hA hθ htime
  refine ⟨B p, hB p, ?_⟩
  filter_upwards [hbuf, hQa.eventually_ge_atTop θ] with n hn hθn
  intro y hy
  obtain ⟨first, hle, htrace, hstart⟩ := hn.2.2
  have hwn : a n ≤ s n - θ / Q n := by
    have hQn : 0 < Q n := zero_lt_one.trans_le (hQ n)
    have h1 : θ / Q n ≤ s n - a n := (div_le_iff₀ hQn).mpr (by linarith)
    linarith
  have hsub : Ici (s n - θ / Q n) ⊆ Ici (a n) := Ici_subset_Ici.mpr hwn
  exact hbound (H n) first (last n) hle (G n) (L n) (hinit n) (x n)
    (hq n) (hqQ n) (hQ n) hn.1 (U n)
    (fun y hy => hU n y
      (riemannianClosedBallOf_subset_riemannianBallOf_P6L _ _ hRr (hR.trans hRrho) hy))
    (fun j hf hl z hz A t ht hct => hderiv n j first hle hf hl z hz A t ht (hwn.trans hct))
    (fun y hy t ht hct => hfinal n y hy t ht (hwn.trans hct))
    (fun j _ hj => RetainedCoreHistory.phiAlmostNonnegative_mono_P6N (hpinch n j hj)
      (inter_subset_inter_right _ hsub))
    (RetainedCoreHistory.phiAlmostNonnegative_mono_P6N (hpinchFinal n)
      (inter_subset_inter_right _ hsub)) hn.2.1
    htrace hstart p y hy


/-- **`_window_P6WA`**：`_P6L`（合同 §3 行 9，接口）的时间窗版；原
`ObservedHistory.exists_terminal_pointed_convergence_of_buffered_backward_traces`
（`TracedTerminalCompactness:170`）。改动：`U` 后加 `a`、`hQa`；`hderiv` / `hfinal` guard `a n ≤ t`，
pinching 取 `Ici (a n)`。`hvol` 不变。结论逐字。 -/
theorem exists_terminal_pointed_convergence_of_buffered_backward_traces_window_P6WA
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → ObservedHistory.{u})
    (last : ∀ n, Fin ((H n).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (last n)).IncomingSlab ((H n).time (last n)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (last n)) = (H n).initialMetric (last n))
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (U : ∀ n, Set ((H n).stage (last n)).Carrier) (a : ℕ → ℝ)
    (hQa : Tendsto (fun n => Q n * (s n - a n)) atTop atTop)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ last n),
      ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last n,
      ∀ z ∈ U n, ∀ A : BackwardPointTrace (H n) first (last n) hle z,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ), a n ≤ t →
      q n < ((H n).event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => ((H n).event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * ((H n).event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ n, ∀ y ∈ U n,
      ∀ t ∈ Ioo ((H n).time (last n)) (s n), a n ≤ t → q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      Perelman.PhiAlmostNonnegative ((H n).event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ) ∩ Ici (a n)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (last n)) (s n) ∩ Ici (a n)) Phi)
    {rho : ℝ} (hrho : 0 < rho)
    (hU : ∀ n, ∀ y ∈ riemannianBallOf
      (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) rho, y.val ∈ U n)
    (hbuffer : ∀ R : ℝ, 0 < R → R < rho → ∃ r A θ : ℝ,
      0 < r ∧ R + r < rho ∧ 1 ≤ A ∧ 0 < θ ∧ 6 * C * (A * θ) ≤ 1 ∧
      ∀ᶠ n in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r)) ∧
        (∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
          metricScalarAt (L n).metric y ≤ 2 * (A * Q n)) ∧
        ∃ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ last n),
          (∀ y ∈ riemannianClosedBallOf
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) (R + r),
            Nonempty (BackwardPointTrace (H n) first (last n) hle y.val)) ∧
          (H n).time first ≤ s n - θ / Q n)
    (hvol : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) (x n) r,
        ENNReal.ofReal (κ * a ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel (G n).terminalRegularOpen
            (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric)
            (riemannianBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric) y a)) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } }
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (F : PointedRiemannianConvergenceMaps X.connectedComponent P f),
        let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint
        let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
        let F' := F.liftTargetOpen U hp
        ∃ M : MetricConvergenceData F',
        (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
        (∀ z : P.M, riemannianEDistOf P.metric P.basepoint z < ENNReal.ofReal rho) ∧
        (∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf P.metric P.basepoint R)) ∧
        (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆
          F'.target n) ∧
        ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ z ∈ F'.source n, ∀ v : TangentSpace ThreeModel z,
          (1 - eps) * P.metric.inner z v v ≤
            (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) ∧
          (X.obj (f n)).metric.inner (F'.map n z)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v)
              (mfderiv ThreeModel ThreeModel (F'.map n) z v) ≤
            (1 + eps) * P.metric.inner z v v := by
  dsimp only
  let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (L n).metric } }
  have hcompact : ∀ R : ℝ, 0 < R → R < rho → ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint R) := by
    intro R hR hRrho
    obtain ⟨r, A, θ, hr, _, _, _, _, hbuf⟩ := hbuffer R hR hRrho
    filter_upwards [hbuf] with n hn
    exact hn.1.of_isClosed_subset
      (isClosed_le
        (Geometry.Riemannian.continuous_riemannianEDist (X.obj n).metric (X.obj n).basepoint)
        continuous_const) (riemannianClosedBallOf_mono _ _ (by linarith))
  have hjets :=
    exists_terminal_normalized_inner_ball_curvature_derivative_bounds_of_backward_traces_window_P6WA
    Phi hPhi H last s G L hinit x q Q hq hqQ hQ U a hQa hderiv hfinal hpinch hpinchFinal hU hbuffer
  have hvolX : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ ThreeSpace) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric y a) := by
    simpa only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin] using hvol
  exact exists_pointed_convergence_with_uniform_metric_bounds_on_base_components
    X hrho hcompact hjets hvolX

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- 窗口起点的存在性（consumer 用）：任意 `Q n > 0`、`s n` 都有 `a n < s n` 使
`Q n * (s n - a n) → ∞`（取 `a n = s n - (n + 1) / Q n`）。 -/
theorem exists_window_start_P6WA (s Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n) :
    ∃ a : ℕ → ℝ, (∀ n, a n < s n) ∧ Tendsto (fun n => Q n * (s n - a n)) atTop atTop := by
  refine ⟨fun n => s n - ((n : ℝ) + 1) / Q n, fun n => ?_, ?_⟩
  · have : 0 < ((n : ℝ) + 1) / Q n := div_pos (by positivity) (hQ n)
    linarith
  · have heq : (fun n : ℕ => Q n * (s n - (s n - ((n : ℝ) + 1) / Q n))) =
        fun n : ℕ => (n : ℝ) + 1 := by
      funext n
      have := (hQ n).ne'
      field_simp
      ring
    rw [heq]
    exact tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))

universe u in
open ObservedHistory in
/-- consumer：`_P6L`（`TTC:110`）由窗口版推回（取 `a n = s n - (n + 1) / Q n`）。 -/
example : type_of%
    @exists_terminal_normalized_inner_ball_curvature_derivative_bounds_of_backward_traces_P6L.{u}
    := by
  intro Phi hPhi C H last s G L hinit x q Q hq hqQ hQ U hderiv hfinal hpinch hpinchFinal rho hU
    hbuffer
  obtain ⟨a, -, hQa⟩ := exists_window_start_P6WA s Q (fun n => zero_lt_one.trans_le (hQ n))
  exact
    exists_terminal_normalized_inner_ball_curvature_derivative_bounds_of_backward_traces_window_P6WA
    Phi hPhi H last s G L hinit x q Q hq hqQ hQ U a hQa
    (fun n j first hle hf hl z hz A t ht _ => hderiv n j first hle hf hl z hz A t ht)
    (fun n y hy t ht _ => hfinal n y hy t ht) (fun n j hj t ht x => hpinch n j hj t ht.1 x)
    (fun n t ht x => hpinchFinal n t ht.1 x) hU hbuffer

universe u in
open ObservedHistory in
/-- consumer：`_P6L`（`TTC:170`）由窗口版推回。 -/
example : type_of%
    @exists_terminal_pointed_convergence_of_buffered_backward_traces_P6L.{u} := by
  intro Phi hPhi C H last s G L hinit x q Q hq hqQ hQ U hderiv hfinal hpinch hpinchFinal rho hrho
    hU hbuffer hvol
  obtain ⟨a, -, hQa⟩ := exists_window_start_P6WA s Q (fun n => zero_lt_one.trans_le (hQ n))
  exact exists_terminal_pointed_convergence_of_buffered_backward_traces_window_P6WA Phi hPhi H
    last s G L hinit x q Q hq hqQ hQ U a hQa
    (fun n j first hle hf hl z hz A t ht _ => hderiv n j first hle hf hl z hz A t ht)
    (fun n y hy t ht _ => hfinal n y hy t ht) (fun n j hj t ht x => hpinch n j hj t ht.1 x)
    (fun n t ht x => hpinchFinal n t ht.1 x) hrho hU hbuffer hvol

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
