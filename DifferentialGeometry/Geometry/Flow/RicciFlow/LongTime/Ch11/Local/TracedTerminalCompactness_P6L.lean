import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedTerminalCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TerminalCurvatureDerivativeBounds_P6L

/-!
# L6-B 第 1 层：`TracedTerminalCompactness:170` 的局部化（`_P6L`，合同表 §3 行 9）

局部化合同 `docs/geometrization/chapter8/design-C11-P6-localization-contract-20261006.md` §2：
原 `ST/TracedTerminalCompactness.lean:30`（private）/`:110`/`:170` 的
* `hderiv`（事件 slab 导数界，stage 全局）→ **footprint 形**：只在 `U n` 中点的 backward trace 点
  `A.point j.castSucc …` 上要求（`first`、`hle` 一并全称；唯一求值点 `HSIC:271`）；
* `hfinal`（final slab，last stage 全局）→ `∀ y ∈ U n`（`TTC:30` 只在 buffer 球上用）；
* 新增区域 `U : ∀ n, Set ((H n).stage (last n)).Carrier` 与
  `hU : ∀ n, B_{Q n·g}(x n, rho) ⊆ U n`（buffer 球半径 `R + r < rho`，成员关系由
  `riemannianClosedBallOf_subset_riemannianBallOf_P6L` 给出）。
pinching（`hpinch`、`hpinchFinal`）保持全局（合同 §1.3）。证明体照抄，叶子换成
`curvDerivNorm_scaleMetric_terminal_le_on_closedBall_of_backwardPointTrace_P6L`。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : Type*} [TopologicalSpace X] {I : ModelWithCorners ℝ E X}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace X M] [IsManifold I ∞ M]

/-- `_P6L` 辅助：闭球半径 `< ρ` 时含于开球 `B(x, ρ)`（区域成员关系的标准来源）。 -/
theorem riemannianClosedBallOf_subset_riemannianBallOf_P6L (g : SmoothRiemannianMetric I M)
    (x : M) {c ρ : ℝ} (hc : c < ρ) (hρ : 0 < ρ) :
    riemannianClosedBallOf (I := I) g x c ⊆ riemannianBallOf (I := I) g x ρ :=
  fun _ hy => hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hρ).mpr hc)

end DifferentialGeometry

end

noncomputable section
open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- **`_P6L` 私有副本**：原 private
`exists_normalized_curvature_derivative_bounds_of_buffered_backward_traces`
（`TracedTerminalCompactness:30`）。改动：`hderiv` 改 footprint 形、`hfinal` 限于 `U`，
加 `∀ U, (B_{Q·g}(x, a + r) ⊆ U) →`。常数 `B` 仍在历史之前取。 -/
private theorem exists_normalized_curvature_derivative_bounds_of_buffered_backward_traces_P6L
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
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2) →
    (∀ y ∈ U, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi) →
    Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi →
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
  have hbound := H.curvDerivNorm_scaleMetric_terminal_le_on_closedBall_of_backwardPointTrace_P6L
    first last hle G L hinit x (mul_nonneg ha (Real.sqrt_nonneg _))
    (mul_pos hr (Real.sqrt_pos.mpr hAp)) hq hqAQ hAQ (mul_pos hAp hθ)
    (by rw [houter, ← hball]; exact hcompact) U hKUL hPhi hderiv
    (fun y hy => hfinal y.val (hKUL y hy))
    hpinch hpinchFinal (by simpa only [houter, ← hball] using hscalar)
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

/-- **`_P6L`**：原
`ObservedHistory.exists_terminal_normalized_inner_ball_curvature_derivative_bounds_of_backward_traces`
（`TracedTerminalCompactness:110`）。改动：加 `U`、`hU`；`hderiv` footprint 形、`hfinal` 限于 `U`。结论逐字。 -/
theorem exists_terminal_normalized_inner_ball_curvature_derivative_bounds_of_backward_traces_P6L
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → ObservedHistory.{u})
    (last : ∀ n, Fin ((H n).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (last n)).IncomingSlab ((H n).time (last n)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (last n)) = (H n).initialMetric (last n))
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (U : ∀ n, Set ((H n).stage (last n)).Carrier)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ last n),
      ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last n,
      ∀ z ∈ U n, ∀ A : BackwardPointTrace (H n) first (last n) hle z,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => ((H n).event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * ((H n).event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ n, ∀ y ∈ U n,
      ∀ t ∈ Ioo ((H n).time (last n)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      Perelman.PhiAlmostNonnegative ((H n).event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (last n)) (s n)) Phi)
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
    exists_normalized_curvature_derivative_bounds_of_buffered_backward_traces_P6L
    Phi hPhi hR.le hr hA hθ htime
  refine ⟨B p, hB p, ?_⟩
  filter_upwards [hbuf] with n hn
  intro y hy
  obtain ⟨first, hle, htrace, hstart⟩ := hn.2.2
  exact hbound (H n) first (last n) hle (G n) (L n) (hinit n) (x n)
    (hq n) (hqQ n) (hQ n) hn.1 (U n)
    (fun y hy => hU n y
      (riemannianClosedBallOf_subset_riemannianBallOf_P6L _ _ hRr (hR.trans hRrho) hy))
    (fun j hf hl => hderiv n j first hle hf hl) (hfinal n)
    (fun j _ hj => hpinch n j hj) (hpinchFinal n) hn.2.1 htrace hstart p y hy


/-- **`_P6L`（合同 §3 行 9，接口）**：原
`ObservedHistory.exists_terminal_pointed_convergence_of_buffered_backward_traces`
（`TracedTerminalCompactness:170`）。改动：加 `U : ∀ n, Set ((H n).stage (last n)).Carrier`、
`hU : ∀ n, B_{Q n·g}(x n, rho) ⊆ U n`；`hderiv` 改 footprint 形（`∀ first hle hf hl, ∀ z ∈ U n,
∀ A : BackwardPointTrace …`，在 `A.point j.castSucc …` 上），`hfinal` 限于 `U n`。`hvol`、pinching 不变。
结论逐字。 -/
theorem exists_terminal_pointed_convergence_of_buffered_backward_traces_P6L
    (Phi : ℝ → ℝ) (hPhi : Perelman.AdmissiblePinchingFunction Phi) {C : ℝ≥0}
    (H : ℕ → ObservedHistory.{u})
    (last : ∀ n, Fin ((H n).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (last n)).IncomingSlab ((H n).time (last n)) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (hinit : ∀ n, (G n).flow.base.metric ((H n).time (last n)) = (H n).initialMetric (last n))
    (x : ∀ n, (G n).terminalRegularOpen) (q Q : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n) (hQ : ∀ n, 1 ≤ Q n)
    (U : ∀ n, Set ((H n).stage (last n)).Carrier)
    (hderiv : ∀ n, ∀ j : Fin (H n).eventCount,
      ∀ (first : Fin ((H n).eventCount + 1)) (hle : first ≤ last n),
      ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last n,
      ∀ z ∈ U n, ∀ A : BackwardPointTrace (H n) first (last n) hle z,
      ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q n < ((H n).event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => ((H n).event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * ((H n).event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ n, ∀ y ∈ U n,
      ∀ t ∈ Ioo ((H n).time (last n)) (s n), q n < (G n).flow.scalar t y →
      |derivWithin (fun v => (G n).flow.scalar v y) (Iic t) t| ≤ C * (G n).flow.scalar t y ^ 2)
    (hpinch : ∀ n, ∀ j : Fin (H n).eventCount, j.succ ≤ last n →
      Perelman.PhiAlmostNonnegative ((H n).event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    (hpinchFinal : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (last n)) (s n)) Phi)
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
    exists_terminal_normalized_inner_ball_curvature_derivative_bounds_of_backward_traces_P6L
    Phi hPhi H last s G L hinit x q Q hq hqQ hQ U hderiv hfinal hpinch hpinchFinal hU hbuffer
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
