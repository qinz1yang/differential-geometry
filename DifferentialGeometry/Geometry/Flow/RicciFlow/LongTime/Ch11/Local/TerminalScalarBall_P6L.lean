import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.LocalPropagation_P6L

/-!
# L6-A 第 2 层：`TerminalScalarBall` 的梯度小球界局部化（`_P6L`）

局部化合同 `docs/geometrization/chapter8/design-C11-P6-localization-contract-20261006.md` §2 (G)：
原 `ST/TerminalScalarBall.lean:47`（时间窗版）与 `:110` 的 `hgradient : ∀ x : P.Carrier, …`（carrier 全局）
在证明里只经 `scalar_le_on_ball_of_gradient_bound`（`CN/LocalPropagation:347`）于时刻 `t ∈ 𝓝[<] s`、
`B_t(x, 2·rad)` 内的路径点求值。这里 `hgradient` 只要求在 `U` 上，并加移动球包含前提
`hU : ∀ᶠ t in 𝓝[<] s, B_t(x, 2·localPropagationRadius C/√(2Q)) ⊆ U`（ClosedSlab 调用方由
`exists_pos_moving_closedBall_subset_terminal_ball`（`RF/Estimates/TerminalBallProtection`）给）。
证明体照抄，叶子换成 `scalar_le_on_ball_of_gradient_bound_P6L`。
-/

set_option autoImplicit false

open Filter Set Bundle Manifold
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

/-- **`_P6L`**：原 `TerminalLimitMetric.scalar_le_on_small_ball_of_gradient_bound_on_time_window`
（`TerminalScalarBall:47`），`hgradient` 限于 `U`，加 `hU`；结论逐字。 -/
theorem TerminalLimitMetric.scalar_le_on_small_ball_of_gradient_bound_on_time_window_P6L
    {P : OrientedThreeStage.{u}} {a s c : ℝ} {G : P.IncomingSlab a s}
    (L : G.TerminalLimitMetric) {q Q : ℝ} (C : ℝ≥0)
    (hQ : 0 < Q) (hqQ : q ≤ Q) (hcs : c < s) (U : Set P.Carrier)
    (hgradient : ∀ x ∈ U, ∀ t ∈ Ioo a s, c ≤ t → q < G.flow.scalar t x →
      ∀ v : TangentSpace ThreeModel x,
        |scalarDifferential G.flow t x v| ≤ C * G.flow.scalar t x *
          Real.sqrt (G.flow.scalar t x) * Real.sqrt ((G.flow.base.metric t).inner x v v))
    (x : G.terminalRegularOpen)
    (hU : ∀ᶠ t in 𝓝[<] s, riemannianBallOf (G.flow.base.metric t) x.val
      (2 * (localPropagationRadius C / Real.sqrt (2 * Q))) ⊆ U)
    (hx : metricScalarAt L.metric x ≤ Q)
    (y : G.terminalRegularOpen)
    (hy : y ∈ riemannianClosedBallOf L.metric x
      (localPropagationRadius C / (2 * Real.sqrt (2 * Q)))) :
    metricScalarAt L.metric y ≤ 6 * Q := by
  have htwoQ : 0 < 2 * Q := by positivity
  have hrad : 0 < localPropagationRadius C / Real.sqrt (2 * Q) :=
    div_pos (localPropagationRadius_pos C.coe_nonneg) (Real.sqrt_pos.mpr htwoQ)
  have hdist : riemannianEDistOf L.metric x y <
      ENNReal.ofReal (localPropagationRadius C / Real.sqrt (2 * Q)) := by
    apply hy.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff hrad).mpr
    have heq : localPropagationRadius C / (2 * Real.sqrt (2 * Q)) =
        (localPropagationRadius C / Real.sqrt (2 * Q)) / 2 := by ring
    rw [heq]
    exact half_lt_self hrad
  have hbase : ∀ᶠ t in 𝓝[<] s, G.flow.scalar t x.val < 2 * Q :=
    (L.tendsto_metricScalarAt x).eventually_lt_const (by linarith)
  apply le_of_tendsto (L.tendsto_metricScalarAt y)
  filter_upwards [Ioo_mem_nhdsLT G.lt, Ioo_mem_nhdsLT hcs, hbase,
    L.eventually_riemannianEDistOf_lt x y hdist, hU] with t ht hct hb hd hUt
  have hgrad (w : P.Carrier) (hwU : w ∈ U) (hw : 2 * (2 * Q) ≤ G.flow.scalar t w)
      (v : TangentSpace ThreeModel w) :
      |scalarDifferential G.flow t w v| ≤
        2 * C * (G.flow.scalar t w * Real.sqrt (G.flow.scalar t w)) *
          Real.sqrt ((G.flow.base.metric t).inner w v v) := by
    have hhigh : q < G.flow.scalar t w := by linarith
    have hpos : 0 ≤ G.flow.scalar t w := by linarith
    have hbound := hgradient w hwU t ht hct.1.le hhigh v
    have hterm : 0 ≤ (C : ℝ) * G.flow.scalar t w * Real.sqrt (G.flow.scalar t w) *
        Real.sqrt ((G.flow.base.metric t).inner w v v) := by positivity
    nlinarith
  have hh := scalar_le_on_ball_of_gradient_bound_P6L G.flow C.coe_nonneg htwoQ U hUt hgrad
    hb.le hd.le
  change G.flow.scalar t y.val ≤ 6 * Q
  simpa only [show (3 : ℝ) * (2 * Q) = 6 * Q by ring] using hh


/-- **`_P6L`**：原 `TerminalLimitMetric.scalar_le_on_small_ball_of_gradient_bound`（`:110`，无时间窗）。 -/
theorem TerminalLimitMetric.scalar_le_on_small_ball_of_gradient_bound_P6L
    {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
    (L : G.TerminalLimitMetric) {q Q : ℝ} (C : ℝ≥0)
    (hQ : 0 < Q) (hqQ : q ≤ Q) (U : Set P.Carrier)
    (hgradient : ∀ x ∈ U, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      ∀ v : TangentSpace ThreeModel x,
        |scalarDifferential G.flow t x v| ≤ C * G.flow.scalar t x *
          Real.sqrt (G.flow.scalar t x) * Real.sqrt ((G.flow.base.metric t).inner x v v))
    (x : G.terminalRegularOpen)
    (hU : ∀ᶠ t in 𝓝[<] s, riemannianBallOf (G.flow.base.metric t) x.val
      (2 * (localPropagationRadius C / Real.sqrt (2 * Q))) ⊆ U)
    (hx : metricScalarAt L.metric x ≤ Q)
    (y : G.terminalRegularOpen)
    (hy : y ∈ riemannianClosedBallOf L.metric x
      (localPropagationRadius C / (2 * Real.sqrt (2 * Q)))) :
    metricScalarAt L.metric y ≤ 6 * Q :=
  L.scalar_le_on_small_ball_of_gradient_bound_on_time_window_P6L C hQ hqQ G.lt U
    (fun x hx t ht _ => hgradient x hx t ht) x hU hx y hy

/-- consumer：原 `:110`（全局 `hgradient`）由 `_P6L` 版（`U = univ`）推出。 -/
example {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
    (L : G.TerminalLimitMetric) {q Q : ℝ} (C : ℝ≥0)
    (hQ : 0 < Q) (hqQ : q ≤ Q)
    (hgradient : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      ∀ v : TangentSpace ThreeModel x,
        |scalarDifferential G.flow t x v| ≤ C * G.flow.scalar t x *
          Real.sqrt (G.flow.scalar t x) * Real.sqrt ((G.flow.base.metric t).inner x v v))
    (x : G.terminalRegularOpen) (hx : metricScalarAt L.metric x ≤ Q)
    (y : G.terminalRegularOpen)
    (hy : y ∈ riemannianClosedBallOf L.metric x
      (localPropagationRadius C / (2 * Real.sqrt (2 * Q)))) :
    metricScalarAt L.metric y ≤ 6 * Q :=
  L.scalar_le_on_small_ball_of_gradient_bound_P6L C hQ hqQ univ
    (fun x _ => hgradient x) x (Eventually.of_forall fun _ => subset_univ _) hx y hy

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
