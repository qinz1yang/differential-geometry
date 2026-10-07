import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceChainBuffers
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TerminalScalarBall_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.TerminalBallProtection

/-!
# L6-B 第 4 层（起）：`BoundedCurvatureAtDistanceChainBuffers:18` 的局部化（`_P6L`）

局部化合同 §2 (G)：原 `ClosedSlab.scalar_le_six_mul_on_ball_of_gradient_bound`
（`ST/BoundedCurvatureAtDistanceChainBuffers.lean:18`）的 `hgradient : ∀ y, …`（carrier 全局）只整体
传给 `TerminalLimitMetric.scalar_le_on_small_ball_of_gradient_bound`（`TerminalScalarBall:110`）；
这里换成 P6A 的 `…_P6L`（`hgradient` 限于 `U`，移动球 `hUt`）。另给：
* `ClosedSlab.eventually_moving_ball_subset_of_terminal_ball_P6L`：静态球
  `B_T(p, 2ρ) ⊆ U` ⇒ `∀ᶠ t in 𝓝[<] T, B_t(p, ρ) ⊆ U`（经 B3 已落地的
  `exists_pos_moving_closedBall_subset_terminal_ball`，合同 §2 (G) 的成员关系来源）；
* `…_static_P6L`：静态前提 `B_T(p, 4·rad) ⊆ U` 版。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **`_P6L`**：原 `OrientedThreeStage.ClosedSlab.scalar_le_six_mul_on_ball_of_gradient_bound`
（`ChainBuffers:18`）。改动：`hgradient` 限于 `U`，加移动球
`hUt : ∀ᶠ t in 𝓝[<] T, B_t(p, 2·rad) ⊆ U`（`rad = localPropagationRadius C / √(2Mb)`）。
叶子换 `TerminalLimitMetric.scalar_le_on_small_ball_of_gradient_bound_P6L`（P6A G6）。结论逐字。 -/
theorem OrientedThreeStage.ClosedSlab.scalar_le_six_mul_on_ball_of_gradient_bound_P6L
    {P : OrientedThreeStage.{u}} {a T : ℝ} (A : P.ClosedSlab a T)
    (C : ℝ≥0) {q Mb : ℝ} (hMb : 0 < Mb) (hqMb : q ≤ Mb) (U : Set P.Carrier)
    (hgradient : ∀ y ∈ U, ∀ t ∈ Ioo a T, q < A.flow.scalar t y →
      ∀ v : TangentSpace ThreeModel y,
        |scalarDifferential (A.restrictIncoming le_rfl A.lt le_rfl).flow t y v| ≤
          C * A.flow.scalar t y * Real.sqrt (A.flow.scalar t y) *
            Real.sqrt ((A.flow.base.metric t).inner y v v))
    (p : P.Carrier)
    (hUt : ∀ᶠ t in 𝓝[<] T, riemannianBallOf (A.flow.base.metric t) p
      (2 * (localPropagationRadius C / Real.sqrt (2 * Mb))) ⊆ U)
    (hp : A.flow.scalar T p ≤ Mb) :
    ∀ z ∈ riemannianBallOf (A.flow.base.metric T) p
      (localPropagationRadius C / (2 * Real.sqrt (2 * Mb))), A.flow.scalar T z ≤ 6 * Mb := by
  intro z hz
  have hU : ∀ w : P.Carrier, w ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen := by
    intro w
    change w ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
    rw [A.terminalRegularRegion_eq_univ P]
    trivial
  have hL (w : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) :
      metricScalarAt (A.endpointTerminalLimitMetric P).metric w = A.flow.scalar T w.val :=
    metricScalarAt_restrictOpen _ _ _
  have h := (A.endpointTerminalLimitMetric P).scalar_le_on_small_ball_of_gradient_bound_P6L C hMb
    hqMb U hgradient ⟨p, hU p⟩ hUt (by rw [hL]; exact hp) ⟨z, hU z⟩ (by
      change riemannianEDistOf _ _ _ ≤ _
      rw [A.riemannianEDistOf_endpointTerminalLimitMetric]
      exact hz.le)
  rwa [hL] at h

/-- `_P6L` 辅助（合同 §2 (G) 的成员关系来源）：closed slab 终端时刻的静态球 `B_T(p, 2ρ) ⊆ U`
推出 `t` 足够近 `T` 时移动球 `B_t(p, ρ) ⊆ U`（`exists_pos_moving_closedBall_subset_terminal_ball`）。 -/
theorem OrientedThreeStage.ClosedSlab.eventually_moving_ball_subset_of_terminal_ball_P6L
    {P : OrientedThreeStage.{u}} {a T : ℝ} (A : P.ClosedSlab a T) (U : Set P.Carrier)
    (p : P.Carrier) {ρ : ℝ} (hρ : 0 < ρ)
    (hUT : riemannianBallOf (A.flow.base.metric T) p (2 * ρ) ⊆ U) :
    ∀ᶠ t in 𝓝[<] T, riemannianBallOf (A.flow.base.metric t) p ρ ⊆ U := by
  obtain ⟨δ, hδ, -, hδball⟩ := exists_pos_moving_closedBall_subset_terminal_ball A.flow A.equation
    A.lt (fun _ h => h) (fun _ h => h) p hρ (by linarith : ρ < 2 * ρ)
    ((isClosed_le (Geometry.Riemannian.continuous_riemannianEDist _ p)
      continuous_const).isCompact)
  filter_upwards [Ioo_mem_nhdsLT (sub_lt_self T hδ)] with t ht y hy
  have hy' : riemannianEDistOf (A.flow.base.metric t) p y ≤ ENNReal.ofReal ρ :=
    le_of_lt (show riemannianEDistOf (A.flow.base.metric t) p y < ENNReal.ofReal ρ from hy)
  exact hUT ((hδball t ⟨ht.1.le, ht.2.le⟩).1 hy')

/-- **`_P6L`（静态前提版）**：同 `scalar_le_six_mul_on_ball_of_gradient_bound_P6L`，移动球前提换成
终端时刻静态球 `B_T(p, 4·rad) ⊆ U`。 -/
theorem OrientedThreeStage.ClosedSlab.scalar_le_six_mul_on_ball_of_gradient_bound_static_P6L
    {P : OrientedThreeStage.{u}} {a T : ℝ} (A : P.ClosedSlab a T)
    (C : ℝ≥0) {q Mb : ℝ} (hMb : 0 < Mb) (hqMb : q ≤ Mb) (U : Set P.Carrier)
    (hgradient : ∀ y ∈ U, ∀ t ∈ Ioo a T, q < A.flow.scalar t y →
      ∀ v : TangentSpace ThreeModel y,
        |scalarDifferential (A.restrictIncoming le_rfl A.lt le_rfl).flow t y v| ≤
          C * A.flow.scalar t y * Real.sqrt (A.flow.scalar t y) *
            Real.sqrt ((A.flow.base.metric t).inner y v v))
    (p : P.Carrier)
    (hUT : riemannianBallOf (A.flow.base.metric T) p
      (2 * (2 * (localPropagationRadius C / Real.sqrt (2 * Mb)))) ⊆ U)
    (hp : A.flow.scalar T p ≤ Mb) :
    ∀ z ∈ riemannianBallOf (A.flow.base.metric T) p
      (localPropagationRadius C / (2 * Real.sqrt (2 * Mb))), A.flow.scalar T z ≤ 6 * Mb :=
  A.scalar_le_six_mul_on_ball_of_gradient_bound_P6L C hMb hqMb U hgradient p
    (A.eventually_moving_ball_subset_of_terminal_ball_P6L U p
      (by have := localPropagationRadius_pos C.coe_nonneg; positivity) hUT) hp

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- consumer：原 `ChainBuffers:18`（全局 `hgradient`）由 `_P6L` 版（`U = univ`）推出。 -/
example : type_of% @OrientedThreeStage.ClosedSlab.scalar_le_six_mul_on_ball_of_gradient_bound.{0}
    := by
  intro P a T A C q Mb hMb hqMb hgradient p hp
  exact A.scalar_le_six_mul_on_ball_of_gradient_bound_static_P6L C hMb hqMb univ
    (fun y _ => hgradient y) p (subset_univ _) hp

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
