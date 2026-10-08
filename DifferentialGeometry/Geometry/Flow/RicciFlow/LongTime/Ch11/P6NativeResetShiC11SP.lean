import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialLocalEndpointHorizon
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.PositiveTimeUniform
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall

set_option autoImplicit false

/-!
# newborn reset Shi（O-CH11-SPINE-B G3 = SL2-a，后缀 `_C11SP`）

native 路线 B（局部 Shi + newborn jets reset）的基本情形：一个 stage 的实际 slab flow `G`
（`IncomingSlab` 的 `flow / equation / smoothUpTo`，或 final slab），窗口 `[u, t]` 从该 stage 的
birth `u` 开始。**闭窗 Gram 光滑**由 slab 自带的 `MetricSmoothUpTo`（含 birth 端点）付，
不再是外部 binder；时间平移后调用 `Estimates/Shi/InitialLocalEndpointHorizon:13`。
输入只剩两项局部量（都在 birth 时刻的度量球 `B_{g(u)}(p, R)` 上）：
* 零阶 `curvDerivNormSq 0 ≤ K` 于整个 `[u, t]`——native 链里由 first-exit + pinching 付
  （SL1 的 Rm 行）；
* 初始 jets `curvDerivNormSq k (g u) ≤ A k`（`1 ≤ k ≤ N`）——由 G63 born-cap jets 经 G1b
  `bornCap_jets_normalized_le_C11SP` 付（patch 在 `u` 时整块落在 G63 window 内）。
结论：`B_{g(u)}(p, R/2)` 上 `[u, t]` 全时段所有阶 `≤ N` 的 jets `≤ B(N, T, R, K, A)`，**不需要深度下界**
（`t − u` 可任意小，这正是 guard 式 Shi 不能处理 newborn 点的地方）。

**不覆盖（SL2-b，见 native-route §N1）**：窗口内另有 event（别处手术）使 patch 跨 stage 的情形——
需把 trace 公共 flow（`exists_common_flow_with_compact_neighborhood_of_isTracedRegion`）的闭窗 Gram
在两端由 birth / terminal slab 的 `smoothUpTo` 拼出（`closed a t` 的 regular 只有 `Ioo a t`）。
-/

noncomputable section

open Set Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch11

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

/-- **G3 = SL2-a（PROVED 目标）**：从 birth `u` 起的单 stage 窗口上的 reset Shi。 -/
theorem exists_newborn_reset_shi_C11SP (N : ℕ) (T R K : ℝ) (hR : 0 < R) (A : ℕ → ℝ)
    (hA : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ A k) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {P : OrientedThreeStage.{u}} {D : RealTimeInterval}
      (G : SolutionOn (I := ThreeModel) (M := P.Carrier) D), IsSolutionOn G →
      ∀ {J : Set ℝ}, P.MetricSmoothUpTo G.base.metric J →
      ∀ (s t : ℝ), s < t → t - s ≤ T → Icc s t ⊆ D.carrier → Ioo s t ⊆ D.regular →
      Icc s t ⊆ J → ∀ p : P.Carrier,
      (∀ v ∈ Icc s t, ∀ x : P.Carrier,
        riemannianEDistOf (G.base.metric s) p x ≤ ENNReal.ofReal R →
          curvDerivNormSq 0 (G.base.metric v) x ≤ K) →
      (∀ k, 1 ≤ k → k ≤ N → ∀ x : P.Carrier,
        riemannianEDistOf (G.base.metric s) p x ≤ ENNReal.ofReal R →
          curvDerivNormSq k (G.base.metric s) x ≤ A k) →
      ∀ k ≤ N, ∀ v ∈ Icc s t, ∀ x : P.Carrier,
        riemannianEDistOf (G.base.metric s) p x ≤ ENNReal.ofReal (R / 2) →
          curvDerivNormSq k (G.base.metric v) x ≤ B := by
  obtain ⟨B, hB, hb⟩ :=
    exists_uniform_initial_curvature_derivative_bound_on_compact_ball_of_open_regular_interval
      (I := ThreeModel) N T R K hR A hA
  refine ⟨B, hB, ?_⟩
  intro P D G hG J hsm s t hst htT hcar hreg hJ p hK hinit k hk v hv x hx
  have h0 : (G.timeShift s).base.metric 0 = G.base.metric s := by
    rw [SolutionOn.timeShift_base_metric, zero_add]
  have hgram : ∀ (x₀ : P.Carrier) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × P.Carrier => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((G.timeShift s).base.metric q.1) x₀ q.2 i j)
        (Icc 0 (t - s) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet) := by
    intro x₀ i j
    have hJg := chartGramMatrix_joint_contMDiffOn G.base.metric J hsm.jointContMDiffOn x₀ i j
    have hφ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
        (fun q : ℝ × P.Carrier => (q.1 + s, q.2)) :=
      (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd
    refine (hJg.comp hφ.contMDiffOn ?_).congr ?_
    · intro q hq
      exact ⟨hJ ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hq.2⟩
    · intro q _
      rfl
  have key := hb P.Carrier (D.timeShift s) (G.timeShift s) (t - s) (by linarith) htT
    (isSolutionOn_timeShift hG s)
    (fun r hr => hcar ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    (fun r hr => hreg ⟨by linarith [hr.1], by linarith [hr.2]⟩) hgram p
    (by rw [h0]; exact (Geometry.Metric.isClosed_riemannianClosedBallOf _ p R).isCompact)
    (fun r hr y hy => by
      rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, SolutionOn.timeShift_base_metric]
      exact hK (r + s) ⟨by linarith [hr.1], by linarith [hr.2]⟩ y (h0 ▸ hy))
    (fun j hj1 hjN y hy => by
      rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, h0]
      exact hinit j hj1 hjN y (h0 ▸ hy))
    k hk (v - s) ⟨by linarith [hv.1], by linarith [hv.2]⟩ x (h0 ▸ hx)
  rwa [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, SolutionOn.timeShift_base_metric,
    sub_add_cancel] at key

/-- 实例化检查：`IncomingSlab` 的实际 flow 满足 SL2-a 的结构前提（`J = Ico a s`）。 -/
theorem incomingSlab_newborn_reset_shi_C11SP (N : ℕ) (T R K : ℝ) (hR : 0 < R) (A : ℕ → ℝ)
    (hA : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ A k) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {P : OrientedThreeStage.{u}} {a b : ℝ} (G : P.IncomingSlab a b)
      (t : ℝ), a < t → t < b → t - a ≤ T → ∀ p : P.Carrier,
      (∀ v ∈ Icc a t, ∀ x : P.Carrier,
        riemannianEDistOf (G.flow.base.metric a) p x ≤ ENNReal.ofReal R →
          curvDerivNormSq 0 (G.flow.base.metric v) x ≤ K) →
      (∀ k, 1 ≤ k → k ≤ N → ∀ x : P.Carrier,
        riemannianEDistOf (G.flow.base.metric a) p x ≤ ENNReal.ofReal R →
          curvDerivNormSq k (G.flow.base.metric a) x ≤ A k) →
      ∀ k ≤ N, ∀ v ∈ Icc a t, ∀ x : P.Carrier,
        riemannianEDistOf (G.flow.base.metric a) p x ≤ ENNReal.ofReal (R / 2) →
          curvDerivNormSq k (G.flow.base.metric v) x ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_newborn_reset_shi_C11SP.{u} N T R K hR A hA
  refine ⟨B, hB, ?_⟩
  intro P a b G t hat htb htT p hK hinit
  exact hb G.flow G.equation G.smoothUpTo a t hat htT
    (fun r hr => ⟨hr.1, hr.2.trans_lt htb⟩) (fun r hr => ⟨hr.1, hr.2.trans htb⟩)
    (fun r hr => ⟨hr.1, hr.2.trans_lt htb⟩) p hK hinit

end GC.LongTime.Ch11
