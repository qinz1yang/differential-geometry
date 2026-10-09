import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeClosedGramC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialLocalEndpointHorizon
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.PositiveTimeUniform
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.LocalDistanceComparison
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullbackScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionShiWholeBall

set_option autoImplicit false

/-!
# 跨 stage 的 reset Shi（O-CH11-SPINE-B G7 = SL2-b，后缀 `_C11SP`）

对 trace 公共 flow（`exists_common_flow_with_compact_neighborhood_of_isTracedRegion` 的
`U / f / S / hmetric / hRm / hterminal` 形，`[a, t]` 内可跨任意多个 event，`a` 可是 birth）给 **带初始数据的** Shi：
* 闭窗 Gram：G6 `commonFlow_closedGram_C11SP` + 时间平移；
* `a` 时刻 U 内闭球紧性：`isCompact_intrinsic_closedBall_of_terminal_ball`（`[a,t]` 上 Rm 界的距离畸变）；
* 初始 jets：`a` 时刻 `S(a) = localPullMetric (stageMetric (activeStage a) a) (f ja)`，经
  `curvDerivNormSq_localPullMetric` 化为 stage 度量在 `f ja x` 处的 jets（native 下由 G63 + G1b 付）；
* 终端：`hterminal` + `curvDerivNorm_restrictOpen`。
深度 `t − a` **无下界**（newborn 点）。零阶 `K` 在 native 链里由 first-exit + pinching 付（SL1）。
-/

noncomputable section

open Set Bundle
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

/-- **G7 = SL2-b（PROVED 目标）**：跨 stage 的 reset Shi；常数 `B` 先于 history / 窗口 / 点选取。 -/
theorem exists_reset_shi_commonFlow_C11SP (N : ℕ) (T R K : ℝ) (hR : 0 < R) (A : ℕ → ℝ)
    (hA : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ A k) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t),
      (a : ℝ) < t → (t : ℝ) - a ≤ T → H.time (H.activeStage t) < t →
      ∀ (U : TopologicalSpace.Opens (H.stageAt t).Carrier)
        (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U →
          (H.stage j.val).Carrier)
        (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
        (S : SolutionOn (I := ThreeModel) (M := U) (RealTimeInterval.closed a.val t.val hat)),
        IsSolutionOn S →
        (∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
          ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
            S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) →
        (∀ v ∈ Icc a.val t.val, ∀ x : U,
          normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ K) →
        S.base.metric t = (H.stageMetric (H.activeStage t) t).restrictOpen U →
      ∀ (pU : U) (Rbig : ℝ≥0),
        {x | riemannianEDistOf (H.stageMetric (H.activeStage t) t) pU.val x ≤ Rbig} ⊆ U →
        ENNReal.ofReal (Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt K *
          |(a : ℝ) - t|)) * ENNReal.ofReal R ≤ Rbig →
        (∀ k, 1 ≤ k → k ≤ N → ∀ x : U,
          riemannianEDistOf (S.base.metric a) pU x ≤ ENNReal.ofReal R →
          curvDerivNormSq k (H.stageMetric (H.activeStage a) a)
            (f ⟨H.activeStage a, le_rfl, H.activeStage_mono hat⟩ x) ≤ A k) →
      ∀ k ≤ N, curvDerivNorm k (H.stageMetric (H.activeStage t) t) pU.val ≤ Real.sqrt B := by
  obtain ⟨B, hB, hb⟩ :=
    exists_uniform_initial_curvature_derivative_bound_on_compact_ball_of_open_regular_interval
      (I := ThreeModel) N T R K hR A hA
  refine ⟨B, hB, ?_⟩
  intro H a t hat hlt hT hpos U f hf S hS hmetric hRm hterm pU Rbig hball hfit hinit k hk
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have hcar : Icc a.val t.val ⊆ (RealTimeInterval.closed a.val t.val hat).carrier :=
    fun _ h => h
  have hreg : Ioo a.val t.val ⊆ (RealTimeInterval.closed a.val t.val hat).regular :=
    fun _ h => h
  have h0 : (S.timeShift a.val).base.metric 0 = S.base.metric a.val := by
    rw [SolutionOn.timeShift_base_metric, zero_add]
  have hgram : ∀ (x₀ : U) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × U => Tensor.Coordinates.chartGramMatrix
          ((S.timeShift a.val).base.metric q.1) x₀ q.2 i j)
        (Icc 0 (t.val - a.val) ×ˢ
          (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet) := by
    intro x₀ i j
    have hG := commonFlow_closedGram_C11SP H hat hlt hpos f hf S hS hmetric x₀ i j
    have hφ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
        (fun q : ℝ × U => (q.1 + a.val, q.2)) :=
      (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd
    refine (hG.comp hφ.contMDiffOn ?_).congr ?_
    · intro q hq
      exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hq.2⟩
    · intro q _
      rfl
  have hcomp : IsCompact
      {x | riemannianEDistOf (H.stageMetric (H.activeStage t) t) pU.val x ≤ (Rbig : ℝ≥0∞)} := by
    have h := (Geometry.Metric.isClosed_riemannianClosedBallOf
      (H.stageMetric (H.activeStage t) t) pU.val (Rbig : ℝ)).isCompact
    simpa only [riemannianClosedBallOf, ENNReal.ofReal_coe_nnreal] using h
  have hcpt : IsCompact {x : U |
      riemannianEDistOf ((S.timeShift a.val).base.metric 0) pU x ≤ ENNReal.ofReal R} := by
    rw [h0]
    exact isCompact_intrinsic_closedBall_of_terminal_ball (H.stageMetric (H.activeStage t) t) U
      S hS hcar hreg hRm ⟨le_rfl, hat⟩ hterm pU (r := R.toNNReal) (R := Rbig) hcomp hball hfit
  have key := hb U (RealTimeInterval.closed a.val t.val hat |>.timeShift a.val)
    (S.timeShift a.val) (t.val - a.val) (by linarith) hT (isSolutionOn_timeShift hS a.val)
    (fun r hr => hcar ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    (fun r hr => hreg ⟨by linarith [hr.1], by linarith [hr.2]⟩) hgram pU hcpt
    (fun s hs x _ => by
      rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, SolutionOn.timeShift_base_metric,
        FILL910.curvDerivNormSq_zero_eq_normSq0S_metricRm04At]
      exact hRm (s + a.val) ⟨by linarith [hs.1], by linarith [hs.2]⟩ x)
    (fun j hj1 hjN x hx => by
      rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, h0,
        hmetric ⟨H.activeStage a, le_rfl, H.activeStage_mono hat⟩ a.val ⟨le_rfl, hat⟩
          (H.activeStage_mem a), curvDerivNormSq_localPullMetric]
      exact hinit j hj1 hjN x (h0 ▸ hx))
    k hk (t.val - a.val) ⟨by linarith, le_rfl⟩ pU
    (by rw [h0, riemannianEDistOf_self]; exact bot_le)
  rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, SolutionOn.timeShift_base_metric,
    sub_add_cancel, hterm] at key
  calc curvDerivNorm k (H.stageMetric (H.activeStage t) t) pU.val
      = curvDerivNorm k ((H.stageMetric (H.activeStage t) t).restrictOpen U) pU :=
        (curvDerivNorm_restrictOpen _ U k pU).symm
    _ ≤ Real.sqrt B := Real.sqrt_le_sqrt key

end GC.LongTime.Ch11
