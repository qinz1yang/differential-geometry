import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialOwnThresholdDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.NativeObservationCertificates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecentCaptureScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabGradientScalarControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabGradientScalarControlC11X

/-!
# S-CH11-FIX9 port of astra `PreparedSpatialReserveBall`（`PortC11P`）

来源：donor `PreparedSpatialReserveBall.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* 缺 import：donor 用的 `IncomingSlab.scalar_le_four_mul_max_of_gradient_bound_at_time_of_max_pos`
  在树内只在 `Surgery/Topology/SlabGradientScalarControlC11X`（宿主 `SlabGradientScalarControl`
  保持不变，astra 新增的两个定理由 O-CH11-FIX3 的 EXT 副本提供；其文档点名了本模块是直接用户）→
  加 `import …SlabGradientScalarControlC11X`；
* `hspace` 里 `exact le_of_lt hx`：目标是闭球成员、`hx` 是开球成员，`le_of_lt` 的 `?a < ?b` 对
  成员关系统一不了（`hx.le` 同样）→ 显式 `show riemannianEDistOf … y x < ENNReal.ofReal b from hx`
  再 `.le`。

原路径 `PreparedSpatialReserveBall` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal Topology
namespace GC.GeneralFlow
universe u

/-- Any low-scalar center uses the retained own-threshold estimates at its
actual metric. The positive own threshold pays the gradient maximum condition. -/
theorem PreparedSpatialStepRetention.isParabolicallyRmControlledBall_at_reserve_of_scalar_le
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext d eta εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (hcan : ∀ i b, ((W.oldNativeRecords i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((W.oldNativeRecords i).static b).neck.scale / 2 ≤
      metricScalarAt ((W.oldNativeRecords i).static b).witness.metric
        (((W.oldNativeRecords i).static b).witness.cap z))
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : W.oldNative.EventSlabsPinched phi)
    (t : Icc (0 : ℝ) W.oldNative.horizon) (htop : (t : ℝ) < W.oldNative.horizon)
    (hlast : W.oldNative.toHistory.activeStage t = Fin.last W.oldNative.eventCount →
      ∃ h : W.oldNative.time (Fin.last W.oldNative.eventCount) < W.oldNative.horizon,
        Perelman.PhiAlmostNonnegative (W.oldNative.finalSlab h).flow
          (Icc (W.oldNative.time (Fin.last W.oldNative.eventCount)) W.oldNative.horizon) phi)
    (y : (W.oldNative.toHistory.stageAt t).Carrier)
    (hRle : metricScalarAt
      (W.oldNative.toHistory.stageMetric (W.oldNative.toHistory.activeStage t) t) y ≤ L.prepared.Qall)
    (hback : (L.radius / 100) ^ 2 ≤ (t : ℝ))
    (hgradScale : (C.Cgrad : ℝ) * (L.radius / 100) * Real.sqrt L.prepared.Qall ≤ 1 / 4)
    (htimeScale : C.Ctime * (4 * L.prepared.Qall) * (L.radius / 100) ^ 2 ≤ 1 / 2)
    (hpinchScale : (L.radius / 100) ^ 4 *
      (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (4 * L.prepared.Qall)) ^ 2 ≤ 1)
    (hlarge : ∀ i : Fin W.oldNative.eventCount,
      W.oldNative.time i.succ ∈ Ioc ((t : ℝ) - (L.radius / 100) ^ 2) (t : ℝ) →
      ∀ b : (W.oldNative.toHistory.event i).RetainedBoundaryIndex,
        16 * L.prepared.Qall < ((W.oldNativeRecords i).static b).neck.scale) :
    W.oldNative.toHistory.isParabolicallyRmControlledBall t y (L.radius / 100) := by
  let K := W.oldNative
  let M := L.prepared.Qall
  let b := L.radius / 100
  have hb : 0 < b := div_pos L.radius_pos (by norm_num)
  let u : Icc (0 : ℝ) K.horizon :=
    ⟨(t : ℝ) - b ^ 2, sub_nonneg.mpr hback,
      (sub_le_self _ (sq_nonneg b)).trans t.property.2⟩
  have hut : u ≤ t := sub_le_self _ (sq_nonneg b)
  have hM : 1 ≤ M := by
    apply le_trans ((le_max_left 1 (max L.prepared.qcan L.prepared.qs)).trans
      L.prepared.Qbirth_ge)
    change L.prepared.Qbirth ≤ L.prepared.Qall
    rw [L.prepared.Qall_eq]
    exact le_max_left _ _
  obtain ⟨hslabs, _, hcurrent, hfinal, hpoint⟩ := W.own_threshold_native_certificates t htop
  obtain ⟨s, G, _, _, _, hG, _, _, _, _⟩ :=
    W.oldNative_estimates.exists_outgoingSlab_of_lt_horizon t htop
  have hgradNow : ∀ w, M < G.flow.scalar t w → ∀ v : TangentSpace I3 w,
      |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t w v| ≤
        C.Cgrad * G.flow.scalar t w * Real.sqrt (G.flow.scalar t w) *
          Real.sqrt ((G.flow.base.metric t).inner w v v) := by
    intro w hw
    have hw' : M < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t) w := by
      change M < metricScalarAt (G.flow.base.metric t) w at hw
      rwa [hG t] at hw
    change ∀ v : TangentSpace I3 w,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (G.flow.base.metric t)) w v)| ≤
        C.Cgrad * metricScalarAt (G.flow.base.metric t) w *
          Real.sqrt (metricScalarAt (G.flow.base.metric t) w) *
          Real.sqrt ((G.flow.base.metric t).inner w v v)
    rw [hG t]
    exact (hpoint w hw').2
  have hmax : max (G.flow.scalar t y) M = M := by
    apply max_eq_right
    change metricScalarAt (G.flow.base.metric t) y ≤ M
    rw [hG t]
    exact hRle
  have hmaxPos : 0 < max (G.flow.scalar t y) M := by
    rw [hmax]
    exact zero_lt_one.trans_le hM
  have hgradNorm : (C.Cgrad : ℝ) * b * Real.sqrt (max (G.flow.scalar t y) M) ≤ 1 / 4 := by
    rw [hmax]
    exact hgradScale
  have hspace : ∀ x ∈ riemannianBallOf
      (K.toHistory.stageMetric (K.toHistory.activeStage t) t) y b,
      metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t) x ≤ 4 * M := by
    intro x hx
    have hxG : x ∈ riemannianClosedBallOf (G.flow.base.metric t) y b := by
      rw [hG t]
      exact (show riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage t) t) y x <
        ENNReal.ofReal b from hx).le
    have h := G.scalar_le_four_mul_max_of_gradient_bound_at_time_of_max_pos
      hgradNow hmaxPos hgradNorm hxG
    rw [hmax] at h
    change metricScalarAt (G.flow.base.metric t) x ≤ 4 * M at h
    rwa [hG t] at h
  exact K.isParabolicallyRmControlledBall_of_recent_cap_scale_separation
    W.oldNativeRecords hcan hscale hphi hpinch hut hb rfl hlast y
    hslabs hcurrent hfinal (by linarith) (le_refl M) hspace htimeScale hpinchScale hlarge

end GC.GeneralFlow
