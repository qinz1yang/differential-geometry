import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateCoreP6X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterGood_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarControl.TimeLocal

set_option autoImplicit false

/-!
# CX-SPINE G10：native 小种子的全过去时间控制

r≤nr(T) 时，antitone 给全部 0≤v≤T 上 nr(v)⁻²≤r⁻²。
直接使用 native S5/S11 生产 seed 阈值以上的完整 Good，不使用 selected non-Good 或 hP6 closure。
对已存在的 trace，S11 与同一总时长预算给跨事件 scalar 上界；不生产 trace survival。
birth/horizon 处 Good 的时间分量仍保留实际 stage-age/horizon guards。
-/

noncomputable section

open Set DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff NNReal

namespace GC.LongTime.Ch11

universe u

private theorem native_threshold_le_seed_CXSP {q : CutoffParameters}
    (hanti : AntitoneOn q.neckRadius (Ici 0)) {T v r : ℝ}
    (hv0 : 0 ≤ v) (hvT : v ≤ T) (hr : 0 < r) (hradius : r ≤ q.neckRadius T) :
    (q.neckRadius v ^ 2)⁻¹ ≤ (r ^ 2)⁻¹ := by
  have hrv : r ≤ q.neckRadius v := hradius.trans (hanti hv0 (hv0.trans hvT) hvT)
  exact (inv_le_inv₀ (sq_pos_of_pos (q.neckRadius_pos v hv0)) (sq_pos_of_pos hr)).mpr
    (pow_le_pow_left₀ hr.le hrv 2)

/-- native 小种子在全部过去时间、全部点上具有 seed 阈值以上的完整 Good。 -/
theorem native_seed_good_before_CXSP {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ}
    {Ctime : ℝ≥0} (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    {T r H₀ : ℝ} (hr : 0 < r) (hradius : r ≤ q.neckRadius T) (hH : 2 < H₀)
    (n : ℕ) (v : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
    (hvT : (v : ℝ) ≤ T) (z : ((F.tower.history n).toHistory.stageAt v).Carrier)
    (hR : H₀ / 2 * (r ^ 2)⁻¹ ≤ metricScalarAt
      ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage v) v) z) :
    (F.tower.history n).toHistory.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z := by
  have hq : (r ^ 2)⁻¹ < H₀ / 2 * (r ^ 2)⁻¹ := by
    nlinarith [inv_pos.mpr (sq_pos_of_pos hr)]
  have hnative := (native_threshold_le_seed_CXSP hanti v.2.1 hvT hr hradius).trans_lt
    (hq.trans_le hR)
  exact ⟨hcan n v z hnative, fun hage htop =>
    stageDerivative_of_timeDerivativeSupply_P6X hder n v z hage htop hnative⟩

/-- native S11 对已有 trace 给整个闭时间窗的 scalar 上界，跨事件只使用一次总预算。 -/
theorem scalar_le_two_mul_on_native_seed_trace_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    {T r : ℝ} (hr : 0 < r) (hradius : r ≤ q.neckRadius T) (n : ℕ)
    {a t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon} (hat : a ≤ t)
    (htT : (t : ℝ) ≤ T) {y : ((F.tower.history n).toHistory.stageAt t).Carrier}
    (A : BackwardPointTrace (F.tower.history n).toHistory
      ((F.tower.history n).toHistory.activeStage a)
      ((F.tower.history n).toHistory.activeStage t)
      ((F.tower.history n).toHistory.activeStage_mono hat) y)
    {M : ℝ} (hM : 0 < M) (hqM : (r ^ 2)⁻¹ ≤ M)
    (hscalar : metricScalarAt ((F.tower.history n).toHistory.stageMetric
      ((F.tower.history n).toHistory.activeStage t) t) y ≤ M)
    (htime : Ctime * M * ((t : ℝ) - a) ≤ 1 / 2) :
    ∀ (v : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage v) v)
        (A.point ((F.tower.history n).toHistory.activeStage v)
          ((F.tower.history n).toHistory.activeStage_mono hav)
          ((F.tower.history n).toHistory.activeStage_mono hvt)) ≤ 2 * M := by
  exact A.scalar_le_two_mul_of_time_local_derivative_control hat hM
    (fun v _hav hvt hage htop hR =>
      stageDerivative_of_timeDerivativeSupply_P6X hder n v _ hage htop
        ((native_threshold_le_seed_CXSP hanti v.2.1
          ((show (v : ℝ) ≤ t from hvt).trans htT) hr hradius).trans_lt
          (hqM.trans_lt hR))) hscalar htime

/-- consumer：同一 native 供给可使用 Q2 的更大 C1/C2/Ctime ceiling，保留 ε。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {ε C1 C2 C1' C2' : ℝ} {Ctime Ctime' : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2') (hCt : Ctime ≤ Ctime')
    {T r H₀ : ℝ} (hr : 0 < r) (hradius : r ≤ q.neckRadius T) (hH : 4 ≤ H₀)
    (n : ℕ) (v : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
    (hvT : (v : ℝ) ≤ T) (z : ((F.tower.history n).toHistory.stageAt v).Carrier)
    (hR : H₀ / 2 * (r ^ 2)⁻¹ ≤ metricScalarAt
      ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage v) v) z) :
    (F.tower.history n).toHistory.HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z := by
  exact ObservedHistory.hasSpatialCanonicalTimeControl_mono_P6L hC1 hC2 hCt
    (native_seed_good_before_CXSP hanti hcan hder hr hradius (by linarith) n v hvT z hR)

end GC.LongTime.Ch11
