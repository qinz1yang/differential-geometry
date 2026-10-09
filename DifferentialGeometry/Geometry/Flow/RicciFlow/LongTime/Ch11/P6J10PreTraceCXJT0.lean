import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10CeilingODECXJT0
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10SlabLocalCXJB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KdataRescaleP6X3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.EarlierGoodTraceLocal_P6N
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart

/-!
# T0：pre-trace / stopped-trace 时间导数 + 定位桥（CX-J10T0 G2，后缀 `_CXJT0`）

R-C11-16 D-2 / D-4 第一步的 T0。全部是 trace-local footprint 形（树内
`BackwardPointTrace.scalar_le_two_mul_of_time_local_derivative_control` 的 `hbound` 形，
即 G1 `scalar_le_two_mul_ceiling_trace_CXJT0` 的输入）；**不出现** `qcap < R`、**不调用**待构造的
traced region、**不用** `hderivKC`（P6CondBridgeP6CD:36–106 的 traced-region 条件形）。
* `timeFootprint_of_hgood_stopped_CXJT0`（stopped-trace，slab 无关）：原始 `hgood` 的**时间分量**
  （`HasSpatialCanonicalTimeControl` 的第二合取，`Cg·R ≤ R(v,z)` 处）+ trace 在 `[a, t]` 上的
  定位 `hstop`（每个 `v` 的 trace 点落在 selected 邻域 Ω：`d_v(seed(v), A(v)) ≤ d_σ(O, y) + L/√R`）
  ⇒ `[a, t]` 上阈值 `Cg·R`、常数 `Ctime'` 的 footprint。`hstop` 是"进入 Ω 之外之前停止"的那一段的
  定位：由调用方给（first-exit 时刻之后的段）。
* `timeFootprint_sameSlab_of_hdistW_CXJT0`（同 slab，序列形）：`hgood + hwin + hdistW + L → ∞`
  ⇒ `∀ D T, ∀ᶠ n`，`B_σ(y, D/√R)` 中点、同 slab 窗口 `[σ − T/R, σ]` 上任意 backward trace 的
  footprint（阈值 `Cg·R n`）。仿 `hgrad_of_selection_sameSlab_Cg_P6CD`（梯度桥）的时间分量；
  `hstop` 由 `hdistW` 逐点给（trace 用 `restrictFirst`）。
* `timeFootprint_of_eventSlabsDerivative_CXJT0`（跨 slab，J9 供给）：`EventSlabsDerivative Ccap q k`
  ⇒ trace 在 event slab（`activeStage v < k`）上的 footprint（阈值 `q`，不要定位）。
* `eventSlabsDerivative_rescaled_upto_CXJT0`：CXJB `eventSlabsDerivative_qcanSup_upto_CXJB`
  （`k = Fin.last`，time-last 阈值 `qcanSup S (time last)`；**不由** horizon 阈值单调下推）+
  `eventSlabsDerivative_rescale_P6X3` ⇒ 重标度 history 的 `EventSlabsDerivative C.Ctime (c·qcap) last`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped NNReal Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **stopped-trace footprint（`_CXJT0`，slab 无关）**：`hgood` 的时间分量 + trace 在 `[a, t]` 上
落在 selected 邻域（`hstop`）⇒ `[a, t]` 上阈值 `Cg·R` 的 footprint。不要 traced region。 -/
theorem timeFootprint_of_hgood_stopped_CXJT0 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (Kh : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) Kh.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {p : (Kh.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace Kh (Kh.activeStage aSeed) (Kh.activeStage Tn)
      (Kh.activeStage_mono haT) p)
    (y : (Kh.stageAt σ).Carrier) (R L : ℝ)
    (hgood : ∀ (v : Icc (0 : ℝ) Kh.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (Kh.stageAt v).Carrier,
        riemannianEDistOf (Kh.stageMetric (Kh.activeStage v) v)
            (seedTrace.point (Kh.activeStage v) (Kh.activeStage_mono hav)
              (Kh.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (Kh.stageMetric (Kh.activeStage σ) σ)
              (seedTrace.point (Kh.activeStage σ) (Kh.activeStage_mono has)
                (Kh.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (Kh.stageMetric (Kh.activeStage v) v) z →
        Kh.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {a t : Icc (0 : ℝ) Kh.horizon} (hat : a ≤ t) (htσ : t ≤ σ) (haS : aSeed ≤ a)
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) {z : (Kh.stageAt t).Carrier}
    (A : BackwardPointTrace Kh (Kh.activeStage a) (Kh.activeStage t) (Kh.activeStage_mono hat) z)
    (hstop : ∀ (v : Icc (0 : ℝ) Kh.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      riemannianEDistOf (Kh.stageMetric (Kh.activeStage v) v)
          (seedTrace.point (Kh.activeStage v) (Kh.activeStage_mono (haS.trans hav))
            (Kh.activeStage_mono ((hvt.trans htσ).trans hsT)))
          (A.point (Kh.activeStage v) (Kh.activeStage_mono hav) (Kh.activeStage_mono hvt)) ≤
        riemannianEDistOf (Kh.stageMetric (Kh.activeStage σ) σ)
            (seedTrace.point (Kh.activeStage σ) (Kh.activeStage_mono has)
              (Kh.activeStage_mono hsT)) y +
          ENNReal.ofReal (L / Real.sqrt R)) :
    ∀ (v : Icc (0 : ℝ) Kh.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      Kh.time (Kh.activeStage v) < (v : ℝ) → (v : ℝ) < Kh.horizon →
      Cg * R < metricScalarAt (Kh.stageMetric (Kh.activeStage v) v)
        (A.point (Kh.activeStage v) (Kh.activeStage_mono hav) (Kh.activeStage_mono hvt)) →
      |derivWithin (fun s => metricScalarAt (Kh.stageMetric (Kh.activeStage v) s)
        (A.point (Kh.activeStage v) (Kh.activeStage_mono hav)
          (Kh.activeStage_mono hvt))) (Iic (v : ℝ)) v| ≤
        Ctime' * metricScalarAt (Kh.stageMetric (Kh.activeStage v) v)
          (A.point (Kh.activeStage v) (Kh.activeStage_mono hav) (Kh.activeStage_mono hvt)) ^ 2 :=
  fun v hav hvt h1 h2 hR =>
    (hgood v (haS.trans hav) (hvt.trans htσ) (haL.trans hav) _ (hstop v hav hvt) hR.le).2 h1 h2

/-- **同 slab pre-trace footprint（`_CXJT0`，序列形）**：`hgood + hwin + hdistW + L → ∞` ⇒
`B_σ(y, D/√R)` 中点在同 slab 窗口 `[σ − T/R, σ]` 上任意 backward trace 的 footprint
（阈值 `Cg·R n`，常数 `Ctime'`）。`hgrad_of_selection_sameSlab_Cg_P6CD` 的时间分量。 -/
theorem timeFootprint_sameSlab_of_hdistW_CXJT0 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (p : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (p n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v → (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (a : Icc (0 : ℝ) (Kh n).horizon) (haσ : a ≤ σ n), (σ n : ℝ) - T / R n ≤ a →
        (Kh n).activeStage a = (Kh n).activeStage (σ n) →
      ∀ A : BackwardPointTrace (Kh n) ((Kh n).activeStage a) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono haσ) x,
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : a ≤ v) (hvt : v ≤ σ n),
        (Kh n).time ((Kh n).activeStage v) < (v : ℝ) → (v : ℝ) < (Kh n).horizon →
        Cg * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (A.point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
            ((Kh n).activeStage_mono hvt)) →
        |derivWithin (fun s => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) s)
          (A.point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
            ((Kh n).activeStage_mono hvt))) (Iic (v : ℝ)) v| ≤
          Ctime' * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (A.point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono hvt)) ^ 2 := by
  intro D T hD hT
  filter_upwards [eventually_window_scale_le_P6N hL T D, hwin T hT, hdistW D T hD hT]
    with n hsc hw hd
  intro x hx a haσ hTa hact A
  have haS : aSeed n ≤ a := show (aSeed n : ℝ) ≤ a from hw.trans hTa
  have hLT : (σ n : ℝ) - L n ^ 2 / R n ≤ (σ n : ℝ) - T / R n :=
    sub_le_sub_left (div_le_div_of_nonneg_right hsc.1 (hR n).le) _
  refine timeFootprint_of_hgood_stopped_CXJT0 (Kh n) (haT n) (hsT n) (has n) (seedTrace n) (y n)
    (R n) (L n) (hgood n) haσ le_rfl haS (hLT.trans hTa) A ?_
  intro v hav hvt
  have hvact : (Kh n).activeStage v = (Kh n).activeStage (σ n) :=
    le_antisymm ((Kh n).activeStage_mono hvt) (hact ▸ (Kh n).activeStage_mono hav)
  exact hd x hx v (haS.trans hav) hvt (hTa.trans hav) hvact
    (A.restrictFirst ((Kh n).activeStage_mono hav) ((Kh n).activeStage_mono hvt))

end ObservedHistory

namespace RetainedCoreHistory

private theorem lt_time_succ_of_activeStage_eq_CXJT0 (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (i : Fin H.eventCount) (hi : H.activeStage t = i.castSucc) :
    (t : ℝ) < H.time i.succ := by
  have hval : (H.activeStage t).val < H.eventCount := by
    rw [hi]
    exact i.isLt
  have h := H.activeStage_before_next t hval
  have he : (⟨(H.activeStage t).val + 1, Nat.succ_lt_succ hval⟩ :
      Fin (H.eventCount + 1)) = i.succ := by
    ext
    simp [hi]
  rw [he] at h
  exact h

/-- **跨 slab J9 footprint（`_CXJT0`）**：`EventSlabsDerivative Ccap q k` ⇒ 任意 backward trace 在
event slab（`activeStage v < k`）上的 footprint（阈值 `q`，不要定位）。 -/
theorem timeFootprint_of_eventSlabsDerivative_CXJT0 (K : RetainedCoreHistory.{u}) {Ccap : ℝ≥0}
    {q : ℝ} {k : Fin (K.eventCount + 1)} (hJ9 : K.EventSlabsDerivative Ccap q k)
    {a t : Icc (0 : ℝ) K.toHistory.horizon} (hat : a ≤ t)
    {z : (K.toHistory.stageAt t).Carrier}
    (A : BackwardPointTrace K.toHistory (K.toHistory.activeStage a) (K.toHistory.activeStage t)
      (K.toHistory.activeStage_mono hat) z) :
    ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      K.toHistory.activeStage v < k →
      K.toHistory.time (K.toHistory.activeStage v) < (v : ℝ) → (v : ℝ) < K.toHistory.horizon →
      q < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
        (A.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
          (K.toHistory.activeStage_mono hvt)) →
      |derivWithin (fun s => metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) s)
        (A.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
          (K.toHistory.activeStage_mono hvt))) (Iic (v : ℝ)) v| ≤
        Ccap * metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
          (A.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
            (K.toHistory.activeStage_mono hvt)) ^ 2 := by
  intro v hav hvt hvk h1 _
  have hne : K.toHistory.activeStage v ≠ Fin.last K.eventCount :=
    ne_of_lt (hvk.trans_le (Fin.le_last k))
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hne
  have hvs := lt_time_succ_of_activeStage_eq_CXJT0 K.toHistory v i hi.symm
  have key : ∀ (m : Fin (K.eventCount + 1)) (hm : i.castSucc = m)
      (hfm : K.toHistory.activeStage a ≤ m) (hml : m ≤ K.toHistory.activeStage t),
      K.toHistory.time m < v →
      q < metricScalarAt (K.toHistory.stageMetric m v) (A.point m hfm hml) →
      |derivWithin (fun s => metricScalarAt (K.toHistory.stageMetric m s) (A.point m hfm hml))
          (Iic (v : ℝ)) v| ≤
        Ccap * metricScalarAt (K.toHistory.stageMetric m v) (A.point m hfm hml) ^ 2 := by
    intro m hm hfm hml hm1 hR
    subst hm
    simp only [ObservedHistory.stageMetric_castSucc_apply] at hR ⊢
    exact hJ9 i (hi ▸ hvk) (A.point i.castSucc hfm hml) v ⟨hm1, hvs⟩ hR
  exact key _ hi _ _ h1

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

open GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **CXJB time-last 供给的重标度形（`_CXJT0`）**：`eventSlabsDerivative_qcanSup_upto_CXJB`（`k = Fin.last`，
阈值 `qcanSup S (time last)`，直接取 upto 引理，不经 horizon 阈值）+ `eventSlabsDerivative_rescale_P6X3`
⇒ 重标度 history 的 `EventSlabsDerivative C.Ctime (c·qcanSup S (time last)) (Fin.last)`。 -/
theorem eventSlabsDerivative_rescaled_upto_CXJT0 {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower) (n : ℕ) {c : ℝ}
    (hc : 0 < c) :
    ((F.tower.history n).rescale_P6N c hc).EventSlabsDerivative C.Ctime
      (c * qcanSup_P6WR S ((F.tower.history n).time (Fin.last (F.tower.history n).eventCount)))
      (Fin.last _) :=
  RetainedCoreHistory.eventSlabsDerivative_rescale_P6X3 (F.tower.history n) hc
    (eventSlabsDerivative_qcanSup_upto_CXJB S εcut Dcut mcut W hshift hoffset F hTower n
      (Fin.last _))

end GC.LongTime.Ch11
