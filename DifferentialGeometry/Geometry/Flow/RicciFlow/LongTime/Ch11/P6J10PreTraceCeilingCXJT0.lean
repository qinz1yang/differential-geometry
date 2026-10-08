import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10PreTraceCXJT0

/-!
# T0 + T1 合成：pre-trace / stopped-trace ceiling（CX-J10T0 G3，后缀 `_CXJT0`）

G2 的 footprint 喂 G1 的 trace ceiling：
* `scalar_le_two_mul_stopped_ceiling_CXJT0`：stopped-trace（slab 无关）—— `hgood` 时间分量 + 定位
  `hstop` + 端点 `≤ C_ball·R` + 深度 `t − a ≤ T/R`、`2·Ctime'·Q_b·T ≤ 1` ⇒ 沿 trace `≤ 2·Q_b·R`；
* `scalar_le_two_mul_sameSlab_ceiling_CXJT0`：同 slab 序列形（`hdistW` 付定位）——
  `∀ D T, 2·Ctime'·Q_b·T ≤ 1 ⇒ ∀ᶠ n`，`B_σ(y, D/√R)` 中 `R(σ,x) ≤ C_ball·R` 的点沿同 slab 窗口
  `[σ − T/R, σ]` 上任意 backward trace `≤ 2·Q_b·R n`；
* `scalar_le_two_mul_eventSlabs_maxCeiling_CXJT0`：跨 slab 只用 J9 供给（CXJB upto，阈值 `q`）时的
  ceiling 取 `max{Q_b·R*, q}`——**不假设** `q ≤ R` 或 `q < R`，代价是 ceiling / 深度条件含 `q`。
无 `qcap < R`，无 traced region 前提，无 `hderivKC`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped NNReal Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **stopped-trace ceiling（`_CXJT0`）**：G2 stopped footprint + G1 trace 深度形。 -/
theorem scalar_le_two_mul_stopped_ceiling_CXJT0 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg Cball Qb T : ℝ}
    (Kh : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) Kh.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {p : (Kh.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace Kh (Kh.activeStage aSeed) (Kh.activeStage Tn)
      (Kh.activeStage_mono haT) p)
    (y : (Kh.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR : 0 < R)
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
    (hQb : max (max Cball Cg) 1 ≤ Qb) (hstep : 2 * Ctime' * Qb * T ≤ 1)
    {a t : Icc (0 : ℝ) Kh.horizon} (hat : a ≤ t) (htσ : t ≤ σ) (haS : aSeed ≤ a)
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) (hdepth : (t : ℝ) - a ≤ T / R)
    {z : (Kh.stageAt t).Carrier}
    (hz : metricScalarAt (Kh.stageMetric (Kh.activeStage t) t) z ≤ Cball * R)
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
      metricScalarAt (Kh.stageMetric (Kh.activeStage v) v)
        (A.point (Kh.activeStage v) (Kh.activeStage_mono hav) (Kh.activeStage_mono hvt)) ≤
        2 * (Qb * R) :=
  BackwardPointTrace.scalar_le_two_mul_ceiling_trace_scaled_CXJT0 hat A hR hQb
    (timeFootprint_of_hgood_stopped_CXJT0 Kh haT hsT has seedTrace y R L hgood hat htσ haS haL A
      hstop) hz hdepth hstep

/-- **同 slab pre-trace ceiling（`_CXJT0`，序列形）**：G2 同 slab footprint（`hdistW` 付定位）+
G1 trace 深度形。端点上界 `R(σ, x) ≤ C_ball·R n` 由调用方给（球上界）。 -/
theorem scalar_le_two_mul_sameSlab_ceiling_CXJT0 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg Cball Qb : ℝ}
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
            ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hQb : max (max Cball Cg) 1 ≤ Qb) :
    ∀ D T : ℝ, 0 < D → 0 < T → 2 * Ctime' * Qb * T ≤ 1 → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) x ≤ Cball * R n →
      ∀ (a : Icc (0 : ℝ) (Kh n).horizon) (haσ : a ≤ σ n), (σ n : ℝ) - T / R n ≤ a →
        (Kh n).activeStage a = (Kh n).activeStage (σ n) →
      ∀ A : BackwardPointTrace (Kh n) ((Kh n).activeStage a) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono haσ) x,
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : a ≤ v) (hvt : v ≤ σ n),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (A.point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
            ((Kh n).activeStage_mono hvt)) ≤ 2 * (Qb * R n) := by
  intro D T hD hT hstep
  filter_upwards [timeFootprint_sameSlab_of_hdistW_CXJT0 Kh Tn aSeed σ haT hsT has p seedTrace y
    R L hR hL hgood hwin hdistW D T hD hT] with n hn
  intro x hx hxR a haσ hTa hact A
  have hdepth : (σ n : ℝ) - a ≤ T / R n := by linarith
  exact BackwardPointTrace.scalar_le_two_mul_ceiling_trace_scaled_CXJT0 haσ A (hR n) hQb
    (hn x hx a haσ hTa hact A) hxR hdepth hstep

end ObservedHistory

namespace RetainedCoreHistory

/-- **跨 slab、仅 J9 供给的 max-ceiling（`_CXJT0`）**：trace 全在 event slab（`activeStage t < k`），
`EventSlabsDerivative Ccap q k`；ceiling `B' = max{Q_b·R*, q}`、端点 `≤ C_ball·R*`、
`Ccap·B'·(t − a) ≤ 1/2` ⇒ 沿 trace `≤ 2·B'`。**不比较** `q` 与 `R*`。 -/
theorem scalar_le_two_mul_eventSlabs_maxCeiling_CXJT0 (K : RetainedCoreHistory.{u})
    {Ccap : ℝ≥0} {q Rs Cball Qb : ℝ} {k : Fin (K.eventCount + 1)}
    (hJ9 : K.EventSlabsDerivative Ccap q k) (hRs : 0 < Rs) (hQb : max Cball 1 ≤ Qb)
    {a t : Icc (0 : ℝ) K.toHistory.horizon} (hat : a ≤ t) (htk : K.toHistory.activeStage t < k)
    {z : (K.toHistory.stageAt t).Carrier}
    (hz : metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t) z ≤ Cball * Rs)
    (A : BackwardPointTrace K.toHistory (K.toHistory.activeStage a) (K.toHistory.activeStage t)
      (K.toHistory.activeStage_mono hat) z)
    (htime : Ccap * max (Qb * Rs) q * ((t : ℝ) - a) ≤ 1 / 2) :
    ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
        (A.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
          (K.toHistory.activeStage_mono hvt)) ≤ 2 * max (Qb * Rs) q := by
  have hQ1 : 1 ≤ Qb := (le_max_right _ _).trans hQb
  have hCb : Cball ≤ Qb := (le_max_left _ _).trans hQb
  have hM : 0 < max (Qb * Rs) q := (mul_pos (by linarith) hRs).trans_le (le_max_left _ _)
  refine BackwardPointTrace.scalar_le_two_mul_ceiling_trace_CXJT0 hat A hM (le_max_right _ _)
    (fun v hav hvt => K.timeFootprint_of_eventSlabsDerivative_CXJT0 hJ9 hat A v hav hvt
      ((K.toHistory.activeStage_mono hvt).trans_lt htk))
    (hz.trans ((mul_le_mul_of_nonneg_right hCb hRs.le).trans (le_max_left _ _))) htime

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

open GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- consumer（`_CXJT0` G3）：CXJB time-last 供给（重标度）⇒ event slab trace 的 max-ceiling
`≤ 2·max{Q_b·R*, c·qcanSup S (time last)}`；不出现 `c·qcap < R`。 -/
example {pBase : CutoffParameters} {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}}
    {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower) (n : ℕ) {c : ℝ}
    (hc : 0 < c) {Rs Cball Qb : ℝ} (hRs : 0 < Rs) (hQb : max Cball 1 ≤ Qb)
    {a t : Icc (0 : ℝ) ((F.tower.history n).rescale_P6N c hc).toHistory.horizon} (hat : a ≤ t)
    (htk : ((F.tower.history n).rescale_P6N c hc).toHistory.activeStage t < Fin.last _)
    {z : (((F.tower.history n).rescale_P6N c hc).toHistory.stageAt t).Carrier}
    (hz : metricScalarAt (((F.tower.history n).rescale_P6N c hc).toHistory.stageMetric
      (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage t) t) z ≤ Cball * Rs)
    (A : BackwardPointTrace ((F.tower.history n).rescale_P6N c hc).toHistory
      (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage a)
      (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage t)
      (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage_mono hat) z)
    (htime : C.Ctime * max (Qb * Rs) (c * qcanSup_P6WR S
      ((F.tower.history n).time (Fin.last (F.tower.history n).eventCount))) *
        ((t : ℝ) - a) ≤ 1 / 2)
    (v : Icc (0 : ℝ) ((F.tower.history n).rescale_P6N c hc).toHistory.horizon) (hav : a ≤ v)
    (hvt : v ≤ t) :
    metricScalarAt (((F.tower.history n).rescale_P6N c hc).toHistory.stageMetric
        (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage v) v)
      (A.point (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage v)
        (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage_mono hav)
        (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage_mono hvt)) ≤
      2 * max (Qb * Rs) (c * qcanSup_P6WR S
        ((F.tower.history n).time (Fin.last (F.tower.history n).eventCount))) :=
  RetainedCoreHistory.scalar_le_two_mul_eventSlabs_maxCeiling_CXJT0 _
    (eventSlabsDerivative_rescaled_upto_CXJT0 S εcut Dcut mcut W hshift hoffset F hTower n hc)
    hRs hQb hat htk hz A htime v hav hvt

end GC.LongTime.Ch11
