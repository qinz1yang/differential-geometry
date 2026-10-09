import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionCoeffP6M3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceHistoryBridgeP6M

/-!
# 条件化 closed 主形的支撑件（O-CH11-P6COND G1，后缀 `_P6CD`）

* `hwitC_hderivC_of_hdistC_Cg_P6CD`：P6ANCH2 G2 条件形 witness / 导数界的阈值 `Cg·R` 副本；
* `hgrad_of_selection_sameSlab_Cg_P6CD`：基点 anchor 的 SLT 窗口梯度界，只吃 (TR₀) `hdistW`（同 slab 窗口
  的 seed 距离）——基点 anchor 在任何 traced region 之前就要用，条件形 `hdistC` 给不出（设计文档 §(i)）；
* E 层条件桥 `hwitC_seq_of_eventPrefix_P6CD` / `hbcadC_seq_of_eventPrefix_P6CD`：K 层条件形 ⇒
  `Hs n = (K n).eventPrefix (j n) (t n)` 层条件形（E → K traced 用 `isTracedRegion_of_eventPrefix'_P6M`，
  结论逐点用 `hwit_ / hbcad_of_eventPrefix_P6M`）；
* `hcondC_of_global_P6CD`：全局 trace-local 前提 ⇒ 条件形（忽略 traced 条件，`filter_mono`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped NNReal Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **条件形 `hwit` / `hderiv` ⇐ 条件形 `hdist`，阈值 `Cg·R`（`_P6CD`）**：P6ANCH2 G2
`hwitC_hderivC_of_hdistC_P6M2` 的 Cg 副本（`4 * R n` → `Cg * R n`，L9 / L10 换 `_Cg_P6L3`）；证明体逐字。
`hdistC` 只在同一 `(φ, D, T, K)` 取值。 -/
theorem hwitC_hderivC_of_hdistC_Cg_P6CD {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
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
    (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
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
    (∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
        Cg * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
        ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1' C2'
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
          Wt.capTubeHasNeckChart eps) ∧
    (∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
        Cg * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
        |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
          (Iic (v : ℝ)) v| ≤
          Ctime' * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2) := by
  have key : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvs : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvs) x,
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) →
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) := by
    intro φ hφ D T K hD hT hK htr
    filter_upwards [Filter.Eventually.filter_mono hφ.tendsto_atTop
        (eventually_window_scale_le_P6N hL T D),
      Filter.Eventually.filter_mono hφ.tendsto_atTop (hwin T hT), hdistC φ hφ D T K hD hT hK htr]
      with n hn hw hd
    exact (Kh n).hasSpatialCanonicalTimeControl_on_window_traces_Cg_P6L3 (haT n) (hsT n) (has n)
      (seedTrace n) (y n) (hR n) (hgood n) hn.1 hw hd
  refine ⟨fun φ hφ D T K hD hT hK htr => ?_, fun φ hφ D T K hD hT hK htr => ?_⟩
  · filter_upwards [key φ hφ D T K hD hT hK htr] with n hn
    intro x hx v hvt hTv _ _ tr hq
    exact (hn x hx v hvt hTv tr hq.le).1
  · filter_upwards [key φ hφ D T K hD hT hK htr] with n hn
    intro x hx v hvt hTv hvσ hage tr hq
    exact (Kh n).derivative_footprint_on_window_traces_Cg_P6L3 (y n) hn x hx v hvt hTv tr hage
      (hvσ.trans_le (σ n).2.2) hq

end ObservedHistory

namespace RetainedCoreHistory

/-- 首末 stage 指标相等时的单点 trace。 -/
private theorem exists_trace_of_stage_eq_P6CD (H : ObservedHistory.{u})
    {f l : Fin (H.eventCount + 1)} (h : f = l) (hle : f ≤ l) (x : (H.stage l).Carrier) :
    ∃ tr : BackwardPointTrace H f l hle x, HEq (tr.point f le_rfl hle) x := by
  subst h
  exact ⟨BackwardPointTrace.singleton H f x, HEq.rfl⟩

/-- slab 内部时刻的 `activeStage`。 -/
private theorem activeStage_eq_of_mem_slab_P6CD (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) (τ : Icc (0 : ℝ) K.toHistory.horizon)
    (h1 : K.time j.castSucc ≤ τ) (h2 : (τ : ℝ) < K.time j.succ) :
    K.toHistory.activeStage τ = j.castSucc :=
  (K.toHistory.mem_stageDomain_iff τ j.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (τ : ℝ) ∈ Ico (K.time j.castSucc) (K.time j.succ) from ⟨h1, h2⟩))

/-- 球成员 incoming → `stageMetric m`（`m = j.castSucc`）。 -/
private theorem mem_ball_of_incoming_P6CD (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {m : Fin (K.eventCount + 1)} (hm : j.castSucc = m) (v r : ℝ)
    (z yG : (K.stage j.castSucc).Carrier) (x y : (K.stage m).Carrier) (hx : HEq x z)
    (hy : HEq y yG)
    (h : z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) yG r) :
    x ∈ riemannianBallOf (K.toHistory.stageMetric m v) y r := by
  subst hm
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  rw [ObservedHistory.stageMetric_castSucc_apply]
  exact h

/-- 标量 `stageMetric m` ↔ incoming（`m = j.castSucc`）。 -/
private theorem scalar_of_incoming_P6CD (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {m : Fin (K.eventCount + 1)} (hm : j.castSucc = m) (v : ℝ)
    (z : (K.stage j.castSucc).Carrier) (x : (K.stage m).Carrier) (hx : HEq x z) :
    metricScalarAt (K.toHistory.stageMetric m v) x =
      (K.toHistory.event j).incoming.flow.scalar v z := by
  subst hm
  obtain rfl := eq_of_heq hx
  rw [ObservedHistory.stageMetric_castSucc_apply]
  rfl

/-- witness `stageMetric m` → incoming（`m = j.castSucc`）。 -/
private theorem witness_of_stage_P6CD (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {m : Fin (K.eventCount + 1)} (hm : j.castSucc = m) (v : ℝ) {ε C1 C2 : ℝ}
    (z : (K.stage j.castSucc).Carrier) (x : (K.stage m).Carrier) (hx : HEq x z)
    (h : ∃ W : SpatialCanonicalWitness (K.toHistory.stageMetric m v) ε C1 C2 x,
      W.capTubeHasNeckChart ε) :
    ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric v) ε C1 C2 z,
      W.capTubeHasNeckChart ε := by
  subst hm
  obtain rfl := eq_of_heq hx
  rw [ObservedHistory.stageMetric_castSucc_apply] at h
  exact h

end RetainedCoreHistory

namespace ObservedHistory

/-- **SLT 窗口 `hgrad` ⇐ selection + 同 slab 基点窗口距离 `hdistW`（`_P6CD`，阈值 `Cg·R`）**：
`hgrad_of_selection_Cg_P6M3` 的副本；`hdist` 换成 (TR₀) `hdistW`（`hdist` 体加前件 `activeStage v =
activeStage σ`：只问同 slab、单点 trace 的点），L9 直接用 `hgood`。证明其余逐字。 -/
theorem hgrad_of_selection_sameSlab_Cg_P6CD {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2')
    {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ∀ v ∈ Ioo ((K n).time (j n).castSucc) (t n),
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
      Cg * R n < ((K n).toHistory.event (j n)).incoming.flow.scalar v x →
      ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential ((K n).toHistory.event (j n)).incoming.flow v x w| ≤
          (C2'.toNNReal : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar v x *
            Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar v x) *
            Real.sqrt
              ((((K n).toHistory.event (j n)).incoming.flow.base.metric v).inner x w w) := by
  intro Rad B
  filter_upwards [eventually_window_scale_le_P6N hL (max B 1) (max Rad 1),
    hwin (max B 1) (by positivity), hdistW (max Rad 1) (max B 1) (by positivity) (by positivity)]
    with n hsc hw hd
  intro x hx v hv hBv hq w
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hσact : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6CD (j n) (σ n) (by rw [hσ n]; exact (hjt n).le)
      (by rw [hσ n]; exact htj n)
  have hv0 : 0 ≤ v := ((K n).toHistory.time_nonneg _).trans hv.1.le
  have hvH : v ≤ (K n).horizon :=
    (hv.2.trans (htj n)).le.trans ((K n).toHistory.time_le_horizon_at (j n).succ)
  let v' : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v, hv0, hvH⟩
  have hvact : (K n).toHistory.activeStage v' = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6CD (j n) v' hv.1.le (hv.2.trans (htj n))
  have hvt : v' ≤ σ n := show v ≤ (σ n : ℝ) by rw [hσ n]; exact hv.2.le
  let x' : ((K n).toHistory.stageAt (σ n)).Carrier :=
    cast (congrArg (fun m => ((K n).stage m).Carrier) hσact.symm) x
  have hxx : HEq x' x := cast_heq _ _
  have hx' : x' ∈ riemannianBallOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (max Rad 1 / Real.sqrt (R n)) := by
    refine (K n).mem_ball_of_incoming_P6CD (j n) hσact.symm (σ n) _ x (yG n) x' (y n) hxx
      (hyG n) ?_
    rw [hσ n, ← hRn n] at *
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hx
  obtain ⟨tr, htr⟩ := RetainedCoreHistory.exists_trace_of_stage_eq_P6CD (K n).toHistory
    (hvact.trans hσact.symm) ((K n).toHistory.activeStage_mono hvt) x'
  have hBv' : (σ n : ℝ) - max B 1 / R n ≤ v' := by
    change (σ n : ℝ) - max B 1 / R n ≤ v
    rw [hσ n]
    rw [← hRn n] at hBv
    have : B / R n ≤ max B 1 / R n := div_le_div_of_nonneg_right (le_max_left _ _) (hR n).le
    linarith
  have hav : aSeed n ≤ v' := hw.trans hBv'
  have hLθ : (σ n : ℝ) - L n ^ 2 / R n ≤ (σ n : ℝ) - max B 1 / R n :=
    sub_le_sub_left (div_le_div_of_nonneg_right hsc.1 (hR n).le) _
  have hptx : HEq (tr.point ((K n).toHistory.activeStage v') le_rfl
      ((K n).toHistory.activeStage_mono hvt)) x := htr.trans hxx
  have hsc' := (K n).scalar_of_incoming_P6CD (j n) hvact.symm v x _ hptx
  have hgoodv := hgood n v' hav hvt (hLθ.trans hBv') _
    (hd x' hx' v' hav hvt hBv' (hvact.trans hσact.symm) tr) (by rw [hsc']; exact hq.le)
  have hW := (K n).witness_of_stage_P6CD (j n) hvact.symm v x _ hptx hgoodv.1
  obtain ⟨W, -⟩ := hW
  rw [Real.coe_toNNReal _ hC2]
  exact W.gradient w

/-- **全局 ⇒ 条件形（`_P6CD`）**：任意 trace-local 前提 `P`（`∀ D T, ∀ᶠ n`）⇒ driver 第二版的条件形
（忽略 traced 条件；`map φ atTop ≤ atTop`）。用于数据给出的 `hderiv`。 -/
theorem hcondC_of_global_P6CD (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ) {P : ℝ → ℝ → ℕ → Prop}
    (h : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop, P D T n) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
        (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop, P D T n :=
  fun _ hφ D T _ hD hT _ _ => (h D T hD hT).filter_mono hφ.tendsto_atTop

section Seq

variable {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
  {hjt : ∀ n, (K n).time (j n).castSucc < t n} {htj : ∀ n, t n < (K n).time (j n).succ}
  {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon} {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier}
  {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
  {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {R : ℕ → ℝ}

/-- E 层 traced region（沿 `map φ atTop`）⇒ K 层（同半径 / 深度 / 曲率界）。 -/
theorem tracedC_of_eventPrefix_P6CD
    (hHs : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n)) {F : Filter ℕ} {ρ δ C : ℕ → ℝ}
    (h : ∀ᶠ n in F, (Hs n).isTracedRegion (ts n) (ys n) (ρ n) (δ n) (C n)) :
    ∀ᶠ n in F, (K n).toHistory.isTracedRegion (σ n) (y n) (ρ n) (δ n) (C n) :=
  h.mono fun n hn => (K n).isTracedRegion_of_eventPrefix'_P6M (j n) (hjt n) (htj n) (Hs n) (hHs n)
    (ts n) (σ n) (hσ n) (ys n) (y n) (hys n) hn

/-- **`_P6CD`（序列 `hwitC`，E 层）**：K 层条件形 witness ⇒ `Hs` 层条件形（driver 第二版 `hwitC` 逐字）。 -/
theorem hwitC_seq_of_eventPrefix_P6CD
    (hHs : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n)) {ε C1s C2s : ℝ} {qs : ℕ → ℝ}
    (hK : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
          (2 * D / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n)) (y n) (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (K n).toHistory.time ((K n).toHistory.activeStage v) < v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x,
          qs n < metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) ε C1s C2s
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) ε C1s C2s
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε := by
  intro φ hφ D T Kc hD hT hKc htr
  filter_upwards [hK φ hφ D T Kc hD hT hKc (tracedC_of_eventPrefix_P6CD hHs hσ hys htr)] with n hn
  exact (K n).hwit_of_eventPrefix_P6M (j n) (hjt n) (htj n) (Hs n) (hHs n) (ts n) (σ n) (hσ n)
    (ys n) (y n) (hys n) hn

/-- **`_P6CD`（序列 `hbcadC`，E 层）**：K 层条件形 BCAD ⇒ `Hs` 层条件形（driver 第二版 `hbcadC` 逐字）。 -/
theorem hbcadC_seq_of_eventPrefix_P6CD
    (hHs : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n))
    (hK : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
          (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n),
          (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvt) x₂),
          metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt))
              (tr₂.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₂.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)) ≤ C * R n) :
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (Kc * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (v : ℝ) = ts n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
            ((Hs n).activeStage_mono hvt) x₂),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤
            C * R n := by
  intro A Dd hA hDd
  obtain ⟨C, hC⟩ := hK A Dd hA hDd
  refine ⟨C, fun φ hφ σ' hσ' Dw hDw T Kc hT hKc htr => ?_⟩
  filter_upwards [hC φ hφ σ' hσ' Dw hDw T Kc hT hKc
    (tracedC_of_eventPrefix_P6CD hHs hσ hys htr)] with n hn
  exact (K n).hbcad_of_eventPrefix_P6M (j n) (hjt n) (htj n) (Hs n) (hHs n) (ts n) (σ n) (hσ n)
    (ys n) (y n) (hys n) hn

end Seq

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
