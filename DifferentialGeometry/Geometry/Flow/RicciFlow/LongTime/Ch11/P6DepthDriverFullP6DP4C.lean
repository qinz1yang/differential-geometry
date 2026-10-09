import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DepthDriverP6DP4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HpinRescaledP6HI

/-!
# 深度归纳期 4 收口 G1：hPN 塔帧的 driver 主定理（路 ii，O-CH11-DEPTH4C，后缀 `_P6DP4C`）

设计依据：`docs/geometrization/chapter8/out/P6-CORE-INDUCTION-DESIGN-20261008.md` §6 / §8 期 4；
lead 07:5x 裁定：
* **路 ii**：一律走 DEPTH4A G2 的位置无关支 `exists_subseq_forall_depthExtendable_of_hPN_anyPos_P6DP4`，
  不需要 event / 末 slab 子列统一。代价是 `hsepWK` 对全部 event（DC2 合同形），这与过去 event 的尺度分离
  是同一个 (SEP-ρ) 问题（owner HNOT-LOCALDT）。路 i（G1 子列统一 + 搬运）只写调用形（state）。
* 帧特化为 hPN 塔帧 `K n = (F.tower.history (ind n)).rescale_P6N (c n) (hc n)`；DEPTH1 的 `hpin` 槽
  （`a₀ := 0`）由 HINIT `hpin_rescaled_of_records_P6HI` 付，只剩全 records 族（hrecT 已有 producer）。
* `hbcadC` **仍为 driver binder**（lead (B)）：DEPTH3 的 producer 吃 `hslabK ∧ hqR`（= J10 残余，源头
  `slice_dichotomy_late_Cg_window_P6LS3`），待 SLICEDICH 车道局部化孪生后再接。
剩余 PROVISIONAL：hsepWK（全部 event）、hbcadC（⇐ hclosC/hclosCF，B2 + SLICEDICH）、hanchor0、hkappaC / hseed、
hsurvive / hextend、hpinch（driver 原 binder 逐字，owner 表见 DEPTH4A G2 文件头）。
陈述由 `build-logs/scratch/O-CH11-DEPTH4C/gen/gen_g1.py` 从 DEPTH4A G2 文本生成（sha256 断言；实参表由
binder 文本解析得到）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **路 ii 主定理（`_P6DP4C`）**：hPN 塔帧（`K n` = 塔第 `ind n` 个 history 按 `c n` 重标度）上，任意位置的
坏点族 `(ts, ys)`（含 `ts = horizon`）：driver 原 binder + selection 的 seed / `hgood` / `hwin` + C11G3 数据 +
全 records 族 ⇒ 精度 eventually ≤ ε₀ 时 `∃ σ ↑, ∀ T > 0, DepthExtendable`。`hpin` 已由 HINIT 付（`a₀ := 0`）。
PROVISIONAL[hsepWK（全部 event）, hbcadC, hanchor0, hkappaC, hseed, hsurvive, hextend, hpinch]。 -/
theorem exists_subseq_forall_depthExtendable_of_hPN_full_P6DP4C
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (K : ℕ → RetainedCoreHistory.{u})
    (hKF : K = fun n => (F.tower.history (ind n)).rescale_P6N (c n) (hc n))
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) {Cst : ℝ≥0}
    (hsurvive : ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (A / Real.sqrt (R n)),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n) →
        (Hs n).isTracedRegion (ts n) (ys n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n)
    (hextend : ∀ σ : ℕ → ℕ, StrictMono σ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Hs ts ys R σ T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Hs (σ i)).stageMetric
          ((Hs (σ i)).activeStage (ts (σ i))) (ts (σ i))) (ys (σ i))
          (A / Real.sqrt (R (σ i))),
      ∀ (w : Icc (0 : ℝ) (Hs (σ i)).horizon),
        (w : ℝ) = ts (σ i) - T' / R (σ i) →
      ∀ (hwt : w ≤ ts (σ i))
        (Bt : BackwardPointTrace (Hs (σ i)) ((Hs (σ i)).activeStage w)
          ((Hs (σ i)).activeStage (ts (σ i)))
          ((Hs (σ i)).activeStage_mono hwt) x),
        metricScalarAt ((Hs (σ i)).stageMetric ((Hs (σ i)).activeStage w) w)
          (Bt.point ((Hs (σ i)).activeStage w) le_rfl
            ((Hs (σ i)).activeStage_mono hwt)) ≤
          M * R (σ i)) →
      DepthExtendable Hs ts ys R σ (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1))))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
            ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
            (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappaC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Hs n).isParabolicallyRmControlledBall v
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))))
    {ε : ℝ} (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u})
    (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (K * R n)) →
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
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n)
    {C1' C2' : ℝ} {Ctime' : ℝ≥0}
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, ts n ≤ Tn n) (has : ∀ n, aSeed n ≤ ts n)
    (p : ∀ n, ((Hs n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (Tn n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ ts n),
      (ts n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Hs n).stageAt v).Carrier,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedTrace n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                ((Hs n).activeStage_mono (hsT n))) (ys n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) z →
        (Hs n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ ts n - T / R n)
    (hKh : Hs = fun n => (K n).toHistory) (r : ℕ → ℝ)
    (hhalf : ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (ts n : ℝ))
    (htime : ∀ᶠ n in atTop, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ᶠ n in atTop, GC.LongTime.hasSmallParabolicCurvature (Hs n) (Tn n) (p n) (r n))
    (hclock : ∀ᶠ n in atTop, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {pF : CutoffParameters}
    (records : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (q n))
    (hcan : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
      ((recordsK n i hi).static b).hasCanonicalWindow)
    (hord : ∀ᶠ n in atTop, 2 ≤ (q n).modelOrder)
    (hrad : ∀ᶠ n in atTop, StandardCap.transitionEnd + 10 < (q n).modelRadius)
    (hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        (ts n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale)
    (hT₀ : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (ts n : ℝ) - T / R n) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ((∀ᶠ n in atTop, (q n).modelAccuracy ≤ ε₀) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Hs ts ys R σ T) := by
  subst hKF
  exact exists_subseq_forall_depthExtendable_of_hPN_anyPos_P6DP4 _ Hs ts ys R hR hRlim hsurvive
    hanchor0 hextend hr₀ hw hseed hκ ρnc hradii hkappaC hPhi hpinch hε hεX hεN hbcadC Tn aSeed haT
    hsT has p seedTrace L hL hgood hwin hKh r hhalf htime hsmall hclock hRr le_rfl
    (Filter.Eventually.of_forall fun n => hpin_rescaled_of_records_P6HI F records ind c hc n) q T₀
    recordsK hcan hord hrad hsep hT₀

/-- **consumer（G1）**：路 ii 主定理在 `T = A = 1` 处展开 `DepthExtendable`：driver 子列上
深度 `1/R`、半径 `1/√R` 的 traced region（`K₁·R` 曲率界）eventually 成立。 -/
example
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (K : ℕ → RetainedCoreHistory.{u})
    (hKF : K = fun n => (F.tower.history (ind n)).rescale_P6N (c n) (hc n))
    (Hs : ℕ → ObservedHistory.{u}) (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) {Cst : ℝ≥0}
    (hsurvive : ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (A / Real.sqrt (R n)),
          metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n) →
        (Hs n).isTracedRegion (ts n) (ys n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) z ≤ Q * R n)
    (hextend : ∀ σ : ℕ → ℕ, StrictMono σ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Hs ts ys R σ T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Hs (σ i)).stageMetric
          ((Hs (σ i)).activeStage (ts (σ i))) (ts (σ i))) (ys (σ i))
          (A / Real.sqrt (R (σ i))),
      ∀ (w : Icc (0 : ℝ) (Hs (σ i)).horizon),
        (w : ℝ) = ts (σ i) - T' / R (σ i) →
      ∀ (hwt : w ≤ ts (σ i))
        (Bt : BackwardPointTrace (Hs (σ i)) ((Hs (σ i)).activeStage w)
          ((Hs (σ i)).activeStage (ts (σ i)))
          ((Hs (σ i)).activeStage_mono hwt) x),
        metricScalarAt ((Hs (σ i)).stageMetric ((Hs (σ i)).activeStage w) w)
          (Bt.point ((Hs (σ i)).activeStage w) le_rfl
            ((Hs (σ i)).activeStage_mono hwt)) ≤
          M * R (σ i)) →
      DepthExtendable Hs ts ys R σ (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1))))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
            ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
            (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappaC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Hs n).isParabolicallyRmControlledBall v
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))))
    {ε : ℝ} (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u})
    (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (K * R n)) →
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
              (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤ C * R n)
    {C1' C2' : ℝ} {Ctime' : ℝ≥0}
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, ts n ≤ Tn n) (has : ∀ n, aSeed n ≤ ts n)
    (p : ∀ n, ((Hs n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (Tn n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ ts n),
      (ts n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Hs n).stageAt v).Carrier,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedTrace n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                ((Hs n).activeStage_mono (hsT n))) (ys n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) z →
        (Hs n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ ts n - T / R n)
    (hKh : Hs = fun n => (K n).toHistory) (r : ℕ → ℝ)
    (hhalf : ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (ts n : ℝ))
    (htime : ∀ᶠ n in atTop, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ᶠ n in atTop, GC.LongTime.hasSmallParabolicCurvature (Hs n) (Tn n) (p n) (r n))
    (hclock : ∀ᶠ n in atTop, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {pF : CutoffParameters}
    (records : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (q n))
    (hcan : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
      ((recordsK n i hi).static b).hasCanonicalWindow)
    (hord : ∀ᶠ n in atTop, 2 ≤ (q n).modelOrder)
    (hrad : ∀ᶠ n in atTop, StandardCap.transitionEnd + 10 < (q n).modelRadius)
    (hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        (ts n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale)
    (hT₀ : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (ts n : ℝ) - T / R n) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ((∀ᶠ n in atTop, (q n).modelAccuracy ≤ ε₀) →
      ∃ σ' : ℕ → ℕ, StrictMono σ' ∧ ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ᶠ i in atTop,
        (Hs (σ' i)).isTracedRegion (ts (σ' i)) (ys (σ' i)) (1 / Real.sqrt (R (σ' i)))
          (1 / R (σ' i)) (K₁ * R (σ' i))) := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_subseq_forall_depthExtendable_of_hPN_full_P6DP4C F ind c hc K hKF
    Hs ts ys R hR hRlim hsurvive hanchor0 hextend hr₀ hw hseed hκ ρnc hradii hkappaC hPhi hpinch
    hε hεX hεN hbcadC Tn aSeed haT hsT has p seedTrace L hL hgood hwin hKh r hhalf htime hsmall
    hclock hRr records q T₀ recordsK hcan hord hrad hsep hT₀
  refine ⟨ε₀, hε₀, fun hacc => ?_⟩
  obtain ⟨σ', hσ', hdep⟩ := h hacc
  exact ⟨σ', hσ', hdep 1 one_pos 1 one_pos⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
