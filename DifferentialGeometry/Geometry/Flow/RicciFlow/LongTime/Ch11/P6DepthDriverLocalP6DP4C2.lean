import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DepthDriverFullP6DP4C
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceLateCgLocalP6SD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HdistQCWireP6HQ

/-!
# 深度归纳期 4 driver 局部化接线（O-CH11-DEPTH4C2，后缀 `_P6DP4C2`）

DEPTH4C G1 的主定理 `exists_subseq_forall_depthExtendable_of_hPN_full_P6DP4C`（路 ii，位置无关支）把
`hbcadC` 留作 binder（lead (B)：DEPTH3 §3 / §4 的 producer 吃全局 Dt `hslabK` 与 `max(n+1, Q n) ≤ R n`，
合起来就是 J10 残余）。本文件在 **event 位置**（`ts n` 落在第 `j n` 个 event slab 内部）上把这个槽接到
SLICEDICH G2 的局部化 producer `hbcadC_of_hclosC_local_P6SD`（L7，P6SliceLateCgLocalP6SD:1049）：
L7 不要 `Q n ≤ R n`，只要 `n + 1 ≤ R n`，`hslabK` 只在天花板阈值 `Q n` 处经 CWP 支消费。

同时接上：
* `hdistQC` ⇐ HDISTQC `hdistQC_of_C11G3_eventually_P6HQ`（P6HdistQCWireP6HQ:121，PROVED）：`L ↦ L/4`、
  `t := ts`、`hpin` ⇐ HINIT `hpin_rescaled_of_records_P6HI`（`a₀ := 0`），event 版 (SEP) ⇐ DEPTH4C
  的全 event `hsep`（丢掉 `i < j n`）；代价是位置结构数据 `hjt`（event slab 内部下界，同 DEPTH1）。
* L7 的 `recordsF` ⇐ 塔 records 的重标度 `(records (ind n) i).rescale_P6M (c n) (hc n)`
  （参数 `pF.rescale_P6N (c n) (hc n)`，`hδF` 在该参数上陈述）。
* L7 的逐 `n` 切片数据（`hacc ≤ 1/(n+1)`、`n+1 ≤ radius`、`n+2 ≤ order`、`hcanK`、`hRn1`）推出 DEPTH4C 的
  `hcan / hord / hrad / hR / hRlim` 与精度前件 ⇒ 结论不再带 `∃ ε₀`，直接是 `∃ σ ↑, ∀ T > 0, DepthExtendable`。
* `hgood` 阈值 `4·R` ⇒ L7 的 `Cg := 4`（选择子约束 Cg ≥ 4，Q5.4）。

**final 支**（`ts n` 在末 slab）：SLICEDICH 只做了 event 支；DEPTH3 §4 `hbcadC_final_of_hclosC_P6DP3` 仍吃全局 Dt
（`hslabK` / `hderF` 在阈值 `Q n`，配 `Q n ≤ R n`）⇒ 没有局部化 producer。final 支保留 `hbcadC` binder，
即 DEPTH4C 主定理原样使用，**待 SLICEDICH final 孪生**。

剩余 PROVISIONAL（binder 逐项 owner 见主定理 docstring 的表）：`hclosC`（B2）、`hstaySlC`（SLTPROD 体 + 条件
前缀；SLICEDICH G3 sepRho producer 落地后由 G1′ 去掉）、`hslabK`@天花板（cap 输入，(α′) / HNOT）、`hsepWK`
（全部 event，(SEP-ρ)，HNOT-LOCALDT）、`hanchor0`、`hkappaC` / `hseed`、`hsurvive`、`hextend`、`hpinch`。
不声称 J10 已去，不写端点已闭。陈述由 `build-logs/scratch/O-CH11-DEPTH4C2/gen/gen_g1.py` 从 DEPTH4C G1 与 SLICEDICH G2
源文本生成（sha256 断言；L7 结论与 DEPTH4C `hbcadC` 槽在 `Kh := Hs, σ := ts, y := ys` 下逐字相等的断言）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **期 4 driver 局部化主定理（event 支，`_P6DP4C2`）**：hPN 塔帧（`K n` = 塔第 `ind n` 个 history 按 `c n`
重标度，`Hs = (K ·).toHistory`），坏点 `ts n` 在第 `j n` 个 event slab 内部（`hjt` / `htj`）。
DEPTH4C 主定理的 `hbcadC` 槽 ⇐ SLICEDICH L7 `hbcadC_of_hclosC_local_P6SD`，`hdistQC` ⇐ HDISTQC
`hdistQC_of_C11G3_eventually_P6HQ`，`recordsF` ⇐ 塔 records 的重标度，`hpin` ⇐ HINIT；精度前件由 `hacc` 消去。

binder owner：
* DEPTH4C 原 binder（逐字）：`hsurvive`（J10CORE / HNOT）、`hanchor0`（SLICE-BCBD / R4）、
  `hextend`（CX-J10DEPTH / HNOT）、`hseed` / `hkappaC`（KAPPA-ADAPT + R4）、`hpinch`（HI 传播）、
  `hsep` = hsepWK 全部 event（(SEP-ρ)，HNOT-LOCALDT）；selection / C11G3 / 塔 records 数据为 hPN 合同结构数据。
* L7 带入（kernel body 切片输入原样）：`hclosC`（B2）、`hstaySlC`（SLTPROD `hstaySl` 体 + 条件前缀；SLICEDICH G3）、
  `hslabK`@天花板 `Q n`（cap 输入，(α′) / HNOT 前缀 Dt）、`hscaleK`（(SEP-ρ⁺)，HNOT G3）、`hbirthA`、`hHI` / `a₀`
  （初始 HI，HINIT `exists_initialHI_P6WR` 给 `a₀ n := a / c n`，与 `hbirthA` 同 `a₀` 故保留）、`hδF`、`hacc` /
  `hrad` / `hord` / `hcanK` / `hRn1`（kernel 索引条款）、`hpinchK0`、`hroom` / `hdistσ` / `hκR`
  （selection slice 输入）、  常数 `hεle`、`hC2`、`κU`、`ρV`、`Aκ`、`phi`。
* 位置结构数据：`j`、`hjt`、`htj`（event slab 内部；DEPTH1 / `eventInterior_data_P6X` 同形）。
PROVISIONAL[hclosC, hstaySlC, hslabK@天花板, hsepWK, hanchor0, hkappaC, hseed, hsurvive, hextend,
hpinch]。 -/
theorem exists_subseq_forall_depthExtendable_of_hPN_local_P6DP4C2
    {P : OrientedThreeStage.{u}}
    {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (ind : ℕ → ℕ)
    (c : ℕ → ℝ)
    (hc : ∀ n, 0 < c n)
    (K : ℕ → RetainedCoreHistory.{u})
    (hKF : K = fun n => (F.tower.history (ind n)).rescale_P6N (c n) (hc n))
    (Hs : ℕ → ObservedHistory.{u})
    (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier)
    (R : ℕ → ℝ)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    {Cst : ℝ≥0}
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
    {r₀ w : ℝ}
    (hr₀ : 0 < r₀)
    (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
            ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
            (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ}
    (hκ : 0 < κ)
    (ρnc : ℕ → ℝ)
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
    {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi)
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
    {ε : ℝ}
    (hε : 0 < ε)
    (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u})
    {C1' C2' : ℝ}
    {Ctime' : ℝ≥0}
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, ts n ≤ Tn n)
    (has : ∀ n, aSeed n ≤ ts n)
    (p : ∀ n, ((Hs n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (Tn n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (L : ℕ → ℝ)
    (hL : Tendsto L atTop atTop)
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
    (hKh : Hs = fun n => (K n).toHistory)
    (r : ℕ → ℝ)
    (hhalf : ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (ts n : ℝ))
    (htime : ∀ᶠ n in atTop, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ᶠ n in atTop, GC.LongTime.hasSmallParabolicCurvature (Hs n) (Tn n) (p n) (r n))
    (hclock : ∀ᶠ n in atTop, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    {pF : CutoffParameters}
    (records : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    (q : ℕ → CutoffParameters)
    (T₀ : ℕ → ℝ)
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (q n))
    (hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        (ts n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale)
    (hT₀ : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (ts n : ℝ) - T / R n)
    {j : ∀ n, Fin (K n).eventCount}
    (hjt : ∀ᶠ n in atTop, (K n).time (j n).castSucc < ts n)
    (htj : ∀ n, (ts n : ℝ) < (K n).time (j n).succ)
    (hεle : ε ≤ coneAccuracy)
    {κU : ℝ}
    (hκU : 0 < κU)
    {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Q : ℕ → ℝ}
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF.rescale_P6N (c n) (hc n)).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (q n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (q n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (q n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime' (Q n) (Fin.last (K n).eventCount))
    (ρV : ℕ → ℝ)
    (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hC2 : 0 ≤ C2')
    {Aκ : ℝ}
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ ts n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
          ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
            ((Hs n).activeStage_mono (hsT n))) (ys n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Hs n).eventCount) (c : ((Hs n).stage j.castSucc).Carrier)
      (U : Set ((Hs n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Hs n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Hs n).time j.castSucc < τ → (τ : ℝ) < (Hs n).time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((Hs n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Hs n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Hs n).time j.castSucc < τ → (τ : ℝ) < (Hs n).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Hs n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage τ) τ)
              ((seedTrace n).point ((Hs n).activeStage τ) ((Hs n).activeStage_mono hav)
                ((Hs n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Hs n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Hs n).time j.castSucc < τ → (τ : ℝ) < (Hs n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Hs n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Hs n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κU * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Hs n).stageAt τ).Carrier
              ((Hs n).stageMetric ((Hs n).activeStage τ) τ)
              (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage τ) τ) zz b))
    (hclosC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Hs n).eventCount) (v : ℝ), (Hs n).time j'.castSucc < v →
        v < (Hs n).time j'.succ → (ts n : ℝ) + σ₁ / R n ≤ v → v ≤ ts n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Hs n).activeStage (ts n))
        (tr : BackwardPointTrace (Hs n) j'.castSucc ((Hs n).activeStage (ts n)) hjσ x₁),
      ∀ (h1 : (Hs n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Hs n).activeStage (Tn n)) (w : ((Hs n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Hs n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                ((Hs n).activeStage_mono (hsT n))) (ys n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Hs n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Hs n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Hs n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Hs n).event j').incoming.flow.scalar v w)),
        ∀ τ : ℝ, v - B / ((Hs n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
          (Hs n).time j'.castSucc < τ →
          riemannianEDistOf (((Hs n).event j').incoming.flow.base.metric τ)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
                ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                  ((Hs n).activeStage_mono (hsT n))) (ys n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hstaySlC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Hs n).eventCount) (v : ℝ), (Hs n).time j'.castSucc < v →
        v < (Hs n).time j'.succ → (ts n : ℝ) + σ₁ / R n ≤ v → v ≤ ts n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Hs n).activeStage (ts n))
        (tr : BackwardPointTrace (Hs n) j'.castSucc ((Hs n).activeStage (ts n)) hjσ x₁),
      ∀ (h1 : (Hs n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Hs n).activeStage (Tn n)) (w : ((Hs n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Hs n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                ((Hs n).activeStage_mono (hsT n))) (ys n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Hs n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Hs n).event j').incoming.flow.scalar v w →
        ∀ (i : Fin (Hs n).eventCount) (first : Fin ((Hs n).eventCount + 1))
          (hf : first ≤ i.castSucc) (hij : i.castSucc < j'.castSucc),
        ∀ z ∈ riemannianBallOf (((Hs n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Hs n).event j').incoming.flow.scalar v w)),
        ∀ Btr : BackwardPointTrace (Hs n) first j'.castSucc (hf.trans hij.le) z,
        ∀ v' ∈ Ioo ((Hs n).time i.castSucc) ((Hs n).time i.succ),
        v - B / ((Hs n).event j').incoming.flow.scalar v w ≤ v' →
        (v - v') * max (4 * R n) (((Hs n).event j').incoming.flow.scalar v z) ≤
          1 / (2 * max (Ctime' : ℝ) 1) →
        4 * R n < ((Hs n).event i).incoming.flow.scalar v' (Btr.point i.castSucc hf hij.le) →
        ∀ (h1' : (Hs n).activeStage (aSeed n) ≤ i.castSucc)
          (h2' : i.castSucc ≤ (Hs n).activeStage (Tn n)),
          riemannianEDistOf (((Hs n).event i).incoming.flow.base.metric v')
              ((seedTrace n).point i.castSucc h1' h2') (Btr.point i.castSucc hf hij.le) ≤
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
                ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                  ((Hs n).activeStage_mono (hsT n))) (ys n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ T : ℝ, 0 < T → DepthExtendable Hs ts ys R σ T := by
  subst hKF
  subst hKh
  have hR : ∀ n, 0 < R n := fun n => lt_of_lt_of_le (by positivity) (hRn1 n)
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRn1 (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hordE : ∀ᶠ n in atTop, 2 ≤ (q n).modelOrder :=
    Filter.Eventually.of_forall fun n => le_trans (Nat.le_add_left 2 n) (hord n)
  have hradE : ∀ᶠ n in atTop, StandardCap.transitionEnd + 10 < (q n).modelRadius := by
    obtain ⟨N, hN⟩ := exists_nat_gt (StandardCap.transitionEnd + 10)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith [hrad n]
  have hacc_ev : ∀ ε₀ : ℝ, 0 < ε₀ → ∀ᶠ n in atTop, (q n).modelAccuracy ≤ ε₀ := by
    intro ε₀ hε₀
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε₀
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hn 1
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hNn
    linarith [hacc n]
  have hT₀' : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (ts n : ℝ) - B / R n := by
    intro B
    filter_upwards [hT₀ (max B 1) (lt_of_lt_of_le one_pos (le_max_right B 1))] with n hn
    have hBR : B / R n ≤ max B 1 / R n := div_le_div_of_nonneg_right (le_max_left B 1) (hR n).le
    linarith
  obtain ⟨ε₁, hε₁, hQC⟩ := hdistQC_of_C11G3_eventually_P6HQ.{u}
  have hdistQC := hQC (fun n => (F.tower.history (ind n)).rescale_P6N (c n) (hc n)) j
    (fun n => (ts n : ℝ)) hjt (Filter.Eventually.of_forall htj) ts ys R r (fun n => L n / 4) Tn
    aSeed haT hsT has p seedTrace (Filter.Eventually.of_forall fun n => le_rfl) hhalf htime
    (Filter.Eventually.of_forall hR) (Filter.Tendsto.atTop_div_const (by norm_num) hL) hsmall
    hclock hRr le_rfl
    (Filter.Eventually.of_forall fun n => hpin_rescaled_of_records_P6HI F records ind c hc n) q T₀
    recordsK (Filter.Eventually.of_forall hcanK) (hacc_ev ε₁ hε₁) hordE hradE
    (fun T hT C hC => (hsep T hT C hC).mono fun n h i _ hi b => h i hi b) hT₀
  have hb := ObservedHistory.hbcadC_of_hclosC_local_P6SD (Cg := 4) (t := fun n => (ts n : ℝ))
    (pF := fun n => pF.rescale_P6N (c n) (hc n)) (p := q) (Q := Q) hεle hκU hphi (by norm_num)
    htj (fun n i => (records (ind n) i).rescale_P6M (c n) (hc n)) hHI hcanK hδF hacc hrad hord
    hscaleK hbirthA hpinchK0 hslabK _ rfl ts ys R (fun n => rfl) hR hRn1 hT₀' Tn aSeed haT hsT
    has p seedTrace L hL hwin ρV hρV hdistQC hC2 r hgood hroom hdistσ hκR hclosC hstaySlC
  obtain ⟨ε₀, hε₀, hmain⟩ := exists_subseq_forall_depthExtendable_of_hPN_full_P6DP4C F ind c hc _
    rfl _ ts ys R hR hRlim hsurvive hanchor0 hextend hr₀ hw hseed hκ ρnc hradii hkappaC hPhi
    hpinch hε hεX hεN hb Tn aSeed haT hsT has p seedTrace L hL hgood hwin rfl r hhalf htime hsmall
    hclock hRr records q T₀ recordsK (Filter.Eventually.of_forall hcanK) hordE hradE hsep hT₀
  exact hmain (hacc_ev ε₀ hε₀)


/-- **consumer（§2.3，G1）**：局部化主定理在 `T = A = 1` 处展开 `DepthExtendable`：driver 子列上深度 `1/R`、
半径 `1/√R` 的 traced region（`K₁·R` 曲率界）eventually 成立；不再有精度前件。 -/
example
    {P : OrientedThreeStage.{u}}
    {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (ind : ℕ → ℕ)
    (c : ℕ → ℝ)
    (hc : ∀ n, 0 < c n)
    (K : ℕ → RetainedCoreHistory.{u})
    (hKF : K = fun n => (F.tower.history (ind n)).rescale_P6N (c n) (hc n))
    (Hs : ℕ → ObservedHistory.{u})
    (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier)
    (R : ℕ → ℝ)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    {Cst : ℝ≥0}
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
    {r₀ w : ℝ}
    (hr₀ : 0 < r₀)
    (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
            ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
            (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ}
    (hκ : 0 < κ)
    (ρnc : ℕ → ℝ)
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
    {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi)
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
    {ε : ℝ}
    (hε : 0 < ε)
    (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u})
    {C1' C2' : ℝ}
    {Ctime' : ℝ≥0}
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, ts n ≤ Tn n)
    (has : ∀ n, aSeed n ≤ ts n)
    (p : ∀ n, ((Hs n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (Tn n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (L : ℕ → ℝ)
    (hL : Tendsto L atTop atTop)
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
    (hKh : Hs = fun n => (K n).toHistory)
    (r : ℕ → ℝ)
    (hhalf : ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (ts n : ℝ))
    (htime : ∀ᶠ n in atTop, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ᶠ n in atTop, GC.LongTime.hasSmallParabolicCurvature (Hs n) (Tn n) (p n) (r n))
    (hclock : ∀ᶠ n in atTop, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    {pF : CutoffParameters}
    (records : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    (q : ℕ → CutoffParameters)
    (T₀ : ℕ → ℝ)
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (q n))
    (hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        (ts n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale)
    (hT₀ : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (ts n : ℝ) - T / R n)
    {j : ∀ n, Fin (K n).eventCount}
    (hjt : ∀ᶠ n in atTop, (K n).time (j n).castSucc < ts n)
    (htj : ∀ n, (ts n : ℝ) < (K n).time (j n).succ)
    (hεle : ε ≤ coneAccuracy)
    {κU : ℝ}
    (hκU : 0 < κU)
    {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Q : ℕ → ℝ}
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF.rescale_P6N (c n) (hc n)).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (q n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (q n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (q n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime' (Q n) (Fin.last (K n).eventCount))
    (ρV : ℕ → ℝ)
    (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hC2 : 0 ≤ C2')
    {Aκ : ℝ}
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ ts n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
          ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
            ((Hs n).activeStage_mono (hsT n))) (ys n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Hs n).eventCount) (c : ((Hs n).stage j.castSucc).Carrier)
      (U : Set ((Hs n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Hs n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Hs n).time j.castSucc < τ → (τ : ℝ) < (Hs n).time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((Hs n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Hs n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Hs n).time j.castSucc < τ → (τ : ℝ) < (Hs n).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Hs n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage τ) τ)
              ((seedTrace n).point ((Hs n).activeStage τ) ((Hs n).activeStage_mono hav)
                ((Hs n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Hs n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Hs n).time j.castSucc < τ → (τ : ℝ) < (Hs n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Hs n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Hs n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κU * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Hs n).stageAt τ).Carrier
              ((Hs n).stageMetric ((Hs n).activeStage τ) τ)
              (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage τ) τ) zz b))
    (hclosC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Hs n).eventCount) (v : ℝ), (Hs n).time j'.castSucc < v →
        v < (Hs n).time j'.succ → (ts n : ℝ) + σ₁ / R n ≤ v → v ≤ ts n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Hs n).activeStage (ts n))
        (tr : BackwardPointTrace (Hs n) j'.castSucc ((Hs n).activeStage (ts n)) hjσ x₁),
      ∀ (h1 : (Hs n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Hs n).activeStage (Tn n)) (w : ((Hs n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Hs n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                ((Hs n).activeStage_mono (hsT n))) (ys n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Hs n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Hs n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Hs n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Hs n).event j').incoming.flow.scalar v w)),
        ∀ τ : ℝ, v - B / ((Hs n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
          (Hs n).time j'.castSucc < τ →
          riemannianEDistOf (((Hs n).event j').incoming.flow.base.metric τ)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
                ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                  ((Hs n).activeStage_mono (hsT n))) (ys n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hstaySlC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Hs n).eventCount) (v : ℝ), (Hs n).time j'.castSucc < v →
        v < (Hs n).time j'.succ → (ts n : ℝ) + σ₁ / R n ≤ v → v ≤ ts n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Hs n).activeStage (ts n))
        (tr : BackwardPointTrace (Hs n) j'.castSucc ((Hs n).activeStage (ts n)) hjσ x₁),
      ∀ (h1 : (Hs n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Hs n).activeStage (Tn n)) (w : ((Hs n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Hs n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                ((Hs n).activeStage_mono (hsT n))) (ys n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Hs n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Hs n).event j').incoming.flow.scalar v w →
        ∀ (i : Fin (Hs n).eventCount) (first : Fin ((Hs n).eventCount + 1))
          (hf : first ≤ i.castSucc) (hij : i.castSucc < j'.castSucc),
        ∀ z ∈ riemannianBallOf (((Hs n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Hs n).event j').incoming.flow.scalar v w)),
        ∀ Btr : BackwardPointTrace (Hs n) first j'.castSucc (hf.trans hij.le) z,
        ∀ v' ∈ Ioo ((Hs n).time i.castSucc) ((Hs n).time i.succ),
        v - B / ((Hs n).event j').incoming.flow.scalar v w ≤ v' →
        (v - v') * max (4 * R n) (((Hs n).event j').incoming.flow.scalar v z) ≤
          1 / (2 * max (Ctime' : ℝ) 1) →
        4 * R n < ((Hs n).event i).incoming.flow.scalar v' (Btr.point i.castSucc hf hij.le) →
        ∀ (h1' : (Hs n).activeStage (aSeed n) ≤ i.castSucc)
          (h2' : i.castSucc ≤ (Hs n).activeStage (Tn n)),
          riemannianEDistOf (((Hs n).event i).incoming.flow.base.metric v')
              ((seedTrace n).point i.castSucc h1' h2') (Btr.point i.castSucc hf hij.le) ≤
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
                ((seedTrace n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (has n))
                  ((Hs n).activeStage_mono (hsT n))) (ys n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∃ σ' : ℕ → ℕ, StrictMono σ' ∧ ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ᶠ i in atTop,
      (Hs (σ' i)).isTracedRegion (ts (σ' i)) (ys (σ' i)) (1 / Real.sqrt (R (σ' i)))
        (1 / R (σ' i)) (K₁ * R (σ' i)) := by
  obtain ⟨σ', hσ', hdep⟩ := exists_subseq_forall_depthExtendable_of_hPN_local_P6DP4C2 F ind c hc K
    hKF Hs ts ys R hRn1 hsurvive hanchor0 hextend hr₀ hw hseed hκ ρnc hradii hkappaC hPhi hpinch hε
    hεX hεN Tn aSeed haT hsT has p seedTrace L hL hgood hwin hKh r hhalf htime hsmall hclock hRr
    records q T₀ recordsK hsep hT₀ hjt htj hεle hκU hphi hHI hcanK hδF hacc hrad hord hscaleK
    hbirthA hpinchK0 hslabK ρV hρV hC2 hroom hdistσ hκR hclosC hstaySlC
  exact ⟨σ', hσ', hdep 1 one_pos 1 one_pos⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
