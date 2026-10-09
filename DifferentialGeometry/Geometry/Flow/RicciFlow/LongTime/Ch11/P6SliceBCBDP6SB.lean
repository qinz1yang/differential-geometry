import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SLTLocalStarAnchorP6SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDSupplyP6SB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KDataSupplyP6D
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SliceRecords_P6N
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SliceTerminalRt_P6LS

/-!
# 切片 BCBD 主定理（选出族上，kernel 帧；O-CH11-SLICE-BCBD G2，后缀 `_P6SB`）

验收终点（R-C11-20 D-20-7）：`∀ A > 0, ∃ C_A, R(σ, z) ≤ C_A·R(σ, y)` 于 `z ∈ B_σ(y, A/√R(σ, y))`。
* **`sliceBCBD_kernel_fresh_P6SB`**：结论 = SLTPROD G3d `hanchor0_eventSlab_star_firstExit_P6SP` 的结论
  逐字（kernel 帧 `K / j / t / yG`）。与 G3d 的差别：
  (i) κ：G3d 前提 `hvolK`（跨 event 全 trace、`∀ D L B`）删去，换成 FRESH 原尺度 seed 数据
  （`KappaSeedWindowFwd_C11PK` + `hTκ / htimeS / hvolS / hnrS`，与 `hsmall / hclock` 同一 seed
  `(Tn, pT, r)`）
  + 时间窗 `hwinF` + gate `hgate`；kernel `hnc` 槽由 G1 `hnc_window_of_fresh_P6SB` 付（同 stage
  `hdistW` 给 footprint）。
  (ii) `hcan / hpar / hθcap / hpinch / hnot / hT₀ / hRt` 不再作前提，改由 J10 kernel 帧自身的 binder
  生产，做法与 `P6KernelAssembleP6JK2.lean:298–336` 逐字相同：
  `hpar ⇐ hacc + hrad + hord + exists_params_P6D`，
  `hnot ⇐ hnotK`（`not_capWindowPoint_prefix_of_late_P6N`），`hpinch ⇐ hpinchK0`，
  `hcan ⇐ hcanK`（`prefixLateRecords_hcan_P6N`），
  `hRt ⇐ hwin`（`tendsto_scalar_mul_time_of_window_P6LS`）。
  (iii) c⋆ 局部导数：`hstayLocStar_of_firstExit_P6SP`（G3c）→ `hslabsLoc_cstar_of_hgood_P6SP`，与 G3d 相同。
  kernel = `RetainedCoreHistory.hanchor0_lateW_local_star_P6WA2`（`shortSLT_guarded_C11KX` 一支）。
* 状态：PROVISIONAL[hgood、CXJD 结构输入族、选点 `hdistW`、FRESH seed 数据、J10 kernel 帧 binder
  `hacc / hrad / hord / hnotK / hpinchK0 / recordsK / hcanK / hT₀`]。**不**以前提接受切片 BCBD、完整 hTR、
  完整 TimeCore；无 `hvolK`、无 `EventSlabsDerivative`、无 `hstayLoc*` / `hslabsLoc*` binder。
* consumer：`hanchor0_obs_of_kernel_P6SB`（kernel 帧 BCBD ⇒ driver
  `exists_subseq_forall_depthExtendable_kappaC_P6KA` 的 `hanchor0` 槽逐字形，
  `Hs := (K n).toHistory`、`ts := σ`、`ys := y`）。
生成器 `build-logs/scratch/O-CH11-SLICE-BCBD/gen/gen2.py`（G3d binder 块切片，源 sha256 见 DELIVERIES）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **切片 BCBD（选出族，kernel 帧，c⋆ 档，`_P6SB`）**：G3d 结论逐字；κ ⇐ FRESH（G1），kernel 帧槽 ⇐
J10 kernel 自身 binder。PROVISIONAL[hgood、CXJD 结构输入族、`hdistW`、FRESH seed 数据、kernel 帧 binder]。 -/
theorem sliceBCBD_kernel_fresh_P6SB
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hnotK : ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        t n - (K n).time i.succ ≤
          (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) {Cg : ℝ} (hCg : 2 ≤ Cg)
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
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
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
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon)
      (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (qX : ℕ → CutoffParameters) (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (recordsX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      GeometricCutoffRecord (Kh n) e (qX n))
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hcanX : ∀ n (e : Fin (Kh n).eventCount) (he : T₀X n ≤ (Kh n).time e.succ) b,
      ((recordsX n e he).static b).hasCanonicalWindow)
    (haccX : ∀ n, (qX n).modelAccuracy ≤ 1 / 2)
    (hDmX : ∀ n, StandardCap.transitionEnd + 10 < (qX n).modelRadius)
    (hprotC : ∀ n (v' : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v')
      (hvs : v' ≤ σ n) (z'' : ((Kh n).stageAt (σ n)).Carrier)
      (A : BackwardPointTrace (Kh n) ((Kh n).activeStage v')
          ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono hvs) z'')
      (e : Fin (Kh n).eventCount) (h1 : (Kh n).activeStage (aSeed n) ≤ e.castSucc)
      (h2 : e.succ ≤ (Kh n).activeStage (Tn n))
      (h3 : (Kh n).activeStage v' ≤ e.castSucc)
      (h4 : e.succ ≤ (Kh n).activeStage (σ n))
      (he : T₀X n ≤ (Kh n).time e.succ),
      (∀ (w : Icc (0 : ℝ) (Kh n).horizon) (hw : v' ≤ w) (hwσ : w ≤ σ n),
        (Kh n).time e.succ ≤ (w : ℝ) →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage w) w)
            ((seedTrace n).point ((Kh n).activeStage w)
              ((Kh n).activeStage_mono (hav.trans hw))
              ((Kh n).activeStage_mono (hwσ.trans (hsT n))))
            (A.point ((Kh n).activeStage w) ((Kh n).activeStage_mono hw)
              ((Kh n).activeStage_mono hwσ)) <
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n))
                ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n))) → ∀ b,
      (seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
          ((recordsX n e he).static b).window ''
            {w : standardCapWindow (qX n).modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
        A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
          ((recordsX n e he).static b).window ''
            {w : standardCapWindow (qX n).modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10})
    (hdσ : ∀ n, riemannianEDistOf ((Kh n).stageMetric
        ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤)
    {nr : ℝ → ℝ} {Aκ κ Tκ : ℝ} (hκ : 0 < κ)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr Aκ κ Tκ (Kh n))
    (hTκ : ∀ n, Tκ ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ Geometry.Collapse.ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
  subst hKh
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have h1 := hRlt n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hRlim : Tendsto R atTop atTop := tendsto_atTop_mono (fun n => (hRlt n).le) hnat
  have hRlimG : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
      atTop atTop := hRlim.congr fun n => hRn n
  have hRt := tendsto_scalar_mul_time_of_window_P6LS hσ hRn hRpos hwin
  obtain ⟨-, θcap, Dp, -, hθ, hD, -, -, hθcap, hDn⟩ := exists_params_P6D (fun _ => (0 : ℝ))
  have hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ Dp n ∧
      Dp n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧
      (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ⟨hacc n, hDn n, by rw [hD n]; exact hrad n, hord n, le_rfl⟩
  have hnot := fun n => (K n).not_capWindowPoint_prefix_of_late_P6N (j n).castSucc (recordsK n)
    (yG n) (hnotK n)
  have hnot' : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl =
          (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).window x ∧
        ‖x.val‖ < Dp n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤ θcap n *
          ((((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).neck.scale
            )⁻¹ :=
    fun n => by
      rw [hD n, hθ n]
      exact hnot n
  have hT₀' : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    fun B => (hT₀ B).mono fun n hn => by
      rw [← hRn n, ← hσ n]
      exact hn
  have hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
            (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi :=
    fun n => ⟨fun i => hpinchK0 n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i),
      hpinchK0 n (j n)⟩
  have hcan := fun n => (K n).prefixLateRecords_hcan_P6N (j n).castSucc (recordsK n) (hcanK n)
  have hstay := hstayLocStar_of_firstExit_P6SP hC20 (by linarith) hjt htj σ hσ y yG hyG R hRpos
    hR1 hRn Tn aSeed haT hsT has pT seedTrace L hL hgood hr hsmall hclock a₀ ha₀ hpin hRa qX T₀X
    hT₀X recordsX hOldX hcanX haccX hDmX hprotC hdσ
  have hslabs := hslabsLoc_cstar_of_hgood_P6SP (by linarith) hjt htj σ hσ y yG R hRpos Tn aSeed
    haT hsT has pT seedTrace L hL hgood hwin hstay
  obtain ⟨hρ, hnc⟩ := hnc_window_of_fresh_P6SB hjt htj σ hσ y yG hyG R hRpos hRlim hRn hκ hr hWK
    Tn aSeed haT hsT has pT seedTrace L hL hTκ htimeS hsmall hvolS hnrS hclock hwinF hgate hdistW
  have hW := hW_of_selection_Cg_P6M3 hjt htj σ hσ y yG hyG R hRpos hRn Tn aSeed haT hsT has pT
    seedTrace L hL hgood
  have hgrad := hgrad_of_selection_sameSlab_Cg_P6CD hC20 hjt htj σ hσ y yG hyG R hRpos hRn Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdistW
  have hder := hderSel_of_selection_sameSlab_Cg_P6JG3 hjt htj σ hσ y yG hyG R hRpos hRn Tn
    aSeed haT hsT has pT seedTrace L hL hgood hwin hdistW
  have hR0 : ∀ n, 0 < ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    fun n => (hRn n) ▸ hRpos n
  have hCg0 : ∀ n, 0 < Cg * R n := fun n => mul_pos (by linarith) (hRpos n)
  have hqC : ∀ n, Cg * R n ≤
      Cg * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := fun n => by
    rw [hRn n]
  exact RetainedCoreHistory.hanchor0_lateW_local_star_P6WA2
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG) (ρ := fun _ => r / 200) hεcone hκ hphi
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hcan hpar
    hθcap hpinch hjt htj hnot' hT₀' hRt hRlimG hR0 (Cq := Cg) (fun n => Cg * R n) hCg0 hqC
    hslabs hder hW hgrad hnc hρ

end ObservedHistory

namespace RetainedCoreHistory

/-- 球成员反向：`stageMetric m` ↔ incoming slab 度量（`mem_ball_incoming_P6SB` 的反向）。 -/
theorem mem_ball_incoming_rev_P6SB (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {m : Fin (K.eventCount + 1)} (hm : j.castSucc = m) (v r : ℝ)
    (z yG : (K.stage j.castSucc).Carrier) (x y : (K.stage m).Carrier) (hx : HEq x z)
    (hy : HEq y yG)
    (h : x ∈ riemannianBallOf (K.toHistory.stageMetric m v) y r) :
    z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) yG r := by
  subst hm
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  rw [ObservedHistory.stageMetric_castSucc_apply] at h
  exact h

end RetainedCoreHistory

namespace ObservedHistory

/-- **consumer：kernel 帧切片 BCBD ⇒ driver `hanchor0` 槽（`_P6SB`，PROVED，纯帧转换）**：结论 =
`exists_subseq_forall_depthExtendable_kappaC_P6KA`（KAPPA-ADAPT G3）的 `hanchor0` binder 逐字形，
`Hs := (K n).toHistory`、`ts := σ`、`ys := y`；前提 `hK` = `sliceBCBD_kernel_fresh_P6SB` 结论逐字。 -/
theorem hanchor0_obs_of_kernel_P6SB {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hK : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (A / Real.sqrt (R n)),
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          z ≤ Q * R n := by
  intro A hA
  obtain ⟨Q, hQ, hev⟩ := hK A hA
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [hev] with n hn
  intro z hz
  have hact : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6SB (j n) (σ n) (by rw [hσ n]; exact (hjt n).le)
      (by rw [hσ n]; exact htj n)
  let zG : ((K n).stage (j n).castSucc).Carrier :=
    cast (congrArg (fun m => ((K n).stage m).Carrier) hact) z
  have hzG : HEq z zG := (cast_heq _ _).symm
  rw [hσ n, hRn n] at hz
  have hz' := (K n).mem_ball_incoming_rev_P6SB (j n) hact.symm (t n) _ zG (yG n) z (y n) hzG
    (hyG n) hz
  have h1 := hn zG hz'
  rw [(K n).scalar_of_incoming_P6X (j n) hact.symm (σ n) zG z hzG, hσ n, hRn n]
  exact h1

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
