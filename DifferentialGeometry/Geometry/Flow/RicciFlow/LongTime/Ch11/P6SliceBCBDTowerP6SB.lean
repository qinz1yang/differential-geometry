import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDSepP6SB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FreshRescaleP6JA

/-!
# 切片 BCBD：FRESH seed 参数逐 `n`（重标度 tower 帧接线；O-CH11-SLICE-BCBD G8，后缀 `_P6SB`）

G1–G7 的 FRESH 数据用常数 `nr`、`Tκ`。重标度 tower 帧（`K n := (F.tower.history (ind n)).rescale_P6N (c n)`）
里，J11ADAPT `fresh_rescale_adapter_P6JA` 给出的是 `nr(c n · w)/√(c n)` 与 `T/c n`，都随 `n` 变。本文件把
`nr`、`Tκ` 换成逐 `n` 序列（其余逐字）：
* `ObservedHistory.hkappaS_of_fresh_seq_P6SB` / `hnc_window_of_fresh_seq_P6SB`（G1 孪生）；
* `ObservedHistory.sliceBCBD_kernel_fresh_theta_ev_seq_P6SB`（G5 主定理孪生）；
* **`ObservedHistory.sliceBCBD_kernel_fresh_sep_seq_P6SB`**（G7 最终主定理孪生）；
* consumer `example`：tower 原尺度 FRESH 经 `fresh_rescale_adapter_P6JA` 付 `hWK` 槽（重标度 tower 帧）。
常数版是 `nr n := nr`、`Tκ n := Tκ` 的特例。生成器 `build-logs/scratch/O-CH11-SLICE-BCBD/gen/gen8.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **同 stage trace-κ ⇐ FRESH，逐 `n` 参数（`_P6SB`）**：G1 `hkappaS_of_fresh_P6SB` 逐字，
`nr`、`Tκ` 逐 `n`。 -/
theorem hkappaS_of_fresh_seq_P6SB {H : ℕ → ObservedHistory.{u}}
    {nr : ℕ → ℝ → ℝ} {Tκ : ℕ → ℝ} {Aκ κ r : ℝ}
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK (nr n) Aκ κ (Tκ n) (H n))
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (H n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((H n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (H n) ((H n).activeStage (aSeed n))
      ((H n).activeStage (Tn n)) ((H n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((H n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hTκ : ∀ n, Tκ n ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (H n) (Tn n) (pT n) r)
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ ballVolume ((H n).stageMetric
      ((H n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr n w ≤ r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((H n).activeStage (σ n)) ((H n).activeStage_mono (has n))
            ((H n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (H n).activeStage v = (H n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (σ n))
          ((H n).activeStage_mono hvs) x,
        riemannianEDistOf ((H n).stageMetric ((H n).activeStage v) v)
            ((seedTrace n).point ((H n).activeStage v) ((H n).activeStage_mono hav)
              ((H n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((H n).activeStage (σ n)) ((H n).activeStage_mono (has n))
                ((H n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (H n).activeStage v = (H n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v)
        ((H n).activeStage (σ n)) ((H n).activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ r / 200 →
        (H n).isParabolicallyRmControlledBall v
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' := by
  intro D T hD hT
  filter_upwards [hdistW D T hD hT, hwinF T hT, hgate, hL.eventually_ge_atTop 0] with
    n hdW hwin hg hL0
  intro x hx v hvt hvT hst tr r'' hr'' hr''le hball
  have hTv : (Tn n : ℝ) - r ^ 2 / 2 ≤ v := hwin.trans hvT
  have hav : aSeed n ≤ v := by
    change (aSeed n : ℝ) ≤ v
    rw [hclock n]
    have : 0 ≤ r ^ 2 := sq_nonneg r
    linarith
  have hvTn : v ≤ Tn n := hvt.trans (hsT n)
  have hd := hdW x hx v hav hvt hvT hst tr
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hRpos n)
  have hlt : ENNReal.ofReal (L n / Real.sqrt (R n)) <
      ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (div_pos (by linarith) hsR)]
    exact div_lt_div_of_pos_right (by linarith) hsR
  have hne : riemannianEDistOf ((H n).stageMetric ((H n).activeStage (σ n)) (σ n))
      ((seedTrace n).point ((H n).activeStage (σ n)) ((H n).activeStage_mono (has n))
        ((H n).activeStage_mono (hsT n))) (y n) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hg)
  have hmem : tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt) ∈
      riemannianBallOf ((H n).stageMetric ((H n).activeStage v) v)
        ((seedTrace n).point ((H n).activeStage v) ((H n).activeStage_mono hav)
          ((H n).activeStage_mono hvTn)) (Aκ * r) :=
    lt_of_le_of_lt hd ((ENNReal.add_lt_add_left hne hlt).trans_le hg)
  exact hWK n (Tn n) (pT n) r (hTκ n) (htimeS n) (hsmallS n) (hvolS n) (hnrS n) (aSeed n)
    (haT n) (hclock n) (seedTrace n) v hav hvTn hTv _ hmem r'' hr''.le (by linarith) hball

/-- **kernel `hnc` 槽 ⇐ FRESH，逐 `n` 参数（`_P6SB`）**：G1 `hnc_window_of_fresh_P6SB` 逐字，
`nr`、`Tκ` 逐 `n`。 -/
theorem hnc_window_of_fresh_seq_P6SB {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    {nr : ℕ → ℝ → ℝ} {Tκ : ℕ → ℝ} {Aκ κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK (nr n) Aκ κ (Tκ n) (K n).toHistory)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hTκ : ∀ n, Tκ n ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hsmallS : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr n w ≤ r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
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
    Tendsto (fun n => r / 200 *
      Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))) atTop atTop ∧
    ∀ Rad B : ℝ, ∀ᶠ n in atTop, ∀ (T : ℝ)
      (hT : ((K n).prefixAt (j n).castSucc).time
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) < T)
      (hTs : T < (K n).time (j n).succ), T ≤ t n →
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ T →
        let Bh := ((K n).prefixAt (j n).castSucc).extendHorizon T
          ((K n).prefixAt_time_last _ ▸ hT.le)
          (((K n).toHistory.event (j n)).incoming.closedPrefix T hT hTs) ((K n).event_initial (j n))
        let tm : Icc (0 : ℝ) Bh.horizon :=
          ⟨T, ((K n).prefixAt (j n).castSucc).horizon_nonneg.trans
            ((K n).prefixAt_time_last _ ▸ hT.le), le_rfl⟩
        ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
            (yG n) (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n)
              (yG n))),
        ∀ (yy : (Bh.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ r / 200 →
          Bh.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (Bh.toHistory.stageAt tm).Carrier
                (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                (riemannianBallOf (Bh.toHistory.stageMetric (Bh.toHistory.activeStage tm) tm)
                  yy b) := by
  refine ⟨?_, ?_⟩
  · have hs : Tendsto (fun n => Real.sqrt (R n)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hRlim
    refine (hs.const_mul_atTop (by positivity : (0 : ℝ) < r / 200)).congr fun n => ?_
    rw [hRn n]
  · exact hnc_window_sameStage_P6SB hjt htj σ hσ y yG hyG R hRpos hRn hκ (fun _ => r / 200)
      (hkappaS_of_fresh_seq_P6SB hWK Tn aSeed σ haT hsT has pT seedTrace y R L hRpos hL hTκ
        htimeS hsmallS hvolS hnrS hclock hwinF hgate hdistW)

/-- **G5 主定理，逐 `n` FRESH 参数（`_P6SB`）**：`sliceBCBD_kernel_fresh_theta_ev_P6SB` 逐字。 -/
theorem sliceBCBD_kernel_fresh_theta_ev_seq_P6SB
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
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
    (hnotK : ∀ᶠ n in atTop, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        t n - (K n).time i.succ ≤
          θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹)
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
    {nr : ℕ → ℝ → ℝ} {Tκ : ℕ → ℝ} {Aκ κ : ℝ} (hκ : 0 < κ)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK (nr n) Aκ κ (Tκ n) (Kh n))
    (hTκ : ∀ n, Tκ n ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ Geometry.Collapse.ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr n w ≤ r)
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
  obtain ⟨-, -, Dp, -, -, hD, -, -, -, hDn⟩ := exists_params_P6D (fun _ => (0 : ℝ))
  have hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ Dp n ∧
      Dp n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧
      (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ⟨hacc n, hDn n, by rw [hD n]; exact hrad n, hord n, le_rfl⟩
  have hnot' : ∀ᶠ n in atTop, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl =
          (((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).window x ∧
        ‖x.val‖ < Dp n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤ θ₀ *
          ((((K n).prefixLateRecords_P6N (j n).castSucc (recordsK n) i hi).static b).neck.scale
            )⁻¹ :=
    hnotK.mono fun n hn => by
      rw [hD n]
      exact (K n).not_capWindowPoint_prefix_of_late_P6N (j n).castSucc (recordsK n) (yG n) hn
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
  obtain ⟨hρ, hnc⟩ := hnc_window_of_fresh_seq_P6SB hjt htj σ hσ y yG hyG R hRpos hRlim hRn hκ hr hWK
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
  exact RetainedCoreHistory.hanchor0_lateW_local_star_theta_ev_P6SB (θcap := fun _ => θ₀)
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming)
    (s := fun n => (K n).time (j n).succ) (y := yG) (ρ := fun _ => r / 200) hεcone hκ hphi hθ₀
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hcan hpar
    (fun _ => le_rfl) hpinch hjt htj hnot' hT₀' hRt hRlimG hR0 (Cq := Cg)
    (fun n => Cg * R n) hCg0 hqC
    hslabs hder hW hgrad hnc hρ

/-- **最终主定理，逐 `n` FRESH 参数（`_P6SB`）**：G7 `sliceBCBD_kernel_fresh_sep_P6SB` 逐字，`nr`、`Tκ` 逐 `n`；
结论 = G3d 结论逐字（验收终点形）。 -/
theorem sliceBCBD_kernel_fresh_sep_seq_P6SB
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad2 : ∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
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
    {nr : ℕ → ℝ → ℝ} {Tκ : ℕ → ℝ} {Aκ κ : ℝ} (hκ : 0 < κ)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK (nr n) Aκ κ (Tκ n) (Kh n))
    (hTκ : ∀ n, Tκ n ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ Geometry.Collapse.ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr n w ≤ r)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
    (hsepT : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      θ₀ * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) / max (max 1 Cg) 1 *
        ((recordsK n i hi).static b).neck.scale)
    (hsep4 : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK n i hi).static b).neck.scale) :
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
  obtain ⟨ε₀, hε₀, hlow⟩ := exists_capWindow_scalar_lower_C11G.{u}
  have hceil := ObservedHistory.capCeiling_of_firstExit_P6SB hC20 hjt htj σ hσ y yG hyG R hRpos
    hR1 hRn Tn aSeed haT hsT has pT seedTrace L hL hgood hr hsmall hclock a₀ ha₀ hpin hRa qX T₀X
    hT₀X recordsX hOldX hcanX haccX hDmX hprotC hdσ hwin recordsK hsepT
  have haccE : ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ε₀ := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [h0.eventually (ge_mem_nhds hε₀)] with n hn
    exact (hacc n).trans hn
  have hnotKev : ∀ᶠ n in atTop, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
    filter_upwards [hceil, haccE] with n hc ha
    rintro ⟨i, hi, hl, A, b, x, h1, h2, h3⟩
    have hx : ‖x.val‖ < (p n).modelRadius := lt_of_lt_of_le h2 (hrad2 n)
    have hS := hlow ((K n).toHistory.event i) ha (le_trans (by omega) (hord n))
      ((recordsK n i hi).static b) (hcanK n i hi b) x hx
    rw [← h1] at hS
    have hC := hc i hi hl A b h3
    have hP := hsep4 n i hi b hl h3
    linarith
  exact ObservedHistory.sliceBCBD_kernel_fresh_theta_ev_seq_P6SB (hεcone := hεcone) (hC20 := hC20)
    (hphi := hphi) (hθ₀ := hθ₀) (hjt := hjt) (htj := htj) (hcanK := hcanK) (hacc := hacc)
    (hrad := fun n => le_trans (by linarith) (hrad2 n)) (hord := hord) (hpinchK0 := hpinchK0)
    (hnotK := hnotKev) (Kh := fun n => (K n).toHistory) (hKh := rfl) (σ := σ) (hσ := hσ) (y := y)
    (hyG := hyG) (R := R) (hRpos := hRpos) (hRn := hRn) (hRlt := hRlt) (hT₀ := hT₀) (Tn := Tn)
    (aSeed := aSeed) (haT := haT) (hsT := hsT) (has := has) (pT := pT) (seedTrace := seedTrace)
    (L := L) (hL := hL) (hCg := hCg) (hgood := hgood) (hwin := hwin) (hdistW := hdistW) (hr := hr)
    (hsmall := hsmall) (hclock := hclock) (a₀ := a₀) (ha₀ := ha₀) (hpin := hpin) (hRa := hRa)
    (qX := qX) (T₀X := T₀X) (hT₀X := hT₀X) (recordsX := recordsX) (hOldX := hOldX) (hcanX := hcanX)
    (haccX := haccX) (hDmX := hDmX) (hprotC := hprotC) (hdσ := hdσ) (hκ := hκ) (hWK := hWK)
    (hTκ := hTκ) (htimeS := htimeS) (hvolS := hvolS) (hnrS := hnrS) (hwinF := hwinF)
    (hgate := hgate)

end ObservedHistory

/-- consumer：重标度 tower 帧的 `hWK` 槽 ⇐ tower 原尺度 FRESH（J11ADAPT `fresh_rescale_adapter_P6JA`），
`nr n := nr(c n · ·)/√(c n)`、`Tκ n := T / c n`（= `sliceBCBD_kernel_fresh_sep_seq_P6SB` 的 `hWK` 形，
`Kh n := ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {nr : ℝ → ℝ} {A κ T : ℝ}
    (hsup : ∀ n, KappaSeedWindowFwd_C11PK nr A κ T (F.tower.history n).toHistory)
    (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) :
    ∀ n, KappaSeedWindowFwd_C11PK ((fun k w => nr (c k * w) / Real.sqrt (c k)) n) A κ
      ((fun k => T / c k) n) ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory :=
  GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup ind c hc

/-- consumer：常数 FRESH 参数是逐 `n` 版的特例（`nr n := nr`、`Tκ n := Tκ`）。 -/
example : type_of% @ObservedHistory.hnc_window_of_fresh_P6SB.{u} := by
  intro K j t hjt htj σ hσ y yG hyG R hRpos hRlim hRn nr Aκ κ Tκ r hκ hr hWK Tn aSeed haT hsT has pT
    seedTrace L hL hTκ htimeS hsmallS hvolS hnrS hclock hwinF hgate hdistW
  exact ObservedHistory.hnc_window_of_fresh_seq_P6SB (nr := fun _ => nr) (Tκ := fun _ => Tκ) hjt htj
    σ hσ y yG hyG R hRpos hRlim hRn hκ hr hWK Tn aSeed haT hsT has pT seedTrace L hL hTκ htimeS
    hsmallS hvolS hnrS hclock hwinF hgate hdistW

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
