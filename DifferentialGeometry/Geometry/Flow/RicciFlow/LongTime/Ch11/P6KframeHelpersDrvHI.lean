import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverDrvW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HIPropagationP6HP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KdataRescaleP6X3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedVolumeP6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HpinRescaledP6HI
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaRegionalCenterC11Q4

/-!
# DRVHI G1：K 帧辅助引理（`_DH`）

`DrvResE2_DW`（G2）所需的四个 K 帧 producer 辅助引理，均 PROVED、无新 binder：
* `curvatureOperatorLowerBoundAt_stage_of_pinched_DH`：K 帧 `stageMetric (activeStage v) v` 的曲率算子下界
  ⇐ event slab 窗口 Φ-pinching + final slab（`restrictIncoming`）窗口 Φ-pinching（照
  `curvatureOperatorLowerBoundAt_extendAt_of_pinched_window_P6LT` 的 `Fin.lastCases`，无 extendAt）；
* `hκR_K_DH` / `hκRF_K_DH`：`hκR` / `hκRF` 槽（K 帧，event / final slab）⇐ 逐 `n` 的 FRESH 窗口
  `KappaSeedWindowFwd_C11PK (nr n) Aw κ (Tf n) (Kh n)`；`CXSK` / `P6M6` 证明的 `n` 依赖 `nr`、阈值版；
* `hseed_of_tracedKappa_smallT_DH`：`hseed_of_tracedKappa_P6M` 的小深度版（只用 `D = 1`、`v = ts`、
  深度 `T/R`，`T` 任意正）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **K 帧 stage 曲率下界 ⇐ 窗口 Φ-pinching（`_DH`，PROVED）**。 -/
theorem curvatureOperatorLowerBoundAt_stage_of_pinched_DH (K : RetainedCoreHistory.{u})
    {phi : ℝ → ℝ} {w : ℝ}
    (hev : ∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
      (K.toHistory.event i).incoming.flow
      (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici w) phi)
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    (hpG : Perelman.PhiAlmostNonnegative
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow
      (Ico (K.time (Fin.last K.eventCount)) K.horizon ∩ Ici w) phi)
    (v : Icc (0 : ℝ) K.toHistory.horizon) (hvw : w ≤ (v : ℝ)) (hvh : (v : ℝ) < K.horizon)
    (x : (K.toHistory.stage (K.toHistory.activeStage v)).Carrier) :
    curvatureOperatorLowerBoundAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) x
      (metricAlgebraicCurvatureTensorAt
        (K.toHistory.stageMetric (K.toHistory.activeStage v) v) x)
      (phi (metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) x)) := by
  have hmem := K.toHistory.activeStage_mem v
  revert x
  generalize K.toHistory.activeStage v = k at hmem ⊢
  intro x
  cases k using Fin.lastCases with
  | last =>
    have hmem' := (K.toHistory.mem_stageDomain_last v).1 hmem
    have hmet : K.toHistory.stageMetric (Fin.last K.eventCount) v =
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.base.metric v := by
      rw [ObservedHistory.stageMetric_last_of_lt (h := hfin)]
      rfl
    rw [hmet]
    exact hpG v ⟨⟨hmem'.1, hvh⟩, hvw⟩ x
  | cast j =>
    rw [ObservedHistory.stageMetric_castSucc_apply]
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at hmem
    exact hev j v ⟨hmem, hvw⟩ x

/-- **`hκR`（K 帧 event slab）⇐ 逐 `n` FRESH 窗口（`_DH`，PROVED）**：`CXSK` 的 `n` 依赖 `nr`、阈值版。 -/
theorem hκR_K_DH (Kh : ℕ → ObservedHistory.{u}) {nr : ℕ → ℝ → ℝ} {Aκ Aw κ : ℝ} (hκ : 0 ≤ κ)
    (hAw : Aκ ≤ Aw) {Tf : ℕ → ℝ}
    (hW : ∀ n, KappaSeedWindowFwd_C11PK (nr n) Aw κ (Tf n) (Kh n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (r ρV : ℕ → ℝ)
    (hTf : ∀ᶠ n in atTop, Tf n ≤ (Tn n : ℝ))
    (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hvol : ∀ n, ENNReal.ofReal (Aw⁻¹ * r n ^ 3) ≤
      ballVolume ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hρV : ∀ n, ρV n ≤ r n / 200)
    (hnr : ∀ n w, (Tn n : ℝ) - r n ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr n w ≤ r n) :
    ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
      (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b) := by
  filter_upwards [hTf] with n hn
  intro j c U a t ρU ha ht hUc hdistV τ haτ hτt hs1 hs2 z hz zz hzz b hb hbρ hball
  have hr0 : 0 < r n := (hsmall n).1
  have hav : aSeed n ≤ τ := by
    change (aSeed n : ℝ) ≤ (τ : ℝ)
    rw [hclock n]
    nlinarith [sq_nonneg (r n)]
  have hvt : τ ≤ Tn n := by
    change (τ : ℝ) ≤ (Tn n : ℝ)
    linarith
  have hcc : HEq (cast (type_eq_of_heq hzz).symm c) c := cast_heq _ _
  have hx := GC.LongTime.Ch11.edist_lt_of_center_C11Q4
    ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
    (hUc τ haτ hτt hs1 hs2 z hz zz _ hzz hcc)
    (hdistV τ haτ hτt hs1 hs2 hav hvt _ hcc)
  have hx' : riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
      ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
        ((Kh n).activeStage_mono hvt)) zz < ENNReal.ofReal (Aw * r n) :=
    lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAw hr0.le))
  have h := hW n (Tn n) (pT n) (r n) hn (htime n) (hsmall n) (hvol n)
    (hnr n) (aSeed n) (haT n) (hclock n) (seedTrace n) τ hav hvt (by linarith) zz hx' b hb.le
    (by linarith [hρV n]) hball
  rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

/-- **`hκRF`（K 帧 final slab）⇐ 逐 `n` FRESH 窗口（`_DH`，PROVED）**：`P6M6` 的 `n` 依赖 `nr`、阈值版。 -/
theorem hκRF_K_DH (Kh : ℕ → ObservedHistory.{u}) {nr : ℕ → ℝ → ℝ} {Aκ Aw κ : ℝ} (hκ : 0 ≤ κ)
    (hAw : Aκ ≤ Aw) {Tf : ℕ → ℝ}
    (hW : ∀ n, KappaSeedWindowFwd_C11PK (nr n) Aw κ (Tf n) (Kh n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (r ρV : ℕ → ℝ)
    (hTf : ∀ᶠ n in atTop, Tf n ≤ (Tn n : ℝ))
    (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hvol : ∀ n, ENNReal.ofReal (Aw⁻¹ * r n ^ 3) ≤
      ballVolume ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hρV : ∀ n, ρV n ≤ r n / 200)
    (hnr : ∀ n w, (Tn n : ℝ) - r n ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr n w ≤ r n) :
    ∀ᶠ n in atTop, ∀ (c : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier)
      (U : Set ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b) := by
  filter_upwards [hTf] with n hn
  intro c U a t ρU ha ht hUc hdistV τ haτ hτt hs1 hs2 z hz zz hzz b hb hbρ hball
  have hr0 : 0 < r n := (hsmall n).1
  have hav : aSeed n ≤ τ := by
    change (aSeed n : ℝ) ≤ (τ : ℝ)
    rw [hclock n]
    nlinarith [sq_nonneg (r n)]
  have hvt : τ ≤ Tn n := by
    change (τ : ℝ) ≤ (Tn n : ℝ)
    linarith
  have hcc : HEq (cast (type_eq_of_heq hzz).symm c) c := cast_heq _ _
  have hx := GC.LongTime.Ch11.edist_lt_of_center_C11Q4
    ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
    (hUc τ haτ hτt hs1 hs2 z hz zz _ hzz hcc)
    (hdistV τ haτ hτt hs1 hs2 hav hvt _ hcc)
  have hx' : riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
      ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
        ((Kh n).activeStage_mono hvt)) zz < ENNReal.ofReal (Aw * r n) :=
    lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAw hr0.le))
  have h := hW n (Tn n) (pT n) (r n) hn (htime n) (hsmall n) (hvol n)
    (hnr n) (aSeed n) (haT n) (hclock n) (seedTrace n) τ hav hvt (by linarith) zz hx' b hb.le
    (by linarith [hρV n]) hball
  rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

/-- **trace-local κ ⇒ `hseed`，小深度版（`_DH`，PROVED）**：`hseed_of_tracedKappa_P6M` 只在
`D = 1`、`v = ts` 处取值；这里把深度 `1/R` 换成任意正 `T/R`，使 `hkappaC` 只需在 `T` 小时的 traced
region（`hsurvive` 的 `4·Cst·Q·T ≤ 1` 区）上成立。 -/
theorem hseed_of_tracedKappa_smallT_DH {Hs : ℕ → ObservedHistory.{u}}
    {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier}
    {R : ℕ → ℝ} (hR : ∀ n, 0 < R n) {κ : ℝ} (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) {T : ℝ} (hT : 0 < T)
    (hkappa : ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (1 / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Hs n).isParabolicallyRmControlledBall v
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'')
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hctrl : ∀ᶠ n in atTop,
      (Hs n).isParabolicallyRmControlledBall (ts n) (ys n) (r₀ / Real.sqrt (R n))) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal (κ * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
          ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
          (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (r₀ / Real.sqrt (R n))) := by
  filter_upwards [hkappa, hctrl, hradii.eventually_ge_atTop r₀] with n hn hc hρ
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hy : ys n ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
      (ys n) (1 / Real.sqrt (R n)) := by
    change riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
      (ys n) < ENNReal.ofReal (1 / Real.sqrt (R n))
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (div_pos one_pos hsR)
  have h0 : (ts n : ℝ) - T / R n ≤ ts n := sub_le_self _ (div_pos hT (hR n)).le
  have hρ' : r₀ / Real.sqrt (R n) ≤ ρnc n := (div_le_iff₀ hsR).mpr hρ
  exact hn (ys n) hy (ts n) le_rfl h0
    (BackwardPointTrace.singleton (Hs n) ((Hs n).activeStage (ts n)) (ys n))
    (r₀ / Real.sqrt (R n)) (div_pos hr₀ hsR) hρ' hc

/-- **受控球 ⇐ traced region（`_DH`，PROVED）**：`isTracedRegion σ y (2/√R) (T0/R) (K1·R)` 缩半径到
`r₀/√R`（`r₀ ≤ 1`、`r₀ ≤ T0`、`r₀(K1+1) ≤ 1`）即基点受控球。 -/
theorem controlled_of_traced_DH (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) {R K1 T0 r₀ : ℝ} (hR : 0 < R) (hK1 : 0 ≤ K1) (hr₀ : 0 < r₀)
    (hr₁ : r₀ ≤ 1) (hrT : r₀ ≤ T0) (hrK : r₀ * (K1 + 1) ≤ 1)
    (h : H.isTracedRegion t p (2 * 1 / Real.sqrt R) (T0 / R) (K1 * R)) :
    H.isParabolicallyRmControlledBall t p (r₀ / Real.sqrt R) := by
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  rw [H.isParabolicallyRmControlledBall_iff_isTracedRegion]
  have hsq : (r₀ / Real.sqrt R) ^ 2 = r₀ ^ 2 / R := by rw [div_pow, Real.sq_sqrt hR.le]
  have hr2 : r₀ ^ 2 ≤ r₀ := by nlinarith
  have hKr : K1 * r₀ ^ 2 ≤ 1 := by
    have h1 : K1 * r₀ ^ 2 ≤ K1 * r₀ := mul_le_mul_of_nonneg_left hr2 hK1
    nlinarith
  refine h.mono (div_pos hr₀ hsR) ?_ (by rw [hsq]; positivity) ?_ (by positivity) ?_
  · exact div_le_div_of_nonneg_right (by linarith) hsR.le
  · rw [hsq]
    exact div_le_div_of_nonneg_right (hr2.trans hrT) hR.le
  · rw [hsq, inv_div, le_div_iff₀ (by positivity)]
    nlinarith

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
