import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6JointProducersP6CK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CwsUniformP6SN

/-!
# 联合主形冻结合同 `hgapJ`：`canonicalLateCore_of_jointD_P6CK`（O-CH11-P6CGK G3，后缀 `_P6CK`）

lead 14:2x / 14:4x：联合主形 gap 以已交 producer 为输入，G3 交付后 `hgapJ` 即 hP6b 侧冻结合同。
* `false_of_selected_eventInterior_lateHI_cond_kappaOnly_notK_P6CK`：selected 形 `hcwpL`（任意 `j'`）→
  `hnotKs`（只对含 `σ` 的 event）。
* `canonicalLateCore_of_jointWN_P6CK`（内部）：`jointW` 的 late 阈值换一般 `T₀g` + kernel 形 `hT₀`，
  `hcwpL` → `hnotKs`。
* **`canonicalLateCore_of_jointD_P6CK`（冻结）**：前置 `∃ c₀ > 0` 与 diagonal 序列
  `Cb Rn ζ δ₀ m₀ : ℝ≥0 → ℕ → _`
  （SEPTN G3 `hnotK_of_diagonal_cws_P6SN`，只依赖 `(Ctime₀, n)`，先于任何 K 数据）；`hgapJ` 逐字见
  build-logs/scratch/O-CH11-P6CGK/hgapJ.txt。映射证明里付清：
  - (CWS) `hnotKs` ⇐ 原尺度 diagonal `hnotK`（`K := Ho`、`t := c·σ`、`R := R/c`）+ event 唯一 + 时间换算；其 (SEP′)
    `hsep` ⇐ SEPTN `sepK_eventually_of_smallAtTn_P6SN`（原尺度 `Tn := Tno`、`ρn := q.neckRadius
      Tno`、`hsel4` ⇐
    prefix ceiling、`hscaleK` ⇐ `hscaleK_of_diag_P6SN`、小性 / (DLT) ⇐ gap 的 `hsmO` / `hδK`），eventually
      →
    ∀ n 用 **late 阈值抬升** `T₀g n = max T₀w (cσ+1)`（`n < N`，此时 (SEP′) 与 `hnotK` 空真）；
  - `hdistC` ⇐ G3a `hdistC_rescaled_P6CK`；`hdistW` ⇐ HDISTW（残余 `hscalW`）；κ ⇐ G2a 原尺度搬运；
  - `hacc hrad hord hδF` ⇐ diagonal 界（`ζ, δ₀ ≤ 1/(n+1)`、`n+1 ≤ Rn`、`n+2 ≤ m₀`）。
  **a₀ 约定**（lead 14:4x (1)）：`hgapJ` 用原尺度**单个**实数 `a₀`（diagonal (CWS) 要求一致 `a₀`）；重标度 frame
  内部用 `a₀/c n`（`hHI_rescale_P6X3`），不出现在合同里。**hnomId 参考族**（(2)）：合同里只出现 `hsmO`（late records
  自身的小性），不绑定 selection 后的 `d`；producer = prefix 给定的 native 族（与 SCRS 同源）的
  `recent_cutoff_smallness` + `hnomId`（`recordsK_smallness_of_native_P6CD` 形）。
陈述由 build-logs/scratch/O-CH11-P6CGK/mk_g3b.py 生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- 含同一时刻的 event 唯一（`time` 严格单调）。 -/
theorem event_eq_of_mem_P6CK (H : ObservedHistory.{u}) {j j' : Fin H.eventCount} {s : ℝ}
    (h1 : H.time j.castSucc < s) (h2 : s < H.time j.succ)
    (h1' : H.time j'.castSucc < s) (h2' : s < H.time j'.succ) : j = j' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hle : j.succ ≤ j'.castSucc := by
      rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
      exact Nat.succ_le_of_lt (Fin.lt_def.mp h)
    have := H.time_strictMono.monotone hle
    linarith
  · have hle : j'.succ ≤ j.castSucc := by
      rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
      exact Nat.succ_le_of_lt (Fin.lt_def.mp h)
    have := H.time_strictMono.monotone hle
    linarith

/-- 混合 frame 时间条件 ⇒ 原尺度：`σ − t/c ≤ θ (c s)⁻¹` ⇒ `c σ − t ≤ θ s⁻¹`。 -/
theorem time_conv_P6CK {c σ t θ s : ℝ} (hc : 0 < c) (hs : 0 < s)
    (h : σ - t / c ≤ θ * (c * s)⁻¹) : c * σ - t ≤ θ * s⁻¹ := by
  have h' := mul_le_mul_of_nonneg_left h hc.le
  have e1 : c * (σ - t / c) = c * σ - t := by
    rw [mul_sub, mul_div_cancel₀ t hc.ne']
  have e2 : c * (θ * (c * s)⁻¹) = θ * s⁻¹ := by
    field_simp
  rw [e1, e2] at h'
  exact h'

namespace ObservedHistory

/-- **selected 形（κ-only、条件距离），`hcwpL` → `hnotKs`（`_P6CK`）**：
`false_of_selected_eventInterior_lateHI_cond_kappaOnly_P6CK` 的 `hcwpL`（late cap-window 点 ⇒ Good，
对**任意**`j'`）换成 `hnotKs`：只对含 `σ n` 的 event `j'`（`time j'.castSucc < σ < time j'.succ`）
要求"无 late cap-window
点"——kernel 只在该 `j'` 处用（diagonal (CWS) producer 给的正是此形）。 -/
theorem false_of_selected_eventInterior_lateHI_cond_kappaOnly_notK_P6CK :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, C ≤ C1' → C ≤ C2' → C.toNNReal ≤ Ctime' →
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ}, (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} →
      {Q T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
      (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
      (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
      (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
        ((K n).toHistory.event i).incoming.flow
        (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount)) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (hpos : ∀ n, ∃ j : Fin (Kh n).eventCount, (Kh n).time j.castSucc < (σ n : ℝ) ∧
        (σ n : ℝ) < (Kh n).time j.succ) →
      (R : ℕ → ℝ) →
      (hRdef : ∀ n, R n =
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)) →
      (hRpos : ∀ n, 0 < R n) →
      (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n) → (hQR : ∀ n, Q n < R n) →
      (hnotKs : ∀ (n : ℕ) (j' : Fin (K n).eventCount) (yG' : ((K n).stage j'.castSucc).Carrier),
        HEq (y n) yG' → (K n).time j'.castSucc < (σ n : ℝ) → (σ n : ℝ) < (K n).time j'.succ →
        ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ j'.castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ j'.castSucc hl yG')
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) →
      {κd : ℝ} → (hκd : 0 < κd) →
      (hvolK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (ϱ / Real.sqrt (R n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            Geometry.Collapse.ballVolume
              (scaleMetric (R n) (hRpos n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ) →
      {aP : ℝ} → (haP : 0 < aP) →
      (hpinL : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon), v ≤ σ n → (σ n : ℝ) - T / R n ≤ v →
        ∀ x : ((Kh n).stageAt v).Carrier, ∃ a : ℝ, aP ≤ a ∧
          InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage v) v) a x) →
      (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (haT : ∀ n, aSeed n ≤ Tn n) →
      (hsT : ∀ n, σ n ≤ Tn n) → (has : ∀ n, aSeed n ≤ σ n) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n) →
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier) →
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)) →
      (L : ℕ → ℝ) → (hL : Tendsto L atTop atTop) →
      (Cg : ℝ) → (hCg : 2 ≤ Cg) →
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
          (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z) →
      (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      (hdistC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
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
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
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
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      {κ Aκ : ℝ} → (hκ : 0 < κ) → (r ρV : ℕ → ℝ) →
      (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) →
      (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) →
      (hdistσ : ∀ᶠ n in atTop,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n)) →
      (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
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
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) →
      (hclosG : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∀ᶠ n in atTop,
        ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
          v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
          (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
        ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
          (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              ((seedTrace n).point j'.castSucc h1 h2) w ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
              (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
          ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
            (Kh n).time j'.castSucc < τ →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n))) →
      (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
      False := by
  obtain ⟨epsW, hepsW, hB⟩ := false_of_selection_eventSlab_lateHI_closed_cond_kappaOnly_P6CK.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1' C2' Ctime'} hC1 hC2 hCt => ?_⟩
  intro Ctime phi hphi K Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord hscaleK
    hbirthA hpinchK0 hslabK Kh hKh σ y hpos R hRdef hRpos hRlt hQR hnotKs κd hκd hvolK aP haP hpinL
    Tn aSeed
    haT hsT has hT₀ pT seedTrace L hL Cg hCg hgood hwin hdistC hdistW κ Aκ hκ r ρV hρV hroom hdistσ
    hκR
    hclosG hsel
  subst hKh
  have hev := RetainedCoreHistory.eventInterior_data_P6X σ y hpos
  obtain ⟨j, yG, hjt, htj, hyG, hsc⟩ := hev
  have hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) :=
    fun n => (hRdef n).trans (hsc n)
  have hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) <
      ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) := fun n => by
    rw [← hRn n]
    exact max_lt (hRlt n) (hQR n)
  exact hB' hC1 hC2 hCt hphi (K := K) (t := fun n => (σ n : ℝ)) hjt htj (recordsK := recordsK)
    recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK hqR
    (fun n => hnotKs n (j n) (yG n) (hyG n) (hjt n) (htj n)) _ rfl σ y R (fun _ => rfl) hyG hRn
    hRpos hκd hvolK haP hpinL hT₀ Tn aSeed haT hsT has pT seedTrace L hL Cg hCg hgood hwin hdistC
    hdistW hκ r ρV hρV
    hroom hdistσ hκR hclosG hsel

/-- **联合主形内部形（`_P6CK`）**：`canonicalLateCore_of_jointW_P6CK` 的 late 阈值 `T₀w` 换成 gap 给的一般
`T₀g`（gap 多 kernel 形 `hT₀`），`hcwpL` 换成 `hnotKs`（只对含 `σ` 的 event）；kernel =
`false_of_selected_eventInterior_lateHI_cond_kappaOnly_notK_P6CK`。
供 `canonicalLateCore_of_jointD_P6CK` 映射用。 -/
theorem canonicalLateCore_of_jointWN_P6CK :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1 C2 : ℝ} {Ctime : ℝ≥0}, C ≤ C1 → C ≤ C2 → C.toNNReal ≤ Ctime →
      ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
        {q : CutoffParameters},
      AntitoneOn q.neckRadius (Ici 0) →
      GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime →
      ∀ (Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ), Monotone T₀ → Monotone Qt →
      (hgapJN : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        ∃ (p pF : ℕ → CutoffParameters) (Qs T₀g : ℕ → ℝ)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            T₀g n ≤ (Ho n).time i.succ →
              GeometricCutoffRecord (Ho n).toHistory i (p n))
          (a₀ : ℕ → ℝ),
          (∀ B : ℝ, ∀ᶠ n in atTop, max 1 (T₀g n / c n) ≤ (σ n : ℝ) - B / R n) ∧
          Nonempty (∀ n i, GeometricCutoffRecord (Ho n).toHistory i (pF n)) ∧
          (∀ n, 0 < a₀ n) ∧
          (∀ n x, InFixedHamiltonIveyRegion ((Ho n).initialMetric 0) (a₀ n) x ∧
            -3 / a₀ n ≤ metricScalarAt ((Ho n).initialMetric 0) x) ∧
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
          (∀ n (i : Fin (Ho n).eventCount), T₀g n ≤ (Ho n).time i.succ →
            (pF n).delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) ∧
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n, (Ho n).EventSlabsDerivative Ctime₀ (Qs n) (Fin.last (Ho n).eventCount)) ∧
          (∀ n, c n * Qs n < R n) ∧
          (∀ (n : ℕ) (j' : Fin (K n).eventCount) (yG' : ((K n).stage j'.castSucc).Carrier),
        HEq (y n) yG' → (K n).time j'.castSucc < (σ n : ℝ) → (σ n : ℝ) < (K n).time j'.succ →
        ¬ ∃ (i : Fin (Ho n).eventCount) (hi : T₀g n ≤ (Ho n).time i.succ)
        (hl : i.succ ≤ j'.castSucc)
        (A : BackwardPointTrace (Ho n).toHistory i.succ j'.castSucc hl yG')
        (b : ((Ho n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (c n * ((recordsK n i hi).static b).neck.scale)⁻¹) ∧
          (∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (ϱ / Real.sqrt (R n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            ballVolume (scaleMetric (R n) (hRpos n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ) ∧
          (∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
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
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) ∧
          (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
              ENNReal.ofReal (L n / Real.sqrt (R n))) ∧
          (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
            (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
            (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
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
              ENNReal.ofReal ((A + 3) * 1)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))) ∧
          (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
          v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
          (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
        ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
          (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              ((seedTrace n).point j'.castSucc h1 h2) w ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
              (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
          ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
            (Kh n).time j'.castSucc < s →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n)) →
            ∀ z : ((Kh n).stage j'.castSucc).Carrier,
              riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
                  ENNReal.ofReal
                    (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
                ((Kh n).event j').incoming.flow.scalar s z ≤
                  C * ((Kh n).event j').incoming.flow.scalar v w)) →
      (hrestP : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
        ((∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧ (σ k : ℝ) < (Kh k).horizon) ∨
          (∀ k, ¬ ∃ W : SpatialCanonicalWitness
            ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ε C1 C2 (y k), W.capTubeHasNeckChart ε)) → False) →
      GC.LongTime.Ch11.CanonicalLateCore_P6X F ε C1 C2 := by
  obtain ⟨epsW, hepsW, hB⟩ := false_of_selected_eventInterior_lateHI_cond_kappaOnly_notK_P6CK.{u}
  obtain ⟨Phi, hPhi, hK⟩ := KdataRescale_P6X3.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall' hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall' hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1 C2 Ctime} hC1 hC2 hCt => ?_⟩
  intro P g F q hanti hcan hder Ctime₀ T₀ Qt hT₀m hQm hgap hrest
  have evb : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
          let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
          ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
            (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
            (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
            (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
            (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
            (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
              ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
          let c : ℕ → ℝ := fun k => r k ^ 2
          let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
          let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
          let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
          let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
          let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
            (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
          ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
            (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
            (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
            (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
          ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
              ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
            (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
            (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
            (∀ k, R k =
              metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
            ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
            Tendsto L atTop atTop →
            (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
            (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
              (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
              ∀ z : ((Kh k).stageAt v).Carrier,
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                    ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                      ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                  riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                      ((seedTrace k).point ((Kh k).activeStage (σ k))
                        ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                    ENNReal.ofReal (L k / Real.sqrt (R k)) →
                4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
                (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
            (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
            (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
            Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
            Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
            (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
            (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
            (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
            (∀ᶠ k in atTop,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                    ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
            (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
            (σ k : ℝ) < (Kh k).time j.succ) →
            (∀ k : ℕ, (k : ℝ) + 1 < R k) →
          False := by
    intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1
      hsm hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii
      hQρ hroom hball hdistσ hev hlt
    obtain ⟨p, pF, Qs, T₀g, recordsK, a₀, hT₀', ⟨recordsF⟩, ha₀, hHI, hcanK, hδF, hacc, hrad, hord,
      hscaleK,
      hbirthA, hslabK, hQs, hcwpL, ⟨κd, hκd, hvolK⟩, hdistC, hdistW, ⟨κ, ρV, hκ, hρV, hκR⟩,
      hscalU⟩ :=
      hgap A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm hT₀l seedTrace
        σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ hroom hball
        hdistσ hev hlt
    obtain ⟨hHI', hcanK', hδF', hscaleK', hbirthA', hpinch', hslab'⟩ :=
      hK Ho c hc Ctime₀ Qs T₀g p pF recordsK a₀ recordsF
        ha₀ hHI hcanK hδF hscaleK hbirthA hslabK
    -- κ-only C2：迟窗 pinching（`aP = 1`）⇐ G3 `hpin_rescale_P6X3`（年龄 `0 + v`）+ `1 ≤ aSeed ≤ σ − T/R`
    have hpinL : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon), v ≤ σ n → (σ n : ℝ) - T / R n ≤ v →
        ∀ x : ((Kh n).stageAt v).Carrier, ∃ a : ℝ, 1 ≤ a ∧
          InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage v) v) a x := by
      intro T hT
      filter_upwards [hwin T hT] with n hn
      intro v _ hv x
      exact ⟨0 + (v : ℝ), by linarith [h1 n],
        (Ho n).toHistory.hpin_rescale_P6X3 (hc n) (recordsF n) (ha₀ n) (hHI n) v x⟩
    have hR1 : ∀ n, 1 ≤ R n := fun n => by
      have := hRr n
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hRr1 : Tendsto (fun n => R n * (fun _ : ℕ => (1 : ℝ)) n ^ 2) atTop atTop := by
      simp only [one_pow, mul_one]
      exact tendsto_atTop_mono hRr (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hlateR : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n) := by
      intro T hT
      filter_upwards [hwin T hT] with n hn
      have ha1 : (1 : ℝ) ≤ (σ n : ℝ) - T / R n := (h1 n).trans hn
      calc (1 : ℝ) ≤ R n * 1 := by linarith [hR1 n]
        _ ≤ R n * ((σ n : ℝ) - T / R n) := mul_le_mul_of_nonneg_left ha1 (by linarith [hR1 n])
    have hclosG := hclosG_of_firstExit_P6M4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hRpos
      (fun _ => 1) hL hsm hclock hRr1 hwin hlateR le_rfl
      (fun n => (Ho n).toHistory.hpin_rescale_P6X3 (hc n) (recordsF n) (ha₀ n) (hHI n)) hscalU
    refine hB' hC1 hC2 hCt hPhi (K := K) (Q := fun n => c n * Qs n)
      (T₀ := fun n => max 1 (T₀g n / c n)) (p := fun n => (p n).rescale_P6N (c n) (hc n))
      (pF := fun n => (pF n).rescale_P6N (c n) (hc n)) (a₀ := fun n => a₀ n / c n)
      (recordsK := fun n => (Ho n).recordsKRescale_P6X3 (hc n) (recordsK n))
      (fun n i => (recordsF n i).rescale_P6M (c n) (hc n)) hHI' hcanK' hδF' hacc hrad hord hscaleK'
      hbirthA' hpinch' hslab' Kh rfl σ y hev R hRdef hRpos hlt hQs
      (fun n j' yG' hy hjt' htj' hcw => ?_) hκd hvolK one_pos hpinL Tn aSeed haT hsT has hT₀' pT
      seedTrace L hL 4 (by norm_num)
      hgood hwin hdistC hdistW (Aκ := A + 3) hκ (fun _ => 1) ρV hρV hroom hdistσ hκR hclosG
      hsel
    obtain ⟨i, hi, hl, A', b, x, hA', hx, ht⟩ := hcw
    have hi' : T₀g n ≤ (Ho n).time i.succ :=
      RetainedCoreHistory.le_time_of_rescale_P6X3 (hc n) (t := (Ho n).time i.succ) hi
    refine hcwpL n j' yG' hy hjt' htj' ⟨i, hi', hl, (Ho n).traceOfRescale_P6N (c n) (hc n) A', b, x,
      ?_, hx,
      ?_⟩
    · exact hA'.trans (congrArg (fun w => w x)
        (((recordsK n i hi').static b).rescale_P6M_window (c n) (hc n)))
    · exact ht.trans_eq (congrArg (fun z => (1 - 1 / ((n : ℝ) + 2)) * z⁻¹)
        (((recordsK n i hi').static b).rescale_P6M_scale (c n) (hc n)))
  refine GC.LongTime.Ch11.canonicalLateCore_of_normalized_prefix_P6X3 hanti hcan hder T₀ Qt ?_
  intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1
    hsm hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii
    hQρ hroom hball hdistσ
  have key : ∀ φ : ℕ → ℕ, StrictMono φ →
      ((∀ k, ∃ j : Fin (Kh (φ k)).eventCount, (Kh (φ k)).time j.castSucc < (σ (φ k) : ℝ) ∧
          (σ (φ k) : ℝ) < (Kh (φ k)).time j.succ) ∧ ∀ k : ℕ, (k : ℝ) + 1 < R (φ k)) ∨
        (∀ k, (Kh (φ k)).time (Fin.last (Kh (φ k)).eventCount) < (σ (φ k) : ℝ) ∧
          (σ (φ k) : ℝ) < (Kh (φ k)).horizon) ∨
        (∀ k, ¬ ∃ W : SpatialCanonicalWitness ((Kh (φ k)).stageMetric
            ((Kh (φ k)).activeStage (σ (φ k))) (σ (φ k))) ε C1 C2 (y (φ k)),
          W.capTubeHasNeckChart ε) → False := by
    intro φ hφ hcls
    have hφt := hφ.tendsto_atTop
    have hlate' : ∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno (φ k) : ℝ) := fun k =>
      (GC.LongTime.Ch11.natCast_succ_le_of_strictMono_P6X hφ k).trans (hlate (φ k))
    have hRr' : ∀ k : ℕ, (k : ℝ) + 1 ≤ R (φ k) := fun k =>
      (GC.LongTime.Ch11.natCast_succ_le_of_strictMono_P6X hφ k).trans (hRr (φ k))
    have hT₀l' : ∀ k, T₀ k ≤ c (φ k) * (aSeed (φ k) : ℝ) := fun k =>
      (hT₀m (hφ.id_le k)).trans (hT₀l (φ k))
    have hQR' : ∀ k, Qt k < R (φ k) := fun k => (hQm (hφ.id_le k)).trans_lt (hQR (φ k))
    rcases hcls with ⟨hev, hlt⟩ | hcls'
    · exact evb A hA (fun k => ind (φ k)) (fun k => Tno (φ k)) (fun k => pTo (φ k))
        (fun k => r (φ k)) (fun k => hr (φ k)) hlate' (fun k => htime (φ k))
        (fun k => hsmallo (φ k)) (fun k => hvolo (φ k)) (fun k => aSeed (φ k))
        (fun k => haT (φ k)) (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => hsm (φ k))
        hT₀l' (fun k => seedTrace (φ k)) (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k))
        (fun k => hsT (φ k)) (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k))
        (fun k => hRpos (φ k)) hRr' hQR' (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
        (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
        (hroomT.comp hφt) (hradii.comp hφt) (fun k => hQρ (φ k)) (fun k => hroom (φ k))
        (fun k => hball (φ k)) (hφt.eventually hdistσ) hev hlt
    · exact hrest A hA (fun k => ind (φ k)) (fun k => Tno (φ k)) (fun k => pTo (φ k))
        (fun k => r (φ k)) (fun k => hr (φ k)) hlate' (fun k => htime (φ k))
        (fun k => hsmallo (φ k)) (fun k => hvolo (φ k)) (fun k => aSeed (φ k))
        (fun k => haT (φ k)) (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => hsm (φ k))
        hT₀l' (fun k => seedTrace (φ k)) (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k))
        (fun k => hsT (φ k)) (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k))
        (fun k => hRpos (φ k)) hRr' hQR' (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
        (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
        (hroomT.comp hφt) (hradii.comp hφt) (fun k => hQρ (φ k)) (fun k => hroom (φ k))
        (fun k => hball (φ k)) (hφt.eventually hdistσ) hcls'
  obtain ⟨ψ, hψ, hcls⟩ := exists_strictMono_interior_or_boundary_P6S (Kh := Kh) σ y hsel
  rcases hcls with hev | hfin | hbd
  · have hs : StrictMono fun k : ℕ => ψ (k + 1) :=
      hψ.comp fun a b hab => Nat.add_lt_add_right hab 1
    refine key (fun k => ψ (k + 1)) hs (Or.inl ⟨fun k => hev (k + 1), fun k => ?_⟩)
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ (ψ (k + 1) : ℝ) := by exact_mod_cast hψ.id_le (k + 1)
    have hk2 := hRr (ψ (k + 1))
    push_cast at hk1
    linarith
  · exact key ψ hψ (Or.inr (Or.inl hfin))
  · exact key ψ hψ (Or.inr (Or.inr hbd))

/-- **联合主形冻结合同（`_P6CK`）**：normalized + retained + lateHI + 条件距离 + κ-only（原尺度投影）+ S6(b)
+ producer 已接（diagonal (CWS) / (SEP′) / HDISTC / HDISTW）。`hgapJ` 逐字：
build-logs/scratch/O-CH11-P6CGK/hgapJ.txt。 -/
theorem canonicalLateCore_of_jointD_P6CK :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ),
    (∀ (C : ℝ≥0) (n : ℕ), 0 < Cb C n ∧ Cb C n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
    (∀ (C : ℝ≥0) (n : ℕ), 0 < ζ C n ∧ ζ C n ≤ 1 / ((n : ℝ) + 1)) ∧
    (∀ (C : ℝ≥0) (n : ℕ), 0 < δ₀ C n ∧ δ₀ C n ≤ 1 / ((n : ℝ) + 1)) ∧
    (∀ (C : ℝ≥0) (n : ℕ), (n : ℝ) + 1 ≤ Rn C n) ∧ (∀ (C : ℝ≥0) (n : ℕ), n + 2 ≤ m₀ C n) ∧
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1 C2 : ℝ} {Ctime : ℝ≥0}, C ≤ C1 → C ≤ C2 → C.toNNReal ≤ Ctime →
      ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
        {q : CutoffParameters},
      AntitoneOn q.neckRadius (Ici 0) →
      GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime →
      ∀ (Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ), Monotone T₀ → Monotone Qt →
      (hgapJ : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        ∃ (p pF : ℕ → CutoffParameters) (Qs : ℕ → ℝ)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
              GeometricCutoffRecord (Ho n).toHistory i (p n))
          (a₀ : ℝ),
          Nonempty (∀ n i, GeometricCutoffRecord (Ho n).toHistory i (pF n)) ∧
          0 < a₀ ∧
          (∀ n x, InFixedHamiltonIveyRegion ((Ho n).initialMetric 0) a₀ x ∧
            -3 / a₀ ≤ metricScalarAt ((Ho n).initialMetric 0) x) ∧
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
          (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
            i.succ →
            (pF n).delta ((Ho n).time i.succ) ≤ δ₀ Ctime₀ n) ∧
          (∀ n : ℕ, (p n).modelAccuracy ≤ ζ Ctime₀ n) ∧
          (∀ n : ℕ, Rn Ctime₀ n ≤ (p n).modelRadius) ∧
          (∀ n : ℕ, m₀ Ctime₀ n ≤ (p n).modelOrder) ∧
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n i hi b, max (Qs n) 1 ≤ Cb Ctime₀ n * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n, (Ho n).EventSlabsDerivative Ctime₀ (Qs n) (Fin.last (Ho n).eventCount)) ∧
          (∀ n, c n * Qs n < R n) ∧
          (∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Ho n).toHistory.stageMetric
            ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).uncastRescale_P6CK (hc n) (σ n) (y n)) (D / Real.sqrt (R n / c n)),
        ∀ (v : Icc (0 : ℝ) (Ho n).toHistory.horizon)
          (hvt : v ≤ (Ho n).unscaleTime_P6X (hc n) (σ n)),
          (((Ho n).unscaleTime_P6X (hc n) (σ n) : Icc (0 : ℝ) (Ho n).toHistory.horizon) : ℝ) -
            B / (R n / c n) ≤ v →
        ∀ tr : BackwardPointTrace (Ho n).toHistory ((Ho n).toHistory.activeStage v)
          ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
          ((Ho n).toHistory.activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
          (Ho n).toHistory.isParabolicallyRmControlledBall v
            (tr.point ((Ho n).toHistory.activeStage v) le_rfl
              ((Ho n).toHistory.activeStage_mono hvt))
            (ϱ / Real.sqrt (R n / c n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            ballVolume (scaleMetric (R n / c n) (div_pos (hRpos n) (hc n))
              ((Ho n).toHistory.stageMetric ((Ho n).toHistory.activeStage v) v))
              (tr.point ((Ho n).toHistory.activeStage v) le_rfl
                ((Ho n).toHistory.activeStage_mono hvt)) ϱ) ∧
          (∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
            (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) ∧
          (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (Ho n).eventCount),
            (Ho n).time i.succ ∈ Icc (τ / 2) τ →
            ∀ (hi : max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ) h,
              (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius τ) ∧
          (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stageAt (σ n)).Carrier,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
                ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
              metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n) ∧
          (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
            (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
            (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
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
              ENNReal.ofReal ((A + 3) * 1)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))) ∧
          (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
          v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
          (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
        ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
          (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              ((seedTrace n).point j'.castSucc h1 h2) w ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
              (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
          ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
            (Kh n).time j'.castSucc < s →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n)) →
            ∀ z : ((Kh n).stage j'.castSucc).Carrier,
              riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
                  ENNReal.ofReal
                    (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
                ((Kh n).event j').incoming.flow.scalar s z ≤
                  C * ((Kh n).event j').incoming.flow.scalar v w)) →
      (hrestP : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
        ((∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧ (σ k : ℝ) < (Kh k).horizon) ∨
          (∀ k, ¬ ∃ W : SpatialCanonicalWitness
            ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ε C1 C2 (y k), W.capTubeHasNeckChart ε)) → False) →
      GC.LongTime.Ch11.CanonicalLateCore_P6X F ε C1 C2 := by
  obtain ⟨c₀, hc₀, hall⟩ := hnotK_of_diagonal_cws_P6SN.{u}
  choose Cb Rn ζ δ₀ m₀ hCb hζ hδ₀ hRn hm₀ hdiag using hall
  refine ⟨c₀, hc₀, Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ₀, hRn, hm₀, ?_⟩
  obtain ⟨epsW, hepsW, hB⟩ := canonicalLateCore_of_jointWN_P6CK.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1 C2 Ctime} hC1 hC2 hCt => ?_⟩
  intro P g F q hanti hcan hder Ctime₀ T₀ Qt hT₀m hQm hgap hrest
  refine hB' hC1 hC2 hCt hanti hcan hder Ctime₀ T₀ Qt hT₀m hQm ?_ hrest
  intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1
    hsm hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii
    hQρ hroom hball hdistσ hev hlt
  obtain ⟨p, pF, Qs, recordsK, a₀, ⟨recordsF⟩, ha₀, hHI, hcanK, hδF, hacc, hrad, hord, hscaleK,
    hbirth, hbirthA, hslabK, hQs, ⟨κd, hκd, hO⟩, hδK, hsmO, hscalW, hκg, hscalU⟩ :=
    hgap A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm hT₀l seedTrace
      σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ hroom hball
      hdistσ hev hlt
  obtain ⟨jc, yGc, hjtc, htjc, hyGc, hscc⟩ :=
    RetainedCoreHistory.eventInterior_data_P6X (K := K) σ y hev
  have hcr : ∀ n, c n = r n ^ 2 := fun _ => rfl
  have hcTn : ∀ n, c n * (Tn n : ℝ) = Tno n := fun n => (Ho n).mul_rescaleTime_P6X (hc n) (Tno n)
  have hTnoT : Tendsto (fun n => (Tno n : ℝ)) atTop atTop :=
    tendsto_atTop_mono hlate (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hjtO : ∀ n, (Ho n).time (jc n).castSucc < c n * σ n := fun n => by
    have h := hjtc n
    change (Ho n).time (jc n).castSucc / c n < σ n at h
    rw [div_lt_iff₀ (hc n)] at h
    linarith [mul_comm (σ n : ℝ) (c n)]
  have htjO : ∀ n, c n * σ n < (Ho n).time (jc n).succ := fun n => by
    have h := htjc n
    change (σ n : ℝ) < (Ho n).time (jc n).succ / c n at h
    rw [lt_div_iff₀ (hc n)] at h
    linarith [mul_comm (σ n : ℝ) (c n)]
  have hRO : ∀ n, R n / c n =
      ((Ho n).toHistory.event (jc n)).incoming.flow.scalar (c n * σ n) (yGc n) := fun n => by
    have e : ((K n).toHistory.event (jc n)).incoming.flow.scalar (σ n) (yGc n) =
        c n * ((Ho n).toHistory.event (jc n)).incoming.flow.scalar (c n * σ n) (yGc n) :=
      RetainedCoreHistory.rescale_scalar_P6N ((Ho n).toHistory.event (jc n)).incoming (c n) (hc n)
        (σ n) (yGc n)
    rw [(hRdef n).trans (hscc n), e, mul_div_cancel_left₀ _ (hc n).ne']
  have hhalfO : ∀ n, (Tno n : ℝ) - r n ^ 2 / 2 ≤ c n * σ n := fun n => by
    have h0 : 0 ≤ L n ^ 2 / R n := div_nonneg (sq_nonneg _) (hRpos n).le
    have h1' := hroom n
    have h2 : (Tn n : ℝ) - 1 / 2 ≤ σ n := by
      rw [one_pow] at h1'
      linarith
    rw [← hcTn n, ← hcr n]
    have := mul_le_mul_of_nonneg_left h2 (hc n).le
    linarith [mul_sub (c n) (Tn n : ℝ) (1 / 2)]
  have htTO : ∀ n, c n * σ n ≤ (Tno n : ℝ) := fun n => by
    rw [← hcTn n]
    exact mul_le_mul_of_nonneg_left (hsT n) (hc n).le
  have hsel4O : ∀ n, R n / c n ≤ (q.neckRadius (Tno n) ^ 2)⁻¹ := fun n => by
    have h := hQρ n
    change R n ≤ ((q.neckRadius (c n * (Tn n : ℝ)) / Real.sqrt (c n)) ^ 2)⁻¹ at h
    rw [hcTn n, div_pow, Real.sq_sqrt (hc n).le, inv_div] at h
    rw [div_le_iff₀ (hc n)]
    calc R n ≤ c n / q.neckRadius (Tno n) ^ 2 := h
      _ = (q.neckRadius (Tno n) ^ 2)⁻¹ * c n := by ring
  have hδO : ∀ᶠ n in atTop, ∀ (i : Fin (Ho n).eventCount),
      (Ho n).time i.succ ∈ Icc ((Tno n : ℝ) / 2) (Tno n) →
      (p n).recenterConstant * (p n).delta ((Ho n).time i.succ) ≤ 1 / 2 := by
    obtain ⟨Tδ, hTδ⟩ := hδK
    filter_upwards [hTnoT.eventually_ge_atTop (2 * Tδ)] with n hn i hi
    exact hTδ n _ (by linarith [hi.1])
  have hsmO' : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (i : Fin (Ho n).eventCount),
      (Ho n).time i.succ ∈ Icc ((Tno n : ℝ) / 2) (Tno n) →
      ∀ (hi : max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ) h,
        (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius (Tno n) := by
    intro ε hε
    obtain ⟨T, -, hTsm⟩ := hsmO ε hε
    filter_upwards [hTnoT.eventually_ge_atTop T] with n hn i hti hi h
    exact hTsm _ hn n i hti hi h
  have hsepEv := sepK_eventually_of_smallAtTn_P6SN (K := Ho) (j := jc) (recordsK := recordsK)
    (t := fun n => c n * σ n) (Tn := fun n => (Tno n : ℝ)) (r := r) (R := fun n => R n / c n)
    (ρn := fun n => q.neckRadius (Tno n)) hjtO htTO hhalfO htime
    (fun n => div_pos (hRpos n) (hc n)) hsel4O
    ⟨1, one_pos, Eventually.of_forall fun n => by
      have := hlate n
      have h0 : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith⟩
    (fun n i hi b => hscaleK_of_diag_P6SN (hCb Ctime₀ n).2
      ((recordsK n i hi).static b).neck.scale_pos (hbirth n i hi b))
    hδO hsmO' hc₀
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsepEv
  set T₀g : ℕ → ℝ := fun n => if n < N then max (max (T₀ n) (c n * ((σ n : ℝ) - L n / R n))) (c n *
    σ n + 1) else
    max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) with hT₀gdef
  have hT₀g_ge : ∀ n, max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ T₀g n := fun n => by
    rw [hT₀gdef]
    dsimp only
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  have hT₀g_ev : ∀ᶠ n in atTop, T₀g n = max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) :=
    eventually_atTop.2 ⟨N, fun n hn => by
      rw [hT₀gdef]
      dsimp only
      split_ifs with hh
      · exact absurd hh (not_lt.mpr hn)
      · rfl⟩
  have hsepAll : ∀ n (i : Fin (Ho n).eventCount) (hi : T₀g n ≤ (Ho n).time i.succ)
      (b : ((Ho n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (jc n).castSucc →
      c n * σ n - (Ho n).time i.succ ≤
        (((recordsK n i ((hT₀g_ge n).trans hi)).static b).neck.scale)⁻¹ →
      R n / c n < c₀ * ((recordsK n i ((hT₀g_ge n).trans hi)).static b).neck.scale := by
    intro n i hi b hl ht
    by_cases hn : n < N
    · exfalso
      have h1 : c n * σ n + 1 ≤ (Ho n).time i.succ := by
        have h := hi
        rw [hT₀gdef] at h
        dsimp only at h
        split_ifs at h
        exact (le_max_right _ _).trans h
      have h2 : (Ho n).time i.succ ≤ (Ho n).time (jc n).castSucc :=
        (Ho n).toHistory.time_strictMono.monotone hl
      linarith [hjtO n]
    · exact hN n (not_lt.mp hn) i _ b hl ht
  have hnotKo := hdiag Ctime₀ (K := Ho) (j := jc) (t := fun n => c n * σ n) hjtO htjO (Q := Qs)
    (T₀ := T₀g) (recordsK := fun n i hi => recordsK n i ((hT₀g_ge n).trans hi)) recordsF hHI
    (fun n i hi b => hcanK n i _ b) (fun n i hi => hδF n i ((hT₀g_ge n).trans hi)) hacc hrad hord
    hslabK (fun n i hi b => hbirth n i _ b) (fun n i hi b => hbirthA n i _ b) (yG := yGc)
    (R := fun n => R n / c n) hRO hsepAll
  have hRr1 : Tendsto (fun n => R n * (fun _ : ℕ => (1 : ℝ)) n ^ 2) atTop atTop := by
    simp only [one_pow, mul_one]
    exact tendsto_atTop_mono hRr (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hT₀' : ∀ B : ℝ, ∀ᶠ n in atTop, max 1 (T₀g n / c n) ≤ (σ n : ℝ) - B / R n := by
    intro B
    filter_upwards [hwin (max B 1) (lt_of_lt_of_le one_pos (le_max_right _ _)),
      hL.eventually_ge_atTop (max B 1), hT₀g_ev] with n hn hLn hgn
    rw [hgn]
    have hB1 : B / R n ≤ max B 1 / R n :=
      div_le_div_of_nonneg_right (le_max_left _ _) (hRpos n).le
    have hLB : max B 1 / R n ≤ L n / R n := div_le_div_of_nonneg_right hLn (hRpos n).le
    have h2 : (aSeed n : ℝ) ≤ (σ n : ℝ) - B / R n := hn.trans (by linarith)
    refine max_le ((h1 n).trans h2) ?_
    rw [div_le_iff₀ (hc n)]
    refine max_le ?_ ?_
    · calc T₀ n ≤ c n * (aSeed n : ℝ) := hT₀l n
        _ ≤ c n * ((σ n : ℝ) - B / R n) := mul_le_mul_of_nonneg_left h2 (hc n).le
        _ = ((σ n : ℝ) - B / R n) * c n := mul_comm _ _
    · have h3 : (σ n : ℝ) - L n / R n ≤ (σ n : ℝ) - B / R n := by linarith
      exact (mul_le_mul_of_nonneg_left h3 (hc n).le).trans_eq (mul_comm _ _)
  have htime' : ∀ n, 2 * (1 : ℝ) ^ 2 < (Tn n : ℝ) := fun n => by
    rw [one_pow, mul_one]
    change 2 < (Tno n : ℝ) / r n ^ 2
    rw [lt_div_iff₀ (hc n)]
    linarith [htime n]
  have hTno : Tendsto (fun n => c n * (Tn n : ℝ)) atTop atTop := by
    refine hTnoT.congr fun n => ?_
    rw [hcTn n]
  have hσev : ∀ n, ∃ e : Fin (Kh n).eventCount, (Kh n).activeStage (σ n) = e.castSucc :=
    fun n => (hev n).imp fun j hj => (Kh n).activeStage_eq_castSucc_C11G j (σ n) hj.1.le hj.2
  refine ⟨p, pF, Qs, T₀g, fun n i hi => recordsK n i ((hT₀g_ge n).trans hi), fun _ => a₀, hT₀',
    ⟨recordsF⟩, fun _ => ha₀, hHI, fun n i hi b => hcanK n i _ b,
    fun n i hi => (hδF n i ((hT₀g_ge n).trans hi)).trans (hδ₀ Ctime₀ n).2,
    fun n => (hacc n).trans (hζ Ctime₀ n).2, fun n => (hRn Ctime₀ n).trans (hrad n),
    fun n => (hm₀ Ctime₀ n).trans (hord n), fun n i hi b => hscaleK n i _ b,
    Eventually.of_forall fun n i hi b => hbirthA n i _ b, hslabK, hQs, ?_,
    ⟨κd, hκd, hvolK_of_orig_P6CK (Ho := Ho) hc σ y R hRpos hO⟩,
    hdistC_rescaled_P6CK (Ho := Ho) hc (fun n i hi => recordsK n i ((hT₀g_ge n).trans hi))
      recordsF (fun _ => ha₀) hHI (fun n i hi b => hcanK n i _ b)
      (fun n => (hacc n).trans (hζ Ctime₀ n).2) (fun n => (hRn Ctime₀ n).trans (hrad n))
      (fun n => (hm₀ Ctime₀ n).trans (hord n)) σ y R hRpos hev Tn aSeed haT hsT has pT seedTrace
      L hL hroom htime' hsm hclock (fun n => hRr n) hT₀' hQρ hTno hδK
      (fun ε hε => (hsmO ε hε).imp fun T hT => ⟨hT.1, fun τ hτ n i hti hi h =>
        hT.2 τ hτ n i hti _ h⟩),
    ObservedHistory.hdistW_of_firstExit_P6DW Kh Tn aSeed σ haT hsT has pT seedTrace y R L hRpos
      (fun _ => 1) hL hsm hclock hRr1 hwin le_rfl
      (fun n => (Ho n).toHistory.hpin_rescale_P6X3 (hc n) (recordsF n) ha₀ (hHI n)) hσev hscalW,
    hκg, hscalU⟩
  intro n j' yG' hy h1' h2' hcw
  obtain ⟨i, hi, hl, A', b, x, hA', hx, ht⟩ := hcw
  have hj : jc n = j' := event_eq_of_mem_P6CK (K n).toHistory (hjtc n) (htjc n) h1' h2'
  subst hj
  obtain rfl := eq_of_heq ((hyGc n).symm.trans hy)
  refine hnotKo n ⟨i, hi, hl, A', b, x, hA', hx, ?_⟩
  exact time_conv_P6CK (hc n) ((recordsK n i ((hT₀g_ge n).trans hi)).static b).neck.scale_pos ht

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
