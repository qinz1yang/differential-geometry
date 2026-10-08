import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDShiftSeqG9S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDR4FineRU
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DepthR4AssembleP6DP4E

/-!
# R4 中心 kernel 的逐 `n` FRESH + 天花板形，及 E1 底座 hcomp 导出（O-CH11-HCEILT G1，后缀 `_HCT`）

lead R41 (a′)：R4 中心 hK 在 driver 内付。
* `sliceBCBD_kernel_R4center_seq_HCT`（PROVED）：G8 的 R4 换算 + G9S ShiftSeq（逐 `n` FRESH、
  `hceil` 代 `hsepT / hsep4`、eventually `hacc / hrad / hord / hTκ`）。
* `sliceBCBD_kernel_R4center_fine_seq_HCT`（PROVED）：RECUP G2 的 fine-records 孪生（反证子列）。
  因子 2（R4 中心 `R′ < 2R ≤ 2ρ̂⁻²`）由调用方取 `ρs := ρ̂/√2` 吸收（`ρs⁻² = 2ρ̂⁻²`），本文件无常数改动。
* `exists_R4_center_family_hcomp_HCT`（PROVED）：E1 底座逐字 + 输出 hcomp。
无新 binder / Prop。生成器 build-logs/scratch/O-CH11-HCEILT/gen/genA.py。
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

/-- **R4 中心 guarded 切片 BCBD，逐 `n` FRESH + 天花板形（`_HCT`，PROVED ⇐ G9S ShiftSeq）**：
G8 `sliceBCBD_kernel_R4center_G_A2B` 的 R4 换算（`Rt`、`hcmpL`、`Lt`、`hgood′`）套在
`sliceBCBD_kernel_fresh_sep_noProtC_alignedG_seq_ev_G9S` 上：`hsepT / hsep4` 换天花板 `hceil`，
`hRlt` 换 `hRle`，FRESH 参数逐 `n`。 -/
theorem sliceBCBD_kernel_R4center_seq_HCT
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ᶠ n : ℕ in atTop, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ᶠ n : ℕ in atTop, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ᶠ n : ℕ in atTop, n + 2 ≤ (p n).modelOrder)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRle : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (Rt : ℕ → ℝ) (hRtpos : ∀ n, 0 < Rt n) (hcmpL : ∀ n, Rt n / 2 < R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / Rt n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (Lt : ℕ → ℝ) (hL : Tendsto Lt atTop atTop) (L : ℕ → ℝ)
    (hLdef : ∀ n, L n = (Lt n - 2) / 2) {Cg : ℝ} (hCg : 8 ≤ Cg)
    (hgood' : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - (Lt n - 2) ^ 2 / Rt n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((Lt n - 2) / Real.sqrt (Rt n)) →
        4 * Rt n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / Rt n)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon)
      (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hdσ : ∀ n, riemannianEDistOf ((Kh n).stageMetric
        ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤)
    {nr : ℕ → ℝ → ℝ} {Tκ : ℕ → ℝ} {Aκ κ : ℝ} (hκ : 0 < κ)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK (nr n) Aκ κ (Tκ n) (Kh n))
    (hTκ : ∀ᶠ n in atTop, Tκ n ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ Geometry.Collapse.ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr n w ≤ r)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / Rt n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
    (ρs : ℕ → ℝ → ℝ)
    (hceil : ∀ n, R n ≤ (ρs n (t n) ^ 2)⁻¹)
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale)
    (hpre1 : ∀ n, (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹)
      (j n).castSucc)
    (hpre2 : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore Ctime'
      (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹) (t n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
  have hRR : ∀ n (X : ℝ), 0 ≤ X → X / R n ≤ 2 * X / Rt n := fun n X hX => by
    rw [div_le_div_iff₀ (hRpos n) (hRtpos n)]
    nlinarith [hcmpL n]
  have hT₀' : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n := by
    intro B
    filter_upwards [hT₀ (2 * |B|)] with n hn
    have h1 : B / R n ≤ |B| / R n := div_le_div_of_nonneg_right (le_abs_self B) (hRpos n).le
    have h2 := hRR n |B| (abs_nonneg B)
    linarith
  have hwin' : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n := by
    intro T hT
    filter_upwards [hwin (2 * T) (by linarith)] with n hn
    have := hRR n T hT.le
    linarith
  have hwinF' : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n := by
    intro T hT
    filter_upwards [hwinF (2 * T) (by linarith)] with n hn
    have := hRR n T hT.le
    linarith
  have hL' : Tendsto L atTop atTop := by
    have h1 : Tendsto (fun n => Lt n + (-2)) atTop atTop := tendsto_atTop_add_const_right _ _ hL
    refine (h1.atTop_div_const (by norm_num : (0 : ℝ) < 2)).congr fun n => ?_
    rw [hLdef n]
    ring
  have hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
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
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z := by
    intro n v hav hvs hv z hd hz
    refine hgood' n v hav hvs ?_ z ?_ ?_
    · have h4 : ((Lt n - 2) / 2) ^ 2 / R n ≤ (Lt n - 2) ^ 2 / Rt n := by
        have h := hRR n ((Lt n - 2) ^ 2 / 4) (by positivity)
        calc ((Lt n - 2) / 2) ^ 2 / R n = ((Lt n - 2) ^ 2 / 4) / R n := by ring
          _ ≤ 2 * ((Lt n - 2) ^ 2 / 4) / Rt n := h
          _ ≤ (Lt n - 2) ^ 2 / Rt n :=
            div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (Lt n - 2)]) (hRtpos n).le
      rw [hLdef n] at hv
      linarith
    · refine hd.trans (add_le_add le_rfl ?_)
      rw [hLdef n]
      rcases le_or_gt (Lt n - 2) 0 with hneg | hposL
      · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
          (Real.sqrt_nonneg _))]
        exact bot_le
      · apply ENNReal.ofReal_le_ofReal
        have hsR := Real.sqrt_pos.mpr (hRpos n)
        have hsRt := Real.sqrt_pos.mpr (hRtpos n)
        have hsq : Real.sqrt (Rt n) ≤ 2 * Real.sqrt (R n) := by
          have h4 : Real.sqrt (4 * R n) = 2 * Real.sqrt (R n) := by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]
          rw [← h4]
          exact Real.sqrt_le_sqrt (by linarith [hcmpL n, hRpos n])
        rw [div_div, div_le_div_iff₀ (by positivity) hsRt]
        nlinarith
    · have h8 := mul_le_mul_of_nonneg_right hCg (hRpos n).le
      linarith [hcmpL n]
  exact sliceBCBD_kernel_fresh_sep_noProtC_alignedG_seq_ev_G9S
    (hεcone := hεcone) (hC20 := hC20) (hphi := hphi) (hθ₀ := hθ₀) (hjt := hjt) (htj := htj)
    (hcanK := hcanK) (hacc := hacc) (hrad := hrad) (hord := hord) (hpinchK0 := hpinchK0)
    (Kh := Kh) (hKh := hKh) (σ := σ) (hσ := hσ) (y := y) (hyG := hyG) (R := R)
    (hRpos := hRpos) (hRn := hRn)
    (hRle := hRle) (hT₀ := hT₀') (Tn := Tn) (aSeed := aSeed) (haT := haT) (hsT := hsT)
    (has := has) (pT := pT) (seedTrace := seedTrace) (L := L) (hL := hL') (hCg := (by linarith))
    (hgood := hgood) (hwin := hwin') (hr := hr) (hsmall := hsmall) (hclock := hclock) (a₀ := a₀)
    (ha₀ := ha₀) (hpin := hpin) (hRa := hRa) (T₀X := T₀X) (hT₀X := hT₀X) (hOldX := hOldX)
    (hdσ := hdσ) (hκ := hκ) (hWK := hWK) (hTκ := hTκ) (htimeS := htimeS) (hvolS := hvolS)
    (hnrS := hnrS) (hwinF := hwinF') (hgate := hgate) (ρs := ρs) (hceil := hceil)
    (hsepρ := hsepρ) (hpre1 := hpre1) (hpre2 := hpre2)

/-- **R4 中心 fine-records 形（`_HCT`，PROVED ⇐ `sliceBCBD_kernel_R4center_seq_HCT`）**：RECUP G2
`sliceBCBD_kernel_R4center_fine_RU` 的逐字孪生，callee 换逐 `n` FRESH + 天花板形；`hsepT / hsep4`
换 `hceil`（`ρs′` 平移使阈值逐字），`hRlt` 换 `hRle`。 -/
theorem sliceBCBD_kernel_R4center_fine_seq_HCT
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {T₀ : ℕ → ℝ} {p0 : ℕ → CutoffParameters}
    {recordsK0 : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p0 n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hfineK : ∀ l : ℕ, ∀ᶠ n in atTop, ∃ p : CutoffParameters,
      ((l : ℝ) + 1) + 1 ≤ p.modelRadius ∧ p.modelAccuracy ≤ 1 / ((l : ℝ) + 1) ∧
      l + 2 ≤ p.modelOrder ∧
      ∃ rec : ∀ i : Fin (K n).eventCount, T₀ n ≤ (K n).time i.succ →
          GeometricCutoffRecord (K n).toHistory i p,
        (∀ i hi b, ((rec i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((rec i hi).static b).neck.scale = ((recordsK0 n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRle : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (Rt : ℕ → ℝ) (hRtpos : ∀ n, 0 < Rt n) (hcmpL : ∀ n, Rt n / 2 < R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / Rt n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (Lt : ℕ → ℝ) (hL : Tendsto Lt atTop atTop) (L : ℕ → ℝ)
    (hLdef : ∀ n, L n = (Lt n - 2) / 2) {Cg : ℝ} (hCg : 8 ≤ Cg)
    (hgood' : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - (Lt n - 2) ^ 2 / Rt n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((Lt n - 2) / Real.sqrt (Rt n)) →
        4 * Rt n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / Rt n)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon)
      (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hdσ : ∀ n, riemannianEDistOf ((Kh n).stageMetric
        ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤)
    {nr : ℕ → ℝ → ℝ} {Tκ : ℕ → ℝ} {Aκ κ : ℝ} (hκ : 0 < κ)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK (nr n) Aκ κ (Tκ n) (Kh n))
    (hTκ : ∀ᶠ n in atTop, Tκ n ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ Geometry.Collapse.ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr n w ≤ r)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / Rt n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
    (ρs : ℕ → ℝ → ℝ) (hceil : ∀ n, R n ≤ (ρs n (t n) ^ 2)⁻¹)
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK0 n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK0 n i hi).static b).neck.scale)
    (hpre1 : ∀ n, (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹)
      (j n).castSucc)
    (hpre2 : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore Ctime'
      (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹) (t n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
  subst hKh
  intro A hA
  by_contra hneg
  have hfreq : ∀ Q : ℝ, 2 ≤ Q → ∃ᶠ n in atTop,
      ¬ ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) :=
    fun Q hQ => Filter.not_eventually.mp fun h => hneg ⟨Q, hQ, h⟩
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_forall_of_frequently fun l : ℕ =>
    (hfreq ((l : ℝ) + 2) (by have := (Nat.cast_nonneg l : (0 : ℝ) ≤ l); linarith)).and_eventually
      (hfineK l)
  choose pf hradf haccf hordf recf hcanf hscf using fun l => (hφP l).2
  have hφle : ∀ l, l ≤ φ l := hφ.id_le
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hφ1 : ∀ l : ℕ, (l : ℝ) + 1 ≤ (φ l : ℝ) + 1 := fun l => by
    have := (Nat.cast_le (α := ℝ)).mpr (hφle l)
    linarith
  have hXpos : ∀ (l : ℕ) (s : ℝ), 0 < max ((φ l : ℝ) + 1) (ρs (φ l) s ^ 2)⁻¹ := fun l s =>
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hmax : ∀ (l : ℕ) (s : ℝ),
      max ((l : ℝ) + 1) ((Real.sqrt (max ((φ l : ℝ) + 1) (ρs (φ l) s ^ 2)⁻¹))⁻¹ ^ 2)⁻¹ =
        max ((φ l : ℝ) + 1) (ρs (φ l) s ^ 2)⁻¹ := fun l s => by
    rw [inv_pow, Real.sq_sqrt (hXpos l s).le, inv_inv]
    exact max_eq_right ((hφ1 l).trans (le_max_left _ _))
  have hinvX : ∀ (l : ℕ) (s : ℝ),
      ((Real.sqrt (max ((φ l : ℝ) + 1) (ρs (φ l) s ^ 2)⁻¹))⁻¹ ^ 2)⁻¹ =
        max ((φ l : ℝ) + 1) (ρs (φ l) s ^ 2)⁻¹ := fun l s => by
    rw [inv_pow, Real.sq_sqrt (hXpos l s).le, inv_inv]
  obtain ⟨Q₀, -, hev⟩ := sliceBCBD_kernel_R4center_seq_HCT
    (K := fun l => K (φ l)) (j := fun l => j (φ l)) (t := fun l => t (φ l))
    (T₀ := fun l => T₀ (φ l)) (p := pf) (recordsK := recf) (yG := fun l => yG (φ l))
    (hεcone := hεcone) (hC20 := hC20) (hphi := hphi) (hθ₀ := hθ₀)
    (hjt := fun l => hjt (φ l)) (htj := fun l => htj (φ l)) (hcanK := hcanf)
    (hacc := Filter.Eventually.of_forall haccf)
    (hrad := Filter.Eventually.of_forall fun l => le_trans (by linarith) (hradf l))
    (hord := Filter.Eventually.of_forall hordf)
    (hpinchK0 := fun l => hpinchK0 (φ l)) (Kh := fun l => (K (φ l)).toHistory) (hKh := rfl)
    (σ := fun l => σ (φ l)) (hσ := fun l => hσ (φ l)) (y := fun l => y (φ l))
    (hyG := fun l => hyG (φ l)) (R := fun l => R (φ l)) (hRpos := fun l => hRpos (φ l))
    (hRn := fun l => hRn (φ l)) (hRle := fun l => le_trans (hφ1 l) (hRle (φ l)))
    (Rt := fun l => Rt (φ l)) (hRtpos := fun l => hRtpos (φ l))
    (hcmpL := fun l => hcmpL (φ l)) (hT₀ := fun B => hφt.eventually (hT₀ B))
    (Tn := fun l => Tn (φ l)) (aSeed := fun l => aSeed (φ l)) (haT := fun l => haT (φ l))
    (hsT := fun l => hsT (φ l)) (has := fun l => has (φ l)) (pT := fun l => pT (φ l))
    (seedTrace := fun l => seedTrace (φ l)) (Lt := fun l => Lt (φ l)) (hL := hL.comp hφt)
    (L := fun l => L (φ l)) (hLdef := fun l => hLdef (φ l)) (hCg := hCg)
    (hgood' := fun l => hgood' (φ l)) (hwin := fun T hT => hφt.eventually (hwin T hT))
    (hr := hr) (hsmall := fun l => hsmall (φ l)) (hclock := fun l => hclock (φ l))
    (a₀ := fun l => a₀ (φ l)) (ha₀ := fun l => ha₀ (φ l)) (hpin := fun l => hpin (φ l))
    (hRa := fun l => hRa (φ l)) (T₀X := fun l => T₀X (φ l)) (hT₀X := fun l => hT₀X (φ l))
    (hOldX := fun l => hOldX (φ l)) (hdσ := fun l => hdσ (φ l)) (hκ := hκ)
    (nr := fun l => nr (φ l)) (Tκ := fun l => Tκ (φ l))
    (hWK := fun l => hWK (φ l)) (hTκ := hφt.eventually hTκ) (htimeS := fun l => htimeS (φ l))
    (hvolS := fun l => hvolS (φ l)) (hnrS := fun l => hnrS (φ l))
    (hwinF := fun T hT => hφt.eventually (hwinF T hT)) (hgate := hφt.eventually hgate)
    (ρs := fun l s => (Real.sqrt (max ((φ l : ℝ) + 1) (ρs (φ l) s ^ 2)⁻¹))⁻¹)
    (hceil := fun l => by
      rw [hinvX l]
      exact (hceil (φ l)).trans (le_max_right _ _))
    (hsepρ := fun B hB => (hφt.eventually (hsepρ B hB)).mono fun l hl i hi b hle hcond => by
      have e := hscf l i hi b
      rw [e] at hcond ⊢
      rw [hmax l]
      exact le_trans (mul_le_mul_of_nonneg_right (hφ1 l) (hXpos l _).le) (hl i hi b hle hcond))
    (hpre1 := fun l => by
      rw [hmax l]
      exact hpre1 (φ l))
    (hpre2 := fun l => by
      rw [hmax l]
      exact hpre2 (φ l)) A hA
  obtain ⟨l, hl1, hl2⟩ := (hev.and (eventually_ge_atTop ⌈Q₀⌉₊)).exists
  apply (hφP l).1
  intro z hz
  refine (hl1 z hz).trans ?_
  have h2 : ((⌈Q₀⌉₊ : ℕ) : ℝ) ≤ (l : ℝ) + 2 := by exact_mod_cast (show ⌈Q₀⌉₊ ≤ l + 2 by omega)
  have hR0 : 0 < ((K (φ l)).toHistory.event (j (φ l))).incoming.flow.scalar (t (φ l)) (yG (φ l)) :=
    (hRn (φ l)) ▸ hRpos (φ l)
  exact mul_le_mul_of_nonneg_right ((Nat.le_ceil Q₀).trans h2) hR0.le

end ObservedHistory

/-- **E1 底座孪生（`_HCT`，PROVED）**：`exists_R4_center_family_P6DP4E` 逐字，输出加 R4 hcomp
（`d_t(O, y′) ≤ d_σ(O, y) + 1/√R`，原证明的局部 `hcomp`）。 -/
theorem exists_R4_center_family_hcomp_HCT :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} (K : ℕ → RetainedCoreHistory.{u})
      (i : ∀ k, Fin (K k).eventCount) {q : ℕ → CutoffParameters}
      (rec : ∀ k, GeometricCutoffRecord (K k).toHistory (i k) (q k))
      (Tn aSeed σ : ∀ k, Icc (0 : ℝ) (K k).toHistory.horizon)
      (haT : ∀ k, aSeed k ≤ Tn k) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k)
      (p : ∀ k, ((K k).toHistory.stageAt (Tn k)).Carrier)
      (seedTrace : ∀ k, BackwardPointTrace (K k).toHistory ((K k).toHistory.activeStage (aSeed k))
        ((K k).toHistory.activeStage (Tn k)) ((K k).toHistory.activeStage_mono (haT k)) (p k))
      (y : ∀ k, ((K k).toHistory.stageAt (σ k)).Carrier) (R Λ : ℕ → ℝ),
      (∀ k, 0 < R k) → (∀ k, 2 ≤ Λ k) → (∀ k, (aSeed k : ℝ) < σ k) →
      (∀ k, (σ k : ℝ) = (K k).time (i k).succ) →
      ∀ (hf : ∀ k, (K k).toHistory.activeStage (aSeed k) ≤ (i k).castSucc)
        (hl : ∀ k, (i k).succ ≤ (K k).toHistory.activeStage (Tn k)),
      (∀ k, ((K k).toHistory.event (i k)).old =
        ((K k).toHistory.event (i k)).transition.trace.retainedCore) →
      (∀ k b, ((rec k).static b).hasCanonicalWindow) →
      (∀ k, (q k).modelAccuracy ≤ ε₀) → (∀ k, 2 ≤ (q k).modelOrder) →
      (∀ k, StandardCap.transitionEnd + 10 < (q k).modelRadius) →
      (∀ k b, metricScalarAt ((K k).toHistory.event (i k)).outputMetric
          ((seedTrace k).point (i k).succ ((hf k).trans (Fin.castSucc_lt_succ (i := i k)).le)
            (hl k)) < ((rec k).static b).neck.scale / 2) →
      (∀ k (wp : ((K k).toHistory.stage (i k).succ).Carrier), HEq (y k) wp →
        ∀ b, metricScalarAt ((K k).toHistory.event (i k)).outputMetric wp <
          ((rec k).static b).neck.scale / 2) →
      (∀ k, ∀ (v : Icc (0 : ℝ) (K k).toHistory.horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
        (σ k : ℝ) - Λ k ^ 2 / R k ≤ (v : ℝ) →
        ∀ z : ((K k).toHistory.stageAt v).Carrier,
          riemannianEDistOf ((K k).toHistory.stageMetric ((K k).toHistory.activeStage v) v)
              ((seedTrace k).point ((K k).toHistory.activeStage v)
                ((K k).toHistory.activeStage_mono hav)
                ((K k).toHistory.activeStage_mono (hvs.trans (hsT k)))) z ≤
            riemannianEDistOf ((K k).toHistory.stageMetric ((K k).toHistory.activeStage (σ k))
                (σ k))
                ((seedTrace k).point ((K k).toHistory.activeStage (σ k))
                  ((K k).toHistory.activeStage_mono (has k))
                  ((K k).toHistory.activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal (Λ k / Real.sqrt (R k)) →
          4 * R k ≤ metricScalarAt ((K k).toHistory.stageMetric
            ((K k).toHistory.activeStage v) v) z →
          (K k).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z) →
      ∀ (Bad : ∀ k, ((K k).toHistory.stage (i k).castSucc).Carrier → ℝ → Prop),
      (∀ k, ∃ (pm : ((K k).toHistory.stage (i k).castSucc).Carrier)
          (wp : ((K k).toHistory.stage (i k).succ).Carrier),
          HEq (y k) wp ∧ ((K k).toHistory.event (i k)).RegularCrossing pm wp ∧
          ∃ᶠ t in 𝓝[<] (K k).time (i k).succ, Bad k pm t) →
      ∃ (pm : ∀ k, ((K k).toHistory.stage (i k).castSucc).Carrier)
        (t : ∀ k, Icc (0 : ℝ) (K k).toHistory.horizon)
        (y' : ∀ k, ((K k).toHistory.stageAt (t k)).Carrier)
        (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
        (∀ k, Bad k (pm k) (t k)) ∧ (∀ k, HEq (y' k) (pm k)) ∧
        (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) ∧
        (∀ k, riemannianEDistOf ((K k).toHistory.stageMetric ((K k).toHistory.activeStage (t k))
            (t k))
            ((seedTrace k).point ((K k).toHistory.activeStage (t k))
              ((K k).toHistory.activeStage_mono (hat k))
              ((K k).toHistory.activeStage_mono ((hts k).trans (hsT k)))) (y' k) ≤
          riemannianEDistOf ((K k).toHistory.stageMetric ((K k).toHistory.activeStage (σ k))
              (σ k))
              ((seedTrace k).point ((K k).toHistory.activeStage (σ k))
                ((K k).toHistory.activeStage_mono (has k))
                ((K k).toHistory.activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal (1 / Real.sqrt (R k))) ∧
        ∀ k, ∀ (v : Icc (0 : ℝ) (K k).toHistory.horizon) (hav : aSeed k ≤ v) (hvt : v ≤ t k),
          (t k : ℝ) - (Λ k - 2) ^ 2 / R k ≤ (v : ℝ) →
          ∀ z : ((K k).toHistory.stageAt v).Carrier,
            riemannianEDistOf ((K k).toHistory.stageMetric ((K k).toHistory.activeStage v) v)
                ((seedTrace k).point ((K k).toHistory.activeStage v)
                  ((K k).toHistory.activeStage_mono hav)
                  ((K k).toHistory.activeStage_mono (hvt.trans ((hts k).trans (hsT k))))) z ≤
              riemannianEDistOf ((K k).toHistory.stageMetric ((K k).toHistory.activeStage (t k))
                  (t k))
                  ((seedTrace k).point ((K k).toHistory.activeStage (t k))
                    ((K k).toHistory.activeStage_mono (hat k))
                    ((K k).toHistory.activeStage_mono ((hts k).trans (hsT k)))) (y' k) +
                ENNReal.ofReal ((Λ k - 2) / Real.sqrt (R k)) →
            4 * R k ≤ metricScalarAt ((K k).toHistory.stageMetric
              ((K k).toHistory.activeStage v) v) z →
            (K k).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z := by
  obtain ⟨ε₀, hε₀, hR4⟩ := hcomp_R4_eventually_P6DP4E.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro eps C1' C2' Ctime' K i q rec Tn aSeed σ haT hsT has p seedTrace y R Λ hR hΛ hasl hσ hf hl
    hOld hcan hacc hm hDm hseed hysc hgood Bad hbad
  choose pm wp hwp hcr hfreq using hbad
  -- good set per k: the R4 hcomp (δ = 1/√R), closeness, lateness w.r.t. aSeed and the slab start
  have hgoodset : ∀ k, ∀ᶠ t' in 𝓝[<] (K k).time (i k).succ,
      (∀ (tt : Icc (0 : ℝ) (K k).toHistory.horizon), (tt : ℝ) = t' →
        ∀ (hat : aSeed k ≤ tt) (hts : tt ≤ σ k) (yy : ((K k).toHistory.stageAt tt).Carrier),
        HEq yy (pm k) →
        riemannianEDistOf ((K k).toHistory.stageMetric ((K k).toHistory.activeStage tt) tt)
            ((seedTrace k).point ((K k).toHistory.activeStage tt)
              ((K k).toHistory.activeStage_mono hat)
              ((K k).toHistory.activeStage_mono (hts.trans (hsT k)))) yy ≤
          riemannianEDistOf ((K k).toHistory.stageMetric ((K k).toHistory.activeStage (σ k))
              (σ k))
              ((seedTrace k).point ((K k).toHistory.activeStage (σ k))
                ((K k).toHistory.activeStage_mono (has k))
                ((K k).toHistory.activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal (1 / Real.sqrt (R k))) ∧
      ((σ k : ℝ) - t' ≤ 1 / R k ∧ t' < σ k) ∧ (aSeed k : ℝ) < t' ∧
      (K k).time (i k).castSucc < t' := by
    intro k
    have hδ : 0 < 1 / Real.sqrt (R k) := by
      have := Real.sqrt_pos.mpr (hR k)
      positivity
    have h1 := hR4 (K k) (i k) (rec k) (haT k) (seedTrace k) (hf k) (hl k) (hOld k) (hcan k)
      (hacc k) (hm k) (hDm k) (hcr k) (hseed k) (hysc k (wp k) (hwp k)) hδ (σ k) (hσ k) (hsT k)
      (has k) (y k) (hwp k)
    have h2 := eventually_close_P6DP4E (s := (σ k : ℝ)) (hR k)
    rw [hσ k] at h2
    have h3 : ∀ᶠ t' in 𝓝[<] (K k).time (i k).succ, (aSeed k : ℝ) < t' :=
      Filter.mem_of_superset (Ioo_mem_nhdsLT (show (aSeed k : ℝ) < (K k).time (i k).succ from
        (hσ k) ▸ hasl k)) fun t' ht' => ht'.1
    have h4 : ∀ᶠ t' in 𝓝[<] (K k).time (i k).succ, (K k).time (i k).castSucc < t' :=
      Filter.mem_of_superset
        (Ioo_mem_nhdsLT ((K k).time_strictMono (Fin.castSucc_lt_succ (i := i k))))
        fun t' ht' => ht'.1
    filter_upwards [h1, h2, h3, h4] with t' a b c d
    refine ⟨a, ?_, c, d⟩
    rw [hσ k]
    exact b
  obtain ⟨t', ht'⟩ := exists_pick_frequently_eventually_P6DP4E hfreq hgoodset
  have hmem : ∀ k, t' k ∈ Ioo ((K k).time (i k).castSucc) ((K k).time (i k).succ) := fun k =>
    ⟨(ht' k).2.2.2.2, by rw [← hσ k]; exact (ht' k).2.2.1.2⟩
  let t : ∀ k, Icc (0 : ℝ) (K k).toHistory.horizon := fun k =>
    ⟨t' k, mem_Icc_of_mem_slab_P6DP4E (K k) (i k) (hmem k)⟩
  have hact : ∀ k, (K k).toHistory.activeStage (t k) = (i k).castSucc := fun k =>
    RetainedCoreHistory.activeStage_eq_castSucc_of_mem_P6FF (H := K k) (i k) (t k) (hmem k)
  choose y' hy' using fun k => ObservedHistory.exists_heq_stageAt_P6JW (K k).toHistory (hact k)
    (pm k)
  have hat : ∀ k, aSeed k ≤ t k := fun k => (ht' k).2.2.2.1.le
  have hts : ∀ k, t k ≤ σ k := fun k => (ht' k).2.2.1.2.le
  have hclose : ∀ k, (σ k : ℝ) - t k ≤ 1 / R k := fun k => (ht' k).2.2.1.1
  have hcomp := fun k => (ht' k).2.1 (t k) rfl (hat k) (hts k) (y' k) (hy' k)
  refine ⟨pm, t, y', hat, hts, fun k => (ht' k).1, hy', hclose, hcomp, ?_⟩
  exact ObservedHistory.hgood_center_transport_seq_P6DP4D (fun k => (K k).toHistory) Tn aSeed σ t
    haT hsT has hat hts p seedTrace y y' hR hΛ hclose hgood hcomp

/-- consumer：签名稳定。 -/
example : type_of% @ObservedHistory.sliceBCBD_kernel_R4center_fine_seq_HCT :=
  @ObservedHistory.sliceBCBD_kernel_R4center_fine_seq_HCT

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
