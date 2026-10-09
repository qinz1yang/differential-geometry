import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDGuardAlignedA2B

/-!
# R4 中心的 guarded 切片 BCBD（O-CH11-BCBD-A2 G8，后缀 `_A2B`）

DEPTH4E2 R4 driver（`hTR_of_driver_le_P6DP4E2` / `hTR_of_driver_le_v2_CXW`）的 `hanchor0` 经
`hanchor0_driver_of_kernel_comparable_P6SB2` 需要 kernel 帧球界 `hK`（中心 = R4 中心 `(K, i, t, pm)`）。本文件：
`sliceBCBD_kernel_R4center_G_A2B`（PROVISIONAL[G6 清单]）= G6 G9″ 孪生在 R4 中心的实例化，
把 R4 帧数据（塔尺度 `Rt`、`hcmpL : Rt/2 < R(t, pm)`、R4 中心 hgood′：`(Lt − 2)`、阈值 `4·Rt`；窗口 / `T₀` 以 `Rt`
计）换算到 kernel 尺度 `R = R(t, pm)`（`L := (Lt − 2)/2`、`Cg ≥ 8`）。结论 = `hK` 体逐字；**不含 `hdistW`**
（不再需要 DEPTH4B 的 `hdistW_of_depthExt_P6DP4B`）。kernel 帧 diagonal 条款 `hRlt : n + 1 < R(t, pm)`
按 G9″ 原文保留（R4 中心只给 `R(t, pm) > Rt/2 ≥ (n+1)/2`，须由 R4 对角选点 `κ m ≥ 2m + 1` 付，见 state）。
生成器 `gen/gen8.py`（陈述由 G6 切片、断言替换；具名实参由 binder 解析生成）。
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

/-- **R4 中心 guarded 切片 BCBD（`_A2B`，PROVISIONAL[G6 清单，无 `hdistW`]）**：见模块文档。 -/
theorem ObservedHistory.sliceBCBD_kernel_R4center_G_A2B
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
    {nr : ℝ → ℝ} {Aκ κ Tκ : ℝ} (hκ : 0 < κ)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr Aκ κ Tκ (Kh n))
    (hTκ : ∀ n, Tκ ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ Geometry.Collapse.ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / Rt n)
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
      2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK n i hi).static b).neck.scale)
    (ρs : ℕ → ℝ → ℝ)
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
  exact sliceBCBD_kernel_fresh_sep_noProtC_alignedG_A2B
    (hεcone := hεcone) (hC20 := hC20) (hphi := hphi) (hθ₀ := hθ₀) (hjt := hjt) (htj := htj)
    (hcanK := hcanK) (hacc := hacc) (hrad2 := hrad2) (hord := hord) (hpinchK0 := hpinchK0)
    (hKh := hKh) (σ := σ) (hσ := hσ) (y := y) (hyG := hyG) (R := R) (hRpos := hRpos) (hRn := hRn)
    (hRlt := hRlt) (hT₀ := hT₀') (Tn := Tn) (aSeed := aSeed) (haT := haT) (hsT := hsT)
    (has := has) (pT := pT) (seedTrace := seedTrace) (L := L) (hL := hL') (hCg := (by linarith))
    (hgood := hgood) (hwin := hwin') (hr := hr) (hsmall := hsmall) (hclock := hclock) (a₀ := a₀)
    (ha₀ := ha₀) (hpin := hpin) (hRa := hRa) (T₀X := T₀X) (hT₀X := hT₀X) (hOldX := hOldX)
    (hdσ := hdσ) (hκ := hκ) (hWK := hWK) (hTκ := hTκ) (htimeS := htimeS) (hvolS := hvolS)
    (hnrS := hnrS) (hwinF := hwinF') (hgate := hgate) (hsepT := hsepT) (hsep4 := hsep4) (ρs := ρs)
    (hsepρ := hsepρ) (hpre1 := hpre1) (hpre2 := hpre2) (Kh := Kh)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
