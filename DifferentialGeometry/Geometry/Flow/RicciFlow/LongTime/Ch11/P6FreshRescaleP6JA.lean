import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaRescaleP6CK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6VolumeRescaleCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallKappaC11PK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaWireConstsP6M6

/-!
# FRESH supply 的原尺度 ⇒ 重标度 adapter + `N.params = q` 识别（O-CH11-J11ADAPT G1，后缀 `_P6JA`）

FOOT4 G2 / G4 的 κ binder `hsupK` / `hsupA` 写在**重标度** history
`Kh k = (F.tower.history (ind k)).rescale_P6N (c k)` 上（`nr ↦ nr(c·)/√c`、`T ↦ T/c`）；
PBKAPPA 的 producer `kappaSeedWindowFwd_of_retention_C11PK` 给的是**原尺度**
`∀ n, KappaSeedWindowFwd_C11PK (N.params.nr(4·/3)) A κ T
(F.tower.history n)`。本文件补 J11 "原尺度投影" 两半：

* **逐字段 transport**（`rescale_P6N c`：time `t ↦ t/c`、metric `g ↦ c⁻¹g`）：
  Kh 的 seed `(t̃, p̃, r̃)` ↔ Ho 的 `(c t̃, p, √c r̃)`；`T̃ = T/c`；`2r̃² < t̃ ⇔ 2r² < t`；
  K0（`hasSmallParabolicCurvature`）半径 `r̃ ↔ √c r̃`
  （**新写反向** `hasSmallParabolicCurvature_of_rescale_P6JA`，P6X3 只有正向）；体积 `A⁻¹r³` 尺度不变（CXSP
  `le_ballVolume_castRescale_iff_CXSP`）；nr 窗口 `nr(c w)/√c ≤ r̃ ⇔ nr(c w) ≤ r`；aSeed / 窗口时刻 `×c`；
  ball `A·r̃ ↔ A·r`；受控球 `ρ′ ↦ √c ρ′`（P6CK `ctrl_of_rescale_P6CK`）；`κρ′³ ≤ Vol` 尺度不变 ⇒ **κ、A 不变**。
  **`kappaSeedWindowFwd_rescale_P6JA`**（单 history，PROVED）⇒ **`fresh_rescale_adapter_P6JA`**（结论 =
  FOOT4 G2 `hsupK` 逐字，PROVED）。
* **`N.params = q` 的成立层**：**不是字面等式**。KWIRE / P6M6 的 `N`（`blockData_consts_of_certifiedTower_P6M6`）与
  顶层 `q`（hP6b‴ binder 的 `hq`）在 certified-tower 层都满足 "`Ici 0` 上 `delta / neckRadius =
  chainDiagonal_C11A T.toChain`"，且 `N.params` 的静态字段 `= pB`。FRESH supply 只在 `w > 0` 读 `nr`
  （`w ≥ t − r²/2 > 3r²/2`）⇒ `KappaSeedWindowFwd_C11PK.congr_nr_P6JA` 足够。
  `params_eq_q_P6JA`（PROVED，nr / delta 层）；`freshSupply_q_of_certifiedTower_P6JA`（PROVED，显式前提
  `hP3 / hprof / hacc₀` 关于 `pB`）；**`hsupA_of_certifiedTower_P6JA`**（结论 = FOOT4 G4 `hsupA` 逐字）。
* **εP6 选择子约束**（lead 22:5x 裁定 (2)）：`hprof_hacc_of_epsP6_P6JA`——HP6B 共享选择子若取
  `εP6 Γ Γf ≤ min εProf_C11E (epsilon0_C11FR Γf.ε (chainC1_C11KD Γf) (chainC2_C11KD Γf) P)`，
  则 hP6b‴ binder 环境的  `pB.modelAccuracy ≤ εP6`、`capWindowRadius + 1 ≤ modelRadius`、`2 ≤ modelOrder`
  付清 `hprof` 与 `hacc₀`；
  剩 `hcollar`（`collarAdmitsAllOrders_C11E pB.fixed.collarLength`，lead 裁定 (1)：显式 binder 透传到 HP6B 顶层，
  owner pBase provider）。`hsupA_of_hP6bEnv_P6JA` = hP6b‴ binder 环境 + `hcollar` + 该约束 ⇒ `hsupA`。
非循环：只 import P6CK / CXSP / PBKAPPA / P6M6；
不经 Pre841 hdist / hscalU / hclosG / CanonicalLateCore / hspine。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)

/-- **K0 反向重标度（`_P6JA`，PROVED）**：重标度 history 在 `(t/c, p̃)` 半径 `r` 的
`hasSmallParabolicCurvature` ⇒ 原 history 在 `(t, p)` 半径 `r √c` 的同一谓词（P6X3
`hasSmallParabolicCurvature_rescale_P6X3` 的逆向；trace 走 `traceOfRescaleAt_P6CK`，`isRmControlled` 半径
`√3 r ↦ √3 r √c` 走 `isRmControlled_of_rescale_P6CK`）。 -/
theorem hasSmallParabolicCurvature_of_rescale_P6JA (t : Icc (0 : ℝ) K.toHistory.horizon)
    (p : (K.toHistory.stageAt t).Carrier) {r : ℝ}
    (h : GC.LongTime.hasSmallParabolicCurvature (K.rescale_P6N c hc).toHistory
      (K.rescaleTime_P6X hc t) (K.castRescale_P6X hc t p) r) :
    GC.LongTime.hasSmallParabolicCurvature K.toHistory t p (r * Real.sqrt c) := by
  obtain ⟨hr, a', hat', ha', htr⟩ := h
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  obtain ⟨a, rfl⟩ : ∃ a, K.rescaleTime_P6X hc a = a' :=
    ⟨K.unscaleTime_P6X hc a', K.rescale_unscaleTime_P6X hc a'⟩
  have hat : a ≤ t := (div_le_div_iff_of_pos_right hc).mp
    (show (a : ℝ) / c ≤ (t : ℝ) / c from hat')
  refine ⟨mul_pos hr hs, a, hat, ?_, fun x hx => ?_⟩
  · have ha'' : (a : ℝ) / c = (t : ℝ) / c - r ^ 2 := ha'
    rw [div_eq_iff hc.ne'] at ha''
    rw [ha'', sub_mul, div_mul_cancel₀ _ hc.ne', mul_pow, Real.sq_sqrt hc.le]
  · have hx' : K.castRescale_P6X hc t x ∈ riemannianBallOf
        ((K.rescale_P6N c hc).toHistory.stageMetric
          ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc t))
          (K.rescaleTime_P6X hc t)) (K.castRescale_P6X hc t p) r := by
      have h := K.ball_castRescale_P6X hc t p x hx
      rwa [mul_div_cancel_right₀ _ hs.ne'] at h
    obtain ⟨B, hB⟩ := htr _ hx'
    refine ⟨K.traceOfRescaleAt_P6CK hc hat B, ?_⟩
    have hctl := K.isRmControlled_of_rescale_P6CK hc hat B hB
    rwa [mul_assoc] at hctl

/-- **FRESH window-zero supply 的原尺度 ⇒ 重标度 adapter（单 history，`_P6JA`，PROVED）**：
`KappaSeedWindowFwd_C11PK nr A κ T K` ⇒ 重标度 history `K.rescale_P6N c` 上的同一 supply，
`nr ↦ nr(c·)/√c`、`T ↦ T/c`，`A`、`κ` 不变。 -/
theorem kappaSeedWindowFwd_rescale_P6JA {nr : ℝ → ℝ} {A κ T : ℝ}
    (h : KappaSeedWindowFwd_C11PK nr A κ T K.toHistory) :
    KappaSeedWindowFwd_C11PK (fun w => nr (c * w) / Real.sqrt c) A κ (T / c)
      (K.rescale_P6N c hc).toHistory := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  intro t' p' r' hT ht hsm hvol hnr aSeed' haT' hclock seedTrace' v' hav' hvt' hv' x' hx' ρ' hρ0
    hρr hball
  obtain ⟨t, rfl⟩ : ∃ t, K.rescaleTime_P6X hc t = t' :=
    ⟨K.unscaleTime_P6X hc t', K.rescale_unscaleTime_P6X hc t'⟩
  obtain ⟨p, rfl⟩ := K.castRescale_surj_P6CK hc t p'
  obtain ⟨a, rfl⟩ : ∃ a, K.rescaleTime_P6X hc a = aSeed' :=
    ⟨K.unscaleTime_P6X hc aSeed', K.rescale_unscaleTime_P6X hc aSeed'⟩
  obtain ⟨v, rfl⟩ : ∃ v, K.rescaleTime_P6X hc v = v' :=
    ⟨K.unscaleTime_P6X hc v', K.rescale_unscaleTime_P6X hc v'⟩
  obtain ⟨x, rfl⟩ := K.castRescale_surj_P6CK hc v x'
  have hr2 : (r' * Real.sqrt c) ^ 2 = r' ^ 2 * c := by rw [mul_pow, Real.sq_sqrt hc.le]
  have hat : a ≤ t := (div_le_div_iff_of_pos_right hc).mp
    (show (a : ℝ) / c ≤ (t : ℝ) / c from haT')
  have hav : a ≤ v := (div_le_div_iff_of_pos_right hc).mp
    (show (a : ℝ) / c ≤ (v : ℝ) / c from hav')
  have hvt : v ≤ t := (div_le_div_iff_of_pos_right hc).mp
    (show (v : ℝ) / c ≤ (t : ℝ) / c from hvt')
  -- seed 前提逐项搬回原尺度
  have hT0 : T ≤ (t : ℝ) := (div_le_div_iff_of_pos_right hc).mp
    (show T / c ≤ (t : ℝ) / c from hT)
  have ht0 : 2 * (r' * Real.sqrt c) ^ 2 < (t : ℝ) := by
    have h1 := (lt_div_iff₀ hc).mp (show 2 * r' ^ 2 < (t : ℝ) / c from ht)
    rw [hr2]
    linarith
  have hsm0 := K.hasSmallParabolicCurvature_of_rescale_P6JA hc t p hsm
  have hvol0 : ENNReal.ofReal (A⁻¹ * (r' * Real.sqrt c) ^ 3) ≤
      ballVolume (K.toHistory.stageMetric (K.toHistory.activeStage t) t) p (r' * Real.sqrt c) := by
    refine (le_ballVolume_castRescale_iff_CXSP hc (v := t) (p := p) (κ := A⁻¹)
      (r := r' * Real.sqrt c)).mp ?_
    rw [mul_div_cancel_right₀ _ hs.ne']
    exact hvol
  have hnr0 : ∀ w : ℝ, (t : ℝ) - (r' * Real.sqrt c) ^ 2 / 2 ≤ w → w ≤ (t : ℝ) →
      nr w ≤ r' * Real.sqrt c := by
    intro w hw1 hw2
    rw [hr2] at hw1
    have hlo : (t : ℝ) / c - r' ^ 2 / 2 ≤ w / c := by
      rw [le_div_iff₀ hc, sub_mul, div_mul_cancel₀ _ hc.ne']
      linarith
    have hhi : w / c ≤ (t : ℝ) / c := div_le_div_of_nonneg_right hw2 hc.le
    have h3 : nr (c * (w / c)) / Real.sqrt c ≤ r' := hnr (w / c) hlo hhi
    rw [mul_div_cancel₀ w hc.ne'] at h3
    exact (div_le_iff₀ hs).mp h3
  have hclock0 : (a : ℝ) = (t : ℝ) - (r' * Real.sqrt c) ^ 2 := by
    have h1 : (a : ℝ) / c = (t : ℝ) / c - r' ^ 2 := hclock
    rw [div_eq_iff hc.ne'] at h1
    rw [h1, sub_mul, div_mul_cancel₀ _ hc.ne', hr2]
  have hv0 : (t : ℝ) - (r' * Real.sqrt c) ^ 2 / 2 ≤ (v : ℝ) := by
    have h1 : (t : ℝ) / c - r' ^ 2 / 2 ≤ (v : ℝ) / c := hv'
    have h2 := mul_le_mul_of_nonneg_right h1 hc.le
    rw [sub_mul, div_mul_cancel₀ _ hc.ne', div_mul_cancel₀ _ hc.ne'] at h2
    rw [hr2]
    linarith
  -- seed trace 与窗口时刻的中心点
  have h1' : (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc a) ≤
      K.toHistory.activeStage v :=
    (K.activeStage_rescaleTime_P6X hc a).le.trans (K.toHistory.activeStage_mono hav)
  have h2' : K.toHistory.activeStage v ≤
      (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc t) :=
    (K.toHistory.activeStage_mono hvt).trans (K.activeStage_rescaleTime_P6X hc t).ge
  have hpt : seedTrace'.point ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v))
      ((K.rescale_P6N c hc).toHistory.activeStage_mono hav')
      ((K.rescale_P6N c hc).toHistory.activeStage_mono hvt') =
      K.castRescale_P6X hc v ((K.traceOfRescaleAt_P6CK hc hat seedTrace').point
        (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
        (K.toHistory.activeStage_mono hvt)) := by
    have hh : HEq ((K.traceOfRescaleAt_P6CK hc hat seedTrace').point (K.toHistory.activeStage v)
        (K.toHistory.activeStage_mono hav) (K.toHistory.activeStage_mono hvt))
        (seedTrace'.point ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v))
          ((K.rescale_P6N c hc).toHistory.activeStage_mono hav')
          ((K.rescale_P6N c hc).toHistory.activeStage_mono hvt')) := by
      rw [K.traceOfRescaleAt_point_P6CK hc hat seedTrace' _ _ _ h1' h2']
      exact point_heq_P6CK seedTrace' (K.activeStage_rescaleTime_P6X hc v).symm _ _ _ _
    exact eq_of_heq (hh.symm.trans (K.heq_castRescale_P6X hc v _).symm)
  rw [hpt] at hx'
  have hx0 : x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
      ((K.traceOfRescaleAt_P6CK hc hat seedTrace').point (K.toHistory.activeStage v)
        (K.toHistory.activeStage_mono hav) (K.toHistory.activeStage_mono hvt))
      (A * (r' * Real.sqrt c)) := by
    refine K.ball_of_castRescale_P6CK hc v _ x ?_
    rw [mul_div_assoc, mul_div_cancel_right₀ _ hs.ne']
    exact hx'
  -- 受控球与结论
  have hctrl := K.ctrl_of_rescale_P6CK hc v x hball
  have hρ0' : 0 ≤ ρ' * Real.sqrt c := mul_nonneg hρ0 hs.le
  have hρr' : ρ' * Real.sqrt c < r' * Real.sqrt c / 100 := by
    have h1 := mul_lt_mul_of_pos_right hρr hs
    linarith
  have hres := h t p (r' * Real.sqrt c) hT0 ht0 hsm0 hvol0 hnr0 a hat hclock0
    (K.traceOfRescaleAt_P6CK hc hat seedTrace') v hav hvt hv0 x hx0 (ρ' * Real.sqrt c) hρ0' hρr'
    hctrl
  have hfin := (le_ballVolume_castRescale_iff_CXSP hc (v := v) (p := x) (κ := κ)
    (r := ρ' * Real.sqrt c)).mpr hres
  rwa [mul_div_cancel_right₀ _ hs.ne'] at hfin

end RetainedCoreHistory

/-- **nr 同余（`_P6JA`，PROVED）**：FRESH supply 只在 `w ≥ t − r²/2 > 3r²/2 ≥ 0` 读 `nr`，故 `nr`、`nr'`
在 `Ici 0` 上相等即可互换。 -/
theorem KappaSeedWindowFwd_C11PK.congr_nr_P6JA {nr nr' : ℝ → ℝ} {A κ T : ℝ}
    {H : ObservedHistory.{u}} (hnr : ∀ s : ℝ, 0 ≤ s → nr s = nr' s)
    (h : KappaSeedWindowFwd_C11PK nr A κ T H) : KappaSeedWindowFwd_C11PK nr' A κ T H := by
  intro t p r hT ht hsm hvol hw
  refine h t p r hT ht hsm hvol (fun w hw1 hw2 => ?_)
  have hw0 : 0 ≤ w := by nlinarith [sq_nonneg r]
  rw [hnr w hw0]
  exact hw w hw1 hw2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

universe u

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow

/-- **G1 主 adapter（`_P6JA`，PROVED）**：原尺度 FRESH supply（`∀ n`，于 `F.tower.history n`）⇒ FOOT4 G2
`hkappaL_of_fresh_P6F4` 的 binder `hsupK` **逐字**（任意 `ind c hc k`，重标度 history，`nr ↦ nr(c·)/√c`、
`T ↦ T/c`，`A`、`κ` 不变）。 -/
theorem fresh_rescale_adapter_P6JA {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {nr : ℝ → ℝ} {A κ T : ℝ}
    (hsup : ∀ n, KappaSeedWindowFwd_C11PK nr A κ T (F.tower.history n).toHistory) :
    ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
      KappaSeedWindowFwd_C11PK (fun w => nr (c k * w) / Real.sqrt (c k)) A κ
        (T / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory :=
  fun ind _ hc k => (F.tower.history (ind k)).kappaSeedWindowFwd_rescale_P6JA (hc k) (hsup (ind k))

/-- **`N.params = q` 的识别层（`_P6JA`，PROVED）**：两个 cutoff 参数若都在 `Ici 0` 上与同一 chain diagonal
（certified tower `T.toChain`）的 `delta / neckRadius` 相等，则彼此在 `Ici 0` 上相等。用法：`N`
（`blockData_consts_of_certifiedTower_P6M6`）与顶层 `q`（hP6b‴ binder `hq`）——**非字面等式**，只到
`delta / neckRadius on Ici 0`（静态字段另由 P6M6 `= pB`）。 -/
theorem params_eq_q_P6JA {N q d : CutoffParameters}
    (hN : ∀ t : ℝ, 0 ≤ t → N.delta t = d.delta t ∧ N.neckRadius t = d.neckRadius t)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = d.delta t ∧ q.neckRadius t = d.neckRadius t) :
    ∀ t : ℝ, 0 ≤ t → N.delta t = q.delta t ∧ N.neckRadius t = q.neckRadius t :=
  fun t ht => ⟨(hN t ht).1.trans (hq t ht).1.symm, (hN t ht).2.trans (hq t ht).2.symm⟩

/-- **FRESH supply，`nr` 写成顶层 `q`（`_P6JA`，PROVED）**：certified tower `T` + 顶层 `q`（`hq`）+ `pB` 级
`hP3 / hprof / hacc₀` ⇒
`∃ κ T, ∀ n, KappaSeedWindowFwd_C11PK (q.neckRadius (4·/3)) A κ T (F.tower.history n)`。
证明：P6M6 块数据（`N` 常数与静态字段导出）+ `F' = F`（KWIRE）+ PBKAPPA producer + `params_eq_q_P6JA` + nr 同余。 -/
theorem freshSupply_q_of_certifiedTower_P6JA {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {εReserve : ℝ}
    (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve)
    (hcert : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j)
      (T.lookahead j) (T.request j))
    (F : GC.Interface.RawSurgery P g) (hF : F.tower = T.toChain.tower) (q : CutoffParameters)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hP3 : CollarWindowSupply_C11E.{u} pB) (hprof : ModelConstraintsSupply_C11E pB εProf_C11E.{u})
    (hacc₀ : pB.modelAccuracy ≤
      epsilon0_C11FR Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) P)
    {A : ℝ} (hA : 0 < A) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, 0 < Tf ∧ ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory := by
  obtain ⟨F', hF', N, rad, Df, εf, cap, mf, hconst, hdiagN, hrad, hnr1, hev, hdomK3, hdomE,
    hdomU⟩ := blockData_consts_of_certifiedTower_P6M6 T hcert
  obtain rfl : F' = F := rawSurgery_eq_of_tower_eq_C11KW (hF'.trans hF.symm)
  obtain ⟨hε, hC1, hC2, -, hfix, hmrad, hmord, hmacc, -⟩ := hconst
  have hP3N : CollarWindowSupply_C11E.{u} N.params := by
    refine ⟨?_, hP3.2.trans_eq hmrad.symm⟩
    have key : ∀ (A A' : ℝ) (_ : A = A') (h1 : 0 < A) (h2 : 0 < A'),
        collarAdmitsAllOrders_C11E.{u} A h1 → collarAdmitsAllOrders_C11E.{u} A' h2 := by
      intro A A' e h1 h2 h
      subst e
      exact h
    exact key _ _ (by rw [hfix]) _ _ hP3.1
  have hprofN : ModelConstraintsSupply_C11E N.params εProf_C11E.{u} := by
    unfold ModelConstraintsSupply_C11E
    rw [hmacc, hmord, hmrad]
    exact hprof
  have hacc₀N := gap2_of_consts_P6M6 N hε hC1 hC2 hmacc hacc₀
  obtain ⟨κ, hκ, Tf, hTf, hsup⟩ := kappaSeedWindowFwd_of_retention_C11PK N rad Df εf cap mf hrad
    hnr1 hev hdomK3 hdomE hdomU hA hP3N hprofN hacc₀N
  have hNq := params_eq_q_P6JA hdiagN hq
  refine ⟨κ, hκ, Tf, hTf, fun n => (hsup n).congr_nr_P6JA (fun s hs => ?_)⟩
  exact (hNq (4 * s / 3) (by positivity)).2

/-- **FOOT4 G4 `hsupA` 逐字（`_P6JA`，PROVED，显式前提 `hP3 hprof hacc₀`）**：certified tower 层的
`freshSupply_q_of_certifiedTower_P6JA`（`A := Aseed + 7`）∘ `fresh_rescale_adapter_P6JA`。 -/
theorem hsupA_of_certifiedTower_P6JA {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {εReserve : ℝ}
    (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve)
    (hcert : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j)
      (T.lookahead j) (T.request j))
    (F : GC.Interface.RawSurgery P g) (hF : F.tower = T.toChain.tower) (q : CutoffParameters)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hP3 : CollarWindowSupply_C11E.{u} pB) (hprof : ModelConstraintsSupply_C11E pB εProf_C11E.{u})
    (hacc₀ : pB.modelAccuracy ≤
      epsilon0_C11FR Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) P) :
    ∀ Aseed : ℝ, 1 < Aseed → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ,
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
        KappaSeedWindowFwd_C11PK
          (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
          (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory := by
  intro Aseed hA
  obtain ⟨κ, hκ, Tf, -, hsup⟩ := freshSupply_q_of_certifiedTower_P6JA T hcert F hF q hq hP3 hprof
    hacc₀ (A := Aseed + 7) (by linarith)
  exact ⟨κ, hκ, Tf, fresh_rescale_adapter_P6JA hsup⟩

/-- **HP6B 共享选择子约束（`_P6JA`，PROVED；lead 22:5x 裁定 (2)）**：若 `εP6` 取成
`≤ min εProf_C11E (epsilon0_C11FR Γ.ε (chainC1_C11KD Γ) (chainC2_C11KD Γ) P)`
（`Γ` = tower 的常数，v7 中是 `Γf`），
则 hP6b‴ binder 环境的三条 `pB` 界（`modelAccuracy ≤ εP6`、`capWindowRadius + 1 ≤ modelRadius`、
`2 ≤ modelOrder`）付清 `hprof` 与 `hacc₀`。约束本身由后继在 HP6B 槽表登记。 -/
theorem hprof_hacc_of_epsP6_P6JA {P : OrientedThreeStage.{u}} {pB : CutoffParameters}
    {Γ : ClosedBirthConstants} {εP6 : ℝ}
    (hεP6 : εP6 ≤ min εProf_C11E.{u}
      (epsilon0_C11FR Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) P))
    (hacc : pB.modelAccuracy ≤ εP6) (hrad : capWindowRadius_C11E + 1 ≤ pB.modelRadius)
    (hord : 2 ≤ pB.modelOrder) :
    ModelConstraintsSupply_C11E pB εProf_C11E.{u} ∧
      pB.modelAccuracy ≤ epsilon0_C11FR Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) P := by
  have h1 := hacc.trans hεP6
  refine ⟨⟨h1.trans (min_le_left _ _), hord, ?_⟩, h1.trans (min_le_right _ _)⟩
  have hte := DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd_pos
  unfold capWindowRadius_C11E at hrad
  linarith

/-- **`hsupA` 于 hP6b‴ binder 环境（`_P6JA`，PROVISIONAL[`hcollar`]）**：hP6b‴ 的 binder（certified tower
`T hcert`、`F q hF hq`、`pB` 三界）+ 选择子约束 `hεP6` + **唯一显式 binder** `hcollar`
（`collarAdmitsAllOrders_C11E pB.fixed.collarLength`，lead 裁定 (1)：透传到 HP6B 顶层，owner pBase provider）
⇒ FOOT4 G4 `hsupA` 逐字。 -/
theorem hsupA_of_hP6bEnv_P6JA {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {εReserve : ℝ} {εP6 : ℝ}
    (hεP6 : εP6 ≤ min εProf_C11E.{u}
      (epsilon0_C11FR Γ.epsilon (chainC1_C11KD Γ) (chainC2_C11KD Γ) P))
    (hcollar : collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos)
    (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve)
    (hcert : ∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j)
      (T.lookahead j) (T.request j))
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (hF : F.tower = T.toChain.tower)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hacc : pB.modelAccuracy ≤ εP6) (hrad : capWindowRadius_C11E + 1 ≤ pB.modelRadius)
    (hord : 2 ≤ pB.modelOrder) :
    ∀ Aseed : ℝ, 1 < Aseed → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ,
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
        KappaSeedWindowFwd_C11PK
          (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
          (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory := by
  obtain ⟨hprof, hacc₀⟩ := hprof_hacc_of_epsP6_P6JA hεP6 hacc hrad hord
  exact hsupA_of_certifiedTower_P6JA T hcert F hF q hq ⟨hcollar, hrad⟩ hprof hacc₀

end GC.LongTime.Ch11
