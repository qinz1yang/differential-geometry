import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFwdChainC11FR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedScaleWideC11Q4b

/-!
# 前向尺度 wide 与 seed shift（O-CH11-FRESH G1c，后缀 `_C11FR`）

`KappaSeedScaleWideC11Q4b` 的前向版：
* `LocalKappaWideFwdAt_C11FR` / `…Supply_C11FR`：种子尺度 = 前向形；
  `localKappaWideFwd_of_reducedVolumeFwd_C11FR`（证明体逐字，K5 在种子自身调用）；
* `wideWindowFwd_of_wideFwd_C11FR`：seed shift `(v, O_v, r/100)` 的前提 `nr v ≤ r`（R3 的来源：
  crossing seed 的 `v ≤ a_k` 处 `nr v` 是旧块半径）换成 `nr(4(t − r²/2)/3) ≤ r`（前向时刻 ≥ t，
  由 `nr t ≤ r` + antitone 给出）。测试尺度下界 `nr v/100 ≤ ρ'` 不变。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. 前向尺度 wide -/

/-- **前向尺度 wide（逐 `A, L, κ`）**：`LocalKappaWideAt_C11Q` 原文，种子另加前向尺度
`∃ T ∈ [t, 2t − r²], nr T/100 ≤ r`。 -/
def LocalKappaWideFwdAt_C11FR {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ)
    (A L κ : ℝ) : Prop :=
  ∀ n, let H := (F.tower.history n).toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) →
    (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    (∃ T : ℝ, (t : ℝ) ≤ T ∧ T ≤ 2 * (t : ℝ) - r ^ 2 ∧ nr T / 100 ≤ r) →
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ρ' : ℝ, nr t / 100 ≤ ρ' → ρ' ≤ L * r → H.isParabolicallyRmControlledBall t x ρ' →
      ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) x ρ'

/-- 前向尺度 wide 的供给：`∀ A > 0, ∀ L > 0, ∃ κ > 0`。 -/
def LocalKappaWideFwdSupply_C11FR {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ) : Prop :=
  ∀ A L, 0 < A → 0 < L → ∃ κ, 0 < κ ∧ LocalKappaWideFwdAt_C11FR F δ α nr A L κ

/-- **前向 K5 + K6 ⇒ 前向 wide（任意 `L`）**：`localKappaWide_of_reducedVolume_C11Q` 的证明（K6 取树内
`controlledBallVolumeFromReducedVolume_holds_C11Q`），K5 在种子自身调用，种子尺度前提原样传入。 -/
theorem localKappaWideFwd_of_reducedVolumeFwd_C11FR {P : OrientedThreeStage.{u}}
    {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr v : ℝ → ℝ}
    (hK5 : SeedReducedVolumeFwd_C11FR F δ α nr v) :
    LocalKappaWideFwdSupply_C11FR F δ α nr := by
  intro A L hA hL
  obtain ⟨hvA, h5⟩ := hK5 A hA
  obtain ⟨σ, C, hσ, hC, h6⟩ := controlledBallVolumeFromReducedVolume_holds_C11Q.{u}
    (3 / (4 * L ^ 2)) (by positivity) (v A / 2) (half_pos hvA)
  refine ⟨v A / 2 / C, div_pos (half_pos hvA) hC, ?_⟩
  intro n H t p r hr hacc hsmall hvol hscale x hx ρ' hlow hup hball
  have hρ : 0 < ρ' := hball.1
  have hr0 : 0 < r := hsmall.1
  obtain ⟨hupper, hdepth⟩ := h6 (F.tower.history n) t x ρ' (L * r) hρ hup hball
  have hθ : 3 / (4 * L ^ 2) * (L * r) ^ 2 = 3 / 4 * r ^ 2 := by
    field_simp
  rw [hθ] at hdepth
  have hlowV := h5 n t p r hr hacc hsmall hvol hscale x hx ρ' hlow hball
  have hτ : 0 < σ * ρ' ^ 2 := by positivity
  have hmono : redVolTau_C11Q (F.tower.history n) t x (3 / 4 * r ^ 2) ≤
      redVolTau_C11Q (F.tower.history n) t x (σ * ρ' ^ 2) := by
    unfold redVolTau_C11Q
    refine historyReducedVolumeMonotone_holds (F.tower.history n) _ x t _ _
      ((F.tower.history n).toHistory.activeStage_mem t) (Real.sqrt_pos.2 hτ)
      (Real.sqrt_le_sqrt hdepth) ?_
    rw [Real.sq_sqrt (by positivity)]
    linarith
  have hchain := (hlowV.trans hmono).trans hupper
  set V := ballVolume (H.stageMetric (H.activeStage t) t) x ρ' with hV
  have hsplit : ENNReal.ofReal (v A) =
      ENNReal.ofReal (v A / 2) + ENNReal.ofReal (v A / 2) := by
    rw [← ENNReal.ofReal_add (half_pos hvA).le (half_pos hvA).le]
    congr 1
    ring
  rw [hsplit] at hchain
  have hhalf : ENNReal.ofReal (v A / 2) ≤ ENNReal.ofReal (C / ρ' ^ 3) * V :=
    (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hchain
  have hρ3 : 0 < ρ' ^ 3 := pow_pos hρ 3
  have hreal : v A / 2 / C * ρ' ^ 3 = v A / 2 * (ρ' ^ 3 / C) := by
    field_simp
  have hone : C / ρ' ^ 3 * (ρ' ^ 3 / C) = 1 := by
    field_simp
  calc
    ENNReal.ofReal (v A / 2 / C * ρ' ^ 3) =
        ENNReal.ofReal (v A / 2) * ENNReal.ofReal (ρ' ^ 3 / C) := by
      rw [hreal, ENNReal.ofReal_mul (half_pos hvA).le]
    _ ≤ ENNReal.ofReal (C / ρ' ^ 3) * V * ENNReal.ofReal (ρ' ^ 3 / C) :=
      mul_le_mul_left hhalf _
    _ = V := by
      rw [mul_comm (ENNReal.ofReal (C / ρ' ^ 3)) V, mul_assoc,
        ← ENNReal.ofReal_mul (div_pos hC hρ3).le, hone, ENNReal.ofReal_one, mul_one]

/-! ## 2. seed shift：前向 wide ⇒ wide window（前提 `nr T* ≤ r`） -/

/-- **前向 wide + S7 ⇒ wide window（seed shift）**：`wideWindowScaled_of_wideScaled_C11Q4b` 的证明体逐字；
shift 种子 `(v, O_v, r/100)` 的种子尺度由前向时刻 `T* = 4(t − r²/2)/3` 给出（`v ≤ t ≤ T* ≤ 2v − (r/100)²`），
故前提 `nr v ≤ r` 换成 `nr T* ≤ r`（⇐ `nr t ≤ r`，`T* ≥ t`，antitone）——与 `v` 是否跨 activation 无关。 -/
theorem wideWindowFwd_of_wideFwd_C11FR {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α) (h : LocalKappaWideFwdSupply_C11FR F δ α nr)
    {A : ℝ} (hA : 0 < A) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t), (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          nr (4 * ((t : ℝ) - r ^ 2 / 2) / 3) ≤ r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, nr v / 100 ≤ ρ' → ρ' ≤ (A + 1) * r →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ' := by
  have hA' : 0 < 51200 * Real.exp 57 * A := by positivity
  obtain ⟨κ, hκ, hK⟩ := h _ (100 * (A + 1)) hA' (by positivity)
  refine ⟨κ, hκ, 4 / 3 * (51200 * Real.exp 57 * A), by positivity, ?_⟩
  intro n H t p r hTt hr hsmall hvol aSeed haT hclock seedTrace v hav hvt hv hnrv x hx ρ' hlow
    hup hball
  have hr0 : 0 < r := hsmall.1
  have hshift := earlier_seed_on_half_depth_P6B haT p r A hr hclock hsmall hvol seedTrace v hav
    hvt hv
  obtain ⟨hseedV, hvolV, htimeV⟩ := hshift
  have hexp : 1 ≤ Real.exp 57 := Real.one_le_exp (by norm_num)
  have hTv : 51200 * Real.exp 57 * A ≤ (v : ℝ) := by nlinarith
  have hinv : (51200 * Real.exp 57 * A)⁻¹ ≤ A⁻¹ * Real.exp (-57) / 512 := by
    rw [Real.exp_neg, mul_inv, mul_inv]
    have : (51200 : ℝ)⁻¹ ≤ 1 / 512 := by norm_num
    calc (51200 : ℝ)⁻¹ * (Real.exp 57)⁻¹ * A⁻¹ ≤ 1 / 512 * (Real.exp 57)⁻¹ * A⁻¹ := by
          gcongr
      _ = A⁻¹ * (Real.exp 57)⁻¹ / 512 := by ring
  have hvolA' : ENNReal.ofReal ((51200 * Real.exp 57 * A)⁻¹ * (r / 100) ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage v) v)
        (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
        (r / 100) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hinv (by positivity))).trans hvolV
  have hball' : A * r ≤ 51200 * Real.exp 57 * A * (r / 100) := by
    have h1 : 1 ≤ 512 * Real.exp 57 := by nlinarith
    nlinarith [mul_pos hA hr0]
  have hx' := riemannianBallOf_mono _ _ hball' hx
  have hup' : ρ' ≤ 100 * (A + 1) * (r / 100) := by
    have he : 100 * (A + 1) * (r / 100) = (A + 1) * r := by ring
    rw [he]
    exact hup
  have hr2 : (r / 100) ^ 2 = r ^ 2 / 10000 := by ring
  have hvt' : (v : ℝ) ≤ (t : ℝ) := hvt
  have hscale' : ∃ T : ℝ, (v : ℝ) ≤ T ∧ T ≤ 2 * (v : ℝ) - (r / 100) ^ 2 ∧ nr T / 100 ≤ r / 100 :=
    ⟨4 * ((t : ℝ) - r ^ 2 / 2) / 3, by linarith [sq_nonneg r],
      by rw [hr2]; linarith [sq_nonneg r], by linarith⟩
  exact hK n v _ (r / 100) htimeV (accuracy_on_late_half_P6A hacc hA' hTv) hseedV hvolA' hscale'
    x hx' ρ' hlow hup' hball

/-- **consumer**：块数据前向 K5（G1b）型的任意前向 K5 + S7 ⇒ seed shift 后的 wide window。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr v : ℝ → ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α) (hK5 : SeedReducedVolumeFwd_C11FR F δ α nr v)
    {A : ℝ} (hA : 0 < A) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t), (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (w : Icc (0 : ℝ) H.horizon) (haw : aSeed ≤ w) (hwt : w ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (w : ℝ) → nr (4 * ((t : ℝ) - r ^ 2 / 2) / 3) ≤ r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
          (seedTrace.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt))
          (A * r),
        ∀ ρ' : ℝ, nr w / 100 ≤ ρ' → ρ' ≤ (A + 1) * r →
          H.isParabolicallyRmControlledBall w x ρ' →
          ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage w) w) x ρ' :=
  wideWindowFwd_of_wideFwd_C11FR hacc (localKappaWideFwd_of_reducedVolumeFwd_C11FR hK5) hA

end GC.LongTime.Ch11
