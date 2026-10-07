import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedScaleC11Q4b
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaDataSupplyC11KD

/-!
# 尺度 wide + late doubling 种子尺度引理（O-CH11-KAPPA3 G7，后缀 `_C11Q4b`）

lead 裁定（08:4x）：late doubling 作显式前提 `hnrDoubling : ∃ C T₀, ∀ t ≥ T₀, nr(3t/4) ≤ C·nr(t)`
（KL 的 r(t) 在二进块上分段常数、相邻块比有界；由 astra BlockStep 的"相邻块半径比有界"推出的核查 = 重置后
outer 线小任务）。本文件：
* `LocalKappaWideScaledAt_C11Q4b` / `…Supply_C11Q4b`：`LocalKappaWideAt_C11Q` 原文 + 种子 `nr t/100 ≤ r`，
  任意上沿 `L`；`localKappaWideScaled_of_reducedVolumeScaled_C11Q4b`：G6 的尺度 K5 ⇒ 尺度 wide
  （`localKappaWide_of_reducedVolume_C11Q` 的证明，多传 `hscale`）；
* `seedScale_of_doubling_C11Q4b`：`hnrDoubling` + `r n / nr(Tn) → ∞` ⇒ `∀ᶠ n, ∀ v ∈ [Tn − r²/2, Tn],
  nr v ≤ r n`（KDATA / SMALLVOL 在 P6 种子路径上要的 `nr(t − r²/2) ≤ r`）；
  `ratio_of_selection_C11Q4b`：P6SEL 输出（`R n ≤ nr(Tn)⁻²`、`r n/200·√R n → ∞`）⇒ `r n / nr(Tn) → ∞`；
* `wideWindowScaled_of_wideScaled_C11Q4b`：尺度 wide + S7 ⇒ seed shift 后的 wide window（=
  `wideLate_of_wideSupply_C11V3` ∘ `wideWindow_of_wideLate_C11V2`，`L = 100(A+1)`、`A' = 51200e⁵⁷A`），
  只多一个前提 `nr v ≤ r`（shift 种子 `(v, O_v, r/100)` 的尺度条件）。
**剩余（精确形，SMALLVOL / KDATA sonnet）**：`hsmall_of_wide_window_late_C11V3` 的 `hW` 换成本文件的
window 形（多 `nr v ≤ r`），结论 `hsmallScale` 也带 `nr v ≤ r`（或种子侧 `∀ v ∈ [t − r²/2, t], nr v ≤ r`），
再经 `localKappaWindow_zero_of_window_and_small_C11V` / `pre841Data_of_window_C11K` 只在 P6 种子处消费
（P6 种子由 `seedScale_of_doubling_C11Q4b` 满足）。
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

/-! ## 1. 尺度 wide -/

/-- **尺度 wide（逐 `A, L, κ`）**：`LocalKappaWideAt_C11Q` 原文，种子另加 `nr t/100 ≤ r`。 -/
def LocalKappaWideScaledAt_C11Q4b {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ)
    (A L κ : ℝ) : Prop :=
  ∀ n, let H := (F.tower.history n).toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) →
    (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    nr t / 100 ≤ r →
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ρ' : ℝ, nr t / 100 ≤ ρ' → ρ' ≤ L * r → H.isParabolicallyRmControlledBall t x ρ' →
      ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) x ρ'

/-- 尺度 wide 的供给：`∀ A > 0, ∀ L > 0, ∃ κ > 0`。 -/
def LocalKappaWideScaledSupply_C11Q4b {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ) : Prop :=
  ∀ A L, 0 < A → 0 < L → ∃ κ, 0 < κ ∧ LocalKappaWideScaledAt_C11Q4b F δ α nr A L κ

/-- **尺度 K5 + K6 ⇒ 尺度 wide（任意 `L`）**：`localKappaWide_of_reducedVolume_C11Q` 的证明（K6 取树内
`controlledBallVolumeFromReducedVolume_holds_C11Q`），K5 在种子自身调用，种子尺度前提原样传入。 -/
theorem localKappaWideScaled_of_reducedVolumeScaled_C11Q4b {P : OrientedThreeStage.{u}}
    {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr v : ℝ → ℝ}
    (hK5 : SeedReducedVolumeScaled_C11Q4 F δ α nr v) :
    LocalKappaWideScaledSupply_C11Q4b F δ α nr := by
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

/-! ## 2. late doubling ⇒ P6 种子的 shift 尺度条件 -/

/-- **P6SEL 输出 ⇒ `r n / nr(Tn) → ∞`**：`R n ≤ nr(Tn)⁻²`（坏点不在 native canonical 区）且
`r n/200·√R n → ∞`。 -/
theorem ratio_of_selection_C11Q4b {nr : ℝ → ℝ} {Tn r R : ℕ → ℝ} (hnr : ∀ n, 0 < nr (Tn n))
    (hr : ∀ n, 0 < r n) (hRle : ∀ n, R n ≤ (nr (Tn n) ^ 2)⁻¹)
    (hdiv : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop) :
    Tendsto (fun n => r n / nr (Tn n)) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) hdiv
  have hs : Real.sqrt (R n) ≤ (nr (Tn n))⁻¹ := by
    calc Real.sqrt (R n) ≤ Real.sqrt ((nr (Tn n) ^ 2)⁻¹) := Real.sqrt_le_sqrt (hRle n)
      _ = (nr (Tn n))⁻¹ := by rw [Real.sqrt_inv, Real.sqrt_sq (hnr n).le]
  have hs0 := Real.sqrt_nonneg (R n)
  have hrn := hr n
  calc r n / 200 * Real.sqrt (R n) ≤ r n * Real.sqrt (R n) := by nlinarith
    _ ≤ r n * (nr (Tn n))⁻¹ := mul_le_mul_of_nonneg_left hs hrn.le
    _ = r n / nr (Tn n) := (div_eq_mul_inv _ _).symm

/-- **`seedScale_of_doubling_C11Q4b`**：late doubling `nr(3t/4) ≤ C·nr(t)`（`t ≥ T₀`）+ `Tn → ∞` +
`r n / nr(Tn) → ∞`（`ratio_of_selection_C11Q4b`）+ `2 r n² < Tn` ⇒ 最终对所有
`v ∈ [Tn − r n²/2, Tn]`，`nr v ≤ r n`（`v ≥ 3Tn/4`，单调 + doubling）。 -/
theorem seedScale_of_doubling_C11Q4b {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < nr t)
    (hnrDoubling : ∃ C T₀ : ℝ, ∀ t, T₀ ≤ t → nr (3 * t / 4) ≤ C * nr t)
    {Tn r : ℕ → ℝ} (hT : ∀ n, 2 * r n ^ 2 < Tn n) (hlate : Tendsto Tn atTop atTop)
    (hratio : Tendsto (fun n => r n / nr (Tn n)) atTop atTop) :
    ∀ᶠ n in atTop, ∀ v : ℝ, Tn n - r n ^ 2 / 2 ≤ v → v ≤ Tn n → nr v ≤ r n := by
  obtain ⟨C, T₀, hC⟩ := hnrDoubling
  filter_upwards [hlate.eventually_ge_atTop T₀, hratio.eventually_ge_atTop (max C 0)] with
    n hTn hrat
  intro v hv1 _hv2
  have hTn2 := hT n
  have hTpos : 0 < Tn n := by nlinarith [sq_nonneg (r n)]
  have h34 : 3 * Tn n / 4 ≤ v := by nlinarith
  have h1 : nr v ≤ nr (3 * Tn n / 4) :=
    hanti (Set.mem_Ici.mpr (by positivity)) (Set.mem_Ici.mpr (by linarith)) h34
  have h2 := hC (Tn n) hTn
  have hnrpos := hpos (Tn n) hTpos.le
  have h3 : max C 0 * nr (Tn n) ≤ r n := (le_div_iff₀ hnrpos).mp hrat
  have h4 : C * nr (Tn n) ≤ max C 0 * nr (Tn n) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hnrpos.le
  linarith

/-! ## 3. seed shift：尺度 wide ⇒ wide window（多 `nr v ≤ r`） -/

/-- **尺度 wide + S7 ⇒ wide window（seed shift，`nr v ≤ r`）**：`wideLate_of_wideSupply_C11V3`
（`A' = 51200e⁵⁷A`、`L = 100(A+1)`、accuracy 由 `accuracy_on_late_half_P6A`）与
`wideWindow_of_wideLate_C11V2`（`earlier_seed_on_half_depth_P6B`，shift 种子 `(v, O_v, r/100)`）的合成；
shift 种子的尺度条件 `nr v/100 ≤ r/100` 由前提 `nr v ≤ r` 给出。 -/
theorem wideWindowScaled_of_wideScaled_C11Q4b {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α) (h : LocalKappaWideScaledSupply_C11Q4b F δ α nr)
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
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) → nr v ≤ r →
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
  have hscale' : nr v / 100 ≤ r / 100 := by linarith
  exact hK n v _ (r / 100) htimeV (accuracy_on_late_half_P6A hacc hA' hTv) hseedV hvolA' hscale'
    x hx' ρ' hlow hup' hball

/-- **consumer（G7）**：G6 的尺度 K5（例如经 `seedReducedVolumeScaled_of_block_C11Q4`）+ S7 ⇒ seed shift
后的 wide window（多 `nr v ≤ r`），即 `hsmall_of_wide_window_late_C11V3` 的 `hW` 加 `nr v ≤ r` 的形；
P6 种子上该前提由 `seedScale_of_doubling_C11Q4b` 最终成立。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr v : ℝ → ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α) (hK5 : SeedReducedVolumeScaled_C11Q4 F δ α nr v)
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
          (t : ℝ) - r ^ 2 / 2 ≤ (w : ℝ) → nr w ≤ r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
          (seedTrace.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt))
          (A * r),
        ∀ ρ' : ℝ, nr w / 100 ≤ ρ' → ρ' ≤ (A + 1) * r →
          H.isParabolicallyRmControlledBall w x ρ' →
          ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage w) w) x ρ' :=
  wideWindowScaled_of_wideScaled_C11Q4b hacc
    (localKappaWideScaled_of_reducedVolumeScaled_C11Q4b hK5) hA

/-- **consumer（G7，P6 种子）**：P6SEL 型输出 + late doubling ⇒ shift 尺度条件最终成立。 -/
example {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0)) (hpos : ∀ t, 0 ≤ t → 0 < nr t)
    (hnrDoubling : ∃ C T₀ : ℝ, ∀ t, T₀ ≤ t → nr (3 * t / 4) ≤ C * nr t)
    {Tn r R : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hT : ∀ n, 2 * r n ^ 2 < Tn n)
    (hlate : Tendsto Tn atTop atTop) (hRle : ∀ n, R n ≤ (nr (Tn n) ^ 2)⁻¹)
    (hdiv : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop) :
    ∀ᶠ n in atTop, ∀ v : ℝ, Tn n - r n ^ 2 / 2 ≤ v → v ≤ Tn n → nr v ≤ r n := by
  have hTpos : ∀ n, 0 ≤ Tn n := fun n => by nlinarith [hT n, sq_nonneg (r n)]
  exact seedScale_of_doubling_C11Q4b hanti hpos hnrDoubling hT hlate
    (ratio_of_selection_C11Q4b (fun n => hpos _ (hTpos n)) hr hRle hdiv)

end GC.LongTime.Ch11
