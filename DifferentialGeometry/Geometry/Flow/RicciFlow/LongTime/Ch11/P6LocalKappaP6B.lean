import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedShiftP6B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StatementP6A

/-!
# P6 / L5 = M5：局部 κ(A)（KL 84.1(a)）的陈述、seed shift 推广与小 A 情形（O-CH11-P6B G1）

后缀 `_P6B`。`H := (F.tower.history n).toHistory`，`nr` = cutoff 参数的 neck radius（`q.neckRadius`），
尺度下界 `nr t / 100` 照 astra outer tuple（`SH/PreparedSpatialPhysicalVolumeEvent.lean:672–745`）。

* **`hKappaLocal`（OPEN 供给，lead / P6A 22:2x 裁定的 fallback）**：`LocalKappaSupply_P6B F δ α nr`
  = KL 84.1(a) envelope 形：`∀ A > 0, ∃ κ > 0`，S8 的前 4 个前提（`2r² < t`、`[t/2,t]` 上
  `δ < α A`、`hasSmallParabolicCurvature`、`vol B(p,r) ≥ A⁻¹r³`）⇒ `∀ x ∈ B(p, A r)`、
  `∀ ρ' ∈ [nr t/100, r]`，`x` 处尺度 `ρ'` 的 controlled ball 有 `κ ρ'³ ≤ vol B(x, ρ')`。
  KL 的证明是 reduced-volume 论证（`B(p, A r)` 上没有 Ricci 下界），这里**不证**；若 outer tuple 的
  `κVol / κLarge` 子句落地，可直接投影。
* late 形 `LocalKappaLateSupply_P6B F nr`（`∃ κ T`，`T ≤ t`，无 accuracy）；
  envelope + S7 ⇒ late（`localKappaLate_of_envelope_P6B`，`T = A`，用 P6A 的 L1）。
* **树内定理（本文件的数学内容）**：
  - `localKappaWindow_of_late_P6B`：late 形 ⇒ **window 形** `LocalKappaWindowAt_P6B`：种子 `(p,t,r)`
    的 backward 半窗 `v ∈ [t − r²/2, t]` 上、种子 trace 点 `O_v` 周围 `B_v(O_v, A r)` 的点在尺度
    `[nr v/100, r/100)` 处 κ-noncollapsed。这是 point selection 选出的坏点 `(s, y)`（`s ≥ t − r²/2`，
    `y ∈ B_s(O_s, (A+1) r)`）及其 backward 窗所需的形状。几何核心是 seed shift
    `earlier_seed_on_half_depth_P6B`（`P6SeedShiftP6B`）。
  - `localKappaLateAt_of_le_quarter_P6B`：`A ≤ 1/4` 时 late 形无条件成立（`κ = A⁻¹e⁻³/4096`，
    Bishop–Gromov），说明供给非空真；`LocalKappaLateAt_P6B.mono`：对 `A` 向下、对 `κ` 向下单调。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-! ## 陈述 -/

/-- **KL 84.1(a) 在放大因子 `A`、系数 `κ` 处（envelope 形，S8 的前 4 个前提）**。 -/
def LocalKappaAt_P6B {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ)
    (A κ : ℝ) : Prop :=
  ∀ n, let H := (F.tower.history n).toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) →
    (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ρ' : ℝ, nr t / 100 ≤ ρ' → ρ' ≤ r → H.isParabolicallyRmControlledBall t x ρ' →
      ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) x ρ'

/-- **`hKappaLocal`（OPEN）**：KL 84.1(a) 对全部 `A > 0`（envelope 形）。 -/
def LocalKappaSupply_P6B {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ) : Prop :=
  ∀ A, 0 < A → ∃ κ, 0 < κ ∧ LocalKappaAt_P6B F δ α nr A κ

/-- KL 84.1(a) late 形：`∃ T > 0`，`T ≤ t` 代替 accuracy 前提。 -/
def LocalKappaLateAt_P6B {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (nr : ℝ → ℝ) (A κ : ℝ) : Prop :=
  ∃ T : ℝ, 0 < T ∧
  ∀ n, let H := (F.tower.history n).toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    T ≤ (t : ℝ) →
    2 * r ^ 2 < (t : ℝ) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ρ' : ℝ, nr t / 100 ≤ ρ' → ρ' ≤ r → H.isParabolicallyRmControlledBall t x ρ' →
      ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) x ρ'

/-- late 形对全部 `A > 0`。 -/
def LocalKappaLateSupply_P6B {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (nr : ℝ → ℝ) : Prop :=
  ∀ A, 0 < A → ∃ κ, 0 < κ ∧ LocalKappaLateAt_P6B F nr A κ

/-- **window 形**（L8 / point selection 用）：种子 `(p, t, r)` 的 backward 半窗 `v ∈ [t − r²/2, t]`
上，种子 trace 点 `O_v` 周围 `B_v(O_v, A r)` 的点在尺度 `[nr v/100, r/100)` 处 κ-noncollapsed。 -/
def LocalKappaWindowAt_P6B {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (nr : ℝ → ℝ) (A κ : ℝ) : Prop :=
  ∃ T : ℝ, 0 < T ∧
  ∀ n, let H := (F.tower.history n).toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    T ≤ (t : ℝ) →
    2 * r ^ 2 < (t : ℝ) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t), (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono haT) p,
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
      (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
      (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
      (A * r),
    ∀ ρ' : ℝ, nr v / 100 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
      ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ'

/-! ## 单调性与 envelope ⇒ late -/

/-- late 形对 `A` 向下、对 `κ` 向下单调（种子体积前提与球都随 `A` 变弱 / 变小）。 -/
theorem LocalKappaLateAt_P6B.mono {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {nr : ℝ → ℝ} {A A' κ κ' : ℝ}
    (h : LocalKappaLateAt_P6B F nr A κ) (hA' : 0 < A') (hAA : A' ≤ A) (hκ : κ' ≤ κ) :
    LocalKappaLateAt_P6B F nr A' κ' := by
  obtain ⟨T, hT, hK⟩ := h
  refine ⟨T, hT, ?_⟩
  intro n H t p r hTt hr hsmall hvol x hx ρ' hlow hup hball
  have hr0 : 0 < r := hsmall.1
  have hρ' : 0 < ρ' := hball.1
  have hinv : A⁻¹ ≤ A'⁻¹ := inv_anti₀ hA' hAA
  have hvol' : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage t) t) p r :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hinv (by positivity))).trans hvol
  have hx' := riemannianBallOf_mono _ p (mul_le_mul_of_nonneg_right hAA hr0.le) hx
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hκ (by positivity))).trans
    (hK n t p r hTt hr hsmall hvol' x hx' ρ' hlow hup hball)

/-- envelope 形 + S7 ⇒ late 形（`T = A`；`t ≥ A` 时 accuracy 前提由 P6A 的 L1 自动成立）。 -/
theorem localKappaLateAt_of_envelope_P6B {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ} {A κ : ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α) (hA : 0 < A)
    (h : LocalKappaAt_P6B F δ α nr A κ) : LocalKappaLateAt_P6B F nr A κ := by
  refine ⟨A, hA, ?_⟩
  intro n H t p r hT hr hsmall hvol x hx ρ' hlow hup hball
  exact h n t p r hr (accuracy_on_late_half_P6A hacc hA hT) hsmall hvol x hx ρ' hlow hup hball

/-- `hKappaLocal` + S7 ⇒ late 供给。 -/
theorem localKappaLateSupply_of_envelope_P6B {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α) (h : LocalKappaSupply_P6B F δ α nr) :
    LocalKappaLateSupply_P6B F nr := by
  intro A hA
  obtain ⟨κ, hκ, hK⟩ := h A hA
  exact ⟨κ, hκ, localKappaLateAt_of_envelope_P6B hacc hA hK⟩

/-! ## 小 A：树内无条件成立 -/

/-- **树内**：`0 < A ≤ 1/4` 时 late 形对任意 `F`、`nr` 成立（`T = 1`，`κ = A⁻¹e⁻³/4096`）：
`B(p, A r) ⊆ B(p, r/4)`，种子球上 Bishop–Gromov（`volume_lower_of_nearby_center_P6B`）。 -/
theorem localKappaLateAt_of_le_quarter_P6B {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (nr : ℝ → ℝ) {A : ℝ} (hA : 0 < A) (hA4 : A ≤ 1 / 4) :
    LocalKappaLateAt_P6B F nr A (A⁻¹ * Real.exp (-3) / 4096) := by
  refine ⟨1, one_pos, ?_⟩
  intro n H t p r _ _ hsmall hvol x hx ρ' _ hup hball
  have hr : 0 < r := hsmall.1
  have hρ' : 0 < ρ' := hball.1
  have hx4 : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (r / 4) :=
    riemannianBallOf_mono _ p (by nlinarith) hx
  set c : ℝ := A⁻¹ * Real.exp (-3) / 512 with hc
  have hc0 : 0 ≤ c := by positivity
  have hnear := fun (s : ℝ) (hs : 0 < s) (hsr : s ≤ r / 2) =>
    volume_lower_of_nearby_center_P6B hsmall hvol hx4 hs hsr
  have hcoef : A⁻¹ * Real.exp (-3) / 4096 = c / 8 := by rw [hc]; ring
  rw [hcoef]
  rcases le_or_gt ρ' (r / 2) with hρr | hρr
  · refine (ENNReal.ofReal_le_ofReal ?_).trans (hnear ρ' hρ' hρr)
    have h3 : 0 ≤ ρ' ^ 3 := by positivity
    nlinarith
  · have hhalf := hnear (r / 2) (by positivity) le_rfl
    refine (ENNReal.ofReal_le_ofReal ?_).trans (hhalf.trans
      (MeasureTheory.measure_mono (riemannianBallOf_mono _ _ hρr.le)))
    have hρ3 : ρ' ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hρ'.le hup 3
    have : c / 8 * ρ' ^ 3 ≤ c / 8 * r ^ 3 := mul_le_mul_of_nonneg_left hρ3 (by positivity)
    calc c / 8 * ρ' ^ 3 ≤ c / 8 * r ^ 3 := this
      _ = c * (r / 2) ^ 3 := by ring

/-! ## seed shift ⇒ window 形 -/

/-- **L5 主定理（树内）**：late 形的 (a) ⇒ window 形。给定 `A`，在放大因子
`A' = 51200·e⁵⁷·A` 处取 late 形的 `κ`，对每个 `v ∈ [t − r²/2, t]` 用 seed shift 得到种子
`(O_v, v, r/100)`（体积系数 `A⁻¹e⁻⁵⁷/512 ≥ A'⁻¹`），`B_v(O_v, A r) = B_v(O_v, 100A·(r/100)) ⊆
B_v(O_v, A'·(r/100))`；late 阈值 `T' ≤ 3t/4 ≤ v`。 -/
theorem localKappaWindow_of_late_P6B {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {nr : ℝ → ℝ}
    (h : LocalKappaLateSupply_P6B F nr) :
    ∀ A, 0 < A → ∃ κ, 0 < κ ∧ LocalKappaWindowAt_P6B F nr A κ := by
  intro A hA
  set A' : ℝ := 51200 * Real.exp 57 * A with hA'
  have hA'0 : 0 < A' := by positivity
  obtain ⟨κ, hκ, T', hT', hK⟩ := h A' hA'0
  refine ⟨κ, hκ, 4 / 3 * T', by positivity, ?_⟩
  intro n H t p r hTt hr hsmall hvol aSeed haT hclock seedTrace v hav hvt hv x hx ρ' hlow hup
    hball
  have hr0 : 0 < r := hsmall.1
  obtain ⟨hseedV, hvolV, htimeV⟩ :=
    earlier_seed_on_half_depth_P6B haT p r A hr hclock hsmall hvol seedTrace v hav hvt hv
  set O := seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)
  have hexp : 1 ≤ Real.exp 57 := Real.one_le_exp (by norm_num)
  have hTv : T' ≤ (v : ℝ) := by nlinarith
  have hinv : A'⁻¹ ≤ A⁻¹ * Real.exp (-57) / 512 := by
    rw [hA', Real.exp_neg]
    have he : 0 < Real.exp 57 := Real.exp_pos 57
    rw [mul_inv, mul_inv]
    have : (51200 : ℝ)⁻¹ ≤ 1 / 512 := by norm_num
    calc (51200 : ℝ)⁻¹ * (Real.exp 57)⁻¹ * A⁻¹ ≤ 1 / 512 * (Real.exp 57)⁻¹ * A⁻¹ := by
          gcongr
      _ = A⁻¹ * (Real.exp 57)⁻¹ / 512 := by ring
  have hvolA' : ENNReal.ofReal (A'⁻¹ * (r / 100) ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage v) v) O (r / 100) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hinv (by positivity))).trans hvolV
  have hball' : A * r ≤ A' * (r / 100) := by
    rw [hA']
    have : A * r ≤ 512 * Real.exp 57 * A * r := by
      have h1 : 1 ≤ 512 * Real.exp 57 := by nlinarith
      nlinarith [mul_pos hA hr0]
    nlinarith
  have hx' := riemannianBallOf_mono _ O hball' hx
  exact hK n v O (r / 100) hTv htimeV hseedV hvolA' x hx' ρ' hlow hup.le hball

/-! ## consumer -/

/-- consumer：`hKappaLocal` + S7 ⇒ 每个 `A` 的 window 形（point selection 的 backward 窗上的 κ）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α) (hκ : LocalKappaSupply_P6B F δ α nr)
    {A : ℝ} (hA : 0 < A) : ∃ κ, 0 < κ ∧ LocalKappaWindowAt_P6B F nr A κ :=
  localKappaWindow_of_late_P6B (localKappaLateSupply_of_envelope_P6B hacc hκ) A hA

/-- consumer：小 `A` 的 late 形是树内定理，系数显式为正。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (nr : ℝ → ℝ) : ∃ κ, 0 < κ ∧ LocalKappaLateAt_P6B F nr (1 / 4) κ :=
  ⟨(1 / 4 : ℝ)⁻¹ * Real.exp (-3) / 4096, by positivity,
    localKappaLateAt_of_le_quarter_P6B F nr (by norm_num) le_rfl⟩

end GC.LongTime.Ch11
