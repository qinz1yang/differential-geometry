import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaBarrierWindowCoreC11Q2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaClockAttainC11Q2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaReducedLengthC11Q
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ReducedVolumeTruncation

/-!
# K3 窗口版 producer + δ₀ 尺度处理 + K4 常数链闭合（O-CH11-KAPPA2 G1，后缀 `_C11Q2`）

喂 `localKappa_of_K1_K2_K3_K5a_C11Q` 的 K3 槽：`SurgeryActionBarrier_C11Q F δ α nr Λ` 的两个子句
都由树内对象证出，只剩**一条显式尺度前提**（简报 G1 选项二："把 `δ₀(r₀)` 作显式参数"）。

## 子句 1（barely admissible 排除）
`windowBarrier_slice_C11Q2`：`KappaBarrierWindowCoreC11Q2` 的窗口屏障（常数 `(δ₀, ε₀, R₀, m₀)`
= 树内同一组，依赖绝对输入 `(E, A, r₀, qcan, Λ_rec, ρ, Ctime)`）+ 地板换算（合同的任意真实地板 `Bf`
↔ 树内 `3/a₀`：取 `b = min Bf (3/a₀)`，`regularizedCost / regularMinimizerEndpoints_eq_of_scalar_lower_
bound_le`）+ 切片换元（`√(t − s)`）。

## 子句 2（空间边界逃逸 / cutoff 最小值可达）
`cutoffValue_attained_C11Q2`：**无条件**可达（任何 `v ∈ (0, r/√2]`，含 event 时刻切片），由单时钟
可达性 `physicalWeightedCost_exists_min_at_clock_C11Q2`（`KappaClockAttainC11Q2`）+ 近期地板
`3/(a₀ + t/2)`（Hamilton–Ivey 沿 records 传播）。合同里的前提 `M(v) < Λ·2rv` 没有用到。

## 尺度一致性（`δ₀` 依赖绝对半径 `r₀`）
树内常数是**绝对尺度**的；对种子 `(t, r)` 与基点受控球 `ϱ₀ ≥ nr(t)/100`，取最坏情形输入
`E = √(t/2)`（窗口 `[t/2, t]`，正是 S7 accuracy 的窗口；`v ≤ r/√2 < √(t/2)`）、
`A = Λ_A·√(t/2)`（`𝓛 ≤ (Λ_A − 1)r < Λ_A r < Λ_A√(t/2)`）、`r₀ = nr(t)/100`（`mono_radius`）、
`qcan(t)`、`ρ̄(t)`——单调性把每个种子的要求归到**每个时刻 `t` 一组常数**
`kappaWindowConsts_C11Q2 … t`。显式前提 `KappaWindowScale_C11Q2`：F 的 cutoff 参数满足这组常数，且
`α A ≤ δ₀(A, t)` 于 `[t/2, t]`。**注意**：`ε₀, R₀, m₀`（model accuracy / radius / order，F 的固定常数）
随 `t` 的一致性正是"δ₀ 尺度引理"的内容（需 parabolic rescaling 或 seed 归一化重证屏障，本组未做）；
在有界时间段上它由常数单调性满足。

## K4 常数链闭合
`Λ := kappaBarrierLevel_C11Q2 C₂ = 4 e^{C₂/2 + 32/√2}`（K4 的要求，只依赖 `C₂`）；`δ₀` 由该 `Λ` 经
尺度前提给出——**无循环**（`boundedReducedLength_of_window_C11Q2`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. 窗口屏障的常数（树内常数的显式化） -/

/-- 窗口屏障在常数 `c = (δ₀, ε₀, R₀, m₀)` 下成立（`exists_window_regularMinimizerEndpoint_C11Q2`
的结论体；作用量地板 `3/a₀`）。 -/
def WindowBarrierSpec_C11Q2 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (a₀ E A r₀ qcan Λ ρ : ℝ) (Ctime : ℝ≥0) (c : ℝ × ℝ × ℝ × ℕ) : Prop :=
  0 < c.1 ∧ 0 < c.2.1 ∧ 0 < c.2.2.1 ∧
  ∀ (H : ObservedHistory.{u}), Nonempty (InitialIdentification P₀ g₀ H) →
  ∀ (parameters : CutoffParameters),
    c.2.2.2 ≤ parameters.modelOrder → c.2.2.1 ≤ parameters.modelRadius →
    parameters.modelAccuracy ≤ c.2.1 → parameters.recenterConstant ≤ Λ →
  ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
    (∀ i b, ((records i).static b).hasCanonicalWindow) →
  ∀ (t : Icc (0 : ℝ) H.horizon),
    (∀ j : Fin H.eventCount, t.val - E ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
      parameters.delta (H.time j.succ) ≤ c.1) →
    (∀ j : Fin H.eventCount, t.val - E ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
      parameters.neckRadius (H.time j.succ) ≤ ρ) →
    (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier), t.val - E ^ 2 ≤ H.time j →
      ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
        qcan < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
            Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) →
  ∀ (p : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t p r₀ →
  ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ), v ≤ E →
  ∀ q : (H.stage first).Carrier,
    H.regularizedCost first (H.activeStage t) hle t (3 / a₀) 0 v p q < (A : WithTop ℝ) →
    q ∈ H.regularMinimizerEndpoints first (H.activeStage t) hle t (3 / a₀) v p

/-- 初始数据 `(P₀, g₀)` 给 `a₀`（Hamilton–Ivey 区域 + 初始标量地板 `−3/a₀`），并对每组正输入给出窗口屏障
常数。 -/
theorem exists_windowBarrierSpec_C11Q2 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
    (∀ (H : ObservedHistory.{u}), InitialIdentification P₀ g₀ H →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∀ (E A r₀ qcan Λ ρ : ℝ) (Ctime : ℝ≥0), 0 ≤ E → 0 < r₀ → 0 < qcan → 0 < Λ → 0 < ρ →
    ∃ c : ℝ × ℝ × ℝ × ℕ, WindowBarrierSpec_C11Q2 P₀ g₀ a₀ E A r₀ qcan Λ ρ Ctime c := by
  obtain ⟨a₀, ha₀, hinitial⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  refine ⟨a₀, ha₀, hinitial, ?_⟩
  intro E A r₀ qcan Λ ρ Ctime hE hr₀ hqcan hΛ hρ
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hbarrier⟩ :=
    ObservedHistory.exists_window_regularCrossing_minimizer_C11Q2.{u}
      A E r₀ qcan a₀ Λ ρ Ctime hE hr₀ hqcan ha₀ hΛ hρ
  refine ⟨(δ₀, ε₀, R₀, m₀), hδ₀, hε₀, hR₀, ?_⟩
  intro H hid parameters hm hradius haccuracy hrecenter records hcanonical t hδ hρp hderiv
    p hball first hle v hvE q hcost
  obtain ⟨identification⟩ := hid
  have hstart := hinitial H identification
  exact hbarrier H parameters hm hradius haccuracy hrecenter records hstart.1 hstart.2 t hδ hρp
    hderiv p hball first hle v hvE (fun i _ _ b => hcanonical i b) q hcost

/-- 树内 `a₀`（只依赖初始数据）。 -/
def windowBarrierA₀_C11Q2 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : ℝ :=
  Classical.choose (exists_windowBarrierSpec_C11Q2 P₀ g₀)

theorem windowBarrierA₀_spec_C11Q2 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    0 < windowBarrierA₀_C11Q2 P₀ g₀ ∧
    (∀ (H : ObservedHistory.{u}), InitialIdentification P₀ g₀ H →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) (windowBarrierA₀_C11Q2 P₀ g₀) x) ∧
        ∀ x, -3 / windowBarrierA₀_C11Q2 P₀ g₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∀ (E A r₀ qcan Λ ρ : ℝ) (Ctime : ℝ≥0), 0 ≤ E → 0 < r₀ → 0 < qcan → 0 < Λ → 0 < ρ →
    ∃ c : ℝ × ℝ × ℝ × ℕ,
      WindowBarrierSpec_C11Q2 P₀ g₀ (windowBarrierA₀_C11Q2 P₀ g₀) E A r₀ qcan Λ ρ Ctime c :=
  Classical.choose_spec (exists_windowBarrierSpec_C11Q2 P₀ g₀)

/-- **树内窗口屏障常数** `(δ₀, ε₀, R₀, m₀)`（绝对尺度输入；非正输入时取占位值，不被使用）。 -/
def windowBarrierConsts_C11Q2 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (E A r₀ qcan Λ ρ : ℝ) (Ctime : ℝ≥0) : ℝ × ℝ × ℝ × ℕ :=
  if h : 0 ≤ E ∧ 0 < r₀ ∧ 0 < qcan ∧ 0 < Λ ∧ 0 < ρ then
    Classical.choose ((windowBarrierA₀_spec_C11Q2 P₀ g₀).2.2 E A r₀ qcan Λ ρ Ctime h.1 h.2.1
      h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  else (1, 1, 1, 0)

theorem windowBarrierConsts_spec_C11Q2 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    {E A r₀ qcan Λ ρ : ℝ} (Ctime : ℝ≥0) (hE : 0 ≤ E) (hr₀ : 0 < r₀) (hqcan : 0 < qcan)
    (hΛ : 0 < Λ) (hρ : 0 < ρ) :
    WindowBarrierSpec_C11Q2 P₀ g₀ (windowBarrierA₀_C11Q2 P₀ g₀) E A r₀ qcan Λ ρ Ctime
      (windowBarrierConsts_C11Q2 P₀ g₀ E A r₀ qcan Λ ρ Ctime) := by
  have h : 0 ≤ E ∧ 0 < r₀ ∧ 0 < qcan ∧ 0 < Λ ∧ 0 < ρ := ⟨hE, hr₀, hqcan, hΛ, hρ⟩
  unfold windowBarrierConsts_C11Q2
  rw [dite_eq_left h]
  exact Classical.choose_spec ((windowBarrierA₀_spec_C11Q2 P₀ g₀).2.2 E A r₀ qcan Λ ρ Ctime
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)

/-! ## 2. 子句 1：切片形屏障（地板换算 + 窗口屏障） -/

/-- 真实地板 `Bf` 与树内 `3/a₀` 的公共下界 `min Bf (3/a₀)`（records + 初始 Hamilton–Ivey）。 -/
theorem scalarFloor_min_C11Q2 (R : RetainedCoreHistory.{u}) {Bf a₀ : ℝ} (ha₀ : 0 < a₀)
    (hBf : ScalarFloor_C11Q R Bf) {params : CutoffParameters}
    (records : ∀ i, GeometricCutoffRecord R.toHistory i params)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (R.toHistory.initialMetric 0) a₀ x)
    (hscalar : ∀ x, -3 / a₀ ≤ metricScalarAt (R.toHistory.initialMetric 0) x) :
    ∀ (j : Fin (R.toHistory.eventCount + 1)), ∀ s ∈ R.toHistory.stageDomain j,
      ∀ y : (R.toHistory.stage j).Carrier,
        -(min Bf (3 / a₀)) ≤ metricScalarAt (R.toHistory.stageMetric j s) y := by
  intro j s hs y
  have hHI := (R.toHistory.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed
    hscalar).1 j s hs y
  have hs0 : 0 ≤ s := (R.toHistory.stageDomain_subset j hs).1
  have hratio : 3 / (a₀ + s) ≤ 3 / a₀ :=
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀ (le_add_of_nonneg_right hs0)
  have h1 : -(3 / a₀) ≤ metricScalarAt (R.toHistory.stageMetric j s) y :=
    (show -(3 / a₀) ≤ -3 / (a₀ + s) by simpa only [neg_div] using neg_le_neg hratio).trans
      hHI.2
  have h2 : -Bf ≤ metricScalarAt (R.toHistory.stageMetric j s) y := hBf j s hs y
  rw [neg_le]
  rw [neg_le] at h1 h2
  exact le_min h2 h1

/-- **子句 1 的切片形**：窗口屏障常数 `c = windowBarrierConsts …` 满足（model 参数、窗口 δ / neck /
导数控制、基点受控球 `r₀`）时，`𝓛_{Bf}(x → q@s) < A` 且 `√(t − s) ≤ E` ⇒ `q` 是非 barely admissible
极小端点（合同地板 `Bf`）。 -/
theorem windowBarrier_slice_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (R : RetainedCoreHistory.{u}) (hid : Nonempty (InitialIdentification P g R.toHistory))
    (params : CutoffParameters) (records : ∀ i, GeometricCutoffRecord R.toHistory i params)
    (hcanon : ∀ i b, ((records i).static b).hasCanonicalWindow)
    {E A r₀ qcan ρ : ℝ} {Ctime : ℝ≥0} (hE : 0 ≤ E) (hr₀ : 0 < r₀) (hqcan : 0 < qcan)
    (hρ : 0 < ρ)
    (haccuracy : params.modelAccuracy ≤
      (windowBarrierConsts_C11Q2 P g E A r₀ qcan params.recenterConstant ρ Ctime).2.1)
    (hradius : (windowBarrierConsts_C11Q2 P g E A r₀ qcan params.recenterConstant ρ Ctime).2.2.1
      ≤ params.modelRadius)
    (horder : (windowBarrierConsts_C11Q2 P g E A r₀ qcan params.recenterConstant ρ Ctime).2.2.2
      ≤ params.modelOrder)
    (t : Icc (0 : ℝ) R.toHistory.horizon)
    (hδ : ∀ j : Fin R.toHistory.eventCount, t.val - E ^ 2 ≤ R.toHistory.time j.succ →
      R.toHistory.time j.succ ≤ t.val → params.delta (R.toHistory.time j.succ) ≤
        (windowBarrierConsts_C11Q2 P g E A r₀ qcan params.recenterConstant ρ Ctime).1)
    (hneck : ∀ j : Fin R.toHistory.eventCount, t.val - E ^ 2 ≤ R.toHistory.time j.succ →
      R.toHistory.time j.succ ≤ t.val → params.neckRadius (R.toHistory.time j.succ) ≤ ρ)
    (hderiv : ∀ (j : Fin (R.toHistory.eventCount + 1)) (y : (R.toHistory.stage j).Carrier),
      t.val - E ^ 2 ≤ R.toHistory.time j →
      ∀ s ∈ Ioo (R.toHistory.time j) (R.toHistory.stageEndTime j), s < t.val →
        qcan < metricScalarAt (R.toHistory.stageMetric j s) y →
          |derivWithin (fun z => metricScalarAt (R.toHistory.stageMetric j z) y) (Iic s) s| ≤
            Ctime * metricScalarAt (R.toHistory.stageMetric j s) y ^ 2)
    (x : (R.toHistory.stageAt t).Carrier)
    (hball : R.toHistory.isParabolicallyRmControlledBall t x r₀)
    {Bf : ℝ} (hBf : ScalarFloor_C11Q R Bf)
    (s : Icc (0 : ℝ) R.toHistory.horizon) (q : (R.toHistory.stageAt s).Carrier)
    (hvE : Real.sqrt ((t : ℝ) - s) ≤ E)
    (hcost : sliceCost_C11Q R Bf t s x q < (A : WithTop ℝ)) :
    IsRegularMinimizerEndpoint_C11Q R Bf t s x q := by
  have hΛ : 0 < params.recenterConstant :=
    lt_of_lt_of_le (by norm_num) params.recenterConstant_ge_four
  obtain ⟨ha₀, hinit, -⟩ := windowBarrierA₀_spec_C11Q2 P g
  set a₀ := windowBarrierA₀_C11Q2 P g
  obtain ⟨identification⟩ := hid
  have hstart := hinit R.toHistory identification
  have hfloor := scalarFloor_min_C11Q2 R ha₀ hBf records hstart.1 hstart.2
  have hspec := (windowBarrierConsts_spec_C11Q2 P g (A := A) Ctime hE hr₀ hqcan hΛ hρ).2.2.2
  unfold sliceCost_C11Q at hcost
  split_ifs at hcost with hle
  · rw [ObservedHistory.regularizedCost_eq_of_scalar_lower_bound_le hfloor _ _ hle _
      (min_le_left Bf (3 / a₀)) (min_le_right Bf (3 / a₀))] at hcost
    have hmem := hspec R.toHistory ⟨identification⟩ params horder hradius haccuracy le_rfl
      records hcanon t hδ hneck hderiv x hball (R.toHistory.activeStage s) hle
      (Real.sqrt ((t : ℝ) - s)) hvE q hcost
    refine ⟨hle, ?_⟩
    rw [ObservedHistory.regularMinimizerEndpoints_eq_of_scalar_lower_bound_le hfloor _ _ hle _
      (min_le_left Bf (3 / a₀)) (min_le_right Bf (3 / a₀))]
    exact hmem
  · exact absurd hcost (not_lt.mpr le_top)

/-! ## 3. 子句 2：cutoff 最小值无条件可达 -/

/-- **子句 2**：`0 < v`、`v² ≤ r²/2`、`2r² < t`，切片在 `[b, t]` 内 ⇒ cutoff 最小值 `M(v)` 被某点达到
（含 event 时刻切片；地板 `Bf` 为任一真实地板）。 -/
theorem cutoffValue_attained_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (R : RetainedCoreHistory.{u}) (hid : Nonempty (InitialIdentification P g R.toHistory))
    {params : CutoffParameters} (records : ∀ i, GeometricCutoffRecord R.toHistory i params)
    {Bf : ℝ} (hBf : ScalarFloor_C11Q R Bf) {r A : ℝ}
    {t b : Icc (0 : ℝ) R.toHistory.horizon} (hbt : b ≤ t) {p : (R.toHistory.stageAt t).Carrier}
    (seedTrace : BackwardPointTrace R.toHistory (R.toHistory.activeStage b)
      (R.toHistory.activeStage t) (R.toHistory.activeStage_mono hbt) p)
    (x : (R.toHistory.stageAt t).Carrier) {v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (hv2 : v ^ 2 ≤ r ^ 2 / 2) (hT : 2 * r ^ 2 < (t : ℝ))
    (h : b ≤ clockSlice_C11Q R t v ∧ clockSlice_C11Q R t v ≤ t) :
    ∃ q, cutoffValue_C11Q R Bf r A hbt seedTrace x v q =
      cutoffMin_C11Q R Bf r A hbt seedTrace x v := by
  obtain ⟨a₀, ha₀, hinitial⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P g
  obtain ⟨identification⟩ := hid
  have hstart := hinitial R.toHistory identification
  have hHI := (R.toHistory.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hstart.1
    hstart.2).1
  have hle : R.toHistory.activeStage (clockSlice_C11Q R t v) ≤ R.toHistory.activeStage t :=
    R.toHistory.activeStage_mono h.2
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hT0 : 0 < (t : ℝ) := by linarith
  have hden : 0 < a₀ + (t : ℝ) / 2 := by positivity
  have hvr : v < r := by nlinarith [mul_pos hv hr]
  have hroom : (2 * (3 / (a₀ + (t : ℝ) / 2)) / 3) * v ^ 3 < r := by
    have hkey : 2 * v ^ 3 < r * (a₀ + (t : ℝ) / 2) := by nlinarith [mul_pos hv hr]
    have heq : (2 * (3 / (a₀ + (t : ℝ) / 2)) / 3) * v ^ 3 = 2 * v ^ 3 / (a₀ + (t : ℝ) / 2) := by
      field_simp
    rw [heq]
    exact (div_lt_iff₀ hden).mpr hkey
  have hscalar (j : R.toHistory.StageInterval (R.toHistory.activeStage (clockSlice_C11Q R t v))
      (R.toHistory.activeStage t)) (s : ℝ)
      (hs : s ∈ Ioo (R.toHistory.regularizedStageStart (t : ℝ) 0 j.val)
        (R.toHistory.regularizedStageEnd (t : ℝ) v j.val))
      (y : (R.toHistory.stage j.val).Carrier) :
      -Bf ≤ metricScalarAt (R.toHistory.stageMetric j.val ((t : ℝ) - s ^ 2)) y :=
    hBf j.val ((t : ℝ) - s ^ 2) (R.toHistory.mapsTo_regularizedStage_Ioo (t : ℝ) 0 v j.val hs) y
  have hsharp (j : R.toHistory.StageInterval (R.toHistory.activeStage (clockSlice_C11Q R t v))
      (R.toHistory.activeStage t)) (s : ℝ)
      (hs : s ∈ Ioo (R.toHistory.regularizedStageStart (t : ℝ) 0 j.val)
        (R.toHistory.regularizedStageEnd (t : ℝ) v j.val))
      (y : (R.toHistory.stage j.val).Carrier) :
      -(3 / (a₀ + (t : ℝ) / 2)) ≤
        metricScalarAt (R.toHistory.stageMetric j.val ((t : ℝ) - s ^ 2)) y := by
    have hs0 : 0 ≤ s := (Real.sqrt_nonneg _).trans hs.1.le
    have hend : R.toHistory.regularizedStageEnd (t : ℝ) v j.val ≤ v := by
      have hh : (t : ℝ) - max ((t : ℝ) - v ^ 2) (R.toHistory.time j.val) ≤ v ^ 2 := by
        have hm := le_max_left ((t : ℝ) - v ^ 2) (R.toHistory.time j.val)
        linarith
      exact (Real.sqrt_le_sqrt hh).trans_eq (Real.sqrt_sq hv.le)
    have hsv : s ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hs0 (hs.2.le.trans hend) 2
    have hrecent : (t : ℝ) / 2 ≤ (t : ℝ) - s ^ 2 := by linarith
    have htimeDen : 0 < a₀ + ((t : ℝ) - s ^ 2) := by linarith
    have hR := (hHI j.val ((t : ℝ) - s ^ 2)
      (R.toHistory.mapsTo_regularizedStage_Ioo (t : ℝ) 0 v j.val hs) y).2
    have hnear : 3 / (a₀ + ((t : ℝ) - s ^ 2)) ≤ 3 / (a₀ + (t : ℝ) / 2) := by
      apply (div_le_div_iff₀ htimeDen hden).mpr
      linarith
    exact (show -(3 / (a₀ + (t : ℝ) / 2)) ≤ -3 / (a₀ + ((t : ℝ) - s ^ 2)) by
      simpa only [neg_div] using neg_le_neg hnear).trans hR
  obtain ⟨q, hq⟩ := ObservedHistory.physicalWeightedCost_exists_min_at_clock_C11Q2 R.toHistory
    (R.toHistory.activeStage (clockSlice_C11Q R t v)) (R.toHistory.activeStage t) hle (t : ℝ) Bf
    (3 / (a₀ + (t : ℝ) / 2)) r A v hr hv hroom (R.toHistory.activeStage_mem t) hscalar hsharp x
    (seedTrace.point (R.toHistory.activeStage (clockSlice_C11Q R t v))
      (R.toHistory.activeStage_mono h.1) (R.toHistory.activeStage_mono h.2))
  have hfun : cutoffValue_C11Q R Bf r A hbt seedTrace x v =
      fun q => R.toHistory.physicalWeightedCost (R.toHistory.activeStage (clockSlice_C11Q R t v))
        (R.toHistory.activeStage t) hle (t : ℝ) Bf r A v x
        (seedTrace.point (R.toHistory.activeStage (clockSlice_C11Q R t v))
          (R.toHistory.activeStage_mono h.1) (R.toHistory.activeStage_mono h.2)) q := by
    funext q
    unfold cutoffValue_C11Q
    rw [dite_eq_left h]
  refine ⟨q, ?_⟩
  unfold cutoffMin_C11Q
  rw [hfun]
  exact hq.symm

/-! ## 4. 尺度：每个种子时刻一组常数 + 显式尺度前提 -/

/-- **种子时刻 `t` 的最坏情形常数**：`E = √(t/2)`（窗口 `[t/2, t]`）、`A = Λ_A·√(t/2)`、
`r₀ = nr(t)/100`、`qcan(t)`、recenter 常数 `Λrec`、`ρ̄(t)`。 -/
def kappaWindowConsts_C11Q2 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (ΛA : ℝ)
    (nr qcan ρbar : ℝ → ℝ) (Λrec : ℝ) (Ctime : ℝ≥0) (t : ℝ) : ℝ × ℝ × ℝ × ℕ :=
  windowBarrierConsts_C11Q2 P₀ g₀ (Real.sqrt (t / 2)) (ΛA * Real.sqrt (t / 2)) (nr t / 100)
    (qcan t) Λrec (ρbar t) Ctime

/-- **K3 窗口版的 δ₀ 尺度前提**（简报 G1 选项二：`δ₀(r₀)` 作显式参数）：对每个 `A > 0`、每个种子时刻
`t > 0`，F 的 cutoff 参数满足最坏情形树内常数 `kappaWindowConsts_C11Q2 … t = (δ₀, ε₀, R₀, m₀)`
（`modelAccuracy ≤ ε₀`、`R₀ ≤ modelRadius`、`m₀ ≤ modelOrder`），且 S7 accuracy `α A ≤ δ₀` 于窗口
`[t/2, t]`。`δ₀` 的 `t` 依赖由 `α A s` 吸收（KL 的 `δ̄_A(t)`）；`ε₀, R₀, m₀` 对 `t` 的一致性 = 尚缺的
"δ₀ 尺度引理"（parabolic rescaling / seed 归一化屏障）。 -/
def KappaWindowScale_C11Q2 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (params : CutoffParameters) (α : ℝ → ℝ → ℝ) (nr Λ qcan ρbar : ℝ → ℝ) (Ctime : ℝ≥0) : Prop :=
  ∀ A, 0 < A → ∀ t : ℝ, 0 < t →
    params.modelAccuracy ≤
        (kappaWindowConsts_C11Q2 P₀ g₀ (Λ A) nr qcan ρbar params.recenterConstant Ctime t).2.1 ∧
      (kappaWindowConsts_C11Q2 P₀ g₀ (Λ A) nr qcan ρbar params.recenterConstant Ctime t).2.2.1 ≤
        params.modelRadius ∧
      (kappaWindowConsts_C11Q2 P₀ g₀ (Λ A) nr qcan ρbar params.recenterConstant Ctime t).2.2.2 ≤
        params.modelOrder ∧
      ∀ s ∈ Icc (t / 2) t,
        α A s ≤ (kappaWindowConsts_C11Q2 P₀ g₀ (Λ A) nr qcan ρbar params.recenterConstant Ctime
          t).1

/-- 半时钟 `0 < v ≤ r/√2`、`2r² < t` 的切片事实：`clockSlice = t − v²`、`√(t − s) = v ≤ √(t/2)`、
`b ≤ s ≤ t`（`b = t − r²`）、`v² ≤ r²/2`。 -/
theorem halfClock_slice_facts_C11Q2 (R : RetainedCoreHistory.{u})
    {t b : Icc (0 : ℝ) R.toHistory.horizon} {r v : ℝ} (hT : 2 * r ^ 2 < (t : ℝ))
    (hb : (b : ℝ) = (t : ℝ) - r ^ 2) (hv : v ∈ Ioc 0 (r / Real.sqrt 2)) :
    v ^ 2 ≤ r ^ 2 / 2 ∧ (clockSlice_C11Q R t v : ℝ) = (t : ℝ) - v ^ 2 ∧
      Real.sqrt ((t : ℝ) - clockSlice_C11Q R t v) = v ∧
      v ≤ Real.sqrt ((t : ℝ) / 2) ∧
      (b ≤ clockSlice_C11Q R t v ∧ clockSlice_C11Q R t v ≤ t) := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hv2 : v ^ 2 ≤ r ^ 2 / 2 := by
    have h1 : v ^ 2 ≤ (r / Real.sqrt 2) ^ 2 := pow_le_pow_left₀ hv.1.le hv.2 2
    rwa [div_pow, Real.sq_sqrt (by norm_num)] at h1
  have hval := clockSlice_val_C11Q R t (v := v) (by nlinarith)
  refine ⟨hv2, hval, ?_, ?_, ?_, ?_⟩
  · rw [hval, show (t : ℝ) - ((t : ℝ) - v ^ 2) = v ^ 2 by ring, Real.sqrt_sq hv.1.le]
  · apply Real.le_sqrt_of_sq_le
    nlinarith
  · change (b : ℝ) ≤ (clockSlice_C11Q R t v : ℝ)
    rw [hval, hb]
    nlinarith
  · change (clockSlice_C11Q R t v : ℝ) ≤ (t : ℝ)
    rw [hval]
    nlinarith [sq_nonneg v]

/-- **K3 producer（窗口版）**：显式数据（cutoff 参数 / records / canonical windows、`params.delta ≤ δ`、
窗口 neck 界 `ρ̄`、窗口导数控制 `(qcan, Ctime)`、`nr > 0`、`Λ > 0`）+ **尺度前提**
`KappaWindowScale_C11Q2` ⇒ 合同 `SurgeryActionBarrier_C11Q F δ α nr Λ`（两个子句）。 -/
theorem surgeryActionBarrier_of_window_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr Λ : ℝ → ℝ}
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (hcanon : ∀ n i b, ((records n i).static b).hasCanonicalWindow)
    (hδ : ∀ s, 0 ≤ s → params.delta s ≤ δ s)
    (hΛ : ∀ A, 0 < A → 0 < Λ A) (hnr : ∀ t, 0 < t → 0 < nr t)
    (qcan ρbar : ℝ → ℝ) (hqcan : ∀ t, 0 < t → 0 < qcan t) (hρbar : ∀ t, 0 < t → 0 < ρbar t)
    (hneck : ∀ t s, 0 < t → t / 2 ≤ s → s ≤ t → params.neckRadius s ≤ ρbar t)
    (Ctime : ℝ≥0)
    (hderiv : ∀ n, ∀ (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (j : Fin ((F.tower.history n).toHistory.eventCount + 1))
      (y : ((F.tower.history n).toHistory.stage j).Carrier),
      (t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time j →
      ∀ s ∈ Ioo ((F.tower.history n).toHistory.time j)
        ((F.tower.history n).toHistory.stageEndTime j), s < t.val →
        qcan t < metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y →
          |derivWithin (fun z => metricScalarAt ((F.tower.history n).toHistory.stageMetric j z) y)
              (Iic s) s| ≤
            Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y ^ 2)
    (hscale : KappaWindowScale_C11Q2 P g params α nr Λ qcan ρbar Ctime) :
    SurgeryActionBarrier_C11Q F δ α nr Λ := by
  intro A hA n R H t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball Bf hBf v hv
  have hr0 : 0 < r := hsmall.1
  have ht0 : 0 < (t : ℝ) := by nlinarith
  have hid : Nonempty (InitialIdentification P g R.toHistory) := ⟨F.tower.initial n⟩
  obtain ⟨hv2, -, hsq, hvE, hslice⟩ := halfClock_slice_facts_C11Q2 R hr hb hv
  refine ⟨?_, fun _ => cutoffValue_attained_C11Q2 R hid (records n) hBf hbt seedTrace x hr0
    hv.1 hv2 hr hslice⟩
  intro q hq
  obtain ⟨haccuracy, hradius, horder, hα⟩ := hscale A hA t ht0
  have hE2 : (t : ℝ) - Real.sqrt ((t : ℝ) / 2) ^ 2 = (t : ℝ) / 2 := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hnr0 : 0 < nr t / 100 := by have := hnr t ht0; positivity
  have hball' : H.isParabolicallyRmControlledBall t x (nr t / 100) :=
    ObservedHistory.isParabolicallyRmControlledBall.mono_radius _ hball hnr0 hϱ₀
  have hrt : r ≤ Real.sqrt ((t : ℝ) / 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  refine windowBarrier_slice_C11Q2 R hid params (records n) (hcanon n) (Real.sqrt_nonneg _) hnr0
    (hqcan t ht0) (hρbar t ht0) haccuracy hradius horder t ?_ ?_ ?_ x hball' hBf _ q ?_ ?_
  · intro j hj1 hj2
    rw [hE2] at hj1
    have htime0 : 0 ≤ H.time j.succ := by linarith
    exact (hδ _ htime0).trans ((hacc _ ⟨hj1, hj2⟩).le.trans (hα _ ⟨hj1, hj2⟩))
  · intro j hj1 hj2
    rw [hE2] at hj1
    exact hneck t _ ht0 hj1 hj2
  · intro j y hj s hs hst hqs
    rw [hE2] at hj
    exact hderiv n t j y hj s hs hst hqs
  · rw [hsq]
    exact hvE
  · refine lt_of_le_of_lt hq (WithTop.coe_lt_coe.mpr ?_)
    have hΛA := hΛ A hA
    nlinarith

/-! ## 5. K4 常数链闭合与 consumer -/

/-- K4 要求的屏障高度 `Λ_A = 4 e^{C₂(A)/2 + 32/√2}`（只依赖 K2 的 `C₂`）。 -/
def kappaBarrierLevel_C11Q2 (C₂ : ℝ → ℝ) (A : ℝ) : ℝ :=
  4 * Real.exp (C₂ A / 2 + 32 / Real.sqrt 2)

theorem kappaBarrierLevel_pos_C11Q2 (C₂ : ℝ → ℝ) (A : ℝ) : 0 < kappaBarrierLevel_C11Q2 C₂ A := by
  unfold kappaBarrierLevel_C11Q2
  positivity

/-- **K4 常数链在显式 `δ₀` 参数下闭合**：`Λ := kappaBarrierLevel_C11Q2 C₂` 使 K4 的相容条件
`4e^{C₂/2+32/√2} ≤ Λ` 取等号；窗口 K3 producer 在该 `Λ` 处给 K3（`δ₀` 由 `Λ` 经尺度前提定出，无循环）；
`boundedReducedLength_of_maxPrinciple_C11Q` ⇒ K4。 -/
theorem boundedReducedLength_of_window_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₂ : ℝ → ℝ}
    (hC₂ : ∀ A, 0 < A → 0 ≤ C₂ A) (hK2 : LocalizedLCutoffInequality_C11Q F nr C₂)
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (hcanon : ∀ n i b, ((records n i).static b).hasCanonicalWindow)
    (hδ : ∀ s, 0 ≤ s → params.delta s ≤ δ s) (hnr : ∀ t, 0 < t → 0 < nr t)
    (qcan ρbar : ℝ → ℝ) (hqcan : ∀ t, 0 < t → 0 < qcan t) (hρbar : ∀ t, 0 < t → 0 < ρbar t)
    (hneck : ∀ t s, 0 < t → t / 2 ≤ s → s ≤ t → params.neckRadius s ≤ ρbar t)
    (Ctime : ℝ≥0)
    (hderiv : ∀ n, ∀ (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (j : Fin ((F.tower.history n).toHistory.eventCount + 1))
      (y : ((F.tower.history n).toHistory.stage j).Carrier),
      (t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time j →
      ∀ s ∈ Ioo ((F.tower.history n).toHistory.time j)
        ((F.tower.history n).toHistory.stageEndTime j), s < t.val →
        qcan t < metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y →
          |derivWithin (fun z => metricScalarAt ((F.tower.history n).toHistory.stageMetric j z) y)
              (Iic s) s| ≤
            Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y ^ 2)
    (hscale : KappaWindowScale_C11Q2 P g params α nr (kappaBarrierLevel_C11Q2 C₂) qcan ρbar
      Ctime) :
    BoundedReducedLengthNearSeed_C11Q F δ α nr (boundedLengthConst_C11Q C₂) :=
  boundedReducedLength_of_maxPrinciple_C11Q hC₂ (fun _ _ => le_rfl) hK2
    (surgeryActionBarrier_of_window_C11Q2 params records hcanon hδ
      (fun A _ => kappaBarrierLevel_pos_C11Q2 C₂ A) hnr qcan ρbar hqcan hρbar hneck Ctime hderiv
      hscale)

/-- **consumer（G1）**：窗口 K3 producer 喂强链 `localKappa_of_K1_K2_K3_K5a_C11Q` 的 K3 槽
（`Λ = kappaBarrierLevel_C11Q2 C₂`，`hΛ` 取等号）⇒ `LocalKappaWideSupply_C11Q`；剩余前提 = K1、
K1 → K2、K1 → K5a、`C₂ ≥ 0`、K3 的显式数据与尺度前提。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₂ C₅ : ℝ → ℝ}
    (hK1 : ∀ n, AdmissibleLCalculus_C11Q (F.tower.history n))
    (hK2 : (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      LocalizedLCutoffInequality_C11Q F nr C₂)
    (hC₂ : ∀ A, 0 < A → 0 ≤ C₂ A)
    (hK5a : (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      SeedPatchLowAction_C11Q F δ α nr (boundedLengthConst_C11Q C₂) C₅)
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (hcanon : ∀ n i b, ((records n i).static b).hasCanonicalWindow)
    (hδ : ∀ s, 0 ≤ s → params.delta s ≤ δ s) (hnr : ∀ t, 0 < t → 0 < nr t)
    (qcan ρbar : ℝ → ℝ) (hqcan : ∀ t, 0 < t → 0 < qcan t) (hρbar : ∀ t, 0 < t → 0 < ρbar t)
    (hneck : ∀ t s, 0 < t → t / 2 ≤ s → s ≤ t → params.neckRadius s ≤ ρbar t)
    (Ctime : ℝ≥0)
    (hderiv : ∀ n, ∀ (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (j : Fin ((F.tower.history n).toHistory.eventCount + 1))
      (y : ((F.tower.history n).toHistory.stage j).Carrier),
      (t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time j →
      ∀ s ∈ Ioo ((F.tower.history n).toHistory.time j)
        ((F.tower.history n).toHistory.stageEndTime j), s < t.val →
        qcan t < metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y →
          |derivWithin (fun z => metricScalarAt ((F.tower.history n).toHistory.stageMetric j z) y)
              (Iic s) s| ≤
            Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y ^ 2)
    (hscale : KappaWindowScale_C11Q2 P g params α nr (kappaBarrierLevel_C11Q2 C₂) qcan ρbar
      Ctime) :
    LocalKappaWideSupply_C11Q F δ α nr :=
  localKappa_of_K1_K2_K3_K5a_C11Q hK1 hK2
    (surgeryActionBarrier_of_window_C11Q2 params records hcanon hδ
      (fun A _ => kappaBarrierLevel_pos_C11Q2 C₂ A) hnr qcan ρbar hqcan hρbar hneck Ctime hderiv
      hscale)
    hC₂ (fun _ _ => le_rfl) hK5a

end GC.LongTime.Ch11
