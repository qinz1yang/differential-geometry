import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineBarrierCoreC11Q5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaWeightedMinC11Q2

/-!
# fine-cap K3 producer：接口 (4)（O-CH11-FINECAP G2，后缀 `_C11Q5`）

R-C11-4 D-2 (b′) 的消费侧。**D-2 contract correction**（设计文档 §0′）：KAPPA2 的尺度前提
`KappaWindowScale_C11Q2 P g params …` 对固定 `params` **推不出**——`windowBarrierConsts_C11Q2` 是
`Classical.choose`，`WindowBarrierSpec_C11Q2` 对 `ε₀` 向下封闭、对 `R₀, m₀` 向上封闭，而
`params.modelAccuracy > 0`、`modelRadius`、`modelOrder` 是固定数；任何不提 chooser 内部值的前提都给不出
`∀ A ∀ t, modelAccuracy ≤ ε₀(A, t)`。(b′) 因此**替换**该前提：

* `FineBarrierSpec_C11Q5` / `fineBarrierConsts_C11Q5`：fine 窗口屏障的常数 `(δ₀, ε₀, R₀, m₀)`
  （`KappaFineBarrierCoreC11Q5`，地板 `3/a₀`，`a₀ = windowBarrierA₀_C11Q2`），model tuple 不出现，
  改由窗口内 event 的 `FineCapRealization_C11Q5 _ R₀ m₀ ε₀` 支付；E / W 解耦。
* `fineCapThreshold_C11Q5`：接口 (3) 的 `δ_*` chooser（`exists_fineCapRealization_of_actual_C11Q5`）。
* `fineCapDelta_C11Q5 … t := min δ₀(t) (δ_*(R₀, m₀, ε₀)(t) / recenterConstant)`（逐点为正）。
* **接口 (4) + K3 producer** `surgeryActionBarrier_of_fineCap_C11Q5`：records + 每个 static cap 的实际插入
  证书 `hact` + 纯 δ 条件 `α A s ≤ fineCapDelta(A, t)`（`s ∈ [t/2, t]`）+ 窗口数据（时钟上界 `Eb t ≥ √(t/2)`、
  测试半径 `r₀ t ≤ nr t / 100`、导数阈值 `qcan`、neck 上界 `ρbar`）⇒ `SurgeryActionBarrier_C11Q`。
  δ 链：`S.delta ≤ Λrec·params.delta(t_i) ≤ Λrec·δ(t_i) < Λrec·α A t_i ≤ δ_*` ⇒ (3) ⇒
  fine realization。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. fine 窗口屏障的常数 -/

/-- fine 窗口屏障在常数 `c = (δ₀, ε₀, R₀, m₀)` 下成立（`exists_window_regularCrossing_minimizer_C11Q5`
的结论体；地板 `3/a₀`；窗口 `[t − W², t]`、时钟 `v ≤ W ≤ E`）。 -/
def FineBarrierSpec_C11Q5 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (a₀ E A r₀ qcan Λ ρ : ℝ) (Ctime : ℝ≥0) (c : ℝ × ℝ × ℝ × ℕ) : Prop :=
  0 < c.1 ∧ 0 < c.2.1 ∧ StandardCap.transitionEnd < c.2.2.1 ∧
  ∀ (H : ObservedHistory.{u}), Nonempty (InitialIdentification P₀ g₀ H) →
  ∀ (parameters : CutoffParameters), parameters.recenterConstant ≤ Λ →
  ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
  ∀ (t : Icc (0 : ℝ) H.horizon) (W : ℝ), W ≤ E →
    (∀ j : Fin H.eventCount, t.val - W ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
      parameters.delta (H.time j.succ) ≤ c.1) →
    (∀ j : Fin H.eventCount, t.val - W ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
      parameters.neckRadius (H.time j.succ) ≤ ρ) →
    (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier), t.val - W ^ 2 ≤ H.time j →
      ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
        qcan < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
            Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) →
    (∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
      t.val - W ^ 2 ≤ H.time i.succ → H.time i.succ < t.val →
      FineCapRealization_C11Q5 ((records i).static b) c.2.2.1 c.2.2.2 c.2.1) →
  ∀ (p : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t p r₀ →
  ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ), v ≤ W →
  ∀ q : (H.stage first).Carrier,
    H.regularizedCost first (H.activeStage t) hle t (3 / a₀) 0 v p q < (A : WithTop ℝ) →
    q ∈ H.regularMinimizerEndpoints first (H.activeStage t) hle t (3 / a₀) v p

/-- 每组正输入都有 fine 窗口屏障常数（`a₀ = windowBarrierA₀_C11Q2`，与 KAPPA2 同一初始地板）。 -/
theorem exists_fineBarrierSpec_C11Q5 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (E A r₀ qcan Λ ρ : ℝ) (Ctime : ℝ≥0) (hE : 0 ≤ E) (hr₀ : 0 < r₀) (hqcan : 0 < qcan)
    (hΛ : 0 < Λ) (hρ : 0 < ρ) :
    ∃ c : ℝ × ℝ × ℝ × ℕ,
      FineBarrierSpec_C11Q5 P₀ g₀ (windowBarrierA₀_C11Q2 P₀ g₀) E A r₀ qcan Λ ρ Ctime c := by
  obtain ⟨ha₀, hinit, -⟩ := windowBarrierA₀_spec_C11Q2 P₀ g₀
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hbarrier⟩ :=
    ObservedHistory.exists_window_regularCrossing_minimizer_C11Q5.{u}
      A E r₀ qcan (windowBarrierA₀_C11Q2 P₀ g₀) Λ ρ Ctime hE hr₀ hqcan ha₀ hΛ hρ
  refine ⟨(δ₀, ε₀, R₀, m₀), hδ₀, hε₀, hR₀, ?_⟩
  intro H hid parameters hrecenter records t W hWE hδ hρp hderiv hfine p hball first hle v hvW
    q hcost
  obtain ⟨identification⟩ := hid
  have hstart := hinit H identification
  exact hbarrier H parameters hrecenter records hstart.1 hstart.2 t W hWE hδ hρp hderiv hfine
    p hball first hle v hvW q hcost

/-- **fine 窗口屏障常数** `(δ₀, ε₀, R₀, m₀)`（非正输入时取占位值，不被使用）。 -/
def fineBarrierConsts_C11Q5 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (E A r₀ qcan Λ ρ : ℝ) (Ctime : ℝ≥0) : ℝ × ℝ × ℝ × ℕ :=
  if h : 0 ≤ E ∧ 0 < r₀ ∧ 0 < qcan ∧ 0 < Λ ∧ 0 < ρ then
    Classical.choose (exists_fineBarrierSpec_C11Q5 P₀ g₀ E A r₀ qcan Λ ρ Ctime h.1 h.2.1
      h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  else (1, 1, 1, 0)

theorem fineBarrierConsts_spec_C11Q5 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    {E A r₀ qcan Λ ρ : ℝ} (Ctime : ℝ≥0) (hE : 0 ≤ E) (hr₀ : 0 < r₀) (hqcan : 0 < qcan)
    (hΛ : 0 < Λ) (hρ : 0 < ρ) :
    FineBarrierSpec_C11Q5 P₀ g₀ (windowBarrierA₀_C11Q2 P₀ g₀) E A r₀ qcan Λ ρ Ctime
      (fineBarrierConsts_C11Q5 P₀ g₀ E A r₀ qcan Λ ρ Ctime) := by
  have h : 0 ≤ E ∧ 0 < r₀ ∧ 0 < qcan ∧ 0 < Λ ∧ 0 < ρ := ⟨hE, hr₀, hqcan, hΛ, hρ⟩
  unfold fineBarrierConsts_C11Q5
  rw [dite_eq_left h]
  exact Classical.choose_spec (exists_fineBarrierSpec_C11Q5 P₀ g₀ E A r₀ qcan Λ ρ Ctime
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)

/-! ## 2. 接口 (3) 的阈值 chooser -/

/-- 接口 (3) 的阈值（对一切请求给出正数；`D' ≥ transitionEnd`、`ε' > 0` 时有 (3) 的蕴含）。 -/
theorem exists_fineCapThreshold_C11Q5 (fixed : StaticCapScaffold) (D' : ℝ) (m' : ℕ) (ε' : ℝ) :
    ∃ δs : ℝ, 0 < δs ∧ (StandardCap.transitionEnd ≤ D' → 0 < ε' →
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s} {D ε : ℝ}
        {m : ℕ} {b : E.RetainedBoundaryIndex} (S : E.PresentedStaticCap fixed D m ε b),
        ActualCanonicalInsertion_C11Q5 S → S.delta ≤ δs →
          FineCapRealization_C11Q5 S D' m' ε') := by
  by_cases h : StandardCap.transitionEnd ≤ D' ∧ 0 < ε'
  · obtain ⟨δs, hδs, hS⟩ := exists_fineCapRealization_of_actual_C11Q5.{u} fixed D' h.1 m' ε' h.2
    exact ⟨δs, hδs, fun _ _ => hS⟩
  · exact ⟨1, one_pos, fun hD hε => (h ⟨hD, hε⟩).elim⟩

/-- **接口 (3) 的 `δ_*(D', m', ε')`**。 -/
def fineCapThreshold_C11Q5.{v} (fixed : StaticCapScaffold) (D' : ℝ) (m' : ℕ) (ε' : ℝ) : ℝ :=
  Classical.choose (exists_fineCapThreshold_C11Q5.{v} fixed D' m' ε')

theorem fineCapThreshold_spec_C11Q5 (fixed : StaticCapScaffold) (D' : ℝ) (m' : ℕ) (ε' : ℝ) :
    0 < fineCapThreshold_C11Q5.{u} fixed D' m' ε' ∧ (StandardCap.transitionEnd ≤ D' → 0 < ε' →
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s} {D ε : ℝ}
        {m : ℕ} {b : E.RetainedBoundaryIndex} (S : E.PresentedStaticCap fixed D m ε b),
        ActualCanonicalInsertion_C11Q5 S → S.delta ≤ fineCapThreshold_C11Q5.{u} fixed D' m' ε' →
          FineCapRealization_C11Q5 S D' m' ε') :=
  Classical.choose_spec (exists_fineCapThreshold_C11Q5.{u} fixed D' m' ε')

/-! ## 3. 每个种子时刻的请求与 δ 预算 -/

/-- 种子时刻 `t` 的 fine 常数：时钟上界 `Eb t`、作用量上界 `Λ_A·Eb t`、测试半径 `r₀ t`、导数阈值 `qcan t`、
recenter 常数 `Λrec`、neck 上界 `ρbar t`。 -/
def fineKappaConsts_C11Q5 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (ΛA Λrec : ℝ)
    (Eb r₀ qcan ρbar : ℝ → ℝ) (Ctime : ℝ≥0) (t : ℝ) : ℝ × ℝ × ℝ × ℕ :=
  fineBarrierConsts_C11Q5 P₀ g₀ (Eb t) (ΛA * Eb t) (r₀ t) (qcan t) Λrec (ρbar t) Ctime

/-- **δ 预算**（接口 (4) 的阈值）：`min δ₀ (δ_*(R₀, m₀, ε₀) / Λrec)`。 -/
def fineCapDelta_C11Q5 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (fixed : StaticCapScaffold)
    (ΛA Λrec : ℝ) (Eb r₀ qcan ρbar : ℝ → ℝ) (Ctime : ℝ≥0) (t : ℝ) : ℝ :=
  min (fineKappaConsts_C11Q5 P₀ g₀ ΛA Λrec Eb r₀ qcan ρbar Ctime t).1
    (fineCapThreshold_C11Q5.{u} fixed
      (fineKappaConsts_C11Q5 P₀ g₀ ΛA Λrec Eb r₀ qcan ρbar Ctime t).2.2.1
      (fineKappaConsts_C11Q5 P₀ g₀ ΛA Λrec Eb r₀ qcan ρbar Ctime t).2.2.2
      (fineKappaConsts_C11Q5 P₀ g₀ ΛA Λrec Eb r₀ qcan ρbar Ctime t).2.1 / Λrec)

/-- δ 预算逐点为正。 -/
theorem fineCapDelta_pos_C11Q5 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (fixed : StaticCapScaffold) (ΛA : ℝ) {Λrec : ℝ} (Eb r₀ qcan ρbar : ℝ → ℝ) (Ctime : ℝ≥0)
    {t : ℝ} (hE : 0 ≤ Eb t) (hr₀ : 0 < r₀ t) (hqcan : 0 < qcan t) (hΛ : 0 < Λrec)
    (hρ : 0 < ρbar t) :
    0 < fineCapDelta_C11Q5 P₀ g₀ fixed ΛA Λrec Eb r₀ qcan ρbar Ctime t :=
  lt_min (fineBarrierConsts_spec_C11Q5 P₀ g₀ (A := ΛA * Eb t) Ctime hE hr₀ hqcan hΛ hρ).1
    (div_pos (fineCapThreshold_spec_C11Q5.{u} fixed _ _ _).1 hΛ)

/-! ## 4. 子句 1 的切片形（fine） -/

/-- **fine 切片屏障**：fine 常数 `c = fineBarrierConsts …` 下（窗口 `[t − W², t]` 内 δ / neck / 导数控制、
fine realization、基点受控球 `r₀`），`𝓛_{Bf}(x → q@s) < A` 且 `√(t − s) ≤ W ≤ E` ⇒ `q` 是非 barely
admissible 极小端点（合同地板 `Bf`）。 -/
theorem fineWindowBarrier_slice_C11Q5 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (R : RetainedCoreHistory.{u}) (hid : Nonempty (InitialIdentification P g R.toHistory))
    (params : CutoffParameters) (records : ∀ i, GeometricCutoffRecord R.toHistory i params)
    {E A r₀ qcan ρ : ℝ} (Ctime : ℝ≥0) (hE : 0 ≤ E) (hr₀ : 0 < r₀) (hqcan : 0 < qcan)
    (hρ : 0 < ρ) (t : Icc (0 : ℝ) R.toHistory.horizon) (W : ℝ) (hWE : W ≤ E)
    (hδ : ∀ j : Fin R.toHistory.eventCount, t.val - W ^ 2 ≤ R.toHistory.time j.succ →
      R.toHistory.time j.succ ≤ t.val → params.delta (R.toHistory.time j.succ) ≤
        (fineBarrierConsts_C11Q5 P g E A r₀ qcan params.recenterConstant ρ Ctime).1)
    (hneck : ∀ j : Fin R.toHistory.eventCount, t.val - W ^ 2 ≤ R.toHistory.time j.succ →
      R.toHistory.time j.succ ≤ t.val → params.neckRadius (R.toHistory.time j.succ) ≤ ρ)
    (hderiv : ∀ (j : Fin (R.toHistory.eventCount + 1)) (y : (R.toHistory.stage j).Carrier),
      t.val - W ^ 2 ≤ R.toHistory.time j →
      ∀ s ∈ Ioo (R.toHistory.time j) (R.toHistory.stageEndTime j), s < t.val →
        qcan < metricScalarAt (R.toHistory.stageMetric j s) y →
          |derivWithin (fun z => metricScalarAt (R.toHistory.stageMetric j z) y) (Iic s) s| ≤
            Ctime * metricScalarAt (R.toHistory.stageMetric j s) y ^ 2)
    (hfine : ∀ (i : Fin R.toHistory.eventCount) (b : (R.toHistory.event i).RetainedBoundaryIndex),
      t.val - W ^ 2 ≤ R.toHistory.time i.succ → R.toHistory.time i.succ < t.val →
      FineCapRealization_C11Q5 ((records i).static b)
        (fineBarrierConsts_C11Q5 P g E A r₀ qcan params.recenterConstant ρ Ctime).2.2.1
        (fineBarrierConsts_C11Q5 P g E A r₀ qcan params.recenterConstant ρ Ctime).2.2.2
        (fineBarrierConsts_C11Q5 P g E A r₀ qcan params.recenterConstant ρ Ctime).2.1)
    (x : (R.toHistory.stageAt t).Carrier)
    (hball : R.toHistory.isParabolicallyRmControlledBall t x r₀)
    {Bf : ℝ} (hBf : ScalarFloor_C11Q R Bf)
    (s : Icc (0 : ℝ) R.toHistory.horizon) (q : (R.toHistory.stageAt s).Carrier)
    (hvW : Real.sqrt ((t : ℝ) - s) ≤ W)
    (hcost : sliceCost_C11Q R Bf t s x q < (A : WithTop ℝ)) :
    IsRegularMinimizerEndpoint_C11Q R Bf t s x q := by
  have hΛ : 0 < params.recenterConstant :=
    lt_of_lt_of_le (by norm_num) params.recenterConstant_ge_four
  obtain ⟨ha₀, hinit, -⟩ := windowBarrierA₀_spec_C11Q2 P g
  set a₀ := windowBarrierA₀_C11Q2 P g
  obtain ⟨identification⟩ := hid
  have hstart := hinit R.toHistory identification
  have hfloor := scalarFloor_min_C11Q2 R ha₀ hBf records hstart.1 hstart.2
  have hspec := (fineBarrierConsts_spec_C11Q5 P g (A := A) Ctime hE hr₀ hqcan hΛ hρ).2.2.2
  unfold sliceCost_C11Q at hcost
  split_ifs at hcost with hle
  · rw [ObservedHistory.regularizedCost_eq_of_scalar_lower_bound_le hfloor _ _ hle _
      (min_le_left Bf (3 / a₀)) (min_le_right Bf (3 / a₀))] at hcost
    have hmem := hspec R.toHistory ⟨identification⟩ params le_rfl records t W hWE hδ hneck
      hderiv hfine x hball (R.toHistory.activeStage s) hle (Real.sqrt ((t : ℝ) - s)) hvW q hcost
    refine ⟨hle, ?_⟩
    rw [ObservedHistory.regularMinimizerEndpoints_eq_of_scalar_lower_bound_le hfloor _ _ hle _
      (min_le_left Bf (3 / a₀)) (min_le_right Bf (3 / a₀))]
    exact hmem
  · exact absurd hcost (not_lt.mpr le_top)

/-! ## 5. 接口 (4) + K3 producer -/

/-- **K3 producer（fine-cap 版，接口 (4)）**：records + 实际插入证书 `hact` + 窗口数据（`Eb t ≥ √(t/2)`、
`0 < r₀ t ≤ nr t / 100`、`qcan`、`ρbar`、导数控制）+ **纯 δ 条件**
`α A s ≤ fineCapDelta(A, t)`（`s ∈ [t/2, t]`）⇒ 合同 `SurgeryActionBarrier_C11Q F δ α nr Λ`。
**无 model tuple 前提**（对照 `surgeryActionBarrier_of_window_C11Q2` 的 `hscale`）。 -/
theorem surgeryActionBarrier_of_fineCap_C11Q5 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr Λ : ℝ → ℝ}
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((records n i).static b))
    (hδ : ∀ s, 0 ≤ s → params.delta s ≤ δ s) (hΛ : ∀ A, 0 < A → 0 < Λ A)
    (Eb r₀ qcan ρbar : ℝ → ℝ) (hEb : ∀ t, 0 < t → Real.sqrt (t / 2) ≤ Eb t)
    (hr₀ : ∀ t, 0 < t → 0 < r₀ t ∧ r₀ t ≤ nr t / 100)
    (hqcan : ∀ t, 0 < t → 0 < qcan t) (hρbar : ∀ t, 0 < t → 0 < ρbar t)
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
    (hfine : ∀ A, 0 < A → ∀ t, 0 < t → ∀ s ∈ Icc (t / 2) t,
      α A s ≤ fineCapDelta_C11Q5 P g params.fixed (Λ A) params.recenterConstant Eb r₀ qcan ρbar
        Ctime t) :
    SurgeryActionBarrier_C11Q F δ α nr Λ := by
  intro A hA n R H t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball Bf hBf v hv
  have hr0 : 0 < r := hsmall.1
  have ht0 : 0 < (t : ℝ) := by nlinarith
  have hid : Nonempty (InitialIdentification P g R.toHistory) := ⟨F.tower.initial n⟩
  obtain ⟨hv2, -, hsq, hvE, hslice⟩ := halfClock_slice_facts_C11Q2 R hr hb hv
  refine ⟨?_, fun _ => cutoffValue_attained_C11Q2 R hid (records n) hBf hbt seedTrace x hr0
    hv.1 hv2 hr hslice⟩
  intro q hq
  have hΛrec : 0 < params.recenterConstant :=
    lt_of_lt_of_le (by norm_num) params.recenterConstant_ge_four
  obtain ⟨hr₀t, hr₀nr⟩ := hr₀ t ht0
  have hEt := hEb t ht0
  have hE0 : 0 ≤ Eb t := (Real.sqrt_nonneg _).trans hEt
  have hE2 : (t : ℝ) - Real.sqrt ((t : ℝ) / 2) ^ 2 = (t : ℝ) / 2 := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hball' : H.isParabolicallyRmControlledBall t x (r₀ t) :=
    ObservedHistory.isParabolicallyRmControlledBall.mono_radius _ hball hr₀t (hr₀nr.trans hϱ₀)
  have hthr := (fineCapThreshold_spec_C11Q5.{u} params.fixed
    (fineKappaConsts_C11Q5 P g (Λ A) params.recenterConstant Eb r₀ qcan ρbar Ctime t).2.2.1
    (fineKappaConsts_C11Q5 P g (Λ A) params.recenterConstant Eb r₀ qcan ρbar Ctime t).2.2.2
    (fineKappaConsts_C11Q5 P g (Λ A) params.recenterConstant Eb r₀ qcan ρbar Ctime t).2.1).2
  have hspec := fineBarrierConsts_spec_C11Q5 P g (A := Λ A * Eb t) Ctime hE0 hr₀t (hqcan t ht0)
    hΛrec (hρbar t ht0)
  have hα := hfine A hA t ht0
  have hrt : r ≤ Real.sqrt ((t : ℝ) / 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  refine fineWindowBarrier_slice_C11Q5 (A := Λ A * Eb t) R hid params (records n) Ctime hE0 hr₀t
    (hqcan t ht0) (hρbar t ht0) t (Real.sqrt ((t : ℝ) / 2)) hEt ?_ ?_ ?_ ?_ x hball' hBf _ q ?_ ?_
  · intro j hj1 hj2
    rw [hE2] at hj1
    have htime0 : 0 ≤ H.time j.succ := by linarith
    exact (hδ _ htime0).trans ((hacc _ ⟨hj1, hj2⟩).le.trans
      ((hα _ ⟨hj1, hj2⟩).trans (min_le_left _ _)))
  · intro j hj1 hj2
    rw [hE2] at hj1
    exact hneck t _ ht0 hj1 hj2
  · intro j y hj s hs hst hqs
    rw [hE2] at hj
    exact hderiv n t j y hj s hs hst hqs
  · intro i b hi1 hi2
    rw [hE2] at hi1
    have htime0 : 0 ≤ H.time i.succ := by linarith
    have hdel : params.delta (H.time i.succ) ≤
        fineCapThreshold_C11Q5.{u} params.fixed
          (fineKappaConsts_C11Q5 P g (Λ A) params.recenterConstant Eb r₀ qcan ρbar Ctime t).2.2.1
          (fineKappaConsts_C11Q5 P g (Λ A) params.recenterConstant Eb r₀ qcan ρbar Ctime t).2.2.2
          (fineKappaConsts_C11Q5 P g (Λ A) params.recenterConstant Eb r₀ qcan ρbar Ctime t).2.1
          / params.recenterConstant :=
      (hδ _ htime0).trans ((hacc _ ⟨hi1, hi2.le⟩).le.trans
        ((hα _ ⟨hi1, hi2.le⟩).trans (min_le_right _ _)))
    refine hthr hspec.2.2.1.le hspec.2.1 ((records n i).static b) (hact n i b) ?_
    refine (staticCap_delta_le_C11Q5 (records n i) b).trans ?_
    have hmul := mul_le_mul_of_nonneg_left hdel hΛrec.le
    rwa [mul_div_cancel₀ _ hΛrec.ne'] at hmul
  · rw [hsq]
    exact hvE
  · refine lt_of_le_of_lt hq (WithTop.coe_lt_coe.mpr ?_)
    have hΛA := hΛ A hA
    nlinarith

/-- **consumer**：fine K3 producer 的输出直接喂 K4（`boundedReducedLength_of_weightedMinBound_C11Q2`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C : ℝ → ℝ}
    (hW : WeightedMinBound_C11Q2 F δ α nr C)
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((records n i).static b))
    (hδ : ∀ s, 0 ≤ s → params.delta s ≤ δ s)
    (Eb r₀ qcan ρbar : ℝ → ℝ) (hEb : ∀ t, 0 < t → Real.sqrt (t / 2) ≤ Eb t)
    (hr₀ : ∀ t, 0 < t → 0 < r₀ t ∧ r₀ t ≤ nr t / 100)
    (hqcan : ∀ t, 0 < t → 0 < qcan t) (hρbar : ∀ t, 0 < t → 0 < ρbar t)
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
    (hfine : ∀ A, 0 < A → ∀ t, 0 < t → ∀ s ∈ Icc (t / 2) t,
      α A s ≤ fineCapDelta_C11Q5 P g params.fixed (weightedMinLevel_C11Q2 C A)
        params.recenterConstant Eb r₀ qcan ρbar Ctime t) :
    BoundedReducedLengthNearSeed_C11Q F δ α nr (weightedMinLengthConst_C11Q2 C) :=
  boundedReducedLength_of_weightedMinBound_C11Q2 hW
    (surgeryActionBarrier_of_fineCap_C11Q5 params records hact hδ
      (fun A _ => weightedMinLevel_pos_C11Q2 C A) Eb r₀ qcan ρbar hEb hr₀ hqcan hρbar hneck Ctime
      hderiv hfine)
    (fun _ _ => le_rfl)

end GC.LongTime.Ch11
