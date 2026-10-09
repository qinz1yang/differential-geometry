import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNativeLayerRadialC12X

/-!
# S16 uniform strong constants as closed terms of `ε`（O-CH11-S16CEIL G1）

S16 v3 radial engine `native_strongFull_uniform_of_classFull_radial_C12X`（S16K G3c）的形状是
`∃ Ccore Cu, 1 ≤ Ccore ∧ 1 ≤ Cu ∧ ∀ P₀ g₀ B, … ∀ C1 C2 … κ, …`：`Ccore Cu` 在任何
`P₀ / g₀ / B / κ` 之前选出（CX-RADIAL review #7）。本文件对这个 `∃` 取 `choose`，得到**只依赖
`ε`（与宇宙 `u`）的闭项** `strongCore_C11SC ε`、`strongWindow_C11SC ε`，以及 engine 的两个输出式

* `strongC1_C11SC ε C1 = max C1 (max Ccore Cu)`，
* `strongC2_C11SC ε C2 Cgrad = max C2 (max (max Ccore Cu) Cgrad)`。

`if h : 0 < ε ∧ ε ≤ εStrong_C12X` 只是让常数成为 `ε` 的函数（与证明无关）；在 `epsilon_strong`
之下永远走 `then` 分支。规格 `native_strongFull_uniform_radial_spec_C11SC` 就是 engine 本体，
常数处直接写 `strongC1_C11SC ε C1` / `strongC2_C11SC ε C2 Cgrad`。这样 class / state 可以导出
`C1h ≤ strongC1_C11SC ε C1`（REVIEW #8），右边是 `P/g/B/κ` 之前固定的闭项。

本文件只 import engine（不 import `PreparedSpatialStatePortC11P`），所以 State 可以 import 它；
shared ceiling `C1star_C12X` 形式（需要 `ClosedBirthConstants`）在 `StrongCeilingStarC11SC`。
-/

set_option autoImplicit false

noncomputable section

open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **uniform core constant**：radial engine（`θ = 5/4`）在精度 `ε` 处的 `Ccore`，对 engine 的
`∃ Ccore Cu`（位于其 `∀ P₀ g₀ B` 之前）取 `choose`；`ε` 越界时取 `1`（从不使用）。 -/
def strongCore_C11SC (ε : ℝ) : ℝ :=
  if h : 0 < ε ∧ ε ≤ εStrong_C12X.{u} then
    (native_strongFull_uniform_of_classFull_radial_C12X.{u} (θ := 5 / 4) (by norm_num) ε h.1
      h.2).choose
  else 1

/-- **uniform window constant**：同一次 `choose` 的 `Cu`。 -/
def strongWindow_C11SC (ε : ℝ) : ℝ :=
  if h : 0 < ε ∧ ε ≤ εStrong_C12X.{u} then
    (native_strongFull_uniform_of_classFull_radial_C12X.{u} (θ := 5 / 4) (by norm_num) ε h.1
      h.2).choose_spec.choose
  else 1

/-- engine 第一个输出式 `max C1 (max Ccore Cu)`（= `C1S_C12X C Ccore Cu` 当 `C1 := C.C1`）。 -/
def strongC1_C11SC (ε C1 : ℝ) : ℝ :=
  max C1 (max (strongCore_C11SC.{u} ε) (strongWindow_C11SC.{u} ε))

/-- engine 第二个输出式 `max C2 (max (max Ccore Cu) Cgrad)`（= `C2S_C12X`）。 -/
def strongC2_C11SC (ε C2 : ℝ) (Cgrad : ℝ≥0) : ℝ :=
  max C2 (max (max (strongCore_C11SC.{u} ε) (strongWindow_C11SC.{u} ε)) (Cgrad : ℝ))

theorem strongCore_eq_C11SC {ε : ℝ} (hε : 0 < ε) (hεs : ε ≤ εStrong_C12X.{u}) :
    strongCore_C11SC.{u} ε = (native_strongFull_uniform_of_classFull_radial_C12X.{u}
      (θ := 5 / 4) (by norm_num) ε hε hεs).choose :=
  dite_eq_left ⟨hε, hεs⟩

theorem strongWindow_eq_C11SC {ε : ℝ} (hε : 0 < ε) (hεs : ε ≤ εStrong_C12X.{u}) :
    strongWindow_C11SC.{u} ε = (native_strongFull_uniform_of_classFull_radial_C12X.{u}
      (θ := 5 / 4) (by norm_num) ε hε hεs).choose_spec.choose :=
  dite_eq_left ⟨hε, hεs⟩

theorem one_le_strongCore_C11SC (ε : ℝ) : 1 ≤ strongCore_C11SC.{u} ε := by
  unfold strongCore_C11SC
  split_ifs with h
  · exact (native_strongFull_uniform_of_classFull_radial_C12X.{u} (θ := 5 / 4) (by norm_num) ε
      h.1 h.2).choose_spec.choose_spec.1
  · exact le_rfl

theorem one_le_strongWindow_C11SC (ε : ℝ) : 1 ≤ strongWindow_C11SC.{u} ε := by
  unfold strongWindow_C11SC
  split_ifs with h
  · exact (native_strongFull_uniform_of_classFull_radial_C12X.{u} (θ := 5 / 4) (by norm_num) ε
      h.1 h.2).choose_spec.choose_spec.2.1
  · exact le_rfl

/-- **规格**：engine 本体，uniform 常数取上面的闭项。`C1 C2 Cgrad` 之后、`P₀ g₀ B κ` 之前的常数
就是 `strongC1_C11SC ε C1`、`strongC2_C11SC ε C2 Cgrad`。 -/
theorem native_strongFull_uniform_radial_spec_C11SC {ε : ℝ} (hε : 0 < ε)
    (hεs : ε ≤ εStrong_C12X.{u}) :
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (B : ℝ), 0 < B →
    ∀ (C1 C2 C1s C2s qcan qs τmin : ℝ) (Ctime Cgrad : ℝ≥0) (κ : ℝ),
      1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → qcan ≤ qs → 0 < τmin → 0 < κ →
    ∃ (qh δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
      qs ≤ qh ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}), InitialIdentification P₀ g₀ K.toHistory →
      ∀ (pK : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pK),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        RecordHypFar_C12X (5 / 4) K records →
        K.NoncollapsedBefore κ ε K.horizon →
        GC.GeneralFlow.NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad →
        K.EventSlabsStronglyCanonicalFull_C12X ε ε (strongC1_C11SC.{u} ε C1)
          (strongC2_C11SC.{u} ε C2 Cgrad) qh (Fin.last K.eventCount) ∧
        ∀ hfinal : K.time (Fin.last K.eventCount) < K.horizon,
          K.StronglyCanonicalBeforeFull_C12X (Fin.last K.eventCount)
            ((K.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl) ε ε
            (strongC1_C11SC.{u} ε C1) (strongC2_C11SC.{u} ε C2 Cgrad) qh K.horizon := by
  have hU := (native_strongFull_uniform_of_classFull_radial_C12X.{u} (θ := 5 / 4) (by norm_num)
    ε hε hεs).choose_spec.choose_spec.2.2
  rw [← strongWindow_eq_C11SC hε hεs, ← strongCore_eq_C11SC hε hεs] at hU
  exact hU

/-! ### Pure inequalities for the uniform pair -/

theorem C1_le_strongC1_C11SC (ε C1 : ℝ) : C1 ≤ strongC1_C11SC.{u} ε C1 := le_max_left _ _

theorem strongCore_le_strongC1_C11SC (ε C1 : ℝ) :
    strongCore_C11SC.{u} ε ≤ strongC1_C11SC.{u} ε C1 :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem strongWindow_le_strongC1_C11SC (ε C1 : ℝ) :
    strongWindow_C11SC.{u} ε ≤ strongC1_C11SC.{u} ε C1 :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem one_le_strongC1_C11SC {C1 : ℝ} (h : 1 ≤ C1) (ε : ℝ) : 1 ≤ strongC1_C11SC.{u} ε C1 :=
  h.trans (C1_le_strongC1_C11SC ε C1)

theorem C2_le_strongC2_C11SC (ε C2 : ℝ) (Cgrad : ℝ≥0) : C2 ≤ strongC2_C11SC.{u} ε C2 Cgrad :=
  le_max_left _ _

theorem strongCore_le_strongC2_C11SC (ε C2 : ℝ) (Cgrad : ℝ≥0) :
    strongCore_C11SC.{u} ε ≤ strongC2_C11SC.{u} ε C2 Cgrad :=
  ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)

theorem strongWindow_le_strongC2_C11SC (ε C2 : ℝ) (Cgrad : ℝ≥0) :
    strongWindow_C11SC.{u} ε ≤ strongC2_C11SC.{u} ε C2 Cgrad :=
  ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)

theorem Cgrad_le_strongC2_C11SC (ε C2 : ℝ) (Cgrad : ℝ≥0) :
    (Cgrad : ℝ) ≤ strongC2_C11SC.{u} ε C2 Cgrad :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem one_le_strongC2_C11SC {C2 : ℝ} (h : 1 ≤ C2) (ε : ℝ) (Cgrad : ℝ≥0) :
    1 ≤ strongC2_C11SC.{u} ε C2 Cgrad :=
  h.trans (C2_le_strongC2_C11SC ε C2 Cgrad)

/-- `strongC1` 是 engine 常数 `max C1 (max Ccore Cu)` 的最小上界形：任何同时支配 `C1`、core、
window 的 `K` 都支配它。 -/
theorem strongC1_le_of_C11SC {ε C1 K : ℝ} (h1 : C1 ≤ K) (h2 : strongCore_C11SC.{u} ε ≤ K)
    (h3 : strongWindow_C11SC.{u} ε ≤ K) : strongC1_C11SC.{u} ε C1 ≤ K :=
  max_le h1 (max_le h2 h3)

theorem strongC2_le_of_C11SC {ε C2 K : ℝ} {Cgrad : ℝ≥0} (h1 : C2 ≤ K)
    (h2 : strongCore_C11SC.{u} ε ≤ K) (h3 : strongWindow_C11SC.{u} ε ≤ K)
    (h4 : (Cgrad : ℝ) ≤ K) : strongC2_C11SC.{u} ε C2 Cgrad ≤ K :=
  max_le h1 (max_le (max_le h2 h3) h4)

/-- **consumer**：规格忠实——它重新给出 engine 的原陈述（`Ccore Cu` 取闭项）。 -/
example {ε : ℝ} (hε : 0 < ε) (hεs : ε ≤ εStrong_C12X.{u}) :
    type_of% (native_strongFull_uniform_of_classFull_radial_C12X.{u} (θ := 5 / 4)
      (by norm_num) ε hε hεs) :=
  ⟨strongCore_C11SC.{u} ε, strongWindow_C11SC.{u} ε, one_le_strongCore_C11SC ε,
    one_le_strongWindow_C11SC ε, native_strongFull_uniform_radial_spec_C11SC hε hεs⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
