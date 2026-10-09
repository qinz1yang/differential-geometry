import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongCeilingStarC11SC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AncientWitnessDecoupledP6P
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CapWindowWitnessP6CW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HcenCollarP6HE

set_option autoImplicit false

/-!
# P6 closed-term 常数 ceiling `C1P6 / C2P6`（O-CH11-GAPTOP6 G1a，后缀 `_C11GT6`）

R-C11-8 D-4（外审 Q2）：`hP6b` 的结论常数在 selection 之前固定，并支配 coarse kernel、fine recovery
（STAB2 的 `2C1 ≤ C1out`、`1000C2 ≤ C2out`）与 transfer 损失；`εP6 Γ` 不负责抬高常数。本文件给出
closed-term 路线（设计 `design-C11-gaptop6-20261007.md` §1）：

* `C1P6_C11GT6 X Γ := max (C1ceil_C11SC Γ) (X Γ)`（`C2P6` 同形）：对任一只依赖 `Γ` 的附加项 `X` 泛型；
  自动支配旧 ceiling `max Γ.C1s Γ.Cbirth` 与 S16 shared ceiling（v4）。
* closed term `p6CoarseC_C11GT6 η`（`ancientWitness_decoupled_P6P` 的 `C(ηout)`）、
  `p6CapCs_C11GT6 η`（HCAPW `exists_capWitness_of_standardClose_P6CW` 的 `Cs(ηout) = max Cw Cgrad`，
  lead 14:1x 补充）；
* 坏点精度（ceiling v2，R-C11-10 D-15′，O-CH11-CEIL3）`p6FineEta_C11GT6 η :=
  min (η/2) (min (neckModelTolerance (η/2) / 13000) (backgroundJetSmallness ThreeSpace ⌈η⁻¹⌉₊))`：
  `13000 · η₁ ≤ ηN := neckModelTolerance (η/2)`（CX-CAPCORE 精度方向）、
  `η₁ ≤ backgroundJetSmallness ThreeSpace ⌈η⁻¹⌉₊`（round transfer）、`η₁ ≤ η/2`；
* fine 常数 `p6FineC_C11GT6 η := max (Cco η₁) (max (Ccap η₁) (Ccol η))`（`η₁ := p6FineEta η`；
  `Ccol` = HCENP collar 常数 `capCollarCs_P6HE`，取 Good 精度 `η`）；
* 两级坏点常数（ceiling v3，GAMMA2 方案 A / D-15″，O-CH11-GAPTOP7）
  `p6BadC_C11G2 Γ := max (p6FineC ε) (max (C1ceil Γ) (C2ceil Γ))`（名字沿用 GAMMA2，定义上移到本文件）；
* 标准附加项 `p6X1std_C11GT6 / p6X2std_C11GT6`（D-15″：`c := p6BadC_C11G2 Γ`，D-15′ 为 `p6FineC ε`）：
  `max (Cco ε) (max (2 · (max c 9 + √c)) (Ccap ε))` /
  `max (Cco ε) (max (1200000 · c) (Ccap ε))`
  （`9` = STAB4 margin 创造 `exists_hasMargins_of_neck_P6ST4` 的 `max C1 9`；`√c` 与 `1200` =
  CX-CAPCORE 的常数放大 `C1 ↦ max C1 9 + √C2`、`C2 ↦ 1200 · C2`，再复合 STAB2 的 `2C1`、`1000C2`）；
* 支配引理 + `p6CapCs` 的 spec（HCAPW 结论在 closed term 处）+ consumer（HCAPW / STAB2 在 `C1P6` 处）。
-/

noncomputable section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-! ## 1. closed terms -/

/-- **coarse kernel 常数** `C(η)`：`ancientWitness_decoupled_P6P` 在精度 `η` 处的 `∃ C`（只依赖 `η`；
`η ∉ (0, 1/11)` 时取 `1`）。 -/
def p6CoarseC_C11GT6 (η : ℝ) : ℝ :=
  if h : 0 < η ∧ η < 1 / 11 then
    Classical.choose
      ((Classical.choose_spec ObservedHistory.ancientWitness_decoupled_P6P.{u}).2 η h.1 h.2)
  else 1

/-- `p6CoarseC` 在 `(0, 1/11)` 内就是 `ancientWitness_decoupled_P6P` 的 choice（spec 由
`Classical.choose_spec` 取）。 -/
theorem p6CoarseC_eq_C11GT6 {η : ℝ} (h : 0 < η ∧ η < 1 / 11) :
    p6CoarseC_C11GT6.{u} η = Classical.choose
      ((Classical.choose_spec ObservedHistory.ancientWitness_decoupled_P6P.{u}).2 η h.1 h.2) := by
  unfold p6CoarseC_C11GT6
  rw [dite_eq_left h]

theorem one_le_p6CoarseC_C11GT6 (η : ℝ) : 1 ≤ p6CoarseC_C11GT6.{u} η := by
  by_cases h : 0 < η ∧ η < 1 / 11
  · rw [p6CoarseC_eq_C11GT6 h]
    exact (Classical.choose_spec
      ((Classical.choose_spec ObservedHistory.ancientWitness_decoupled_P6P.{u}).2 η h.1 h.2)).1
  · unfold p6CoarseC_C11GT6
    rw [dite_eq_right h]

/-- **hcapW 常数** `Cs(η) = max Cw(η) Cgrad`：HCAPW `exists_capWitness_of_standardClose_P6CW` 的
`∃ Cs`（只依赖 `η`）。 -/
def p6CapCs_C11GT6 (η : ℝ) : ℝ :=
  if h : 0 < η ∧ η < 1 / 11 then
    Classical.choose
      (MetricCutCapEvent.PresentedStaticCap.exists_capWitness_of_standardClose_P6CW.{u} h.1 h.2)
  else 1

/-- **HCAPW 在 closed term 处**：`Cs := p6CapCs η` 时 HCAPW 的结论成立。 -/
theorem p6CapCs_spec_C11GT6 {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (Rcap : ℝ) (mcap : ℕ) (εcap : ℝ), 1 ≤ p6CapCs_C11GT6.{u} ε ∧ 0 < εcap ∧
    ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
      {fixed : StaticCapScaffold} {D ε₀ : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
      (S : E.PresentedStaticCap fixed D m ε₀ b), S.hasCanonicalWindow →
      ε₀ ≤ εcap → Rcap ≤ D → mcap ≤ m →
      ∀ C1 C2 : ℝ, p6CapCs_C11GT6.{u} ε ≤ C1 → p6CapCs_C11GT6.{u} ε ≤ C2 → ∀ x : ThreeBall,
      ∃ W : SpatialCanonicalWitness E.outputMetric ε C1 C2 (S.inclusion (S.witness.cap x)),
        W.capTubeHasNeckChart ε := by
  unfold p6CapCs_C11GT6
  rw [dite_eq_left ⟨hε, hε'⟩]
  exact Classical.choose_spec
    (MetricCutCapEvent.PresentedStaticCap.exists_capWitness_of_standardClose_P6CW.{u} hε hε')

/-- **坏点精度** `η₁`（ceiling v2，R-C11-10 D-15′）：
`min (η/2) (min (ηN / 13000) (backgroundJetSmallness ThreeSpace ⌈η⁻¹⌉₊))`，其中
`ηN := neckModelTolerance (η/2)` 是 STAB2 margin 层精度 `ηfine`（`BufferedTransferData_P6ST2.ηfine_le`
取等号）；`13000 · η₁ ≤ ηN` 是 CX-CAPCORE `hη` 的精度方向，`η₁ ≤ bJS` 是 round transfer 的前提。 -/
def p6FineEta_C11GT6 (η : ℝ) : ℝ :=
  min (η / 2) (min (neckModelTolerance (η / 2) / 13000)
    (backgroundJetSmallness ThreeSpace ⌈η⁻¹⌉₊))

theorem p6FineEta_pos_C11GT6 {η : ℝ} (hη : 0 < η) : 0 < p6FineEta_C11GT6 η :=
  lt_min (by linarith) (lt_min (div_pos (neckModelTolerance_pos (by linarith)) (by norm_num))
    (backgroundJetSmallness_pos _ _))

theorem p6FineEta_le_C11GT6 (η : ℝ) : p6FineEta_C11GT6 η ≤ η / 2 :=
  min_le_left _ _

/-- **fine 常数** `c(η) := max (Cco η₁) (max (Ccap η₁) (Ccol η))`（`η₁ := p6FineEta η`；`Ccol` =
HCENP collar 常数 `capCollarCs_P6HE`，取 Good 精度 `η`，付 `hcenE_of_noShortcut_P6HE` 的
`hCs1 / hCs2`）。坏点常数 `C1₁ = C2₁ := Cco η₁ ≤ c`；`Ccap η₁` 预埋 CEIL2 watch W1。 -/
def p6FineC_C11GT6 (η : ℝ) : ℝ :=
  max (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 η))
    (max (p6CapCs_C11GT6.{u} (p6FineEta_C11GT6 η)) (capCollarCs_P6HE.{u} η))

/-- **两级坏点常数** `c(Γ) := max (p6FineC ε) (max (C1ceil Γ) (C2ceil Γ))`（ceiling v3，GAMMA2 方案 A /
D-15″；`C1₁ = C2₁ := c(Γ)`）：比 D-15′ / CXHT G3 的 `p6FineC ε` 多 `C1ceil Γ`、`C2ceil Γ` 两项，以容纳更细
`Γf` tower 的 S5 常数（`FineOf Γf Γ` 下 `oldC Γf ≤ C1ceil Γf ≤ C1ceil Γ`）。名字沿用 GAMMA2
（原定义在 `P6Gamma2ContractC11G2`，上移到此作 X1 / X2 的 fine 项）。 -/
def p6BadC_C11G2 (Γ : ClosedBirthConstants) : ℝ :=
  max (p6FineC_C11GT6.{u} Γ.epsilon) (max (C1ceil_C11SC.{u} Γ) (C2ceil_C11SC.{u} Γ))

/-! ## 2. ceiling -/

/-- **P6 ceiling（`C1` 侧）**：`max (C1ceil_C11SC Γ) (X Γ)`，`X` 是只依赖 `Γ` 的附加项。 -/
def C1P6_C11GT6 (X : ClosedBirthConstants → ℝ) (Γ : ClosedBirthConstants) : ℝ :=
  max (C1ceil_C11SC.{u} Γ) (X Γ)

/-- **P6 ceiling（`C2` 侧）**。 -/
def C2P6_C11GT6 (X : ClosedBirthConstants → ℝ) (Γ : ClosedBirthConstants) : ℝ :=
  max (C2ceil_C11SC.{u} Γ) (X Γ)

/-- 标准附加项（`C1` 侧）：coarse `C(ε)`、fine recovery + CX-CAPCORE 放大 `2 · (max c 9 + √c)`
（D-15″：`c := p6BadC_C11G2 Γ ≥ p6FineC ε`）、hcapW `Cs(ε)`。 -/
def p6X1std_C11GT6 (Γ : ClosedBirthConstants) : ℝ :=
  max (p6CoarseC_C11GT6.{u} Γ.epsilon)
    (max (2 * (max (p6BadC_C11G2.{u} Γ) 9 +
        Real.sqrt (p6BadC_C11G2.{u} Γ)))
      (p6CapCs_C11GT6.{u} Γ.epsilon))

/-- 标准附加项（`C2` 侧）：coarse `C(ε)`、fine recovery + CX-CAPCORE 放大 `1200000 · c`
（D-15″：`c := p6BadC_C11G2 Γ`；`1000 · 1200`）、hcapW `Cs(ε)`。 -/
def p6X2std_C11GT6 (Γ : ClosedBirthConstants) : ℝ :=
  max (p6CoarseC_C11GT6.{u} Γ.epsilon)
    (max (1200000 * p6BadC_C11G2.{u} Γ)
      (p6CapCs_C11GT6.{u} Γ.epsilon))

/-- D-15″ 结构项（C1 侧）：`2 · (max c(Γ) 9 + √c(Γ)) ≤ X1std Γ`。 -/
theorem two_mul_bad_le_p6X1std_C11G7 (Γ : ClosedBirthConstants) :
    2 * (max (p6BadC_C11G2.{u} Γ) 9 + Real.sqrt (p6BadC_C11G2.{u} Γ)) ≤ p6X1std_C11GT6.{u} Γ :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- D-15″ 结构项（C2 侧）：`1200000 · c(Γ) ≤ X2std Γ`。 -/
theorem mul1200k_bad_le_p6X2std_C11G7 (Γ : ClosedBirthConstants) :
    1200000 * p6BadC_C11G2.{u} Γ ≤ p6X2std_C11GT6.{u} Γ :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- D-15″ 单调（C1 侧）：`p6FineC ε ≤ c(Γ)` ⇒ D-15′ 的 fine 项 `2 · (max c 9 + √c)` 仍被 X1std 支配
（既有支配引理陈述照旧成立）。 -/
theorem two_mul_fine_le_p6X1std_C11G7 (Γ : ClosedBirthConstants) :
    2 * (max (p6FineC_C11GT6.{u} Γ.epsilon) 9 + Real.sqrt (p6FineC_C11GT6.{u} Γ.epsilon)) ≤
      p6X1std_C11GT6.{u} Γ := by
  have hc : p6FineC_C11GT6.{u} Γ.epsilon ≤ p6BadC_C11G2.{u} Γ := le_max_left _ _
  have hm : max (p6FineC_C11GT6.{u} Γ.epsilon) 9 ≤ max (p6BadC_C11G2.{u} Γ) 9 :=
    max_le_max hc le_rfl
  have hs : Real.sqrt (p6FineC_C11GT6.{u} Γ.epsilon) ≤ Real.sqrt (p6BadC_C11G2.{u} Γ) :=
    Real.sqrt_le_sqrt hc
  have hX := two_mul_bad_le_p6X1std_C11G7.{u} Γ
  linarith

/-- D-15″ 单调（C2 侧）：`1200000 · p6FineC ε ≤ X2std Γ`。 -/
theorem mul1200k_fine_le_p6X2std_C11G7 (Γ : ClosedBirthConstants) :
    1200000 * p6FineC_C11GT6.{u} Γ.epsilon ≤ p6X2std_C11GT6.{u} Γ := by
  have hc : p6FineC_C11GT6.{u} Γ.epsilon ≤ p6BadC_C11G2.{u} Γ := le_max_left _ _
  have hX := mul1200k_bad_le_p6X2std_C11G7.{u} Γ
  linarith

theorem C1ceil_le_C1P6_C11GT6 (X : ClosedBirthConstants → ℝ) (Γ : ClosedBirthConstants) :
    C1ceil_C11SC.{u} Γ ≤ C1P6_C11GT6.{u} X Γ :=
  le_max_left _ _

theorem C2ceil_le_C2P6_C11GT6 (X : ClosedBirthConstants → ℝ) (Γ : ClosedBirthConstants) :
    C2ceil_C11SC.{u} Γ ≤ C2P6_C11GT6.{u} X Γ :=
  le_max_left _ _

theorem X_le_C1P6_C11GT6 (X : ClosedBirthConstants → ℝ) (Γ : ClosedBirthConstants) :
    X Γ ≤ C1P6_C11GT6.{u} X Γ :=
  le_max_right _ _

theorem X_le_C2P6_C11GT6 (X : ClosedBirthConstants → ℝ) (Γ : ClosedBirthConstants) :
    X Γ ≤ C2P6_C11GT6.{u} X Γ :=
  le_max_right _ _

/-- 旧 ceiling（native canonical S4 / S5 的常数）≤ `C1P6`。 -/
theorem oldC1_le_C1P6_C11GT6 (X : ClosedBirthConstants → ℝ) (Γ : ClosedBirthConstants) :
    max Γ.C1s Γ.Cbirth ≤ C1P6_C11GT6.{u} X Γ :=
  (oldC1_le_C1ceil_C11SC.{u} Γ).trans (C1ceil_le_C1P6_C11GT6 X Γ)

theorem oldC2_le_C2P6_C11GT6 (X : ClosedBirthConstants → ℝ) (Γ : ClosedBirthConstants) :
    max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ)) ≤ C2P6_C11GT6.{u} X Γ :=
  (oldC2_le_C2ceil_C11SC.{u} Γ).trans (C2ceil_le_C2P6_C11GT6 X Γ)

theorem one_le_C1P6_C11GT6 (X : ClosedBirthConstants → ℝ) (Γ : ClosedBirthConstants) :
    1 ≤ C1P6_C11GT6.{u} X Γ :=
  (one_le_C1ceil_C11SC.{u} Γ).trans (C1ceil_le_C1P6_C11GT6 X Γ)

theorem one_le_C2P6_C11GT6 (X : ClosedBirthConstants → ℝ) (Γ : ClosedBirthConstants) :
    1 ≤ C2P6_C11GT6.{u} X Γ :=
  (one_le_C2ceil_C11SC.{u} Γ).trans (C2ceil_le_C2P6_C11GT6 X Γ)

/-- 标准 ceiling 支配 coarse kernel：`C(ε) ≤ C1P6, C2P6`。 -/
theorem coarse_le_C1P6std_C11GT6 (Γ : ClosedBirthConstants) :
    p6CoarseC_C11GT6.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ :=
  le_trans (le_max_left _ _ : _ ≤ p6X1std_C11GT6.{u} Γ) (X_le_C1P6_C11GT6 p6X1std_C11GT6.{u} Γ)

theorem coarse_le_C2P6std_C11GT6 (Γ : ClosedBirthConstants) :
    p6CoarseC_C11GT6.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  le_trans (le_max_left _ _ : _ ≤ p6X2std_C11GT6.{u} Γ) (X_le_C2P6_C11GT6 p6X2std_C11GT6.{u} Γ)

/-- 标准 ceiling 支配 fine recovery + transfer 损失（STAB2 `2C1 ≤ C1out`，`C1 = max C(η₁) 9`；
v2：经 `Cco η₁ ≤ c` 与 `0 ≤ √c` 由 X1 的 `2 · (max c 9 + √c)` 项支配）。 -/
theorem two_mul_fine_le_C1P6std_C11GT6 (Γ : ClosedBirthConstants) :
    2 * max (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) 9 ≤
      C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ := by
  have hc : p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤
      p6FineC_C11GT6.{u} Γ.epsilon := le_max_left _ _
  have hm : max (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) 9 ≤
      max (p6FineC_C11GT6.{u} Γ.epsilon) 9 := max_le_max hc le_rfl
  have hs := Real.sqrt_nonneg (p6FineC_C11GT6.{u} Γ.epsilon)
  have hX := two_mul_fine_le_p6X1std_C11G7.{u} Γ
  have hC := X_le_C1P6_C11GT6 p6X1std_C11GT6.{u} Γ
  linarith

/-- STAB2 `1000C2 ≤ C2out`，`C2 = C(η₁)`（v2：`1000 · Cco η₁ ≤ 1200000 · c`，`1 ≤ Cco η₁ ≤ c`）。 -/
theorem thousand_mul_fine_le_C2P6std_C11GT6 (Γ : ClosedBirthConstants) :
    1000 * p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤
      C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ := by
  have h1 := one_le_p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)
  have hc : p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤
      p6FineC_C11GT6.{u} Γ.epsilon := le_max_left _ _
  have hX := mul1200k_fine_le_p6X2std_C11G7.{u} Γ
  have hC := X_le_C2P6_C11GT6 p6X2std_C11GT6.{u} Γ
  linarith

/-- 标准 ceiling 支配 hcapW 常数 `Cs(ε)`（HCAPW D-11：`Cs ≤ C1out`）。 -/
theorem capCs_le_C1P6std_C11GT6 (Γ : ClosedBirthConstants) :
    p6CapCs_C11GT6.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ :=
  le_trans (((le_max_right _ _).trans (le_max_right _ _)) : _ ≤ p6X1std_C11GT6.{u} Γ)
    (X_le_C1P6_C11GT6 p6X1std_C11GT6.{u} Γ)

theorem capCs_le_C2P6std_C11GT6 (Γ : ClosedBirthConstants) :
    p6CapCs_C11GT6.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  le_trans (((le_max_right _ _).trans (le_max_right _ _)) : _ ≤ p6X2std_C11GT6.{u} Γ)
    (X_le_C2P6_C11GT6 p6X2std_C11GT6.{u} Γ)

/-- `Γ.epsilon ∈ (0, 1/11)`：closed term 走 `then` 支。 -/
theorem epsilon_mem_C11GT6 (Γ : ClosedBirthConstants) : 0 < Γ.epsilon ∧ Γ.epsilon < 1 / 11 :=
  ⟨Γ.epsilon_pos, Γ.epsilon_small.trans (by norm_num)⟩

/-! ## 3. consumers -/

/-- consumer（HCAPW D-11）：`C1P6 / C2P6`（标准）处的 cap-window witness——HCAPW 的 `Cs ≤ C1out, C2out`
由 ceiling 支付。 -/
theorem capWitness_at_C1P6std_C11GT6 (Γ : ClosedBirthConstants) :
    ∃ (Rcap : ℝ) (mcap : ℕ) (εcap : ℝ), 0 < εcap ∧
    ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
      {fixed : StaticCapScaffold} {D ε₀ : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
      (S : E.PresentedStaticCap fixed D m ε₀ b), S.hasCanonicalWindow →
      ε₀ ≤ εcap → Rcap ≤ D → mcap ≤ m → ∀ x : ThreeBall,
      ∃ W : SpatialCanonicalWitness E.outputMetric Γ.epsilon
          (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ) (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ)
          (S.inclusion (S.witness.cap x)),
        W.capTubeHasNeckChart Γ.epsilon := by
  obtain ⟨Rcap, mcap, εcap, -, hεcap, hW⟩ :=
    p6CapCs_spec_C11GT6.{u} (epsilon_mem_C11GT6 Γ).1 (epsilon_mem_C11GT6 Γ).2
  exact ⟨Rcap, mcap, εcap, hεcap, fun S hS h1 h2 h3 x =>
    hW S hS h1 h2 h3 _ _ (capCs_le_C1P6std_C11GT6 Γ) (capCs_le_C2P6std_C11GT6 Γ) x⟩

/-- consumer（STAB2 fine recovery / transfer）：fine witness 常数 `(max C(ηfine) 9, C(ηfine))` 的
buffered transfer 合同 ⇒ 输出 witness 在 `(Γ.ε, C1P6, C2P6)`（标准）处。 -/
example (Γ : ClosedBirthConstants) {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E : MetricCutCapEvent P Q a s} {p : P.Carrier} {q : Q.Carrier} {m : ℝ} {k : ℕ}
    (D : E.BufferedTransferData_P6ST2 p q (p6FineEta_C11GT6 Γ.epsilon) Γ.epsilon
      (max (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) 9)
      (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) m k) :
    ∃ W : SpatialCanonicalWitness E.outputMetric Γ.epsilon
        (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ) (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) q,
      W.capTubeHasNeckChart Γ.epsilon :=
  E.spatialWitness_of_bufferedTransfer_P6ST2 D (two_mul_fine_le_C1P6std_C11GT6 Γ)
    (thousand_mul_fine_le_C2P6std_C11GT6 Γ)

/-- consumer（coarse kernel，`goodConstants_accommodate_P6P` 的 (ii)）：`C(ε) ≤ C1P6`、`C(ε) ≤ C2P6`，
`1 ≤ C(ε)`。 -/
example (Γ : ClosedBirthConstants) :
    1 ≤ p6CoarseC_C11GT6.{u} Γ.epsilon ∧
      p6CoarseC_C11GT6.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      p6CoarseC_C11GT6.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  ⟨one_le_p6CoarseC_C11GT6 _, coarse_le_C1P6std_C11GT6 Γ, coarse_le_C2P6std_C11GT6 Γ⟩

end GC.LongTime.Ch11
