import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingDomC11CL2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FineMarginImproveCXCC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RoundTransferP6SF

set_option autoImplicit false

/-!
# P6 常数链接线包：CHAIN 20 行不等式表在 D-15′ 赋值下逐条成 theorem（S-CH11-CHAINW G1，后缀 `_C11CW`）

`state-S-CH11-CHAIN.md` §1 的 20 行不等式表（谁要求 / 谁付）在 R-C11-10 addendum D-15′ 的赋值下逐行写成
Lean 引理；每条 docstring 注明 "CHAIN 表第 n 行，消费者 = …"。**赋值**（全是 `Γ.epsilon` 的闭项；
`ε := Γ.epsilon`，`CEIL3` 版 GT6 / CL2）：

* `η₁ := p6FineEta_C11GT6 ε = min (ε/2) (min (ηN/13000) (bJS ThreeSpace ⌈ε⁻¹⌉₊))`（坏点精度），
  `ηN := neckModelTolerance (ε/2) =: p6EtaN_C11CW Γ`（margin 层精度 `ηfine`，STAB2 `hle := le_rfl`）；
* `c := p6FineC_C11GT6 ε = max (Cco η₁) (max (Ccap η₁) (Ccol ε))`；坏点常数 `C1₁, C2₁ ∈ [Cco η₁, c]`
  （RERUN8B 固定实例 `C1₁ = C2₁ = Cco η₁`；CEIL2 W1 预埋实例 `C1₁ = C2₁ = c`；每行对整个区间成立）；
* `C1f := max c 9 + √c`（`p6C1f_C11CW`）、`C2f := 1200 · c`（`p6C2f_C11CW`）、
  `m := min (1/20) (1/(10 · c · √c))`（`p6M_C11CW`）、`kk := max 2 ⌈ε⁻¹⌉₊`（`p6kk_C11CW`）；
* Good 层 `C1 := C1P6 X1std Γ`、`C2 := C2P6 X2std Γ`。

行状态：第 1–6、8–16、18–20 行 PROVED（`chain01`…`chain20`）；第 7 行（footprint，producer = hfoot / P-F）
与第 17 行（类型鸽笼）见各自 docstring 的 BLOCKED 标注（具名 Prop + 缺的事实）。
§4 consumer：CXCC `fineGood_implies_fineMarginGood_CXCC` / `fineMarginGood_of_cap_CXCC`、STAB4
`fineGood_implies_fineMarginGood_P6ST4`、event 层 `frequently_whole_of_not_witness_CXCC`、SCFIN
`frequently_not_wholeComponent_P6SF`、STAB4 G3 `wholeComponent_positive_transfer_P6ST4` 在这组常数处实例化，
前提全由 §2 付。
-/

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Manifold ContDiff Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. closed terms -/

/-- margin 层精度 `ηfine := ηN := neckModelTolerance (ε/2)`（STAB2 `BufferedTransferData_P6ST2.ηfine_le`
取等号）。 -/
def p6EtaN_C11CW (Γ : ClosedBirthConstants) : ℝ :=
  neckModelTolerance (Γ.epsilon / 2)

/-- footprint 层 fine 常数 `C1f := max c 9 + √c`（`c := p6FineC ε`；CX-CAPCORE 放大 `C1 ↦ max C1 9 + √C2`，
`C1 = C2 = c`）。 -/
def p6C1f_C11CW (Γ : ClosedBirthConstants) : ℝ :=
  max (p6FineC_C11GT6.{u} Γ.epsilon) 9 + Real.sqrt (p6FineC_C11GT6.{u} Γ.epsilon)

/-- footprint 层 fine 常数 `C2f := 1200 · c`（CX-CAPCORE 放大 `C2 ↦ 1200 · C2`）。 -/
def p6C2f_C11CW (Γ : ClosedBirthConstants) : ℝ :=
  1200 * p6FineC_C11GT6.{u} Γ.epsilon

/-- margin `m := min (1/20) (1/(10 · c · √c))`：STAB4 neck 的 `m ≤ 1/20` 与 CX-CAPCORE 的
`m ≤ 1/(10 · C1₁ · √C2₁)`（`C1₁, C2₁ ≤ c`）同时被它吸收。 -/
def p6M_C11CW (Γ : ClosedBirthConstants) : ℝ :=
  min (1 / 20) (1 / (10 * p6FineC_C11GT6.{u} Γ.epsilon * Real.sqrt (p6FineC_C11GT6.{u} Γ.epsilon)))

/-- footprint 层阶 `kk := max 2 ⌈ε⁻¹⌉₊`（`BufferedFootprintData_P6ST2.order_le` 取等号）。 -/
def p6kk_C11CW (Γ : ClosedBirthConstants) : ℕ :=
  max 2 ⌈Γ.epsilon⁻¹⌉₊

/-- `0 < c`（算术辅助：`1 ≤ c`）。 -/
theorem fineC_pos_C11CW (Γ : ClosedBirthConstants) : 0 < p6FineC_C11GT6.{u} Γ.epsilon :=
  lt_of_lt_of_le one_pos (one_le_fineC_C11CL3.{u} Γ.epsilon)

/-- `0 < √c`（算术辅助）。 -/
theorem sqrt_fineC_pos_C11CW (Γ : ClosedBirthConstants) :
    0 < Real.sqrt (p6FineC_C11GT6.{u} Γ.epsilon) :=
  Real.sqrt_pos.mpr (fineC_pos_C11CW.{u} Γ)

/-! ## 2. CHAIN 表 20 行 -/

/-- **CHAIN 表第 1 行**：`Cco ε ≤ C1, C2`，`1 ≤ Cco ε`。消费者 = coarse kernel
（`goodConstants_accommodate_P6P` (ii)；GT6 X 首项）。 -/
theorem chain01_coarse_C11CW (Γ : ClosedBirthConstants) :
    1 ≤ p6CoarseC_C11GT6.{u} Γ.epsilon ∧
      p6CoarseC_C11GT6.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      p6CoarseC_C11GT6.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  ⟨one_le_p6CoarseC_C11GT6 _, coarse_le_C1P6_C11CL2 Γ, coarse_le_C2P6_C11CL2 Γ⟩

/-- **CHAIN 表第 2 行**：`Ccap ε ≤ C1, C2`。消费者 = HCAPW `hcapWL_of_records_P6HB` /
`hcapW_of_standardClose_P6CW`（Good 精度 `ε` 处，`capWitness_at_C1P6std_C11GT6`）。 -/
theorem chain02_capGood_C11CW (Γ : ClosedBirthConstants) :
    p6CapCs_C11GT6.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      p6CapCs_C11GT6.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  ⟨capCs_le_C1P6_C11CL2 Γ, capCs_le_C2P6_C11CL2 Γ⟩

/-- **CHAIN 表第 3 行**：`C1ceil Γ ≤ C1`、`C2ceil Γ ≤ C2`。消费者 = S16 shared ceiling / native canonical
S4 S5 常数（`oldC1_le_C1P6_C11GT6`，CX-OUTER `outerSupply_ceiling_CXOU`）。 -/
theorem chain03_ceil_C11CW (Γ : ClosedBirthConstants) :
    C1ceil_C11SC.{u} Γ ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      C2ceil_C11SC.{u} Γ ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  ⟨C1ceil_le_C1P6_C11CL2 Γ, C2ceil_le_C2P6_C11CL2 Γ⟩

/-- **CHAIN 表第 4 行**：`ηfine := ηN ≤ neckModelTolerance (ε/2)`（`le_rfl`），外加 `0 < ηN < 1/11`。
消费者 = STAB2 `BufferedTransferData_P6ST2.ηfine_le`（`frequently_not_fineMargin_P6ST2` 的 `hle`）、
CXCC `frequently_whole_of_not_witness_CXCC` 的 `hle`。 -/
theorem chain04_etaFine_C11CW (Γ : ClosedBirthConstants) :
    p6EtaN_C11CW Γ ≤ neckModelTolerance (Γ.epsilon / 2) ∧ 0 < p6EtaN_C11CW Γ ∧
      p6EtaN_C11CW Γ < 1 / 11 := by
  have hε := epsilon_mem_C11GT6 Γ
  refine ⟨le_rfl, neckModelTolerance_pos (by linarith [hε.1]), ?_⟩
  have h := neckModelTolerance_le (Γ.epsilon / 2)
  change neckModelTolerance (Γ.epsilon / 2) < 1 / 11
  linarith [hε.2]

/-- **CHAIN 表第 5 行**：`2 · C1f ≤ C1`、`1000 · C2f ≤ C2`。消费者 = STAB2
`spatialWitness_of_bufferedTransfer_P6ST2` 的 `h1 : 2 * C1 ≤ C1out`、`h2 : 1000 * C2 ≤ C2out`
（fine 常数取 `C1f / C2f`）；CXCC `frequently_whole_of_not_witness_CXCC` 的 `h1 / h2`。 -/
theorem chain05_recover_C11CW (Γ : ClosedBirthConstants) :
    2 * p6C1f_C11CW.{u} Γ ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      1000 * p6C2f_C11CW.{u} Γ ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  ⟨two_mul_fineCX_le_C1P6_C11CL3 Γ, thousand_mul_fineCX_le_C2P6_C11CL3 Γ⟩

/-- **CHAIN 表第 6 行**：`1 ≤ C1f`、`1 ≤ C2f`、`0 < m ≤ 1/2`、`max 2 ⌈ε⁻¹⌉₊ ≤ kk`，外加 `ε < 1/11`。
消费者 = STAB2 `BufferedFootprintData_P6ST2` 的字段 `ηout_lt / one_le_C1 / one_le_C2 / m_pos / m_le /
order_le`（`ηout := ε`）。 -/
theorem chain06_footprintFields_C11CW (Γ : ClosedBirthConstants) :
    Γ.epsilon < 1 / 11 ∧ 1 ≤ p6C1f_C11CW.{u} Γ ∧ 1 ≤ p6C2f_C11CW.{u} Γ ∧ 0 < p6M_C11CW.{u} Γ ∧
      p6M_C11CW.{u} Γ ≤ 1 / 2 ∧ max 2 ⌈Γ.epsilon⁻¹⌉₊ ≤ p6kk_C11CW Γ := by
  have hc := one_le_fineC_C11CL3.{u} Γ.epsilon
  have hs := Real.sqrt_nonneg (p6FineC_C11GT6.{u} Γ.epsilon)
  have h9 : (9 : ℝ) ≤ max (p6FineC_C11GT6.{u} Γ.epsilon) 9 := le_max_right _ _
  refine ⟨(epsilon_mem_C11GT6 Γ).2, ?_, ?_, ?_, ?_, le_rfl⟩
  · change 1 ≤ max (p6FineC_C11GT6.{u} Γ.epsilon) 9 + Real.sqrt (p6FineC_C11GT6.{u} Γ.epsilon)
    linarith
  · change 1 ≤ 1200 * p6FineC_C11GT6.{u} Γ.epsilon
    linarith
  · exact lt_min (by norm_num) (one_div_pos.mpr (mul_pos (mul_pos (by norm_num)
      (fineC_pos_C11CW.{u} Γ)) (sqrt_fineC_pos_C11CW.{u} Γ)))
  · exact (min_le_left _ _).trans (by norm_num)

/-- **CHAIN 表第 7 行（BLOCKED：producer = hfoot / P-F，几何字段）**：footprint 层合同在这组闭项常数
`(ε, C1f, C2f, m, kk)` 处非空。`BufferedFootprintData_P6ST2` 的**常数**字段（`ηout_lt / one_le_C1 /
one_le_C2 / m_pos / m_le / order_le`）已由 `chain06_footprintFields_C11CW` 付清；缺的是**几何**字段：
`J / U / v / scalar_tendsto / footprint / comparison / gradient_tendsto`——其中 `footprint` 的半径
`(8 · C1f + 3 · ((ε/2)⁻¹ + 7) · √C2f)/√Q_n` 是本组常数的闭项（`p6FootprintRadius_C11CW`），渐近尺度
`/√R_k → 0`，与固定常数无关。repair target = hfoot（HB2 `hbd_stage_late_P6HB2` 的 `hfoot` 槽，
producer 须在**这组**常数处陈述；P-F）。 -/
def Footprint_C11CW (Γ : ClosedBirthConstants) {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) (p : P.Carrier) (q : Q.Carrier) : Prop :=
  Nonempty (E.BufferedFootprintData_P6ST2 p q Γ.epsilon (p6C1f_C11CW.{u} Γ) (p6C2f_C11CW.{u} Γ)
    (p6M_C11CW.{u} Γ) (p6kk_C11CW Γ))

/-- **CHAIN 表第 7 行（常数部分）**：footprint 半径常数 `8 · C1f + 3 · ((ε/2)⁻¹ + 7) · √C2f`（闭项），
消费者 = `BufferedFootprintData_P6ST2.footprint` 的物理半径分子；hfoot 在 `/√Q_n` 之前要与之对齐。 -/
def p6FootprintRadius_C11CW (Γ : ClosedBirthConstants) : ℝ :=
  8 * p6C1f_C11CW.{u} Γ + 3 * ((Γ.epsilon / 2)⁻¹ + 7) * Real.sqrt (p6C2f_C11CW.{u} Γ)

/-- footprint 半径常数为正（hfoot 的球半径非退化）。 -/
theorem p6FootprintRadius_pos_C11CW (Γ : ClosedBirthConstants) :
    0 < p6FootprintRadius_C11CW.{u} Γ := by
  have h1 := (chain06_footprintFields_C11CW.{u} Γ).2.1
  have h2 := (chain06_footprintFields_C11CW.{u} Γ).2.2.1
  have hε := (epsilon_mem_C11GT6 Γ).1
  have hs : 0 < Real.sqrt (p6C2f_C11CW.{u} Γ) := Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos h2)
  have hi : 0 < (Γ.epsilon / 2)⁻¹ := inv_pos.mpr (by linarith)
  unfold p6FootprintRadius_C11CW
  have : 0 < 3 * ((Γ.epsilon / 2)⁻¹ + 7) * Real.sqrt (p6C2f_C11CW.{u} Γ) := by positivity
  linarith

/-- **CHAIN 表第 8 行**：neck 支。`η₁ ≤ ηN`、`max C1₁ 9 ≤ C1f`、`C2₁ ≤ C2f`、`m ≤ 1/20`
（`C1₁, C2₁ ≤ c`）。消费者 = STAB4 G1′ `fineGood_implies_fineMarginGood_P6ST4` /
`fineMarginGood_of_neck_P6ST4` 的 `hη / hC1 / hC2 / hm`。 -/
theorem chain08_neck_C11CW (Γ : ClosedBirthConstants) {C₁ C₂ : ℝ}
    (hC₁ : C₁ ≤ p6FineC_C11GT6.{u} Γ.epsilon) (hC₂ : C₂ ≤ p6FineC_C11GT6.{u} Γ.epsilon) :
    p6FineEta_C11GT6 Γ.epsilon ≤ p6EtaN_C11CW Γ ∧ max C₁ 9 ≤ p6C1f_C11CW.{u} Γ ∧
      C₂ ≤ p6C2f_C11CW.{u} Γ ∧ p6M_C11CW.{u} Γ ≤ 1 / 20 := by
  have hc := one_le_fineC_C11CL3.{u} Γ.epsilon
  have hs := Real.sqrt_nonneg (p6FineC_C11GT6.{u} Γ.epsilon)
  refine ⟨?_, ?_, ?_, min_le_left _ _⟩
  · have h := fineEta_lt_neckTol_C11CL3 (epsilon_mem_C11GT6 Γ).1
    exact h.le
  · change max C₁ 9 ≤
      max (p6FineC_C11GT6.{u} Γ.epsilon) 9 + Real.sqrt (p6FineC_C11GT6.{u} Γ.epsilon)
    have : max C₁ 9 ≤ max (p6FineC_C11GT6.{u} Γ.epsilon) 9 := max_le_max hC₁ le_rfl
    linarith
  · change C₂ ≤ 1200 * p6FineC_C11GT6.{u} Γ.epsilon
    linarith

/-- **CHAIN 表第 9 行**：cap 支精度。`13000 · η₁ ≤ ηN < 1/11`。消费者 = CXCC
`exists_hasMargins_of_cap_CXCC` / `fineMarginGood_of_cap_CXCC` /
`fineGood_implies_fineMarginGood_CXCC` 的 `hη : 13000 * η ≤ η'`、`hη' : η' < 1/11`
（`η := η₁`、`η' := ηN`）。 -/
theorem chain09_capPrecision_C11CW (Γ : ClosedBirthConstants) :
    13000 * p6FineEta_C11GT6 Γ.epsilon ≤ p6EtaN_C11CW Γ ∧ p6EtaN_C11CW Γ < 1 / 11 :=
  ⟨thirteenK_mul_fineEta_le_C11CL3 Γ.epsilon, (chain04_etaFine_C11CW Γ).2.2⟩

/-- **CHAIN 表第 10 行**：cap 支常数放大。`max C1₁ 9 + √C2₁ ≤ C1f`、`1200 · C2₁ ≤ C2f`
（`C1₁, C2₁ ≤ c`）。消费者 = CXCC `fineGood_implies_fineMarginGood_CXCC` 的 `hC1 / hC2`；
`frequently_whole_of_not_witness_CXCC` 的 `hC1 / hC2`。 -/
theorem chain10_capAmplify_C11CW (Γ : ClosedBirthConstants) {C₁ C₂ : ℝ}
    (hC₁ : C₁ ≤ p6FineC_C11GT6.{u} Γ.epsilon) (hC₂ : C₂ ≤ p6FineC_C11GT6.{u} Γ.epsilon) :
    max C₁ 9 + Real.sqrt C₂ ≤ p6C1f_C11CW.{u} Γ ∧ 1200 * C₂ ≤ p6C2f_C11CW.{u} Γ := by
  refine ⟨?_, ?_⟩
  · exact add_le_add (max_le_max hC₁ le_rfl) (Real.sqrt_le_sqrt hC₂)
  · change 1200 * C₂ ≤ 1200 * p6FineC_C11GT6.{u} Γ.epsilon
    exact mul_le_mul_of_nonneg_left hC₂ (by norm_num)

/-- **CHAIN 表第 11 行**：`m ≤ 1/(10 · C1₁ · √C2₁)` 且 `m ≤ 1/20`（`1 ≤ C1₁, C2₁ ≤ c`）。消费者 = CXCC
`hm'` + STAB4 `hm`（`fineGood_implies_fineMarginGood_CXCC` 的 `hm / hm'`）。 -/
theorem chain11_margin_C11CW (Γ : ClosedBirthConstants) {C₁ C₂ : ℝ} (h1 : 1 ≤ C₁) (h2 : 1 ≤ C₂)
    (hC₁ : C₁ ≤ p6FineC_C11GT6.{u} Γ.epsilon) (hC₂ : C₂ ≤ p6FineC_C11GT6.{u} Γ.epsilon) :
    p6M_C11CW.{u} Γ ≤ 1 / (10 * C₁ * Real.sqrt C₂) ∧ p6M_C11CW.{u} Γ ≤ 1 / 20 := by
  refine ⟨?_, min_le_left _ _⟩
  have hs2 : 0 < Real.sqrt C₂ := Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos h2)
  have hpos : 0 < 10 * C₁ * Real.sqrt C₂ :=
    mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le one_pos h1)) hs2
  have hle : 10 * C₁ * Real.sqrt C₂ ≤
      10 * p6FineC_C11GT6.{u} Γ.epsilon * Real.sqrt (p6FineC_C11GT6.{u} Γ.epsilon) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hC₁ (by norm_num)) (Real.sqrt_le_sqrt hC₂)
      (Real.sqrt_nonneg _) (by have := fineC_pos_C11CW.{u} Γ; positivity)
  exact (min_le_right _ _).trans (one_div_le_one_div_of_le hpos hle)

/-- **CHAIN 表第 12 行**：positive whole-component 传递的常数前提。`1 ≤ C1₁, C2₁`；`0 < ε < 1`；
`2 · C1₁ ≤ C1`；`1000 · C2₁ ≤ C2`（`C1₁, C2₁ ≤ c`）。消费者 = STAB4 G3
`wholeComponent_positive_transfer_P6ST4` 的 `hC1 hC2 hη0 hη1 h1 h2`（bad → out 直接传递，不经 STAB2）。 -/
theorem chain12_positive_C11CW (Γ : ClosedBirthConstants) {C₁ C₂ : ℝ} (h1 : 1 ≤ C₁) (h2 : 1 ≤ C₂)
    (hC₁ : C₁ ≤ p6FineC_C11GT6.{u} Γ.epsilon) (hC₂ : C₂ ≤ p6FineC_C11GT6.{u} Γ.epsilon) :
    1 ≤ C₁ ∧ 1 ≤ C₂ ∧ 0 < Γ.epsilon ∧ Γ.epsilon < 1 ∧
      2 * C₁ ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      1000 * C₂ ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ := by
  have hε := epsilon_mem_C11GT6 Γ
  have hc := one_le_fineC_C11CL3.{u} Γ.epsilon
  have hs := Real.sqrt_nonneg (p6FineC_C11GT6.{u} Γ.epsilon)
  have hm : p6FineC_C11GT6.{u} Γ.epsilon ≤ max (p6FineC_C11GT6.{u} Γ.epsilon) 9 := le_max_left _ _
  have h5 := two_mul_fineCX_le_C1P6_C11CL3.{u} Γ
  have h6 := thousand_mul_fineCX_le_C2P6_C11CL3.{u} Γ
  refine ⟨h1, h2, hε.1, by linarith [hε.2], ?_, ?_⟩
  · linarith
  · linarith

/-- **CHAIN 表第 13 行**：round whole-component 传递的前提（含旧链漏掉的 `bJS` 精度）。
`0 < η₁ < ε ≤ 1/2`；**`η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊`**；`2 · C1₁ ≤ C1`；
`1000 · C2₁ ≤ C2`（`C1₁, C2₁ ≤ c`）。消费者 = SCFIN G3 `wholeComponent_round_transfer_P6SF` /
`frequently_not_wholeComponent_P6SF` 的 `hη0 hηlt hηhalf hsmall h1 h2`（`ηfine := η₁`、`ηout := ε`）。 -/
theorem chain13_round_C11CW (Γ : ClosedBirthConstants) {C₁ C₂ : ℝ}
    (hC₁ : C₁ ≤ p6FineC_C11GT6.{u} Γ.epsilon) (hC₂ : C₂ ≤ p6FineC_C11GT6.{u} Γ.epsilon) :
    0 < p6FineEta_C11GT6 Γ.epsilon ∧ p6FineEta_C11GT6 Γ.epsilon < Γ.epsilon ∧ Γ.epsilon ≤ 1 / 2 ∧
      p6FineEta_C11GT6 Γ.epsilon ≤ backgroundJetSmallness ThreeSpace ⌈Γ.epsilon⁻¹⌉₊ ∧
      2 * C₁ ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      1000 * C₂ ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ := by
  have hε := epsilon_mem_C11GT6 Γ
  have hc := one_le_fineC_C11CL3.{u} Γ.epsilon
  have hs := Real.sqrt_nonneg (p6FineC_C11GT6.{u} Γ.epsilon)
  have hm : p6FineC_C11GT6.{u} Γ.epsilon ≤ max (p6FineC_C11GT6.{u} Γ.epsilon) 9 := le_max_left _ _
  have h5 := two_mul_fineCX_le_C1P6_C11CL3.{u} Γ
  have h6 := thousand_mul_fineCX_le_C2P6_C11CL3.{u} Γ
  have hle := p6FineEta_le_C11GT6 Γ.epsilon
  refine ⟨p6FineEta_pos_C11GT6 hε.1, by linarith, by linarith [hε.2],
    fineEta_le_bJS_C11CL3 Γ.epsilon, ?_, ?_⟩
  · linarith
  · linarith

/-- **CHAIN 表第 14 行**：精度链。`0 < η₁ < 1/11`；`η₁ < ηfine = ηN`。消费者 = RERUN8B Event 的 V 形
`hη : 0 < η₁ ∧ η₁ < 1/11`（`false_of_jointPrefix_eventRerun8_P6R8B`）；CXCC `hηle`。 -/
theorem chain14_etaChain_C11CW (Γ : ClosedBirthConstants) :
    0 < p6FineEta_C11GT6 Γ.epsilon ∧ p6FineEta_C11GT6 Γ.epsilon < 1 / 11 ∧
      p6FineEta_C11GT6 Γ.epsilon < p6EtaN_C11CW Γ :=
  ⟨(fineEta_mem_C11CL2 Γ).1, (fineEta_mem_C11CL2 Γ).2,
    fineEta_lt_neckTol_C11CL3 (epsilon_mem_C11GT6 Γ).1⟩

/-- **CHAIN 表第 15 行**：RERUN8B 的坏点下界 `Cco η₁ ≤ C1₁`、`Cco η₁ ≤ C2₁`、
`(Cco η₁).toNNReal ≤ Ctime₁`。两个实例：固定实例 `(Cco η₁, Cco η₁, (Cco η₁).toNNReal)`（`le_rfl`）；
CEIL2 W1 预埋实例 `(c, c, c.toNNReal)`（`Cco η₁ ≤ c`）。消费者 = RERUN8B
`false_of_jointPrefix_eventRerun8_P6R8B`（内部 `…jointPrefixN/V…` 的 `hC1 hC2 hCt`）；
Final8 同形。 -/
theorem chain15_badLower_C11CW (Γ : ClosedBirthConstants) :
    (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6
        Γ.epsilon) ∧
      (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal ≤
        (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal) ∧
    (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ p6FineC_C11GT6.{u} Γ.epsilon ∧
      (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal ≤
        (p6FineC_C11GT6.{u} Γ.epsilon).toNNReal) :=
  ⟨⟨le_rfl, le_rfl⟩, coarseFine_le_fineC_C11CL3 Γ.epsilon,
    Real.toNNReal_le_toNNReal (coarseFine_le_fineC_C11CL3 Γ.epsilon)⟩

/-- **CHAIN 表第 16 行**：坏点谓词不含 `Ctime₁`。`¬∃ W (spatial, η₁ C1₁ C2₁) ⇒
¬HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁`，对任意 `Ctime₁`。消费者 = HbdLate
`htrans`（`hbd_stage_late_P6HB2` 的 `¬∃ W …` 结论）→ `hrerunE8 / hlocH` 的
`¬ HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ k) (y k)`。 -/
theorem chain16_noCtimeCoupling_C11CW (H : ObservedHistory.{u}) {η C1 C2 : ℝ} (Ctime : ℝ≥0)
    {v : Icc (0 : ℝ) H.horizon} {z : (H.stageAt v).Carrier}
    (hbad : ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) η C1 C2 z,
      W.capTubeHasNeckChart η) :
    ¬ H.HasSpatialCanonicalTimeControl η C1 C2 Ctime v z :=
  fun h => hbad h.1

/-- **CHAIN 表第 18 行**：阈值解耦的唯一算术内容。`8 · R ≤ x ⇒ 4 · R ≤ x`（`0 ≤ R`）：RERUN8B 把 Good 区
阈值写成 `8 · R`，hgapJ 冻结文本用 `4 · R`，前者的区域包含于后者。此行与本链常数无关
（CHAIN 表 "✓ 与本链常数无关"）；其余内容归 RERUN8B Event 文件头。消费者 = RERUN8B
`false_of_jointPrefix_eventRerun8_P6R8B` 的 `hgapJ8` 与 `hgapJ` 的阈值比较。 -/
theorem chain18_threshold_C11CW {R x : ℝ} (hR : 0 ≤ R) (h : 8 * R ≤ x) : 4 * R ≤ x := by
  linarith

/-- **CHAIN 表第 19 行**：ceiling 的 X1 / X2 fine 项。`2 · C1f ≤ X1std Γ`、`1000 · C2f ≤ X2std Γ`
（`2 · (max c 9 + √c) ≤ X1`、`1200000 · c ≤ X2`）。消费者 = 第 5 行（经 `X_le_C1P6 / X_le_C2P6`）；
GT6 `p6X1std / p6X2std` 的 B 项（D-15″ 后 B 项的常数为 `p6BadC_C11G2 Γ ≥ c`，经 GT6 单调引理支配）。 -/
theorem chain19_ceilingTerms_C11CW (Γ : ClosedBirthConstants) :
    2 * p6C1f_C11CW.{u} Γ ≤ p6X1std_C11GT6.{u} Γ ∧
      1000 * p6C2f_C11CW.{u} Γ ≤ p6X2std_C11GT6.{u} Γ := by
  refine ⟨two_mul_fine_le_p6X1std_C11G7.{u} Γ, ?_⟩
  change 1000 * (1200 * p6FineC_C11GT6.{u} Γ.epsilon) ≤ p6X2std_C11GT6.{u} Γ
  have := mul1200k_fine_le_p6X2std_C11G7.{u} Γ
  linarith

/-- **CHAIN 表第 20 行**：W1 预埋。`Ccap η₁ ≤ c ≤ C1, C2`（故 `Ccap η₁ ≤ C1₁ = C2₁ := c` 与
`Ccap η₁ ≤ C1, C2`），以及 collar 常数 `Ccol ε ≤ C1, C2`。消费者 = final 侧 `hcwpLF`（CEIL2 W1，若
cap-window 步在 `η₁` 处非空真）；HCENP `hcenE_of_noShortcut_P6HE` 的 `hCs1 / hCs2`。 -/
theorem chain20_capFine_C11CW (Γ : ClosedBirthConstants) :
    p6CapCs_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ p6FineC_C11GT6.{u} Γ.epsilon ∧
      p6FineC_C11GT6.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      p6FineC_C11GT6.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ ∧
      p6CapCs_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      p6CapCs_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ ∧
      capCollarCs_P6HE.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      capCollarCs_P6HE.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  ⟨capFine_le_fineC_C11CL3 Γ.epsilon, fineC_le_C1P6_C11CL3 Γ, fineC_le_C2P6_C11CL3 Γ,
    capFine_le_C1P6_C11CL3 Γ, capFine_le_C2P6_C11CL3 Γ, capCollar_le_C1P6_C11CL3 Γ,
    capCollar_le_C2P6_C11CL3 Γ⟩


/-- **CHAIN 表第 17 行（类型鸽笼；BLOCKED 的只剩 `htube`）**：`comp(p)` 与 cut tubes 不交。
第 17 行本身不含常数——CXCC 的 `∃ᶠ n, ∀ W 带 chart → positive ∨ round` 与 SCFIN 的 whole-component
transfer 合并（取子列）已由 CX-HTRANS G1 `htrans_event_CXHT` 写出，其数值前提正是本文件第 5、9、10、11、
13 行；该证明唯一剩余输入是 `htube`。缺的事实 = `htube`（`comp(p)` 与 `E.transition.trace.tubes` 的像
不交；`hbd_stage_late_P6HB2` 的 `htrans` 槽无此 binder）；repair target = STAB3 / OPEN-C cut-tube 数据
（owner = 切口几何车道），或在 `htrans` 槽加此 binder（须 lead 裁定，接口冻结）。 -/
def CutTubeDisjoint_C11CW {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (p : P.Carrier) : Prop :=
  ∀ i, Disjoint (connectedComponent p) (Set.range (E.transition.trace.tubes.tube i))

/-! ## 3. consumers（G2）：改善定理与 whole-component 传递在这组常数处实例化 -/

section Consumers

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M] {g : SmoothRiemannianMetric I3 M} {x : M}

/-- **consumer（STAB4 G1′ neck 改善）**：坏点精度 `(η₁, C1₁, C2₁)`-Good ⇒ margin 层
`(ηN, C1f, C2f, m)`-FineMarginGood，或存在 cap / whole-component 型 `(η₁, C1₁, C2₁)`-witness。
`hη / hC1 / hC2 / hm` 由第 4、8 行付。 -/
theorem fineGood_neck_C11CW (Γ : ClosedBirthConstants) {C₁ C₂ : ℝ}
    (hC₁ : C₁ ≤ p6FineC_C11GT6.{u} Γ.epsilon) (hC₂ : C₂ ≤ p6FineC_C11GT6.{u} Γ.epsilon)
    (hgood : ∃ W : SpatialCanonicalWitness g (p6FineEta_C11GT6 Γ.epsilon) C₁ C₂ x,
      W.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon)) :
    (∃ W' : SpatialCanonicalWitness g (p6EtaN_C11CW Γ) (p6C1f_C11CW.{u} Γ) (p6C2f_C11CW.{u} Γ) x,
        W'.capTubeHasNeckChart (p6EtaN_C11CW Γ) ∧ W'.HasMargins (p6M_C11CW.{u} Γ)) ∨
      ∃ W : SpatialCanonicalWitness g (p6FineEta_C11GT6 Γ.epsilon) C₁ C₂ x,
        W.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon) ∧
          ((∃ c d, W.alternative = .cap c d) ∨ W.domain.carrier = connectedComponent x) := by
  have h8 := chain08_neck_C11CW.{u} Γ hC₁ hC₂
  exact fineGood_implies_fineMarginGood_P6ST4 h8.1 (chain09_capPrecision_C11CW Γ).2 h8.2.1
    h8.2.2.1 h8.2.2.2 hgood

/-- **consumer（CXCC cap 创造 margins）**：cap 型 `(η₁, C1₁, C2₁)`-witness ⇒ margin 层
`(ηN, C1f, C2f, m)`-FineMarginGood（`fineMarginGood_of_cap_CXCC`；`hη hη' hC1 hC2 hm` 由第 9、10、11
行付）。 -/
theorem fineMarginGood_cap_C11CW (Γ : ClosedBirthConstants) {C₁ C₂ : ℝ} (h1 : 1 ≤ C₁)
    (h2 : 1 ≤ C₂) (hC₁ : C₁ ≤ p6FineC_C11GT6.{u} Γ.epsilon)
    (hC₂ : C₂ ≤ p6FineC_C11GT6.{u} Γ.epsilon)
    (W : SpatialCanonicalWitness g (p6FineEta_C11GT6 Γ.epsilon) C₁ C₂ x)
    (hW : W.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon))
    (hcap : ∃ c d, W.alternative = .cap c d) :
    ∃ W' : SpatialCanonicalWitness g (p6EtaN_C11CW Γ) (p6C1f_C11CW.{u} Γ) (p6C2f_C11CW.{u} Γ) x,
      W'.capTubeHasNeckChart (p6EtaN_C11CW Γ) ∧ W'.HasMargins (p6M_C11CW.{u} Γ) := by
  have h10 := chain10_capAmplify_C11CW.{u} Γ hC₁ hC₂
  have h11 := chain11_margin_C11CW.{u} Γ h1 h2 hC₁ hC₂
  have h9 := chain09_capPrecision_C11CW Γ
  have h10' : max C₁ 9 + Real.sqrt C₂ ≤ p6C1f_C11CW.{u} Γ := h10.1
  exact fineMarginGood_of_cap_CXCC h9.1 h9.2 (le_trans (add_le_add (le_max_left C₁ 9) le_rfl) h10')
    h10.2 h11.1 W hW hcap

/-- **consumer（CXCC cap 创造 margins，原始形）**：`exists_hasMargins_of_cap_CXCC` 在 `η := η₁`、
`η' := ηN`、`m := p6M` 处——输出常数恰为 `(C1₁ + √C2₁, 1200 · C2₁)`，且 domain 包含原 domain。 -/
theorem hasMargins_cap_C11CW (Γ : ClosedBirthConstants) {C₁ C₂ : ℝ} (h1 : 1 ≤ C₁) (h2 : 1 ≤ C₂)
    (hC₁ : C₁ ≤ p6FineC_C11GT6.{u} Γ.epsilon) (hC₂ : C₂ ≤ p6FineC_C11GT6.{u} Γ.epsilon)
    (W : SpatialCanonicalWitness g (p6FineEta_C11GT6 Γ.epsilon) C₁ C₂ x)
    (hW : W.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon))
    (hcap : ∃ c d, W.alternative = .cap c d) :
    ∃ W' : SpatialCanonicalWitness g (p6EtaN_C11CW Γ) (C₁ + Real.sqrt C₂) (1200 * C₂) x,
      W'.capTubeHasNeckChart (p6EtaN_C11CW Γ) ∧ W'.HasMargins (p6M_C11CW.{u} Γ) ∧
        W.domain.carrier ⊆ W'.domain.carrier :=
  exists_hasMargins_of_cap_CXCC (chain09_capPrecision_C11CW Γ).1 (chain09_capPrecision_C11CW Γ).2
    W hW hcap (chain11_margin_C11CW.{u} Γ h1 h2 hC₁ hC₂).1

/-- **consumer（CXCC 改善定理孪生）**：`(η₁, C1₁, C2₁)`-Good ⇒ margin 层 FineMarginGood，或存在
whole-component 型 `(η₁, C1₁, C2₁)`-witness（cap 与 neck 都已创造 margins）。 -/
theorem fineGood_cxcc_C11CW (Γ : ClosedBirthConstants) {C₁ C₂ : ℝ} (h1 : 1 ≤ C₁) (h2 : 1 ≤ C₂)
    (hC₁ : C₁ ≤ p6FineC_C11GT6.{u} Γ.epsilon) (hC₂ : C₂ ≤ p6FineC_C11GT6.{u} Γ.epsilon)
    (hgood : ∃ W : SpatialCanonicalWitness g (p6FineEta_C11GT6 Γ.epsilon) C₁ C₂ x,
      W.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon)) :
    (∃ W' : SpatialCanonicalWitness g (p6EtaN_C11CW Γ) (p6C1f_C11CW.{u} Γ) (p6C2f_C11CW.{u} Γ) x,
        W'.capTubeHasNeckChart (p6EtaN_C11CW Γ) ∧ W'.HasMargins (p6M_C11CW.{u} Γ)) ∨
      ∃ W : SpatialCanonicalWitness g (p6FineEta_C11GT6 Γ.epsilon) C₁ C₂ x,
        W.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon) ∧
          W.domain.carrier = connectedComponent x := by
  have h10 := chain10_capAmplify_C11CW.{u} Γ hC₁ hC₂
  have h11 := chain11_margin_C11CW.{u} Γ h1 h2 hC₁ hC₂
  have h9 := chain09_capPrecision_C11CW Γ
  exact fineGood_implies_fineMarginGood_CXCC h9.1 h9.2 h10.1 h10.2 h11.2 h11.1 hgood

/-- **consumer（RERUN8B 固定实例，同上）**：固定坏点常数 `C1₁ = C2₁ = Cco η₁`（`1 ≤ Cco η₁ ≤ c`）处的
改善定理孪生。 -/
theorem fineGood_cxcc_fixed_C11CW (Γ : ClosedBirthConstants)
    (hgood : ∃ W : SpatialCanonicalWitness g (p6FineEta_C11GT6 Γ.epsilon)
      (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon))
      (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) x,
      W.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon)) :
    (∃ W' : SpatialCanonicalWitness g (p6EtaN_C11CW Γ) (p6C1f_C11CW.{u} Γ) (p6C2f_C11CW.{u} Γ) x,
        W'.capTubeHasNeckChart (p6EtaN_C11CW Γ) ∧ W'.HasMargins (p6M_C11CW.{u} Γ)) ∨
      ∃ W : SpatialCanonicalWitness g (p6FineEta_C11GT6 Γ.epsilon)
        (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon))
        (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) x,
        W.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon) ∧
          W.domain.carrier = connectedComponent x :=
  fineGood_cxcc_C11CW Γ (one_le_p6CoarseC_C11GT6 _) (one_le_p6CoarseC_C11GT6 _)
    (coarseFine_le_fineC_C11CL3 Γ.epsilon) (coarseFine_le_fineC_C11CL3 Γ.epsilon) hgood

end Consumers

section EventConsumers

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

/-- **consumer（CXCC event 层）**：footprint 合同 `Footprint_C11CW`（第 7 行，BLOCKED producer）+ 目标层
`¬witness (ε, C1P6, C2P6)` ⇒ frequently 在 `(v n, p)` 处每个 finer `(η₁, C1₁, C2₁)`-witness（带 chart）
都是 whole-component 型。`hle / hη / hC1 / hC2 / hm / hm' / h1 / h2` 由第 4、9、10、11、5 行付。 -/
theorem frequently_whole_C11CW (Γ : ClosedBirthConstants) {E : MetricCutCapEvent P Q a s}
    {p : P.Carrier} {q : Q.Carrier} (hfoot : Footprint_C11CW.{u} Γ E p q) {C₁ C₂ : ℝ}
    (h1 : 1 ≤ C₁) (h2 : 1 ≤ C₂) (hC₁ : C₁ ≤ p6FineC_C11GT6.{u} Γ.epsilon)
    (hC₂ : C₂ ≤ p6FineC_C11GT6.{u} Γ.epsilon)
    (hnot : ¬ ∃ W : SpatialCanonicalWitness E.outputMetric Γ.epsilon
      (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ) (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) q,
      W.capTubeHasNeckChart Γ.epsilon) :
    ∃ D : E.BufferedFootprintData_P6ST2 p q Γ.epsilon (p6C1f_C11CW.{u} Γ) (p6C2f_C11CW.{u} Γ)
      (p6M_C11CW.{u} Γ) (p6kk_C11CW Γ),
    ∃ᶠ n in atTop, ∀ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (D.v n))
      (p6FineEta_C11GT6 Γ.epsilon) C₁ C₂ p, W.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon) →
        W.domain.carrier = connectedComponent p := by
  obtain ⟨D⟩ := hfoot
  have h10 := chain10_capAmplify_C11CW.{u} Γ hC₁ hC₂
  have h11 := chain11_margin_C11CW.{u} Γ h1 h2 hC₁ hC₂
  have h9 := chain09_capPrecision_C11CW Γ
  have h5 := chain05_recover_C11CW.{u} Γ
  exact ⟨D, MetricCutCapEvent.frequently_whole_of_not_witness_CXCC (ηfine := p6EtaN_C11CW Γ) D
    (chain04_etaFine_C11CW Γ).1 h9.1 h10.1 h10.2 h11.2 h11.1 h5.1 h5.2 hnot⟩

/-- **consumer（STAB4 G1′ event 层 neck-free，逐点版）**：STAB2 逆否
`frequently_not_fineMargin_P6ST2` + `neck_free_of_not_fineMarginGood_P6ST4` ⇒ frequently 在
`(v n, p)` 处没有 neck 型 `(η₁, C1₁, C2₁)`-witness。
（`frequently_neck_free_P6ST4` 把 finer 层的 `C2` 固定为 footprint 的 `C2f`，与 `C2₁ = c` 不同层，
故用逐点引理组装；只用第 4、5、8 行。） -/
theorem frequently_neckFree_C11CW (Γ : ClosedBirthConstants) {E : MetricCutCapEvent P Q a s}
    {p : P.Carrier} {q : Q.Carrier} (hfoot : Footprint_C11CW.{u} Γ E p q) {C₁ C₂ : ℝ}
    (hC₁ : C₁ ≤ p6FineC_C11GT6.{u} Γ.epsilon) (hC₂ : C₂ ≤ p6FineC_C11GT6.{u} Γ.epsilon)
    (hnot : ¬ ∃ W : SpatialCanonicalWitness E.outputMetric Γ.epsilon
      (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ) (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) q,
      W.capTubeHasNeckChart Γ.epsilon) :
    ∃ D : E.BufferedFootprintData_P6ST2 p q Γ.epsilon (p6C1f_C11CW.{u} Γ) (p6C2f_C11CW.{u} Γ)
      (p6M_C11CW.{u} Γ) (p6kk_C11CW Γ),
    ∃ᶠ n in atTop, ∀ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (D.v n))
      (p6FineEta_C11GT6 Γ.epsilon) C₁ C₂ p, ¬ ∃ nn, W.alternative = .neck nn := by
  obtain ⟨D⟩ := hfoot
  have h8 := chain08_neck_C11CW.{u} Γ hC₁ hC₂
  have h4 := chain04_etaFine_C11CW Γ
  have h5 := chain05_recover_C11CW.{u} Γ
  exact ⟨D, (MetricCutCapEvent.frequently_not_fineMargin_P6ST2 (ηfine := p6EtaN_C11CW Γ) D h4.1
    h5.1 h5.2 hnot).mono fun n hn W => neck_free_of_not_fineMarginGood_P6ST4 h8.1 h4.2.2
    h8.2.1 h8.2.2.1 h8.2.2.2 hn W⟩

/-- **consumer（SCFIN round / STAB4 G3 positive 合并，htrans 的 whole-component 支）**：`RegularCrossing`
+ `CutTubeDisjoint_C11CW`（第 17 行 BLOCKED 的 `htube`）+ `v n ↑ s` + 目标层 `¬witness` ⇒ frequently
`(v n, p)` 无 positive ∨ round 型 `(η₁, C1₁, C2₁)`-witness。`hη0 hηlt hηhalf hsmall h1 h2` 由第 13 行付。 -/
theorem frequently_not_wholeComponent_C11CW (Γ : ClosedBirthConstants)
    (E : MetricCutCapEvent P Q a s) {p : P.Carrier} {q : Q.Carrier} (hcross : E.RegularCrossing p q)
    (htube : CutTubeDisjoint_C11CW.{u} E p) {v : ℕ → ℝ} (hv : ∀ n, v n ∈ Ioo a s)
    (hvt : Tendsto v atTop (𝓝 s)) (hQ : 0 < metricScalarAt E.outputMetric q) {C₁ C₂ : ℝ}
    (h1 : 1 ≤ C₁) (h2 : 1 ≤ C₂) (hC₁ : C₁ ≤ p6FineC_C11GT6.{u} Γ.epsilon)
    (hC₂ : C₂ ≤ p6FineC_C11GT6.{u} Γ.epsilon)
    (hnot : ¬ ∃ W : SpatialCanonicalWitness E.outputMetric Γ.epsilon
      (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ) (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) q,
      W.capTubeHasNeckChart Γ.epsilon) :
    ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (v n))
      (p6FineEta_C11GT6 Γ.epsilon) C₁ C₂ p,
      (∃ wh d sc, W.alternative = .positive wh d sc) ∨ ∃ wh R, W.alternative = .round wh R := by
  have h13 := chain13_round_C11CW.{u} Γ hC₁ hC₂
  exact E.frequently_not_wholeComponent_P6SF hcross htube hv hvt hQ h1 h2 h13.1 h13.2.1
    h13.2.2.1 h13.2.2.2.1 h13.2.2.2.2.1 h13.2.2.2.2.2 hnot

/-- **consumer（STAB4 G3 positive transfer）**：eventually positive 型 `(η₁, C1₁, C2₁)`-witness ⇒ `q` 处
positive 型 `(ε, C1P6, C2P6)`-witness（domain = `comp(q)`）。`hC1 hC2 hη0 hη1 h1 h2` 由第 12 行付。 -/
theorem wholeComponent_positive_C11CW (Γ : ClosedBirthConstants)
    (E : MetricCutCapEvent P Q a s) {p : P.Carrier} {q : Q.Carrier} (hcross : E.RegularCrossing p q)
    (htube : CutTubeDisjoint_C11CW.{u} E p) {v : ℕ → ℝ} (hv : ∀ n, v n ∈ Ioo a s)
    (hvt : Tendsto v atTop (𝓝 s)) (hQ : 0 < metricScalarAt E.outputMetric q) {C₁ C₂ : ℝ}
    (h1 : 1 ≤ C₁) (h2 : 1 ≤ C₂) (hC₁ : C₁ ≤ p6FineC_C11GT6.{u} Γ.epsilon)
    (hC₂ : C₂ ≤ p6FineC_C11GT6.{u} Γ.epsilon)
    (hfine : ∀ᶠ n in atTop, ∃ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (v n))
      (p6FineEta_C11GT6 Γ.epsilon) C₁ C₂ p, ∃ wh d sc, W.alternative = .positive wh d sc) :
    ∃ W : SpatialCanonicalWitness E.outputMetric Γ.epsilon
      (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ) (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) q,
      W.capTubeHasNeckChart Γ.epsilon ∧ W.domain.carrier = connectedComponent q ∧
        ∃ wh d sc, W.alternative = .positive wh d sc := by
  have h12 := chain12_positive_C11CW.{u} Γ h1 h2 hC₁ hC₂
  exact E.wholeComponent_positive_transfer_P6ST4 hcross htube hv hvt hQ h1 h2 hfine h12.2.2.1
    h12.2.2.2.1 h12.2.2.2.2.1 h12.2.2.2.2.2

end EventConsumers

/-- **consumer（RERUN8，W1 预埋实例）**：`hrerunE8_P6R8` 的坏点下界 `hC1 / hC2 / hCt` 在
`(C1₁, C2₁, Ctime₁) := (c, c, c.toNNReal)` 处由第 15 行付；对照 CL2 同名 example（固定实例）。 -/
example (Γ : ClosedBirthConstants) {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g}
    (hεW : Γ.epsilon ≤ Classical.choose ObservedHistory.ancientWitness_decoupled_P6P.{u})
    (hεX : Γ.epsilon ≤ crossingWindowNeckAccuracy.{u})
    (hεN : Γ.epsilon ≤ crossingNeckAccuracy.{u}) (hεcone : Γ.epsilon ≤ coneAccuracy)
    {C1 C2 : ℝ} {Ctime : ℝ≥0} (hC2' : 0 ≤ C2) : True := by
  have _h := ObservedHistory.hrerunE8_P6R8 (F := F) (C1 := C1) (Ctime := Ctime)
    (C1₁ := p6FineC_C11GT6.{u} Γ.epsilon) (C2₁ := p6FineC_C11GT6.{u} Γ.epsilon)
    (Ctime₁ := (p6FineC_C11GT6.{u} Γ.epsilon).toNNReal)
    ⟨(chain14_etaChain_C11CW Γ).1, (chain14_etaChain_C11CW Γ).2.1⟩ Γ.epsilon_pos hεW hεX hεN
    hεcone (chain15_badLower_C11CW Γ).2.1 (chain15_badLower_C11CW Γ).2.1
    (chain15_badLower_C11CW Γ).2.2 hC2'
  trivial

end GC.LongTime.Ch11
