import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6OuterTwoLevelC11G7B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingDomC11CL2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BadInstC11G7B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotFinalCwwP6HN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnRCH2

set_option autoImplicit false

/-!
[CEILHN2：自 `P6CeilHnDefsCHN.lean` 机械克隆]
# CEIL-HN G1：HN 扩展 ceiling 的 def 与数值引理包（O-CH11-CEILHN，后缀 `_CHN`）

R18 / R36（lead）：HNOT-A3 判定 O1 支配引理不可证（`Cs(ε)`、`Ctime₀(ε)` 是 `Classical.choose` 输出，
与 `p6X1std / p6X2std / p6Ctime / p6CoarseC` 无可比较不等式）。本文件做 ceiling 的 **max 扩展孪生**
（D-15″ 同款：新 def，不改冻结 def，不新增 binder）：

* `csHN ε`、`ctHN ε`：G9 `hnotK_final_cww_P6HN` 的两个 `∃` 输出（`ε ∈ (0, 1/11)` 取 `choose`，否则 `1`）；
* `p6CoarseCHN η := max (p6CoarseC η) (max (csHN η) (ctHN η))`（J8 / JF8 的 `Cf′`，取 `η := ηf`）；
* `p6BadCHN Γ := max (p6BadC Γ) (p6CoarseCHN (p6FineEta Γ.ε))`（坏点常数 `cb′`）；
* `p6X1HN Γ := max (p6X1std Γ) (max (2 (max cb′ 9 + √cb′)) (csHN Γ.ε))`；
  `p6X2HN Γ := max (p6X2std Γ) (max (1200000 cb′) (csHN Γ.ε))`；
* `p6CtimeHN Γ := max (p6Ctime Γ) (max (C1P6 X1HN Γ)ᵗᵒᴺᴺ (ctHN Γ.ε))`。

**单调桥**：凡只用 `· ≤ ceiling` 的原引理，经 `C1P6std_le_C1P6HN` / `C2P6std_le_C2P6HN` /
`p6Ctime_le_p6CtimeHN` 直接转移（`.trans`），不必重证；本文件只对 `p6BadC`（坏点常数增大）重述
`hdomL / hdomF / htransMBad / hrestP_bad_numerics` 这类依赖 `cb` 的件。
-/

noncomputable section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-! ## 1. `csHN`、`ctHN` -/

/-- G9 的 `Ctime₀`（`ε ∈ (0, 1/11)` 时取 `hnotK_final_cww_P6HN` 的 `∃ Ctime₀`，否则 `1`）。 -/
def ctHN0_CH2 (ε : ℝ) : ℝ≥0 :=
  if h : 0 < ε ∧ ε < 1 / 11 then
    Classical.choose (RetainedCoreHistory.hnotK_final_cww_P6HN.{u} h.1 h.2)
  else 1

/-- G9 的 `Cs`。 -/
def csHN0_CH2 (ε : ℝ) : ℝ :=
  if h : 0 < ε ∧ ε < 1 / 11 then
    Classical.choose
      (Classical.choose_spec (RetainedCoreHistory.hnotK_final_cww_P6HN.{u} h.1 h.2))
  else 1

theorem one_le_csHN0_CH2 (ε : ℝ) : 1 ≤ csHN0_CH2.{u} ε := by
  by_cases h : 0 < ε ∧ ε < 1 / 11
  · unfold csHN0_CH2
    rw [dite_eq_left h]
    exact (Classical.choose_spec
      (Classical.choose_spec (RetainedCoreHistory.hnotK_final_cww_P6HN.{u} h.1 h.2))).2.1
  · unfold csHN0_CH2
    rw [dite_eq_right h]

/-- CEILHN2：`ctHN` = G9 的 choose 与 HNOTRES 常数 `ctHNR` 的 max。 -/
def ctHN_CH2 (ε : ℝ) : ℝ≥0 := max (ctHN0_CH2.{u} ε) (ctHNR_CH2.{u} ε)

/-- CEILHN2：`csHN` = G9 的 choose 与 HNOTRES 常数 `csHNR` 的 max。 -/
def csHN_CH2 (ε : ℝ) : ℝ := max (csHN0_CH2.{u} ε) (csHNR_CH2.{u} ε)

theorem one_le_csHN_CH2 (ε : ℝ) : 1 ≤ csHN_CH2.{u} ε :=
  (one_le_csHN0_CH2.{u} ε).trans (le_max_left _ _)

theorem csHN0_le_csHN_CH2 (ε : ℝ) : csHN0_CH2.{u} ε ≤ csHN_CH2.{u} ε := le_max_left _ _

theorem ctHN0_le_ctHN_CH2 (ε : ℝ) : ctHN0_CH2.{u} ε ≤ ctHN_CH2.{u} ε := le_max_left _ _

theorem csHNR_le_csHN_CH2 (ε : ℝ) : csHNR_CH2.{u} ε ≤ csHN_CH2.{u} ε :=
  le_max_right _ _

theorem ctHNR_le_ctHN_CH2 (ε : ℝ) : ctHNR_CH2.{u} ε ≤ ctHN_CH2.{u} ε :=
  le_max_right _ _

/-! ## 2. ceiling 的 HN 扩展 -/

/-- J8 / JF8 的坏点 hsel 常数 `Cf′ η := max (p6CoarseC η) (max (csHN η) (ctHN η))`。 -/
def p6CoarseCH2_CH2 (η : ℝ) : ℝ :=
  max (p6CoarseC_C11GT6.{u} η) (max (csHN_CH2.{u} η) ((ctHN_CH2.{u} η : ℝ≥0) : ℝ))

/-- 坏点常数 `cb′(Γ) := max (p6BadC Γ) (Cf′ ηf)`。 -/
def p6BadCH2_CH2 (Γ : ClosedBirthConstants) : ℝ :=
  max (p6BadC_C11G2.{u} Γ) (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon))

def p6X1HN_CH2 (Γ : ClosedBirthConstants) : ℝ :=
  max (p6X1std_C11GT6.{u} Γ)
    (max (2 * (max (p6BadCH2_CH2.{u} Γ) 9 + Real.sqrt (p6BadCH2_CH2.{u} Γ)))
      (csHN_CH2.{u} Γ.epsilon))

def p6X2HN_CH2 (Γ : ClosedBirthConstants) : ℝ :=
  max (p6X2std_C11GT6.{u} Γ)
    (max (1200000 * p6BadCH2_CH2.{u} Γ) (csHN_CH2.{u} Γ.epsilon))

def p6CtimeHN_CH2 (Γ : ClosedBirthConstants) : ℝ≥0 :=
  max (p6Ctime_C11G7B.{u} Γ)
    (max (C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ).toNNReal (ctHN_CH2.{u} Γ.epsilon))

/-! ## 3. 单调桥（std ≤ HN） -/

theorem p6X1std_le_p6X1HN_CH2 (Γ : ClosedBirthConstants) :
    p6X1std_C11GT6.{u} Γ ≤ p6X1HN_CH2.{u} Γ := le_max_left _ _

theorem p6X2std_le_p6X2HN_CH2 (Γ : ClosedBirthConstants) :
    p6X2std_C11GT6.{u} Γ ≤ p6X2HN_CH2.{u} Γ := le_max_left _ _

theorem C1P6std_le_C1P6HN_CH2 (Γ : ClosedBirthConstants) :
    C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ :=
  max_le_max le_rfl (p6X1std_le_p6X1HN_CH2 Γ)

theorem C2P6std_le_C2P6HN_CH2 (Γ : ClosedBirthConstants) :
    C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ :=
  max_le_max le_rfl (p6X2std_le_p6X2HN_CH2 Γ)

theorem p6Ctime_le_p6CtimeHN_CH2 (Γ : ClosedBirthConstants) :
    p6Ctime_C11G7B.{u} Γ ≤ p6CtimeHN_CH2.{u} Γ := le_max_left _ _

theorem Ctime_le_p6CtimeHN_CH2 (Γ : ClosedBirthConstants) :
    Γ.Ctime ≤ p6CtimeHN_CH2.{u} Γ :=
  (Ctime_le_p6Ctime_C11G7B.{u} Γ).trans (p6Ctime_le_p6CtimeHN_CH2 Γ)

theorem C1ceil_le_C1P6HN_CH2 (Γ : ClosedBirthConstants) :
    C1ceil_C11SC.{u} Γ ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ := le_max_left _ _

theorem C2ceil_le_C2P6HN_CH2 (Γ : ClosedBirthConstants) :
    C2ceil_C11SC.{u} Γ ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ := le_max_left _ _

/-- 通用桥：`x ≤ C1P6 std Γ ⇒ x ≤ C1P6 HN Γ`。 -/
theorem le_C1P6HN_of_std_CH2 {Γ : ClosedBirthConstants} {x : ℝ}
    (h : x ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ) :
    x ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ := h.trans (C1P6std_le_C1P6HN_CH2 Γ)

theorem le_C2P6HN_of_std_CH2 {Γ : ClosedBirthConstants} {x : ℝ}
    (h : x ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) :
    x ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ := h.trans (C2P6std_le_C2P6HN_CH2 Γ)

theorem le_p6CtimeHN_of_std_CH2 {Γ : ClosedBirthConstants} {x : ℝ≥0}
    (h : x ≤ p6Ctime_C11G7B.{u} Γ) : x ≤ p6CtimeHN_CH2.{u} Γ :=
  h.trans (p6Ctime_le_p6CtimeHN_CH2 Γ)

/-! ## 4. HN 分量 -/

theorem csHN_le_C1P6HN_CH2 (Γ : ClosedBirthConstants) :
    csHN_CH2.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ :=
  ((le_max_right _ _).trans (le_max_right _ _) : _ ≤ p6X1HN_CH2.{u} Γ).trans
    (X_le_C1P6_C11GT6 p6X1HN_CH2.{u} Γ)

theorem csHN_le_C2P6HN_CH2 (Γ : ClosedBirthConstants) :
    csHN_CH2.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ :=
  ((le_max_right _ _).trans (le_max_right _ _) : _ ≤ p6X2HN_CH2.{u} Γ).trans
    (X_le_C2P6_C11GT6 p6X2HN_CH2.{u} Γ)

theorem ctHN_le_p6CtimeHN_CH2 (Γ : ClosedBirthConstants) :
    ctHN_CH2.{u} Γ.epsilon ≤ p6CtimeHN_CH2.{u} Γ :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem p6CoarseC_le_p6CoarseCH2_CH2 (η : ℝ) :
    p6CoarseC_C11GT6.{u} η ≤ p6CoarseCH2_CH2.{u} η := le_max_left _ _

theorem csHN_le_p6CoarseCH2_CH2 (η : ℝ) :
    csHN_CH2.{u} η ≤ p6CoarseCH2_CH2.{u} η :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem ctHN_le_p6CoarseCH2_CH2 (η : ℝ) :
    ((ctHN_CH2.{u} η : ℝ≥0) : ℝ) ≤ p6CoarseCH2_CH2.{u} η :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem one_le_p6CoarseCH2_CH2 (η : ℝ) : 1 ≤ p6CoarseCH2_CH2.{u} η :=
  (one_le_p6CoarseC_C11GT6.{u} η).trans (p6CoarseC_le_p6CoarseCH2_CH2 η)

/-- `ctHN η ≤ (Cf′ η)ᵗᵒᴺᴺ`（JF8 / J8 的 `Ctime₀ ≤ Ctime`，`Ctime := Cf′ᵗᵒᴺᴺ`）。 -/
theorem ctHN_le_toNNReal_p6CoarseCH2_CH2 (η : ℝ) :
    ctHN_CH2.{u} η ≤ (p6CoarseCH2_CH2.{u} η).toNNReal := by
  have h := Real.toNNReal_le_toNNReal (ctHN_le_p6CoarseCH2_CH2.{u} η)
  rwa [Real.toNNReal_coe] at h

theorem p6BadC_le_p6BadCH2_CH2 (Γ : ClosedBirthConstants) :
    p6BadC_C11G2.{u} Γ ≤ p6BadCH2_CH2.{u} Γ := le_max_left _ _

theorem coarseHNFine_le_p6BadCH2_CH2 (Γ : ClosedBirthConstants) :
    p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ p6BadCH2_CH2.{u} Γ := le_max_right _ _

theorem coarseFine_le_p6BadCH2_CH2 (Γ : ClosedBirthConstants) :
    p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ p6BadCH2_CH2.{u} Γ :=
  (p6CoarseC_le_p6CoarseCH2_CH2 _).trans (coarseHNFine_le_p6BadCH2_CH2 Γ)

theorem one_le_p6BadCH2_CH2 (Γ : ClosedBirthConstants) : 1 ≤ p6BadCH2_CH2.{u} Γ :=
  (one_le_p6BadC_C11G7B.{u} Γ).trans (p6BadC_le_p6BadCH2_CH2 Γ)

theorem C1ceil_le_p6BadCH2_CH2 (Γ : ClosedBirthConstants) :
    C1ceil_C11SC.{u} Γ ≤ p6BadCH2_CH2.{u} Γ :=
  (C1ceil_le_p6BadC_C11G2.{u} Γ).trans (p6BadC_le_p6BadCH2_CH2 Γ)

theorem C2ceil_le_p6BadCH2_CH2 (Γ : ClosedBirthConstants) :
    C2ceil_C11SC.{u} Γ ≤ p6BadCH2_CH2.{u} Γ :=
  (C2ceil_le_p6BadC_C11G2.{u} Γ).trans (p6BadC_le_p6BadCH2_CH2 Γ)

/-- D-15″ 结构项（C1 侧，HN）。 -/
theorem two_mul_badHN_le_p6X1HN_CH2 (Γ : ClosedBirthConstants) :
    2 * (max (p6BadCH2_CH2.{u} Γ) 9 + Real.sqrt (p6BadCH2_CH2.{u} Γ)) ≤ p6X1HN_CH2.{u} Γ :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem mul1200k_badHN_le_p6X2HN_CH2 (Γ : ClosedBirthConstants) :
    1200000 * p6BadCH2_CH2.{u} Γ ≤ p6X2HN_CH2.{u} Γ :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem p6BadCH2_le_C1P6HN_CH2 (Γ : ClosedBirthConstants) :
    p6BadCH2_CH2.{u} Γ ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ := by
  have h := (two_mul_badHN_le_p6X1HN_CH2.{u} Γ).trans (X_le_C1P6_C11GT6 p6X1HN_CH2.{u} Γ)
  have hs := Real.sqrt_nonneg (p6BadCH2_CH2.{u} Γ)
  have hm : p6BadCH2_CH2.{u} Γ ≤ max (p6BadCH2_CH2.{u} Γ) 9 := le_max_left _ _
  have h9 : (9 : ℝ) ≤ max (p6BadCH2_CH2.{u} Γ) 9 := le_max_right _ _
  linarith

theorem p6BadCH2_le_C2P6HN_CH2 (Γ : ClosedBirthConstants) :
    p6BadCH2_CH2.{u} Γ ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ := by
  have h := (mul1200k_badHN_le_p6X2HN_CH2.{u} Γ).trans (X_le_C2P6_C11GT6 p6X2HN_CH2.{u} Γ)
  have h1 := one_le_p6BadCH2_CH2.{u} Γ
  linarith

theorem toNNReal_le_p6CtimeHN_CH2 (Γ : ClosedBirthConstants) {x : ℝ}
    (hx : x ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ) : x.toNNReal ≤ p6CtimeHN_CH2.{u} Γ :=
  (Real.toNNReal_le_toNNReal hx).trans
    ((le_max_left _ _).trans (le_max_right _ _))

theorem badTimeHN_le_p6CtimeHN_CH2 (Γ : ClosedBirthConstants) :
    (p6BadCH2_CH2.{u} Γ).toNNReal ≤ p6CtimeHN_CH2.{u} Γ :=
  toNNReal_le_p6CtimeHN_CH2 Γ (p6BadCH2_le_C1P6HN_CH2 Γ)

/-- coarse joint 的时间门槛（std `p6CoarseC ε`）。 -/
theorem coarseTime_le_p6CtimeHN_CH2 (Γ : ClosedBirthConstants) :
    (p6CoarseC_C11GT6.{u} Γ.epsilon).toNNReal ≤ p6CtimeHN_CH2.{u} Γ :=
  le_p6CtimeHN_of_std_CH2 (coarseTime_le_p6Ctime_C11G7B.{u} Γ)

theorem coarse_le_C1P6HN_CH2 (Γ : ClosedBirthConstants) :
    p6CoarseC_C11GT6.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ :=
  le_C1P6HN_of_std_CH2 (coarse_le_C1P6std_C11GT6.{u} Γ)

theorem coarse_le_C2P6HN_CH2 (Γ : ClosedBirthConstants) :
    p6CoarseC_C11GT6.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ :=
  le_C2P6HN_of_std_CH2 (coarse_le_C2P6std_C11GT6.{u} Γ)

theorem p6CtimeHN_bounds_CH2 (Γ : ClosedBirthConstants) :
    Γ.Ctime ≤ p6CtimeHN_CH2.{u} Γ ∧
      (p6CoarseC_C11GT6.{u} Γ.epsilon).toNNReal ≤ p6CtimeHN_CH2.{u} Γ :=
  ⟨Ctime_le_p6CtimeHN_CH2 Γ, coarseTime_le_p6CtimeHN_CH2 Γ⟩

/-- 保留的 fine rerun time 常数（`Cf′`，HN）。 -/
theorem coarseHNFineTime_le_p6CtimeHN_CH2 (Γ : ClosedBirthConstants) :
    (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal ≤ p6CtimeHN_CH2.{u} Γ :=
  toNNReal_le_p6CtimeHN_CH2 Γ
    ((coarseHNFine_le_p6BadCH2_CH2 Γ).trans (p6BadCH2_le_C1P6HN_CH2 Γ))

theorem coarseFineTime_le_p6CtimeHN_CH2 (Γ : ClosedBirthConstants) :
    (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal ≤ p6CtimeHN_CH2.{u} Γ :=
  toNNReal_le_p6CtimeHN_CH2 Γ
    ((coarseFine_le_p6BadCH2_CH2 Γ).trans (p6BadCH2_le_C1P6HN_CH2 Γ))

/-- 三分量 `hdomF`（HN，`Cf′` 版）。 -/
theorem hdomF_twoLevel_CH2 (Γ : ClosedBirthConstants) :
    p6BadCH2_CH2.{u} Γ ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ ∧
      p6BadCH2_CH2.{u} Γ ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ ∧
      (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal ≤ p6CtimeHN_CH2.{u} Γ :=
  ⟨p6BadCH2_le_C1P6HN_CH2 Γ, p6BadCH2_le_C2P6HN_CH2 Γ, coarseHNFineTime_le_p6CtimeHN_CH2 Γ⟩

theorem hdomF_twoLevel_of_le_CH2 (Γ : ClosedBirthConstants) {Ctime Ctime₁ : ℝ≥0}
    (hCt : p6CtimeHN_CH2.{u} Γ ≤ Ctime) (hCt₁ : Ctime₁ ≤ (p6BadCH2_CH2.{u} Γ).toNNReal) :
    p6BadCH2_CH2.{u} Γ ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ ∧
      p6BadCH2_CH2.{u} Γ ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ ∧ Ctime₁ ≤ Ctime :=
  ⟨p6BadCH2_le_C1P6HN_CH2 Γ, p6BadCH2_le_C2P6HN_CH2 Γ,
    hCt₁.trans ((badTimeHN_le_p6CtimeHN_CH2 Γ).trans hCt)⟩

/-- `hdomL` 在 `cb′(Γ)` 处。 -/
theorem hdomL_badHN_CH2 (Γ : ClosedBirthConstants) :
    2 * (max (p6BadCH2_CH2.{u} Γ) 9 + Real.sqrt (p6BadCH2_CH2.{u} Γ)) ≤
        C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ ∧
      1200000 * p6BadCH2_CH2.{u} Γ ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ :=
  ⟨(two_mul_badHN_le_p6X1HN_CH2.{u} Γ).trans (X_le_C1P6_C11GT6 p6X1HN_CH2.{u} Γ),
    (mul1200k_badHN_le_p6X2HN_CH2.{u} Γ).trans (X_le_C2P6_C11GT6 p6X2HN_CH2.{u} Γ)⟩

/-- `htransMBad` 的 HN 版（`c := cb′`）。 -/
def htransMBadHN_CH2 (Γ : ClosedBirthConstants) : ℝ :=
  min (1 / 20) (1 / (10 * p6BadCH2_CH2.{u} Γ * Real.sqrt (p6BadCH2_CH2.{u} Γ)))

theorem htransMBadHN_pos_CH2 (Γ : ClosedBirthConstants) : 0 < htransMBadHN_CH2.{u} Γ := by
  have h1 := one_le_p6BadCH2_CH2.{u} Γ
  have hs : 0 < Real.sqrt (p6BadCH2_CH2.{u} Γ) := Real.sqrt_pos.mpr (by linarith)
  have hc : 0 < 10 * p6BadCH2_CH2.{u} Γ * Real.sqrt (p6BadCH2_CH2.{u} Γ) := by positivity
  exact lt_min (by norm_num) (by positivity)

/-- `hrestP` 的数值前提在 `cb′(Γ)` 处（`C1 / C2 / Ctime` 为 HN ceiling 的 lower bound 形）。 -/
theorem hrestP_bad_numerics_CH2 (Γ : ClosedBirthConstants) {C1 C2 : ℝ} {Ctime : ℝ≥0}
    (h1 : C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ ≤ C1)
    (h2 : C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ ≤ C2)
    (ht : p6CtimeHN_CH2.{u} Γ ≤ Ctime) :
    p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ p6BadCH2_CH2.{u} Γ ∧
      2 * (max (p6BadCH2_CH2.{u} Γ) 9 + Real.sqrt (p6BadCH2_CH2.{u} Γ)) ≤ C1 ∧
      1200000 * p6BadCH2_CH2.{u} Γ ≤ C2 ∧
      (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal ≤ Ctime :=
  ⟨coarseHNFine_le_p6BadCH2_CH2 Γ, (hdomL_badHN_CH2.{u} Γ).1.trans h1,
    (hdomL_badHN_CH2.{u} Γ).2.trans h2, (coarseHNFineTime_le_p6CtimeHN_CH2.{u} Γ).trans ht⟩

/-! ## 5. 其余 `· ≤ ceiling` 的桥（capCollar / capCs / hcapW witness） -/

theorem capCollar_le_C1P6HN_CH2 (Γ : ClosedBirthConstants) :
    capCollarCs_P6HE.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ :=
  le_C1P6HN_of_std_CH2 (capCollar_le_C1P6_C11CL3.{u} Γ)

theorem capCollar_le_C2P6HN_CH2 (Γ : ClosedBirthConstants) :
    capCollarCs_P6HE.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ :=
  le_C2P6HN_of_std_CH2 (capCollar_le_C2P6_C11CL3.{u} Γ)

theorem capCs_le_C1P6HN_CH2 (Γ : ClosedBirthConstants) :
    p6CapCs_C11GT6.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ :=
  le_C1P6HN_of_std_CH2 (capCs_le_C1P6std_C11GT6.{u} Γ)

theorem capCs_le_C2P6HN_CH2 (Γ : ClosedBirthConstants) :
    p6CapCs_C11GT6.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ :=
  le_C2P6HN_of_std_CH2 (capCs_le_C2P6std_C11GT6.{u} Γ)

/-- consumer（HCAPW）：`C1P6 / C2P6` HN 处的 cap-window witness。 -/
theorem capWitness_at_C1P6HN_CH2 (Γ : ClosedBirthConstants) :
    ∃ (Rcap : ℝ) (mcap : ℕ) (εcap : ℝ), 0 < εcap ∧
    ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
      {fixed : StaticCapScaffold} {D ε₀ : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
      (S : E.PresentedStaticCap fixed D m ε₀ b), S.hasCanonicalWindow →
      ε₀ ≤ εcap → Rcap ≤ D → mcap ≤ m → ∀ x : ThreeBall,
      ∃ W : SpatialCanonicalWitness E.outputMetric Γ.epsilon
          (C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ) (C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ)
          (S.inclusion (S.witness.cap x)),
        W.capTubeHasNeckChart Γ.epsilon := by
  obtain ⟨Rcap, mcap, εcap, -, hεcap, hW⟩ :=
    p6CapCs_spec_C11GT6.{u} (epsilon_mem_C11GT6 Γ).1 (epsilon_mem_C11GT6 Γ).2
  exact ⟨Rcap, mcap, εcap, hεcap, fun S hS h1 h2 h3 x =>
    hW S hS h1 h2 h3 _ _ (capCs_le_C1P6HN_CH2 Γ) (capCs_le_C2P6HN_CH2 Γ) x⟩

/-- `hCtt`（KERNB-W7 / KCONS producer 的 `Γf.Ctime ≤ Ctime′`）在 HN 钉上：
`FineOf Γf Γ ⇒ Γf.Ctime ≤ p6CtimeHN Γ`。 -/
theorem ctime_le_p6CtimeHN_of_fine_CH2 {Γf Γ : ClosedBirthConstants}
    (hfine : FineOf_C11G2.{u} Γf Γ) : Γf.Ctime ≤ p6CtimeHN_CH2.{u} Γ :=
  hfine.2.2.2.trans (Ctime_le_p6CtimeHN_CH2 Γ)

end GC.LongTime.Ch11
