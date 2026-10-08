import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV6FwdC11GT6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6OuterCompatCXOU
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GoodConstantsP6P
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ReserveAccuracyCXOU2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HrestJointPrefixP6HP

set_option autoImplicit false

/-!
# γ2：两级精度合同（tower 在更细的 `Γf` 上构造，结论在粗 `Γ`）——设计车道 O-CH11-GAMMA2 的陈述骨架
（后缀 `_C11G2`）

设计文档：`docs/geometrization/chapter8/design-C11-gamma2-20261007.md`（方案 A 推荐）。
根因：v6fwd 冻结顶层的 `hP6b′` 结论精度 = tower 自己的 `Γ.epsilon`，而 HRESTP 的 rerun 需要
`hcan₁ = HistoryCanonicalSupply_C11S F q.neckRadius (p6FineEta Γ.epsilon) C1₁ C2₁`（更细精度、同一阈值
`q.neckRadius`）；SCRS⁺ 只给 `Γ.epsilon` 精度的 HCS，而 HCS 只能"细 ⇒ 粗"（§1），不能反向。修法 =
结论精度与 tower 精度脱钩：tower 在 `Γf`（`Γf.epsilon ≤ p6FineEta Γ.epsilon`）上构造，结论仍在 `Γ`。

本文件（**不声称任何 binder 已闭合**；块状态 PROVISIONAL / 合同登记）：
* §1 **(a) HCS 对精度单调**（树内只有逐点 `exists_witness_monoEps_P6P` 与常数单调
  `historyCanonicalSupply_mono_C12X`，没有 HCS 级 monoEps）：`historyCanonicalSupply_monoEps_C11G2`、
  `historyCanonicalSupply_mono_all_C11G2`。
* §2 两级关系 `FineOf_C11G2 Γf Γ`（合同 def）+ inhabitant `coarsenTo_C11G2`（`Γf` 的常数原样、
  `C1 / C2` 字段抬到 `C1ceil / C2ceil Γf`、`epsilon := εc`）+ `fineOf_coarsenTo_C11G2`。
* §3 坏点常数 `p6BadC_C11G2 Γ := max (p6FineC ε) (max (C1ceil Γ) (C2ceil Γ))`（`C1₁ = C2₁`；
  `≥ p6FineC ε ≥ Cco η₁`：CXHT htrans / RERUN8B 核的单调适配；`≥ C1ceil, C2ceil`：容纳 `Γf` tower 的
  S5 常数）。htrans 要 `2 · (max C1₁ 9 + √C2₁) ≤ C1`，故 ceiling 的 fine 项须从 `p6FineC ε` 换成
  `p6BadC Γ`（D-15″ def 体路线）；可满足性由显式附加项 `p6X1two_C11G2 / p6X2two_C11G2` 证出。
* §4 **`hcan₁` 的付款** `hcan1_of_scrsPlus_fine_C11G2`：SCRS⁺（tower 在 `Γf`）+ `FineOf Γf Γ` ⇒
  `HCS F q.neckRadius (p6FineEta Γ.epsilon) (p6BadC Γ) (p6BadC Γ)`；两级 outer supply
  `outerSupply_twoLevel_C11G2`（CXOU G1 的两级孪生）。
* §5 合同：`HSpineTwoLevel_C11G2`（hspine‴）、`HP6bTwoLevel_C11G2`（hP6b‴）、
  `GapTop7Statement_C11G2`（GAPTOP7 顶层陈述，**只登记陈述**）；`HpbaseTwoLevel_C11G2`（CX-OUTER2
  `hpbase_epsW_CXOU2` 插入点与 `Γf` 选取合并）+ producer `hpbaseTwoLevel_C11G2`
  （`hpbase_accuracy_CXOU2` + `coarsenTo`，PROVED）。
* §6 最终装配的两级形 `a12EnhancedFull_of_chain_cone_C11G2`：`a12EnhancedFull_of_chain_C12X` 逐字，
  只把 `ε = C.epsilon` 换成 `ε ≤ coneAccuracy`（链在 `Γf` 上，元组精度 = 粗 `Γ.epsilon`）。
-/

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Topology ContDiff Manifold ENNReal

namespace GC.LongTime.Ch11

universe u

/-! ## 1. (a) HCS 对精度单调（细 ⇒ 粗，同阈值、同常数） -/

/-- **HCS monoEps**：`ε ≤ ε' < 1/11` ⇒ `HCS(ε) ⇒ HCS(ε')`（逐点 `exists_witness_monoEps_P6P`）。
反方向（粗 ⇒ 细、同阈值 `ρ`）在树内无来源：这正是 `hcan₁` 不能由 SCRS⁺ 直接付的根因。 -/
theorem historyCanonicalSupply_monoEps_C11G2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {ε ε' C1 C2 : ℝ}
    (h : HistoryCanonicalSupply_C11S F ρ ε C1 C2) (hε : ε ≤ ε') (hsmall : ε' < 1 / 11) :
    HistoryCanonicalSupply_C11S F ρ ε' C1 C2 := fun n t x hx =>
  ObservedHistory.exists_witness_monoEps_P6P hε hsmall (h n t x hx)

/-- HCS 对（精度，常数）联合单调。 -/
theorem historyCanonicalSupply_mono_all_C11G2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {ε ε' C1 C2 C1' C2' : ℝ}
    (h : HistoryCanonicalSupply_C11S F ρ ε C1 C2) (hε : ε ≤ ε') (hsmall : ε' < 1 / 11)
    (h1 : C1 ≤ C1') (h2 : C2 ≤ C2') :
    HistoryCanonicalSupply_C11S F ρ ε' C1' C2' :=
  historyCanonicalSupply_mono_C12X (historyCanonicalSupply_monoEps_C11G2 h hε hsmall) h1 h2

/-- 坏点精度在 `(0, 1/11)` 内（`p6FineEta ε ≤ ε/2`，`Γ.epsilon < 1/100`）。 -/
theorem p6FineEta_lt_eleventh_C11G2 (Γ : ClosedBirthConstants) :
    p6FineEta_C11GT6 Γ.epsilon < 1 / 11 := by
  have h1 := p6FineEta_le_C11GT6 Γ.epsilon
  have h2 := Γ.epsilon_small
  linarith

/-! ## 2. 两级关系 `FineOf_C11G2 Γf Γ` 与 inhabitant -/

/-- **两级关系**（合同 def）：tower 常数 `Γf` 比结论常数 `Γ` 细——`Γf.epsilon ≤ p6FineEta Γ.epsilon`
（HRESTP 坏点精度），shared ceiling 与 `Ctime` 不超过 `Γ` 的（S5 / S16 / TDS 常数搬运）。 -/
def FineOf_C11G2 (Γf Γ : ClosedBirthConstants) : Prop :=
  Γf.epsilon ≤ p6FineEta_C11GT6 Γ.epsilon ∧ C1ceil_C11SC.{u} Γf ≤ C1ceil_C11SC.{u} Γ ∧
    C2ceil_C11SC.{u} Γf ≤ C2ceil_C11SC.{u} Γ ∧ Γf.Ctime ≤ Γ.Ctime

/-- **粗化**：`Γf` 的常数原样，`epsilon := εc`，`C1 / C2` 字段抬到 `C1ceil / C2ceil Γf`（使
`C1ceil (coarsenTo Γf εc) ≥ C1ceil Γf`，S16 常数可搬运）。只作结论常数的标签，不对应任何 tower。 -/
def coarsenTo_C11G2 (Γf : ClosedBirthConstants) (εc : ℝ) (h0 : 0 < εc) (h1 : εc < 1 / 100)
    (hcone : εc ≤ coneAccuracy) : ClosedBirthConstants where
  epsilon := εc
  C1 := C1ceil_C11SC.{u} Γf
  C2 := C2ceil_C11SC.{u} Γf
  C1s := Γf.C1s
  C2s := Γf.C2s
  Cs := Γf.Cs
  tauMin := Γf.tauMin
  Cbirth := Γf.Cbirth
  Ctime := Γf.Ctime
  Cgrad := Γf.Cgrad
  epsilon_pos := h0
  epsilon_small := h1
  C1_ge_one := one_le_C1ceil_C11SC.{u} Γf
  C2_ge_one := one_le_C2ceil_C11SC.{u} Γf
  C1s_ge_one := Γf.C1s_ge_one
  C2s_ge_one := Γf.C2s_ge_one
  Cs_ge_one := Γf.Cs_ge_one
  tauMin_pos := Γf.tauMin_pos
  Cbirth_ge_one := Γf.Cbirth_ge_one
  epsilon_cone := hcone

/-- `coarsenTo_C11G2 Γf εc` 满足 `FineOf_C11G2 Γf ·`，只要 `Γf.epsilon ≤ p6FineEta εc`。 -/
theorem fineOf_coarsenTo_C11G2 (Γf : ClosedBirthConstants) (εc : ℝ) (h0 : 0 < εc)
    (h1 : εc < 1 / 100) (hcone : εc ≤ coneAccuracy) (hf : Γf.epsilon ≤ p6FineEta_C11GT6 εc) :
    FineOf_C11G2.{u} Γf (coarsenTo_C11G2.{u} Γf εc h0 h1 hcone) := by
  refine ⟨hf, ?_, ?_, le_rfl⟩
  · exact (le_max_left _ _ :
      C1ceil_C11SC.{u} Γf ≤ strongC1_C11SC.{u} εc (C1ceil_C11SC.{u} Γf)).trans
      (strongC1_le_C1ceil_C11SC.{u} (coarsenTo_C11G2.{u} Γf εc h0 h1 hcone))
  · exact (le_max_left _ _ :
      C2ceil_C11SC.{u} Γf ≤ strongC2_C11SC.{u} εc (C2ceil_C11SC.{u} Γf) Γf.Cgrad).trans
      (strongC2_le_C2ceil_C11SC.{u} (coarsenTo_C11G2.{u} Γf εc h0 h1 hcone))

/-- 两级关系下 tower 精度 ≤ 结论精度（`p6FineEta ε ≤ ε/2 ≤ ε`）。 -/
theorem FineOf_C11G2.epsilon_le {Γf Γ : ClosedBirthConstants} (h : FineOf_C11G2.{u} Γf Γ) :
    Γf.epsilon ≤ Γ.epsilon := by
  have h1 := p6FineEta_le_C11GT6 Γ.epsilon
  have h2 := Γ.epsilon_pos
  linarith [h.1]

/-! ## 3. 坏点常数（`hcan₁`、htrans、`hdomF` 的共同常数）与 ceiling 的可满足性 -/

/-- **坏点常数** `c(Γ) := max (p6FineC ε) (max (C1ceil Γ) (C2ceil Γ))`（`C1₁ = C2₁ := c(Γ)`）：比 D-15′ /
CXHT G3 的 `p6FineC ε` 多 `C1ceil Γ`、`C2ceil Γ` 两项，以容纳 `Γf` tower 的 S5 常数
（`FineOf` 下 `oldC Γf ≤ C1ceil Γf ≤ C1ceil Γ`）。 -/
def p6BadC_C11G2 (Γ : ClosedBirthConstants) : ℝ :=
  max (p6FineC_C11GT6.{u} Γ.epsilon) (max (C1ceil_C11SC.{u} Γ) (C2ceil_C11SC.{u} Γ))

theorem fineC_le_p6BadC_C11G2 (Γ : ClosedBirthConstants) :
    p6FineC_C11GT6.{u} Γ.epsilon ≤ p6BadC_C11G2.{u} Γ :=
  le_max_left _ _

/-- 核常数 `Cco η₁ ≤ c(Γ)`（RERUN8B 核在 `Cco η₁` 处，槽单调适配用）。 -/
theorem coarseFine_le_p6BadC_C11G2 (Γ : ClosedBirthConstants) :
    p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ p6BadC_C11G2.{u} Γ :=
  (le_max_left _ _ : _ ≤ p6FineC_C11GT6.{u} Γ.epsilon).trans (fineC_le_p6BadC_C11G2 Γ)

theorem C1ceil_le_p6BadC_C11G2 (Γ : ClosedBirthConstants) :
    C1ceil_C11SC.{u} Γ ≤ p6BadC_C11G2.{u} Γ :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem C2ceil_le_p6BadC_C11G2 (Γ : ClosedBirthConstants) :
    C2ceil_C11SC.{u} Γ ≤ p6BadC_C11G2.{u} Γ :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- **ceiling 附加项（C1 侧，两级）**：`max (p6X1std Γ) (2 · (max c 9 + √c))`，`c := c(Γ)`。D-15″ def 体
路线 = 把 `p6X1std` 的 fine 项 `p6FineC ε` 换成 `c(Γ)`（`c(Γ) ≥ p6FineC ε`，旧支配引理陈述照旧成立）；
本 def 只用于证可满足性。 -/
def p6X1two_C11G2 (Γ : ClosedBirthConstants) : ℝ :=
  max (p6X1std_C11GT6.{u} Γ)
    (2 * (max (p6BadC_C11G2.{u} Γ) 9 + Real.sqrt (p6BadC_C11G2.{u} Γ)))

/-- **ceiling 附加项（C2 侧，两级）**：`max (p6X2std Γ) (1200000 · c)`。 -/
def p6X2two_C11G2 (Γ : ClosedBirthConstants) : ℝ :=
  max (p6X2std_C11GT6.{u} Γ) (1200000 * p6BadC_C11G2.{u} Γ)

theorem C1P6std_le_C1P6two_C11G2 (Γ : ClosedBirthConstants) :
    C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ≤ C1P6_C11GT6.{u} p6X1two_C11G2.{u} Γ :=
  max_le_max le_rfl (le_max_left _ _)

theorem C2P6std_le_C2P6two_C11G2 (Γ : ClosedBirthConstants) :
    C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ ≤ C2P6_C11GT6.{u} p6X2two_C11G2.{u} Γ :=
  max_le_max le_rfl (le_max_left _ _)

/-- htrans / STAB2 的 `2 · C1f ≤ C1`（`C1f := max c 9 + √c`，`c := c(Γ)`）在两级 ceiling 处。 -/
theorem two_mul_bad_le_C1P6two_C11G2 (Γ : ClosedBirthConstants) :
    2 * (max (p6BadC_C11G2.{u} Γ) 9 + Real.sqrt (p6BadC_C11G2.{u} Γ)) ≤
      C1P6_C11GT6.{u} p6X1two_C11G2.{u} Γ :=
  (le_max_right _ _ : _ ≤ p6X1two_C11G2.{u} Γ).trans (X_le_C1P6_C11GT6 p6X1two_C11G2.{u} Γ)

/-- htrans / STAB2 的 `1000 · C2f ≤ C2`（`C2f := 1200 · c`）在两级 ceiling 处。 -/
theorem bad_le_C2P6two_C11G2 (Γ : ClosedBirthConstants) :
    1200000 * p6BadC_C11G2.{u} Γ ≤ C2P6_C11GT6.{u} p6X2two_C11G2.{u} Γ :=
  (le_max_right _ _ : _ ≤ p6X2two_C11G2.{u} Γ).trans (X_le_C2P6_C11GT6 p6X2two_C11G2.{u} Γ)

/-- **`hdomF`（C1 侧）**：`c(Γ) ≤ C1P6 p6X1two Γ`。 -/
theorem p6BadC_le_C1P6two_C11G2 (Γ : ClosedBirthConstants) :
    p6BadC_C11G2.{u} Γ ≤ C1P6_C11GT6.{u} p6X1two_C11G2.{u} Γ := by
  have h := two_mul_bad_le_C1P6two_C11G2 Γ
  have hs := Real.sqrt_nonneg (p6BadC_C11G2.{u} Γ)
  have hm : p6BadC_C11G2.{u} Γ ≤ max (p6BadC_C11G2.{u} Γ) 9 := le_max_left _ _
  have h9 : (9 : ℝ) ≤ max (p6BadC_C11G2.{u} Γ) 9 := le_max_right _ _
  linarith

/-- **`hdomF`（C2 侧）**：`c(Γ) ≤ C2P6 p6X2two Γ`。 -/
theorem p6BadC_le_C2P6two_C11G2 (Γ : ClosedBirthConstants) :
    p6BadC_C11G2.{u} Γ ≤ C2P6_C11GT6.{u} p6X2two_C11G2.{u} Γ := by
  have h := bad_le_C2P6two_C11G2 Γ
  have h1 := (one_le_C1ceil_C11SC.{u} Γ).trans (C1ceil_le_p6BadC_C11G2 Γ)
  linarith

/-! ## 4. `hcan₁` 的付款与两级 outer supply -/

/-- **两级 outer supply**（CXOU G1 `outerSupply_of_scrsPlus_CXOU` 的两级孪生）：tower `T` 在 `Γf`，
`FineOf Γf Γ` ⇒ joint 定理的外层前提在**粗** `Γ.epsilon`（常数 `C1 ≥ C1ceil Γ` 等），外加坏点精度的
`hcan₁`（`η₁ = p6FineEta Γ.epsilon`，常数 `C1₁ = C2₁ = p6BadC Γ`）。 -/
theorem outerSupply_twoLevel_C11G2 {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    {T : BlockTower_C11W pB Γf P g Cdist cMax Dstar εReserve}
    (hS : SameConstructionRetentionSupplyPlus_C11GT6 T) (hfine : FineOf_C11G2.{u} Γf Γ)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (hF : F.tower = T.toChain.tower)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    {C1 C2 : ℝ} {Ctime : ℝ≥0} (hC1 : C1ceil_C11SC.{u} Γ ≤ C1) (hC2 : C2ceil_C11SC.{u} Γ ≤ C2)
    (hCt : Γ.Ctime ≤ Ctime) :
    AntitoneOn q.neckRadius (Ici 0) ∧
      HistoryCanonicalSupply_C11S F q.neckRadius Γ.epsilon C1 C2 ∧
      HistoryCanonicalSupply_C11S F q.neckRadius (p6FineEta_C11GT6 Γ.epsilon)
        (p6BadC_C11G2.{u} Γ) (p6BadC_C11G2.{u} Γ) ∧
      TimeDerivativeSupply_C11E F q.neckRadius Ctime := by
  have hf1 : max Γf.C1s Γf.Cbirth ≤ C1ceil_C11SC.{u} Γ :=
    (oldC1_le_C1ceil_C11SC.{u} Γf).trans hfine.2.1
  have hf2 : max Γf.C2s (max Γf.Cbirth (Γf.Cgrad : ℝ)) ≤ C2ceil_C11SC.{u} Γ :=
    (oldC2_le_C2ceil_C11SC.{u} Γf).trans hfine.2.2.1
  obtain ⟨hanti, hcanf, hTD⟩ := outerSupply_of_scrsPlus_CXOU hS F q hF hq (hf1.trans hC1)
    (hf2.trans hC2) (hfine.2.2.2.trans hCt)
  have hfineLt := p6FineEta_lt_eleventh_C11G2 Γ
  have hΓ : Γ.epsilon < 1 / 11 := by
    have := Γ.epsilon_small
    linarith
  refine ⟨hanti, historyCanonicalSupply_monoEps_C11G2 hcanf hfine.epsilon_le hΓ, ?_, hTD⟩
  obtain ⟨-, hcan₁, -⟩ := outerSupply_of_scrsPlus_CXOU hS F q hF hq
    (hf1.trans (C1ceil_le_p6BadC_C11G2 Γ)) (hf2.trans (C2ceil_le_p6BadC_C11G2 Γ)) le_rfl
  exact historyCanonicalSupply_monoEps_C11G2 hcan₁ hfine.1 hfineLt

/-- **`hcan₁` 付款**（HRESTP PROVISIONAL binder 的 repair target 的陈述级落地）：SCRS⁺（tower 在 `Γf`）+
`FineOf Γf Γ` ⇒ `HistoryCanonicalSupply_C11S F q.neckRadius η₁ C1₁ C2₁`，
`η₁ = p6FineEta Γ.epsilon`、`C1₁ = C2₁ = p6BadC Γ`。 -/
theorem hcan1_of_scrsPlus_fine_C11G2 {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    {T : BlockTower_C11W pB Γf P g Cdist cMax Dstar εReserve}
    (hS : SameConstructionRetentionSupplyPlus_C11GT6 T) (hfine : FineOf_C11G2.{u} Γf Γ)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (hF : F.tower = T.toChain.tower)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) :
    HistoryCanonicalSupply_C11S F q.neckRadius (p6FineEta_C11GT6 Γ.epsilon)
      (p6BadC_C11G2.{u} Γ) (p6BadC_C11G2.{u} Γ) :=
  (outerSupply_twoLevel_C11G2 hS hfine F q hF hq (le_refl (C1ceil_C11SC.{u} Γ))
    (le_refl (C2ceil_C11SC.{u} Γ)) (le_refl Γ.Ctime)).2.2.1

/-! ## 5. 合同：hspine‴ / hP6b‴ / GAPTOP7 / 两级 provider -/

/-- **hspine‴**（v6fwd `hspine″` 的两级形）：与冻结文本逐字相同，只改两处——`∀ {pB} {Γ Γf},
FineOf Γf Γ →`，链 `S : PreparedSpatialChain pB Γf P g`；阈值 `εsp Γ Γf`。`hP6` 仍在粗
`Γ.epsilon`、标准 `C1P6 / C2P6 Γ`。 -/
def HSpineTwoLevel_C11G2 (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ εsp : ClosedBirthConstants → ClosedBirthConstants → ℝ, (∀ Γ Γf, 0 < εsp Γ Γf) ∧
    ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
    ∀ (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g)
      (q : CutoffParameters),
    F.tower = S.tower →
    (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
    pB.modelAccuracy ≤ εsp Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
    2 ≤ pB.modelOrder →
    ∀ A : ℝ, 1 < A →
    (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
            ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
      LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
        (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) →
      LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A

/-- **hP6b‴**（v6fwd `hP6b′` 的两级形）：只改 `∀ {pB} {Γ Γf}, FineOf Γf Γ →`、CX-OUTER2 G2′ 的两条
Γ-accuracy 门槛 `Γ.epsilon ≤ εStrong → Γ.epsilon ≤ εW →`（`εW := epsW_CXOU2`）、tower
`T : BlockTower_C11W pB Γf …`、`BudgetCertificate … Γf.Ctime …`、阈值 `εP6 Γ Γf`；SCRS⁺ 文本不动
（作用在 `Γf` tower 上），结论 `CanonicalLateCore_P6X F Γ.epsilon (C1P6 std Γ) (C2P6 std Γ)` 逐字
（`p6X1std / p6X2std` 取 D-15″ 新 def 体时）。 -/
def HP6bTwoLevel_C11G2 (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ, (∀ Γ Γf, 0 < εP6 Γ Γf) ∧
    ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
    Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
    ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
      (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
    (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j (T.block j) (T.lookahead j)
      (T.request j)) →
    SameConstructionRetentionSupplyPlus_C11GT6 T →
    ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
    (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
    pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
    2 ≤ pB.modelOrder →
    CanonicalLateCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
      (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ)

/-- **GAPTOP7 顶层陈述**（只登记，**未证**；证明 = 设计文档 §5 的 v7 引擎，估 ≈ 0.9–1.2k 行）：
binder 只有 `hspine‴ hP6b‴`。 -/
def GapTop7Statement_C11G2 (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  HSpineTwoLevel_C11G2.{u} P g → HP6bTwoLevel_C11G2.{u} P g → A12EnhancedFullConclusion_C11F P g

/-- **两级 `hpbase`**（CX-OUTER2 `hpbase_epsW_CXOU2` 的插入点 v6fwd:423 与 `Γf` 选取合并）：粗 `Γ`
（结论标签）与细 `Γf`（tower 常数）同时满足 `≤ εStrong`、`≤ εW`，且 `FineOf Γf Γ`；
`∀ εReserve` 之后的 provider 部分（`pB`、prepared class、`BlockStep`）在 `Γf` 上逐字。 -/
def HpbaseTwoLevel_C11G2 (εW : ℝ) (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (Cdist : ℝ≥0) (Γ Γf : ClosedBirthConstants), FineOf_C11G2.{u} Γf Γ ∧
    Γ.epsilon ≤ εStrong_C12X.{u} ∧ Γ.epsilon ≤ εW ∧
    Γf.epsilon ≤ εStrong_C12X.{u} ∧ Γf.epsilon ≤ εW ∧
    ∀ εReserve : ℝ, 0 < εReserve →
    ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γf P g 1),
      prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
      prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
      collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
      ∀ j : ℕ, BlockStep_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j

/-- 粗精度闭项 `εc := min (1/200) (min coneAccuracy (min εStrong εW))`。 -/
def epsCoarse_C11G2 (εW : ℝ) : ℝ :=
  min (1 / 200) (min coneAccuracy (min εStrong_C12X.{u} εW))

theorem epsCoarse_pos_C11G2 {εW : ℝ} (hεW : 0 < εW) : 0 < epsCoarse_C11G2.{u} εW :=
  lt_min (by norm_num) (lt_min coneAccuracy_pos (lt_min εStrong_C12X_pos hεW))

/-- **两级 provider（泛型核）**：前提 `hacc` 的类型 = CX-OUTER2 `hpbase_accuracy_CXOU2 P g` 逐字
（闭合实例见 `hpbaseTwoLevel_C11G2`）。
选取顺序：`εc := epsCoarse εW` → `Γf`（cap `min εW (p6FineEta εc)`）→ `Γ := coarsenTo Γf εc`；
`∃ Γ Γf` 都在 `∀ εReserve` 之前（D-3：reserve 可含 `epsilon0_C11FR`(Γf) 再选 `pB` 与 tower）。 -/
theorem hpbaseTwoLevel_of_accuracy_C11G2 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hacc : ∀ εcap : ℝ, 0 < εcap →
      ∃ (Cdist : ℝ≥0) (Γ : ClosedBirthConstants), Γ.epsilon ≤ εStrong_C12X.{u} ∧
        Γ.epsilon ≤ εcap ∧
        ∀ εReserve : ℝ, 0 < εReserve →
        ∃ (pB : CutoffParameters) (prepared : ClosedBirthPreparedClass pB Γ P g 1),
          prepared.parameters = pB ∧ prepared.HasDistanceExtension Cdist ∧
          prepared.HasReserveQuality (capWindowRadius_C11E + 1) εReserve ∧
          collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos ∧
          ∀ j : ℕ, BlockStep_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve j)
    (εW : ℝ) (hεW : 0 < εW) : HpbaseTwoLevel_C11G2.{u} εW P g := by
  have hc0 : 0 < epsCoarse_C11G2.{u} εW := epsCoarse_pos_C11G2 hεW
  have hc1 : epsCoarse_C11G2.{u} εW < 1 / 100 :=
    (min_le_left _ _).trans_lt (by norm_num)
  have hccone : epsCoarse_C11G2.{u} εW ≤ coneAccuracy :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hcs : epsCoarse_C11G2.{u} εW ≤ εStrong_C12X.{u} :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcW : epsCoarse_C11G2.{u} εW ≤ εW :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcap : 0 < min εW (p6FineEta_C11GT6 (epsCoarse_C11G2.{u} εW)) :=
    lt_min hεW (p6FineEta_pos_C11GT6 hc0)
  obtain ⟨Cdist, Γf, hfs, hfcap, hmake⟩ := hacc _ hcap
  refine ⟨Cdist, coarsenTo_C11G2.{u} Γf (epsCoarse_C11G2.{u} εW) hc0 hc1 hccone, Γf,
    fineOf_coarsenTo_C11G2 Γf _ hc0 hc1 hccone (hfcap.trans (min_le_right _ _)), hcs, hcW, hfs,
    hfcap.trans (min_le_left _ _), hmake⟩

/-- **两级 provider（闭合）**：v6fwd:423 插入点的 v7 替换——`hpbase_accuracy_CXOU2` + `coarsenTo`，
`εW := epsW_CXOU2`。 -/
theorem hpbaseTwoLevel_C11G2 (P : OrientedThreeStage.{u}) (g : P.Metric) :
    HpbaseTwoLevel_C11G2.{u} epsW_CXOU2.{u} P g :=
  hpbaseTwoLevel_of_accuracy_C11G2 P g (hpbase_accuracy_CXOU2 P g) epsW_CXOU2.{u}
    epsW_CXOU2_pos.{u}

/-! ## 6. 最终装配的两级形（元组精度 = 粗 `ε`，链常数 `C`） -/

/-- **`a12EnhancedFull_of_chain_C12X` 的两级形**：陈述逐字，只把 `ε = C.epsilon` 换成
`ε ≤ coneAccuracy`（原定理只用该等式付 `ConeEpsilonSupply`）。链 `S` 在细 `C`（= `Γf`）上，元组的
`ε C1 C2` 取粗 `Γ.epsilon`、`C1P6 / C2P6 Γ`；`TimeDerivativeSupply` 仍在链的 `C.Ctime`。 -/
theorem a12EnhancedFull_of_chain_cone_C11G2 {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (hP3 : CollarWindowSupply_C11E.{u} pBase)
    (hprof : ModelConstraintsSupply_C11E pBase εProf_C11E.{u})
    (hext : ∃ S : GC.GeneralFlow.PreparedSpatialChain pBase C P g,
      ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
        (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
        F.tower = S.tower ∧ ε ≤ coneAccuracy ∧
        (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
          q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy) ∧
        CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
        AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
        HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
        (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
          (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
        Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records ∧
        LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) ∧
        LinkedWindowsSupply_C11E records ∧ TimeDerivativeSupply_C11E F q.neckRadius C.Ctime ∧
        LateLinkedRecordsSupply_C11E F q ∧ LargerBallCanonicalLateSupply_C11E F ε C1 C2 ∧
        StrongCanonicalSupplyV2_C11E F q.neckRadius ε C1 C2 ∧
        CompatibleCapsSupply_C11E F q records ∧ FrontierCollarSupplyFull_C11F F q) :
    A12EnhancedFullConclusion_C11F P g := by
  obtain ⟨_, F, q, κ, records, ε, C1, C2, -, hcone, ⟨hfixed, hrad, hord, hacc⟩, hconst, hκ,
    hκanti, hδanti, hρanti, hcan, hnc, hδlim, hrecent, hS8, hP1, hP2, hP5, hP6, hStrong, hCompat,
    hRFC⟩ := hext
  have hδ := supply1_of_astra_C11A q hδanti hδlim
  refine ⟨q.delta, F, hδ.1, hδ.2, ⟨EnhancedSurgeryProfile_C11E.toFull_C12X
    (enhancedProfileOfSupplies_C11E F q records _ C1 C2 κ (diagonalAccuracy_C11S q.delta) C.Ctime
      hρanti hconst (supply5_of_astra_C11A F q _ C1 C2 hcan)
      (supply6_of_astra_C11A F κ _ hκ hκanti hnc) (supply7_of_astra_C11A q hδanti) hS8 hrecent
      ⟨hP1, hP2, collarWindowSupply_of_static_C11P2 hfixed hrad hP3,
        coneEpsilonSupply_of_le_coneAccuracy_C11E hcone, hP5, hP6, hStrong, hCompat,
        modelConstraintsSupply_of_static_C11P2 hacc hord hrad hprof,
        frontierCollarSupply_of_full_C11F hRFC⟩) hRFC⟩⟩

/-! ## 7. consumers -/

/-- consumer (i)：`hcan₁` 直接喂 HRESTP `ceiling_of_bad_P6HP`（binder 形逐字）：坏点 `¬∃ W (η₁, c, c)` ⇒
rerun 点 ceiling `R ≤ nr_q̃(Tn)⁻²`——HRESTP G1 的 PROVISIONAL 项在两级 tower 上的付款。 -/
example {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants} {P : OrientedThreeStage.{u}}
    {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pB Γf P g Cdist cMax Dstar εReserve)
    (hS : SameConstructionRetentionSupplyPlus_C11GT6 T) (hfine : FineOf_C11G2.{u} Γf Γ)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (hF : F.tower = T.toChain.tower)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (n : ℕ) {c : ℝ} (hc : 0 < c)
    {t Tn : Icc (0 : ℝ) ((F.tower.history n).rescale_P6N c hc).toHistory.horizon} (htT : t ≤ Tn)
    (z : (((F.tower.history n).rescale_P6N c hc).toHistory.stageAt t).Carrier)
    (hbad : ¬ ∃ W : SpatialCanonicalWitness
      (((F.tower.history n).rescale_P6N c hc).toHistory.stageMetric
        (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage t) t)
        (p6FineEta_C11GT6 Γ.epsilon) (p6BadC_C11G2.{u} Γ) (p6BadC_C11G2.{u} Γ) z,
      W.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon)) :
    metricScalarAt (((F.tower.history n).rescale_P6N c hc).toHistory.stageMetric
        (((F.tower.history n).rescale_P6N c hc).toHistory.activeStage t) t) z ≤
      ((q.rescale_P6N c hc).neckRadius Tn ^ 2)⁻¹ :=
  ObservedHistory.ceiling_of_bad_P6HP (hcan1_of_scrsPlus_fine_C11G2 hS hfine F q hF hq) hanti n hc
    htT z hbad

/-- consumer (ii)：闭合两级 provider 给出 `(Γ, Γf)`：`FineOf`、CX-OUTER2 G2′ 的两条 Γ-accuracy、
`Γf.epsilon ≤ Γ.epsilon`；`GapTop7Statement` 的 binder 直接喂入。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) (htop : GapTop7Statement_C11G2.{u} P g)
    (hs : HSpineTwoLevel_C11G2.{u} P g) (hp : HP6bTwoLevel_C11G2.{u} P g) :
    (∃ Γ Γf : ClosedBirthConstants, FineOf_C11G2.{u} Γf Γ ∧ Γ.epsilon ≤ εStrong_C12X.{u} ∧
      Γ.epsilon ≤ epsW_CXOU2.{u} ∧ Γf.epsilon ≤ Γ.epsilon) ∧
      A12EnhancedFullConclusion_C11F P g := by
  obtain ⟨-, Γ, Γf, hfine, hs1, hW, -⟩ := hpbaseTwoLevel_C11G2.{u} P g
  exact ⟨⟨Γ, Γf, hfine, hs1, hW, hfine.epsilon_le⟩, htop hs hp⟩

/-- consumer (iii)：两级 ceiling 仍支配 D-15′ 的标准 fine 项（`C1P6 std ≤ C1P6 two`），且坏点常数同时
满足 `Cco η₁ ≤ c(Γ)`（核单调）与 `c(Γ) ≤ C1P6 two, C2P6 two`（`hdomF`）。 -/
example (Γ : ClosedBirthConstants) :
    2 * max (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) 9 ≤
        C1P6_C11GT6.{u} p6X1two_C11G2.{u} Γ ∧
      p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ p6BadC_C11G2.{u} Γ ∧
      p6BadC_C11G2.{u} Γ ≤ C1P6_C11GT6.{u} p6X1two_C11G2.{u} Γ ∧
      p6BadC_C11G2.{u} Γ ≤ C2P6_C11GT6.{u} p6X2two_C11G2.{u} Γ :=
  ⟨(two_mul_fine_le_C1P6std_C11GT6 Γ).trans (C1P6std_le_C1P6two_C11G2 Γ),
    coarseFine_le_p6BadC_C11G2 Γ, p6BadC_le_C1P6two_C11G2 Γ, p6BadC_le_C2P6two_C11G2 Γ⟩

end GC.LongTime.Ch11
