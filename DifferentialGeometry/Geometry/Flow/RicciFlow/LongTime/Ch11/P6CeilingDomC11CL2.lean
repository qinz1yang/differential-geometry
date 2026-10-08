import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingC11GT6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RerunEvent8P6R8
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FineMarginImproveP6ST4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HcenProducerP6HE

set_option autoImplicit false

/-!
# P6 ceiling 支配引理包 `C1P6 / C2P6`（S-CH11-CEIL2 G1，后缀 `_C11CL2`；R-C11-10 D-15）

D-15：RERUN8 的坏点常数 `C(η₁)` 恒为 `p6CoarseC_C11GT6 η₁`（与 ceiling 的 `Cco` 同一个 def），`η₁` 须固定为
`ηf := p6FineEta_C11GT6 Γ.epsilon`（RERUN8B / HbdLate rev2 的消费端）；固定之后 `C(η₁) ≡ Cco(ηf)`，
ceiling `C1P6 X1 Γ = max (C1ceil Γ) (X1 Γ)` 的 max 结构给出支配。本文件把消费端要用的每一条不等式
单独成引理（纯 `le_max` / `linarith` 算术，无新分析），每条 docstring 注明消费者：

* `X1 := p6X1std_C11GT6`、`X2 := p6X2std_C11GT6`（`ε := Γ.epsilon`，`ηf := p6FineEta_C11GT6 ε`）；
* C1 侧：`p6CoarseC ε`、`p6CoarseC ηf`、`2 · max (p6CoarseC ηf) 9`、`9`、`max (p6CoarseC ηf) 9`、
  `p6CapCs ε`、`C1ceil Γ` 全部 `≤ C1P6 X1 Γ`；
* C2 侧：`p6CoarseC ε`、`p6CoarseC ηf`、`1000 · p6CoarseC ηf`、`p6CapCs ε`、`C2ceil Γ` 全部 `≤ C2P6 X2 Γ`；
* 时间侧（RERUN8 `hCt` 的形）：`(p6CoarseC ·).toNNReal ≤ (C1P6 / C2P6 ·).toNNReal`。
其中 `GT6` 文件已有的五条（`coarse_le_C1P6std` 等）以同名后缀别名重述，其余为新增（`ηf ≤ ceiling`、
`9 ≤ ceiling`、`max · 9 ≤ ceiling`、时间侧）。两个 consumer `example`：RERUN8 `hrerunE8_P6R8` 的
`hC1 / hC2 / hCt`（η₁ := ηf，坏点常数取 ceiling 本身）与 STAB4 `fineGood_implies_fineMarginGood_P6ST4`
（`max C1 9 ≤ C1'`、`C2 ≤ C2'`，C1' / C2' := `C1P6 / C2P6`）。

**范围**：§1–§4 不含 `2·Ccap(ηf)` / `1000·Ccap(ηf)`（G2 核实结论：当前无消费者，见
`build-logs/resume/state-S-CH11-CEIL2.md`）；不触 v6fwd / hspine″ / hP6b′ 接口。
`Cco` 对精度不单调，故无对任意 `η₁` 的支配，只对固定的 `ηf := p6FineEta_C11GT6 Γ.epsilon`。

**ceiling v2（R-C11-10 D-15′，O-CH11-CEIL3，§5，后缀 `_C11CL3`）**：GT6 的 `p6FineEta` def 体改为
`min (ε/2) (min (neckModelTolerance (ε/2) / 13000) (backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊))`
（坏点精度 `η₁ := ηf`，不再等于 margin 层精度 `ηN := neckModelTolerance (ε/2)`），fine 常数
`c := p6FineC_C11GT6 ε = max (Cco η₁) (max (Ccap η₁) (Ccol ε))`，X1 / X2 的中项为
`2 · (max c 9 + √c)` / `1200000 · c`。§1–§4 的 17 条陈述与证明不变（只经 GT6 引理）；§5 新增
精度侧（`13000 · η₁ ≤ ηN`、`η₁ ≤ bJS`、`η₁ < ηN`）、`c` 的分量、`2 · C1f ≤ C1P6`、`1000 · C2f ≤ C2P6`
（`C1f := max c 9 + √c`、`C2f := 1200 · c`，CX-CAPCORE 放大量）、`√c ≤ C1P6`、`Ccap η₁ ≤ C1P6 / C2P6`、
`Ccol ε ≤ C1P6 / C2P6`（HCENP `hcenE_of_noShortcut_P6HE` 的 `hCs1 / hCs2`）。
-/

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

/-! ## 1. `C1` 侧 -/

/-- Good 区精度处 coarse kernel：`C(ε) ≤ C1P6`。消费者：`goodConstants_accommodate_P6P` (ii)；
`ancientWitness_decoupled_P6P` 的 `C(ηout)` 在 Good 区 `ηout = ε`（GT6 `coarse_le_C1P6std` 的别名）。 -/
theorem coarse_le_C1P6_C11CL2 (Γ : ClosedBirthConstants) :
    p6CoarseC_C11GT6.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ :=
  coarse_le_C1P6std_C11GT6 Γ

/-- 坏点精度 `ηf` 处 coarse kernel：`C(ηf) ≤ C1P6`。消费者：RERUN8 `hrerunE8_P6R8` / `hrerunF8_P6R8` /
`hbd8_P6R8` 的 `hC1 / hK1`（`η₁ := ηf`，坏点常数 `C1₁` 取到 ceiling）；RERUN8B `hgapJ8` 固定坏点
`C1₁ = C(ηf)` 后与 Good 区 `C1` 的比较（D-15）。 -/
theorem coarseFine_le_C1P6_C11CL2 (Γ : ClosedBirthConstants) :
    p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤
      C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ := by
  have h1 := one_le_p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)
  have h2 := two_mul_fine_le_C1P6std_C11GT6.{u} Γ
  have h3 : p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤
      max (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) 9 := le_max_left _ _
  linarith

/-- fine recovery + transfer 损失：`2 · max C(ηf) 9 ≤ C1P6`。消费者：STAB2
`spatialWitness_of_bufferedTransfer_P6ST2` 的 `h1 : 2 * C1 ≤ C1out`（`C1 = max C(ηf) 9`）；STAB4
`frequently_neck_free_P6ST4` 的 `h1`（GT6 `two_mul_fine_le_C1P6std` 的别名）。 -/
theorem two_mul_fine_le_C1P6_C11CL2 (Γ : ClosedBirthConstants) :
    2 * max (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) 9 ≤
      C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ :=
  two_mul_fine_le_C1P6std_C11GT6 Γ

/-- margin 创造的下界 `9 ≤ C1P6`。消费者：STAB4 `exists_hasMargins_of_neck_P6ST4` / 改善定理的
`max C1 9 ≤ C1'`（半径 `9/√Q`，`C1 ↦ max C1 9`）中 `9 ≤ C1'` 一半。 -/
theorem nine_le_C1P6_C11CL2 (Γ : ClosedBirthConstants) :
    (9 : ℝ) ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ := by
  have h1 := one_le_p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)
  have h2 := two_mul_fine_le_C1P6std_C11GT6.{u} Γ
  have h3 : (9 : ℝ) ≤ max (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) 9 := le_max_right _ _
  have h4 : p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤
      max (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) 9 := le_max_left _ _
  linarith

/-- `max C(ηf) 9 ≤ C1P6`（上两条的合取）。消费者：STAB4 `fineGood_implies_fineMarginGood_P6ST4` /
`fineMarginGood_of_neck_P6ST4` 的 `hC1 : max C1 9 ≤ C1'`，`C1 := C(ηf)`、`C1' := C1P6`。 -/
theorem max_fine_le_C1P6_C11CL2 (Γ : ClosedBirthConstants) :
    max (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) 9 ≤
      C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ :=
  max_le (coarseFine_le_C1P6_C11CL2 Γ) (nine_le_C1P6_C11CL2 Γ)

/-- hcapW 常数（Good 精度 `ε` 处）：`Cs(ε) ≤ C1P6`。消费者：HCAPW `hcapWL_of_records_P6HB` /
`hcapW_of_standardClose_P6CW` 的 `Cs ≤ C1`（HbdLate `hcapWL` 槽 `(ε, C1, C2)`）；GT6
`capWitness_at_C1P6std_C11GT6`（GT6 `capCs_le_C1P6std` 的别名）。 -/
theorem capCs_le_C1P6_C11CL2 (Γ : ClosedBirthConstants) :
    p6CapCs_C11GT6.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ :=
  capCs_le_C1P6std_C11GT6 Γ

/-- 旧 ceiling 下界层：`C1ceil Γ ≤ C1P6`。消费者：S16 shared ceiling / native canonical S4 S5 的常数
（`HistoryCanonicalSupply_C11S` 经 `oldC1_le_C1P6_C11GT6`，CX-OUTER `outerSupply_ceiling_CXOU`）。 -/
theorem C1ceil_le_C1P6_C11CL2 (Γ : ClosedBirthConstants) :
    C1ceil_C11SC.{u} Γ ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ :=
  C1ceil_le_C1P6_C11GT6 _ Γ

/-! ## 2. `C2` 侧 -/

/-- Good 区精度处 coarse kernel：`C(ε) ≤ C2P6`。消费者：`goodConstants_accommodate_P6P` (ii)
（GT6 `coarse_le_C2P6std` 的别名）。 -/
theorem coarse_le_C2P6_C11CL2 (Γ : ClosedBirthConstants) :
    p6CoarseC_C11GT6.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  coarse_le_C2P6std_C11GT6 Γ

/-- 坏点精度 `ηf` 处 coarse kernel：`C(ηf) ≤ C2P6`。消费者：RERUN8 `hC2 / hK2`（`η₁ := ηf`，`C2₁` 取到
ceiling）；STAB4 改善定理的 `hC2 : C2 ≤ C2'`（`C2 := C(ηf)`、`C2' := C2P6`）。 -/
theorem coarseFine_le_C2P6_C11CL2 (Γ : ClosedBirthConstants) :
    p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤
      C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ := by
  have h1 := one_le_p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)
  have h2 := thousand_mul_fine_le_C2P6std_C11GT6.{u} Γ
  linarith

/-- fine recovery + transfer 损失：`1000 · C(ηf) ≤ C2P6`。消费者：STAB2
`spatialWitness_of_bufferedTransfer_P6ST2` 的 `h2 : 1000 * C2 ≤ C2out`（`C2 = C(ηf)`）；STAB4
`frequently_neck_free_P6ST4` 的 `h2`（GT6 `thousand_mul_fine_le_C2P6std` 的别名）。 -/
theorem thousand_mul_fine_le_C2P6_C11CL2 (Γ : ClosedBirthConstants) :
    1000 * p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤
      C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  thousand_mul_fine_le_C2P6std_C11GT6 Γ

/-- hcapW 常数（Good 精度 `ε` 处）：`Cs(ε) ≤ C2P6`。消费者：HCAPW `hcapWL_of_records_P6HB` 的
`Cs ≤ C2`；GT6 `capWitness_at_C1P6std_C11GT6`（GT6 `capCs_le_C2P6std` 的别名）。 -/
theorem capCs_le_C2P6_C11CL2 (Γ : ClosedBirthConstants) :
    p6CapCs_C11GT6.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  capCs_le_C2P6std_C11GT6 Γ

/-- 旧 ceiling 下界层：`C2ceil Γ ≤ C2P6`。消费者：同 `C1ceil_le_C1P6_C11CL2` 的 `C2` 侧
（`oldC2_le_C2P6_C11GT6`）。 -/
theorem C2ceil_le_C2P6_C11CL2 (Γ : ClosedBirthConstants) :
    C2ceil_C11SC.{u} Γ ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  C2ceil_le_C2P6_C11GT6 _ Γ

/-! ## 3. 时间侧（RERUN8 `hCt` 的形：`(p6CoarseC ·).toNNReal ≤ Ctime₁`） -/

/-- Good 精度处：`(C(ε)).toNNReal ≤ (C1P6).toNNReal`。消费者：RERUN8 `hCt` 在 Good 区精度取到
`C1P6` 作 `Ctime` 的写法（`Real.toNNReal` 单调）。 -/
theorem coarseTime_le_C1P6_C11CL2 (Γ : ClosedBirthConstants) :
    (p6CoarseC_C11GT6.{u} Γ.epsilon).toNNReal ≤
      (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ).toNNReal :=
  Real.toNNReal_le_toNNReal (coarse_le_C1P6_C11CL2 Γ)

/-- 坏点精度 `ηf` 处：`(C(ηf)).toNNReal ≤ (C1P6).toNNReal`。消费者：RERUN8 `hrerunE8_P6R8` /
`hrerunF8_P6R8` / `hbd8_P6R8` 的 `hCt / hKt`（`Ctime₁ := (C1P6 X1 Γ).toNNReal`）。 -/
theorem coarseFineTime_le_C1P6_C11CL2 (Γ : ClosedBirthConstants) :
    (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal ≤
      (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ).toNNReal :=
  Real.toNNReal_le_toNNReal (coarseFine_le_C1P6_C11CL2 Γ)

/-- `C2` 侧：`(C(ε)).toNNReal ≤ (C2P6).toNNReal`。消费者：`Ctime₁ := (C2P6 X2 Γ).toNNReal` 的 `hCt` 写法。 -/
theorem coarseTime_le_C2P6_C11CL2 (Γ : ClosedBirthConstants) :
    (p6CoarseC_C11GT6.{u} Γ.epsilon).toNNReal ≤
      (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ).toNNReal :=
  Real.toNNReal_le_toNNReal (coarse_le_C2P6_C11CL2 Γ)

/-- `C2` 侧：`(C(ηf)).toNNReal ≤ (C2P6).toNNReal`。消费者：RERUN8 `hCt / hKt`
（`Ctime₁ := (C2P6 X2 Γ).toNNReal`）。 -/
theorem coarseFineTime_le_C2P6_C11CL2 (Γ : ClosedBirthConstants) :
    (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal ≤
      (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ).toNNReal :=
  Real.toNNReal_le_toNNReal (coarseFine_le_C2P6_C11CL2 Γ)

/-- `ηf ∈ (0, 1/11)`：RERUN8 `hη : 0 < η₁ ∧ η₁ < 1 / 11` 在 `η₁ := ηf` 处。 -/
theorem fineEta_mem_C11CL2 (Γ : ClosedBirthConstants) :
    0 < p6FineEta_C11GT6 Γ.epsilon ∧ p6FineEta_C11GT6 Γ.epsilon < 1 / 11 :=
  ⟨p6FineEta_pos_C11GT6 Γ.epsilon_pos,
    (p6FineEta_le_C11GT6 Γ.epsilon).trans_lt (by linarith [(epsilon_mem_C11GT6 Γ).2])⟩

/-! ## 4. consumers -/

/-- consumer（RERUN8，D-15 固定 `η₁ := ηf`）：`hrerunE8_P6R8` 的三条常数前提
`hC1 / hC2 / hCt` 由本包供给，坏点常数 `(C1₁, C2₁, Ctime₁)` 取 ceiling 本身
`(C1P6 X1 Γ, C2P6 X2 Γ, (C1P6 X1 Γ).toNNReal)`。 -/
example (Γ : ClosedBirthConstants) {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g}
    (hεW : Γ.epsilon ≤ Classical.choose ObservedHistory.ancientWitness_decoupled_P6P.{u})
    (hεX : Γ.epsilon ≤ crossingWindowNeckAccuracy.{u})
    (hεN : Γ.epsilon ≤ crossingNeckAccuracy.{u}) (hεcone : Γ.epsilon ≤ coneAccuracy)
    {C1 C2 : ℝ} {Ctime : ℝ≥0} (hC2' : 0 ≤ C2) : True := by
  have _h := ObservedHistory.hrerunE8_P6R8 (F := F) (C1 := C1) (Ctime := Ctime)
    (fineEta_mem_C11CL2 Γ) Γ.epsilon_pos hεW hεX hεN hεcone (coarseFine_le_C1P6_C11CL2 Γ)
    (coarseFine_le_C2P6_C11CL2 Γ) (coarseFineTime_le_C1P6_C11CL2 Γ) hC2'
  trivial

/-- consumer（STAB4 neck 改善）：`(ηf, C(ηf), C(ηf))`-Good ⇒ `(ηf, C1P6, C2P6, 1/20)`-FineMarginGood，
或 witness 为 cap / whole-component 型；`hC1 : max C1 9 ≤ C1'`、`hC2 : C2 ≤ C2'` 由
`max_fine_le_C1P6_C11CL2` / `coarseFine_le_C2P6_C11CL2` 供给。 -/
example (Γ : ClosedBirthConstants) {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {g : SmoothRiemannianMetric I3 M}
    {x : M}
    (hgood : ∃ W : SpatialCanonicalWitness g (p6FineEta_C11GT6 Γ.epsilon)
      (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon))
      (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) x,
      W.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon)) :
    (∃ W' : SpatialCanonicalWitness g (p6FineEta_C11GT6 Γ.epsilon)
        (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ) (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) x,
      W'.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon) ∧ W'.HasMargins (1 / 20)) ∨
      ∃ W : SpatialCanonicalWitness g (p6FineEta_C11GT6 Γ.epsilon)
        (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon))
        (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon)) x,
      W.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon) ∧
        ((∃ c d, W.alternative = .cap c d) ∨ W.domain.carrier = connectedComponent x) :=
  fineGood_implies_fineMarginGood_P6ST4 le_rfl (fineEta_mem_C11CL2 Γ).2
    (max_fine_le_C1P6_C11CL2 Γ) (coarseFine_le_C2P6_C11CL2 Γ) le_rfl hgood

/-! ## 5. ceiling v2（R-C11-10 D-15′，O-CH11-CEIL3，后缀 `_C11CL3`） -/

/-- 精度方向：`13000 · η₁ ≤ ηN := neckModelTolerance (ε/2)`。消费者：CX-CAPCORE
`exists_hasMargins_of_cap_CXCC` 的 `hη : 13000 * η ≤ η'`（`η := η₁`、`η' := ηfine := ηN`）。 -/
theorem thirteenK_mul_fineEta_le_C11CL3 (ε : ℝ) :
    13000 * p6FineEta_C11GT6 ε ≤ neckModelTolerance (ε / 2) := by
  have h : p6FineEta_C11GT6 ε ≤ neckModelTolerance (ε / 2) / 13000 :=
    (min_le_right _ _).trans (min_le_left _ _)
  linarith

/-- round transfer 精度前提：`η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊`。消费者：
`wholeComponent_round_transfer_P6SF` 的 `hsmall`（`ηfine := η₁`、`ηout := ε`）。 -/
theorem fineEta_le_bJS_C11CL3 (ε : ℝ) :
    p6FineEta_C11GT6 ε ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊ :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- `η₁ < ηN`：坏点精度严格细于 margin 层精度（STAB2 `ηfine_le` 取等号的 `ηN`）。 -/
theorem fineEta_lt_neckTol_C11CL3 {ε : ℝ} (hε : 0 < ε) :
    p6FineEta_C11GT6 ε < neckModelTolerance (ε / 2) := by
  have h1 := thirteenK_mul_fineEta_le_C11CL3 ε
  have h2 := p6FineEta_pos_C11GT6 hε
  linarith

/-- `1 ≤ c`（`c := p6FineC ε`）。 -/
theorem one_le_fineC_C11CL3 (ε : ℝ) : 1 ≤ p6FineC_C11GT6.{u} ε :=
  (one_le_p6CoarseC_C11GT6.{u} _).trans (le_max_left _ _)

/-- 坏点常数 `Cco η₁ ≤ c`（RERUN8B 固定实例 `C1₁ = C2₁ := Cco η₁`）。 -/
theorem coarseFine_le_fineC_C11CL3 (ε : ℝ) :
    p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε) ≤ p6FineC_C11GT6.{u} ε :=
  le_max_left _ _

/-- `Ccap η₁ ≤ c`（CEIL2 watch W1 预埋）。 -/
theorem capFine_le_fineC_C11CL3 (ε : ℝ) :
    p6CapCs_C11GT6.{u} (p6FineEta_C11GT6 ε) ≤ p6FineC_C11GT6.{u} ε :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- `Ccol ε ≤ c`（HCENP collar 常数，Good 精度）。 -/
theorem capCollar_le_fineC_C11CL3 (ε : ℝ) :
    capCollarCs_P6HE.{u} ε ≤ p6FineC_C11GT6.{u} ε :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- `2 · C1f ≤ C1P6`，`C1f := max c 9 + √c`（CX-CAPCORE 放大 `C1 ↦ max C1 9 + √C2`，`C1 = C2 = c`）。
消费者：STAB2 `spatialWitness_of_bufferedTransfer_P6ST2` 的 `h1 : 2 * C1 ≤ C1out`（fine 常数取 `C1f`）。 -/
theorem two_mul_fineCX_le_C1P6_C11CL3 (Γ : ClosedBirthConstants) :
    2 * (max (p6FineC_C11GT6.{u} Γ.epsilon) 9 + Real.sqrt (p6FineC_C11GT6.{u} Γ.epsilon)) ≤
      C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ :=
  le_trans (((le_max_left _ _).trans (le_max_right _ _)) : _ ≤ p6X1std_C11GT6.{u} Γ)
    (X_le_C1P6_C11GT6 p6X1std_C11GT6.{u} Γ)

/-- `C1f ≤ C1P6`（Good 层 `C1 := C1P6` 直接收 `C1f`-witness）。 -/
theorem fineCX_le_C1P6_C11CL3 (Γ : ClosedBirthConstants) :
    max (p6FineC_C11GT6.{u} Γ.epsilon) 9 + Real.sqrt (p6FineC_C11GT6.{u} Γ.epsilon) ≤
      C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ := by
  have h := two_mul_fineCX_le_C1P6_C11CL3.{u} Γ
  have h9 : (9 : ℝ) ≤ max (p6FineC_C11GT6.{u} Γ.epsilon) 9 := le_max_right _ _
  have hs := Real.sqrt_nonneg (p6FineC_C11GT6.{u} Γ.epsilon)
  linarith

/-- `c ≤ C1P6`。 -/
theorem fineC_le_C1P6_C11CL3 (Γ : ClosedBirthConstants) :
    p6FineC_C11GT6.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ := by
  have h := fineCX_le_C1P6_C11CL3.{u} Γ
  have hm : p6FineC_C11GT6.{u} Γ.epsilon ≤ max (p6FineC_C11GT6.{u} Γ.epsilon) 9 := le_max_left _ _
  have hs := Real.sqrt_nonneg (p6FineC_C11GT6.{u} Γ.epsilon)
  linarith

/-- `√c ≤ C1P6`。消费者：CX-CAPCORE 的 `m ≤ 1/(10 · C1 · √C2)` 与 `C1f` 中的 `√C2` 项。 -/
theorem sqrt_fineC_le_C1P6_C11CL3 (Γ : ClosedBirthConstants) :
    Real.sqrt (p6FineC_C11GT6.{u} Γ.epsilon) ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ := by
  have h := fineCX_le_C1P6_C11CL3.{u} Γ
  have h9 : (9 : ℝ) ≤ max (p6FineC_C11GT6.{u} Γ.epsilon) 9 := le_max_right _ _
  linarith

/-- `Ccap η₁ ≤ C1P6`（W1 触发时 final 侧 cap-window 在 `η₁` 处的 `Cs ≤ C1₁`，`C1₁ ≤ c`）。 -/
theorem capFine_le_C1P6_C11CL3 (Γ : ClosedBirthConstants) :
    p6CapCs_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ :=
  (capFine_le_fineC_C11CL3.{u} _).trans (fineC_le_C1P6_C11CL3 Γ)

/-- **HCENP `hCs1`**：`capCollarCs_P6HE ε ≤ C1P6 X1 Γ`（`ε := Γ.epsilon`）。消费者：
`hcenE_of_noShortcut_P6HE` 的 `hCs1 : capCollarCs_P6HE ε ≤ C1`（`C1 := C1P6 p6X1std Γ`）。 -/
theorem capCollar_le_C1P6_C11CL3 (Γ : ClosedBirthConstants) :
    capCollarCs_P6HE.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ :=
  (capCollar_le_fineC_C11CL3.{u} _).trans (fineC_le_C1P6_C11CL3 Γ)

/-- `1200000 · c ≤ C2P6`（X2 中项）。 -/
theorem mul1200k_fineC_le_C2P6_C11CL3 (Γ : ClosedBirthConstants) :
    1200000 * p6FineC_C11GT6.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  le_trans (((le_max_left _ _).trans (le_max_right _ _)) : _ ≤ p6X2std_C11GT6.{u} Γ)
    (X_le_C2P6_C11GT6 p6X2std_C11GT6.{u} Γ)

/-- `1000 · C2f ≤ C2P6`，`C2f := 1200 · c`（CX-CAPCORE 放大 `C2 ↦ 1200 · C2`）。消费者：STAB2
`spatialWitness_of_bufferedTransfer_P6ST2` 的 `h2 : 1000 * C2 ≤ C2out`（fine 常数取 `C2f`）。 -/
theorem thousand_mul_fineCX_le_C2P6_C11CL3 (Γ : ClosedBirthConstants) :
    1000 * (1200 * p6FineC_C11GT6.{u} Γ.epsilon) ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ := by
  have h := mul1200k_fineC_le_C2P6_C11CL3.{u} Γ
  linarith

/-- `c ≤ C2P6`。 -/
theorem fineC_le_C2P6_C11CL3 (Γ : ClosedBirthConstants) :
    p6FineC_C11GT6.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ := by
  have h := mul1200k_fineC_le_C2P6_C11CL3.{u} Γ
  have h1 := one_le_fineC_C11CL3.{u} Γ.epsilon
  linarith

/-- `Ccap η₁ ≤ C2P6`。 -/
theorem capFine_le_C2P6_C11CL3 (Γ : ClosedBirthConstants) :
    p6CapCs_C11GT6.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  (capFine_le_fineC_C11CL3.{u} _).trans (fineC_le_C2P6_C11CL3 Γ)

/-- **HCENP `hCs2`**：`capCollarCs_P6HE ε ≤ C2P6 X2 Γ`。消费者：`hcenE_of_noShortcut_P6HE` 的
`hCs2 : capCollarCs_P6HE ε ≤ C2`（`C2 := C2P6 p6X2std Γ`）。 -/
theorem capCollar_le_C2P6_C11CL3 (Γ : ClosedBirthConstants) :
    capCollarCs_P6HE.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  (capCollar_le_fineC_C11CL3.{u} _).trans (fineC_le_C2P6_C11CL3 Γ)

/-- consumer（STAB2 + CX-CAPCORE，v2）：margin 层 `(ηN, C1f, C2f)` 的 buffered transfer 合同 ⇒ 输出 witness
在 `(Γ.ε, C1P6, C2P6)`（标准）处；`h1 / h2` 由 `two_mul_fineCX` / `thousand_mul_fineCX` 供给。 -/
example (Γ : ClosedBirthConstants) {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E : MetricCutCapEvent P Q a s} {p : P.Carrier} {q : Q.Carrier} {m : ℝ} {k : ℕ}
    (D : E.BufferedTransferData_P6ST2 p q (neckModelTolerance (Γ.epsilon / 2)) Γ.epsilon
      (max (p6FineC_C11GT6.{u} Γ.epsilon) 9 + Real.sqrt (p6FineC_C11GT6.{u} Γ.epsilon))
      (1200 * p6FineC_C11GT6.{u} Γ.epsilon) m k) :
    ∃ W : SpatialCanonicalWitness E.outputMetric Γ.epsilon
        (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ) (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) q,
      W.capTubeHasNeckChart Γ.epsilon :=
  E.spatialWitness_of_bufferedTransfer_P6ST2 D (two_mul_fineCX_le_C1P6_C11CL3 Γ)
    (thousand_mul_fineCX_le_C2P6_C11CL3 Γ)

/-- consumer（HCENP，lead 18:1x）：`hcenE_of_noShortcut_P6HE` 在 `ε := Γ.epsilon`、
`C1 := C1P6 p6X1std Γ`、`C2 := C2P6 p6X2std Γ` 处，`hCs1 / hCs2` 由 `capCollar_le_C1P6_C11CL3` /
`capCollar_le_C2P6_C11CL3` 付掉，只剩 `hrec`。 -/
example (Γ : ClosedBirthConstants) {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {Ctime : ℝ≥0} {C1f C2f m : ℝ} {kk : ℕ} : True := by
  have _h := hcenE_of_noShortcut_P6HE (Ctime := Ctime) (C1f := C1f) (C2f := C2f)
    (m := m) (kk := kk) F (epsilon_mem_C11GT6 Γ).1 (epsilon_mem_C11GT6 Γ).2
    (capCollar_le_C1P6_C11CL3 Γ) (capCollar_le_C2P6_C11CL3 Γ)
  trivial

end GC.LongTime.Ch11
