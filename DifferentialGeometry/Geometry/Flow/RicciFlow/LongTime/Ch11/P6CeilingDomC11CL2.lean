import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingC11GT6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RerunEvent8P6R8
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FineMarginImproveP6ST4

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

**范围**：本文件**不含** `2·Ccap(ηf)` / `1000·Ccap(ηf)`（G2 核实结论：当前无消费者，见
`build-logs/resume/state-S-CH11-CEIL2.md`）；不改 `P6CeilingC11GT6`；不触 v6fwd / hspine″ / hP6b′ 接口。
`η₁ < ηf` 时 `Cco` 不单调，故无对任意 `η₁` 的支配（D-15 的固定 `η₁ := ηf` 即为此）。
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

end GC.LongTime.Ch11
