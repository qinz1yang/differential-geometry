# Codex 四车道分派（E3 / F / H / S）— 2026-09-20

分派人：Claude（Fable 5.1，lead）。检出 `D:\differential-geometry-moise-int`，分支
`codex/moise-integration`。各车道此前在做什么一律不管，以本文件为准。验证、编译、审计用你们
自己的 workflow；本文件只规定**任务、文件所有权、验收标准、报告格式**。

先读：`HANDOFF_CODEX_LEMMA2_20260920.md`（自 `76c6478cc` 以来的全部变化、已证/未证、已发现的假
命题清单），再读本车道小节点名的 `consult/*-digest.md`。

## 0. 四条车道共用的硬规则

1. **文件所有权互斥。** 只改本车道小节"所有权"里列出的文件；新文件只建在列出的前缀下。需要
   别的车道的文件里的东西：在报告里提需求，不要自己改。**不要碰根聚合 `DifferentialGeometry.lean`**
   ——在报告里给出 import 行，由 lead 在验收时登记。
2. **不运行任何写入型 git 命令**（add/commit/push/checkout/stash/reset/restore/clean）。交回清单，
   由 lead 验收后按精确路径提交并同步 owner 的库。
3. **绝不为了可证而削弱陈述。** 被已证归约逐字消费的定义（`Moise352InwardPush`、`Moise352Open`、
   `LemmaTwoBufferedStatement`、`GeneralPositionInDoubleBufferedStatement`、`DescentStepStatement`、
   `NormalSingularCellData` 的字段、`PLCrossSeamReading` 的字段等）一个字不能动。
4. **重构 producer 只能"核心 + 包装"**：旧的公开名字保留**原陈述逐字不变**；新导出只能**追加**在
   结论末尾，不许在合取中间插入、重排或删除。
5. **非空性是强制的。** 每个新 `structure` / `Prop` 值的 `def` 必须有居留定理，并带**严格性**事实
   证明它不退化（"源严格大于管内部分"、"模型 cell 确实不单射"这一类）。
6. **先反驳后证明。** 每条新陈述先在量词极端处测试（空集、退化、容差极大/极小、`n ≠ 3`、两端
   重合……），并**读对象是怎么构造的**，不只读它的结论记录了什么。发现陈述为假 = 成功：给出
   反例并**停下报告**，不要绕过去修。本链上已有十条陈述这样被发现是假的（交接文档 §4）。
7. 家规（模块编译抓不到的）：无未使用的假设/实例绑定；`def`/`abbrev`/`structure` 名字不含下划线；
   新公开名全树唯一；行 ≤ 100 码点；每个公开声明和结构字段有 docstring；docstring 行不以裸
   `structure`/`instance`/`theorem`/`def` 开头；无 `sorry`/`admit`/`native_decide`/新 `axiom`。
8. 书：`D:\differential-geometry-moise-plan\.lake\scratch\moise_gtm47.pdf`（书页 + 10 = 一基 PDF
   页）。**转述的书上条款在使用前要对页核实**——我们自己的清单里出过三处誊写错误。

## 1. 验收报告模板（每块砖一份，或每次交付一份）

```
车道 / 砖块编号 / 结论：done | partial | blocked | TARGET FALSE
文件：新建、修改（修改的逐个说明是否只追加、旧陈述是否逐字未变）
新公开名（完整名）；给根聚合的 import 行
最终陈述（Lean 原文，关键定理）
验证证据：聚焦编译结果；外部审计（13 个 linter、公理 ⊆ {propext, Classical.choice, Quot.sound}、
  聚合重名探针）；端点定理的类型断言（若是端点）
非空性：居留见证把参数实例化成了什么、严格性定理名
极端测试：测了哪些、各自结论
与本文件/顾问摘要的偏离及理由；剩余义务（精确到陈述）
```

---

## 车道 S — 边界支的带标记 PL 乘积管（二维核心 → 三维 block → 链）

**读：** `consult/B2-answer-digest.md`（全文）、`consult/B-answer-digest.md`（Lemma A–C）。
**所有权：** `FourSpoke*.lean`（含工作区里两个**未验证草稿** `FourSpokeAbstract.lean`、
`FourSpokeSectorFrontier.lean`——续写或删除）；新文件前缀 `MarkedCone*`、`MarkedLink*`、
`MarkedArcChain*`、`BoundaryAdaptation*`、`CrossDiskIsotopy*`。不改任何已提交文件。
**已有：** `FourSpokeDisk.lean`（平面 T₄）、`FourSpokeSector.lean`、`FourSpokeSquareWitness.lean`、
`DerivedCellSubcomplex.lean`；未标记的现成骨架 `ArcCellGluing.lean:48`、`ArcChainCells.lean:53`、
`ArcCellNormalizationInduction.lean:19`、`ConeDiskPairExtension.lean:20`。

砖块（按序；每块先反驳后证明）：
- **S1 平面 T₄-cap**（B2 摘要同名定理）。修正：假设 `T i ∩ frontier E = {w i}` **不蕴含**四个
  `w i` 在 `∂E` 上的循环序与 `v i` 在 `∂D` 上一致，须在 `frontier E` 上也带一条 cut-pair 假设；
  **先弄清它与 `frontier D` 上那条的关系**（互推？独立？会矛盾吗？），只保留需要的。模型实例：
  `fourSpokeSquare` 里的半尺寸方块。
- **S2 抽象 PL 2-球版本**：T₄、T₄-cap 对 `D = u '' D₀`（`u` PL 同胚，`D₀` 平面四辐条盘）成立；
  边界一律用**内蕴边界**，不用 ambient frontier。
- **S3 Theorem C**（四页带标记的锥延拓，two-cap 形式：出口圆盘的映射是**产出**不是给定）。必须
  同时携带**两种页标签** `a, b : Fin 4 → Bool`（原片划分与弯片划分）——单个 `Bool` 不够。
- **S4 Theorem E**（端点锥）：link 圆盘对应模型盒的**顶面加四壁** `L_* = (Q×{1}) ∪ (∂Q×[0,1])`。
- **S5 带标记 link 的搬运**（B2 摘要 Theorem B2）+ derived cell 底面的自然性
  `B_K(s) ∩ |L| = B_L(s)`（上一轮未交付，需要径向饱和论证）+ 端点 cell 的 (B4)。
- **S6 链定理**：给定具有 `ArcCellGluing`/`ArcChainCells` 相交模式的 cell、S3/S4 的标记数据、
  公共界面上标签一致 ⇒ `Φ : ⋃ C_j → Q × [0, m+1]`（B2 摘要 "Chain"）。
- **S7 Theorem A**（边界适配）：把 crossing 谓词里**存在量化**的半空间重新取卡，适配到实际的
  `(W, H)`；顾问的反例 `H = {t = −min(|x|,|y|)}` 说明现有 chart 里的等式是假的。
- S8（可选，若有余力）闭支用的 cross-disk 同痕引理（B 摘要末节；目标是 pair 的 PL 同痕，**不是**
  共轭到 `Prod.swap`——那是假的）。
**终点（本车道的长期目标）：** B 摘要的 Lemma C——由正规性 + 边界支 + `D(Δ) ⊂ W` +
`D(∂Δ) ⊂ Int_H B` 产出 `CrossSeamTubeData` + `PLSeamTubeChart` + 边/侧/端盘缓冲条款。

## 车道 F — 交叉重粘的 PL 读法与边界情形的接线

**读：** `consult/B2-answer-digest.md` 的 Theorem D 与 Corrections 7–8；
`LoopTheorem/CrossSeamResolvedCell.lean`、`CrossSeamReadingWitness.lean`、
`BoundaryCandidatesOfCut.lean`、`BoundaryCaseOfCut.lean` 的模块 docstring。
**所有权：** `LoopTheorem/CellGluing.lean`、`LoopTheorem/CutAndPaste.lean`、`BoundaryWordFourArcs.lean`、
`LoopTheorem/CrossRegluedCell*.lean`、`LoopTheorem/Boundary*OfCut.lean`（均按规则 4）；新文件前缀
`LoopTheorem/CrossRegluedSource*`、`LoopTheorem/BoundaryCaseFrom*`。
砖块：
- **F1 验收 `LoopTheorem/BoundaryCaseOfCut.lean`**（已聚焦编译通过，外部审计未完成）：审计、
  给出 import 行。
- **F2 源侧三片与接缝**：`V₁ = P' ∩ h⁻¹ P`、`V₂ = P' ∩ h⁻¹ Q`、`V₃ = Q'`，`F₁ = f₁∘h`、`F₂ = f₂∘h`、
  `F₃ = f₃`；证 `G = D ∘ F_i` 于 `V_i`、(D2) 四条相交式、(D3) 两条**逐点**接缝相容式。
  `crossRegluedPullback` 在接缝处**不连续**，不要经由它证 PL 性。
- **F3 原始 cross reglue 的 properness** `Δ' ∩ G⁻¹ H = ∂Δ'`：从源侧粘合证（`G` 在接缝上不正规，
  不能用正规性定理）。
- **F4 Theorem D**：四张源页 `Z₀…Z₃`（一张来自 `U₁`、两张不交的来自 `U₂`、一张来自 `U₃`）及其
  精确相交式 ⇒ `PLCrossSeamReading T.chart G`（对**真实的** `G`，给定一个 PL 管子
  `PLSeamTubeChart` 及其 neat 条款作为假设）。注意相邻配对是 (外 `A`)∪(中 `C`)、(中 `A`)∪(外 `C`)。
- **F5 覆盖条款变成推论**：取 `Ω₁ := e⁻¹(P)`、`Ω₂ := closure(S¹ \ Ω₁)`，由读法推出
  `hcocont hΩ₁tube hΩ₁max hlateral` 与闭性/覆盖，从 `…_of_plReading` 两个组装里去掉这 7 条假设。
- **F6 合并定理**：从**一个 cut** 出发（`exists_boundaryCandidates_of_cut`），把 13 条 cut 级导出
  也内部化；最终形状应是"存在两个候选，使得对交叉候选的任一管子 + 读法，结论成立"——因为
  管子/读法的假设要点名 `G`，请选最诚实的量词形状并在 docstring 里说明。
**验收重点：** 旧 producer 名字的陈述逐字未变（给 `git diff` 证据）；两个谓词模块仍能对着改过的
producer 编译。

## 车道 H — 跨坐标卡的一般位置（`GeneralPositionInDoubleBufferedStatement`）

**读：** `consult/C-answer-digest.md`（全文，尤其末节"对树的复核"与砖块 B1–B7）。
**所有权：** `SingularGeneralPosition.lean`、`GeneralPositionWithin.lean`、`SingularManifoldLocal.lean`、
`SingularChart.lean`、`LoopTheorem/ProjectedBoundaryLocalNormalization.lean`（规则 4；这些文件的反向
闭包极大，**优先在新文件里做推广版并让旧定理不动**，只有确实划算才改原文件）；
`LoopTheorem/SingularSet*.lean`；新文件前缀 `RelativeGeneralPosition*`、
`LoopTheorem/GeneralPositionInDouble*`。
砖块：
- **H1 验收** `LoopTheorem/SingularSetChartGerm.lean`、`SingularSetLocalModel.lean`、
  `SingularSetOfCell.lean`（已聚焦编译通过，审计未完成）。端点
  `SingularTwoCell.nonempty_normalSingularCellData_of_fields`：验收检查 = 用
  `hD.locallyInjective` 等五个字段**不经适配**直接喂给它的 `example`。有了它，一般位置**只需产出
  `crossing`**。
- **H2（B2）** 暴露 `SingularGeneralPosition.lean:1523` 的"任意顶点子集一般位置"（现被 `:1607`、
  `:3183` 丢弃）。
- **H3（B3）** 半空间链里把 `boundaryComplex 2 K` 推广为子复形 `L ⊆ boundaryComplex 2 K`
  （`ℓ∘f = 0 ↔ ∈ L.space`）：cut-out 片的**人工边界**不能被送进 `H`。内部卡的自由边界版本已存在
  （`:1317`）。
- **H4（B4）** cut-out 片 (10)：`f⁻¹(closure V₀) ⊆ Int_S P ⊆ P ⊆ f⁻¹(V)`，必须包含穿过该区域的
  **全部**片；重数在**整个源**上计。
- **H5（B5，大）** 相对版本：冻结已正规区域的一个 collar，`relDerived` 细分 + 相对顶点扰动。
  注意仿射无关的真正失败模式是来自两个**不相交**面的共线三点。**不要**"凡已正规处皆固定"
  （`{z=0}` 与 `{z=|x|+|y|}` 的反例）。
- **H6（B6）** 给定 `W ⋐ V` 的相对局部正规化定理（C 摘要式 (4)），**`W` 是事先给定的**——现有定理
  的 `W` 是围绕单个双重点、在 `V` 之后产出的小球，壳层无法变薄，驱动不了归纳。
- **H7（B7）** 有限覆盖归纳，不变量含 **`V_j ⊆ ⋃ᵢ Wᵢ`**（顾问原版不变量缺这条，是假的）；
  用 `NormalCrossingTransport.lean:215` 与 `DoublePointFibreAgreement.lean`。
- **H8 端点** `theorem … : GeneralPositionInDoubleBufferedStatement`（定义在
  `LoopTheorem/LemmaTwoBuffered.lean`，逐字）。边界同伦的轨迹须留在 `B` 内（式 (12)）；侧保持用
  适配到实际 `(N, H)` 的卡（式 (11)，`ProjectedBoundaryLocalNormalization` 已有）。

## 车道 E3 — 35.2 一侧：`Moise352Open 3` 的 §34 基础设施

**读：** `consult/A2-answer-digest.md`（全文）、`consult/A-answer-digest.md`、
`consult/A-section34-lemma-list.md`（**是我们自己的转述，用前对页核实**）、`Moise352OfOpen.lean`、
`OpenSourceReduction.lean`、`LabelledNormalization.lean`、`ToleranceControl.lean`、
`ChartLocalApproximation.lean`。
**所有权：** 只建新文件，前缀 `Moise308Nested*`、`LinkGraph*`、`MarkedCircle*`、`UniformBallExtension*`、
`SourceCutDiagram*`、`Section34*`。不改任何已提交文件。
砖块：
- **E3.1 正确的 30.8**：`def Moise308Nested`（A2 摘要原文）及其**证明**（壳给出强形变收缩；
  `π₁ J → π₁ S → π₁ S₂` 是无限循环群的同构 ⇒ 两个整数之积为 ±1），以及更小的消费者引理
  （`S ⊂ T` 实心环面、`J ⊂ S` 是 `T` 的 spine ⇒ `π₁ J → π₁ S` 同构）。先查树里实心环面的 `π₁ ≅ ℤ`
  有没有；没有就先做它。不改现有 `Moise308`（它是 30.8 **之前**的那条引理）。
- **E3.2 link 连通性**：有限三角剖分的 2-球面/2-圆盘 `L`，`G = L¹`：(Link-E) 去掉任一条边仍连通；
  (Link-V) 去掉任一顶点仍连通。
- **E3.3 标记圆扇区引理**（A2 摘要；顾问给了反例说明仅靠生成元和交叉数**定不了**标记点顺序）。
- **E3.4 统一延拓引理**：局部有限的 PL `d`-球族（`1 ≤ d ≤ 3`）沿已有 PL 同胚延拓，含关联条件
  `F(P_i ∩ P_j) = Q_i ∩ Q_j`；局部有限性取在 `K` 与**像 `Y`** 内（不是整个 `M₂`——那是假的）。
- **E3.5 源侧 cut diagram (SC1–SC3)**：开的局部有限三角剖分 3-流形里，1-骨架正则邻域的对偶球、
  分裂圆盘、`d_σ`、`Q_t`、`X_{tv}` 及其全部相交式与边界分解。这是 PL 正则邻域定理，不是逼近定理。
  树里已有 `DualCells.lean`（含 `isPLBall_dualCell`）。
- **E3.6 把 P0–P8 写成彼此独立、各自严格小于 35.2 的 `Prop`**，并证明组装
  `P0 ∧ … ∧ P8 → Moise352Open 3`（七个延拓阶段 + 插入的 2b 阶段用 E3.3/E3.4）。**陷阱：**任何一个
  节点若带着 `Moise352` 的结论，就是又一次 modus ponens——逐个说明为什么不是。顺序：先
  E3.1–E3.4（小而独立），再 E3.5，最后 E3.6。
