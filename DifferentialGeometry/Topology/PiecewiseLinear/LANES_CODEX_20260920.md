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
   新公开名全树唯一；行 ≤ 100 码点；无 `sorry`/`admit`/`native_decide`/新 `axiom`。
   **文档口径以本检出的 `AGENTS.md` 为准（owner 2026-09-20 裁定）：** 非 vendored 的 Lean 源码
   **不写行内注释、不写声明 docstring**；只保留必需的版权/作者头和紧跟 import 之后的模块
   docstring（简洁、数学化；模块 docstring 的行不以裸 `structure`/`instance`/`theorem`/`def`
   开头）。上一任 handoff 里"每个公开声明都要 docstring"的说法作废。Claude 车道今天提交的文件
   带有声明 docstring，属于历史遗留：**不要为此做批量清理**（会触发大范围重编译）；只有当你因
   本车道任务本来就要修改某个文件时，顺手把该文件的声明 docstring 去掉，并把其中不可丢的数学
   说明（假设清单、反例记录）并入模块 docstring 或相应的 `.md`。
8. 每块砖的聚焦检查与审计输出都要**落盘**为 `.lake/scratch/Audit<砖块>.log`；若 workflow 支持
   环境 linter（Batteries `#lint`，排除 `docBlame`/`docBlameThm` 后的 13 个），一并运行并保存。
   lead 目前没有编译授权（所有 `claude-*` lease 处于 paused），验收只能以这些日志为准。
9. 书：`D:\differential-geometry-moise-plan\.lake\scratch\moise_gtm47.pdf`（书页 + 10 = 一基 PDF
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

### 车道 F 裁决（2026-09-20 晚）：F1 / F5 的两个组装 / F6 **不收**——`hlong` 不可满足

F2、F3、F4 已收。F5 的 `PLCrossSeamReading.exists_boundary_cover` 数学上认可，随 F8 一起收。
F1、F5 的两个 `…_of_plReading_of_boundaryCover`、F6 全部带假设
`hlong : Function.Injective ⇑(τ.trans (σ.trans φ))`（`τ φ : Path b a`、`σ : Path a b`）。这条
**不可能成立**：拼接路径在参数 `0` 与 `3/4` 都取 `b`，在 `1/2` 与 `1` 都取 `a`；preserving 情形以
回路 `φ.symm : Path a a` 起头。所以这些定理是空洞的，`BoundaryCut…Input` 无居留。这不是车道 F
引入的：错误在已提交的 `BoundaryWordWitnessOfCell.lean:210, 230` 与
`BoundaryCandidatesOfCut.lean:146–254`（Claude 车道写、lead 验收时漏掉）。模块 docstring 里
"`hσinj`、`hυinj`、`hlong` 均由 `exists_boundaryCandidates_of_cut` 产出"一句是假的：producer 给的是
**源圆周** `frontier D.domain` 上 `σ₀ τ₀ υ₀ φ₀` 的单射性，从不是 `X` 里字母的单射性。

不能靠把 `hlong` 减弱成"三个字母各自单射"来修：`τ·σ·φ` 的值域是 θ 图，值域 + 端点不决定同伦类
（`τσφ` 对 `φστ`）；preserving 情形两个字母是回路，值域连方向都不定。而且字母在 `X` 里**本来就
不必单射**（另一条边界支的两条原像弧都落在 `D₁` 里时 `D ∘ σ₀` 不单），所以 `hσinj`、`hυinj` 虽
可满足，在最终接线里也无法解除。

- **F7 源圆周上逐弧匹配的 witness（替换整层）。** 在 `frontier D.domain` 里比较，不在 `X` 里比较：
  候选胞腔在它的每条边界弧上等于 `D ∘ Fᵢ`，`Fᵢ` 是到四条源弧之一的同胚（cross：F2 的
  `V₁ V₂ V₃`、`F₁ = f₁∘h`、`F₂ = f₂∘h`、`F₃ = f₃`；direct：`exists_boundary_surgery_cell_of_cut`
  的 `hGdR hGdT`，不够就在 core 里追加导出）。`Fᵢ ∘ (单射源参数化)` 是 `frontier D.domain` 里
  值域等于 `σ₀`（或 `τ₀ υ₀ φ₀`）的单射路径，在**那里**用
  `Path.Homotopic.of_injective_of_range_eq` 得到与 `σ₀` 或其反向同伦；再沿实现
  `f : frontier D.domain → X`、`ρ (f z) = D z` 推到 `X`（`Path.map` + `Path.cast`），最后
  `hcomp` 拼接与循环旋转。长弧 `R` 的单射参数化要在两个接缝点处切成三段（先查 Mathlib 的
  `Path.subpath`/`Path.truncate`；没有就自己证"路径同伦于其三段子路径的拼接"）。
  **产出：** `BoundaryWordWitness Gd ρ (direct word)` 与 `BoundaryWordWitness G ρ (cross word)`，
  两种端点情形，带 `param = e ∨ param = neg.trans e`；假设里**不得出现** `X` 里任何路径的单射性。
  参数化方向的二分（`hend`）照旧吸收。
- **F8 重述 F1 / F5 / F6**：去掉 `hlong hσinj hυinj`，改接 F7。删除已提交的空洞定理
  `exists_of_fourArcMatch_*`、`exists_of_fourArcMatch_*_of_endpoints`、
  `exists_pair_of_fourArcMatch_*`（先 grep 确认无其它消费者）。`exists_of_twoArcMatch*` 是真的，
  可留。
- **F8 的形状约束（AGENTS.md 第 72–73、110 行）：** `BoundaryCutReversingInput` /
  `BoundaryCutPreservingInput` 是 proposition-valued hypothesis packaging，`BoundaryCutCandidates`
  是为缩短 binder 的 bundled context，owner 未授权——改成显式的 `∃ …, (导出) ∧ ∀ …, 假设 → 结论`。
  `let _ := I` 式的结论 def 一并去掉。
- **F7/F8 的非空洞验收：** 交一个文件外的 probe（不入库）或一条引理，说明 F8 最终定理的每条假设
  要么由 `IsBoundaryBranchCut` + `PLCrossSeamReading` + `PLSeamTubeChart` 的某个已证 producer
  给出，要么列在"仍是真义务"清单里并注明为什么可满足。对每条含 `Function.Injective` 的假设，
  写出它的居留者。

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

### 车道 E3 裁决（2026-09-20 晚）：E3.6 **不收**——`Section34StageContract` 无居留，端点空洞

`Section34StageContract.extend`：对**任意**正序列 `ε`、任意在 `coreSpace i` 上 `ε i`-接近 `h` 的 PL
嵌入 `g`，存在 `f`，`EqOn f g (coreSpace i)` 且在 `coreSpace (i+1)` 上 `ε (i+1)`-接近。取
`ε (i+1) < dist (g x₀) (h x₀) < ε i`（`x₀ ∈ coreSpace i`）：`f x₀ = g x₀`，结论不成立。再取 `ε` 很大，
它又是"任何 PL 嵌入都可延拓"（打结实心环面，Alexander）。所以 P8 为假、`Section34Contracts` 为假、
`section34Open_of_contracts` 空洞。它消费的 `exists_isPLHomeomorphInto_dist_lt_of_stages` 正是本树
**已经记录为不可用**的那条（`CONSULT_QUEUE_20260920.md:163–221`、
`CompactRelativeApproximation.lean:50`：`Moise352Stages` 迫使 `f = h`；`Moise352StageStep` 也假；
修好的子句又装配不起来）。A2 摘要第 125 行写明：§34 是"有限改动地构造**块**，**不是**逼近映射的塔"；
第 82–83 行：七个阶段是在**整个**局部有限族上一次完成的 PL 延拓 E1–E7，误差估计**只**来自载体包含
(C1) `h(C_v) ∪ V_v ⊂ H_v`、`h(Q_t) ∪ R_t ⊂ H_t` 与 `diam H_α < η`，没有任何 `ε` 序列。

- **第二处独立的假：P0 的载体按塔的阶段 `i` 编号——对任何 `η` 都无居留。** 取 `x ∈ coreSpace k`；`coreSpace`
  递增，所以 `x` 属于其后所有阶段，`carrierCore` 给出 `h x ∈ carrier i`（一切 `i ≥ k`），与
  `LocallyFinite carrier`（点有限）矛盾，还没用到小性。（lead 原先的小性论证把量词写反了：塔依赖 `η`，
  必须先固定 `U` 中两点再取 `η`；D 答复指出，已改。）A2/D 里载体 `H_α` 按局部有限三角剖分的**单形 `α`** 编号。
- **E3.6′ 重做装配**：删掉 `Section34StageContract`、`exists_stage_maps`、`exists_approximation`。
  P8 的产出是**块与关联式**（(V)、(TT)），不是阶段映射。装配定理内部用 E3.3（阶段 2）、E3.4（阶段
  2b–7，局部有限族一次延拓）把 E1–E7 真的做出来，得到 `f : U → M₂` PL 嵌入；`dist (f x) (h x) < φ x`
  由 (C0)+(C1) 推出（`x ∈ Q_t ⇒ f x, h x ∈ H_t`，`diam H_t < η`）。如果这一步暂时做不完，就交
  `P0 ∧ … ∧ P8 ∧ (E1–E7 的某几步) → Moise352Open 3`，但每个留下的节点必须过下面的检查。
- **每个 P_i 的验收检查（写进报告）**：(a) 在极端处取值——大 `ε`/大 `η`、相邻阶段、空/单点族；
  (b) 说明它为什么不蕴含"任意 PL 嵌入可延拓"或"`h` 本身是 PL"；(c) 指出 A2 摘要里它对应的行。
- E3.1–E3.5 的文件（`Moise308Nested*`、`LinkGraphConnectivity`、`MarkedCircleSector`、
  `UniformBallExtension`、`SourceCutDiagram*`）**尚未收到验收报告与日志**，请按 §1 模板逐块补交。

### 车道 F 裁决之二：F7 三条里只有 reversing cross 可用

- `exists_of_sourceCrossMatch_preserving` **又是空洞的**：`φ₀ : Path p p`、`τ₀ : Path q q` 被要求
  `Function.Injective`——回路 `γ 0 = γ 1`，不可能。而且类型放错了层：**源圆周**上四条弧永远是
  `σ₀ : p→q`、`τ₀ : q→u`、`υ₀ : u→v`、`φ₀ : v→p`（四个不同的点），只有过了 `f` 之后
  （`f u = f q`、`f v = f p`）`τ`、`φ` 才成为 `X` 里的回路。结论的词也错了：preserving 的 cross 词是
  `σ.trans (τ.symm.trans (υ.trans φ.symm))`（真实边界是 `τ · σ⁻¹ · φ · υ⁻¹`：`σ₀`、`υ₀` 被**反向**
  走），不是 `D` 自己的词 `σ τ υ φ`。
- `exists_of_sourceArcMatch`（direct）可满足，但**套不上真实的 direct 候选**：它要求
  `P₀ : Path p q`、`Q₀ : Path q p` 共用两个源端点；真实的两条源弧是 `σ₀ : p→q` 与 `υ₀ : u→v`
  （reversing 时反向走 `υ₀`），四个端点互不相同。把第二条弧的端点放开成 `{p' q' : Q}`。
- 建议的形状：把 `pushSourceHomotopy` 公开成**单弧**引理，正向与反向各一条
  （`P₁ : Path q p`、`range P₁ = range P₀` ⇒ `P₁.map ≃ (P₀.map).symm`）；四个词（direct/cross ×
  reversing/preserving）各自用 `hcomp` + 循环旋转拼。整体参数化方向（`e` 或 `neg.trans e`）照旧二分。
- `BoundaryCaseFromCut.lean` 现在是 8 行 `export`，无内容——删文件。`BoundaryCaseFromSource.lean`、
  `BoundaryCaseFromReading.lean` 缺版权头与模块 docstring（AGENTS.md 第 80–81 行）。
- **F8 的"真实接口缺口"成立，授权改 core。** 在 `CellGluing`/`CutAndPaste` 的 cross 与 surgery 两个
  core 里**追加导出**（旧名字陈述逐字不变）：长弧 `R` 的单射源参数化 `ρ` 的两个接缝参数
  `t₁ < t₂`，以及三段上的逐点式 `G (ρ t) = D (F₂ (ρ t))`、`D (F₁ …)`、`D (F₂ …)`（F2 的
  `V₁ V₂ V₃`/`F₁ F₂ F₃` 已给出 `G = D ∘ Fᵢ`）；`T` 上 `G = D ∘ F₃`。需要独占窗口，先在
  `WORKING_STATUS`/lease 上协调。
- **验收新增一条（两次都栽在这里）：对每条 `Function.Injective` 假设，在端点 `0`、`1` 和每个拼接点
  处取值；对每个 `Path x x` 类型的对象，禁止出现单射假设。**

---

## 旧分支尾部盘点（2026-09-20 晚，lead 核对；对照本地 `codex/moise-integration` HEAD 的**内容**，不看提交数）

五条旧分支都停在 2026-09-19（最后 16:27），本地与 `origin` 同 SHA，**没有丢失风险**。integration 当时按
批次**拷贝文件**验收，不是 git merge，所以"未合并提交数"（29–48）没有意义；按 blob 比较：与 integration
不同或缺失的共约 15.6k 行，其中约 10.7k 行是各车道自己的 `HANDOFF_CODEX_*.md` / `MOISE_PLAN.md` 日志
（integration 从不收），根聚合 import 约 150 行，**Lean 约 4.3k 行**：

| 分支 | 未进 integration 的 Lean | 判定 |
| --- | --- | --- |
| `codex/moise-s` | 0（34 个 Lean 文件逐字相同） | 已全部并入，无事 |
| `codex/moise-e3` | 116 行，`LimitSeparation.lean` 里两个 `private` 模型引理；integration 的版本更新 | 可弃 |
| `codex/moise-304` | 19 个新文件 1836 行 + 30 行 | 主交付 `moise304_of_moise252` **已在** integration。尾部是 toroidal shell 计划（30.6/30.7 式：`ToroidalShell*`、`SurfaceIncompressibility`、`SurfaceEulerParity`、collared cover）——A2 答复明确"30.6–30.7 不需要"，E3.1 的 `moise308Nested` 不经它们：**对主链是沉没成本（约 1.1k 行）**。其中通用的 `Homology/HurewiczOne*`、`FundamentalGroupRank`、`Path*`、`FundamentalGroup/Torus`（约 750 行）可能在 P3/P4a 的 `H₁ → H₁(T_σ)` 满射条款处有用，到时再按批次验收，不现在收 |
| `codex/moise-h` | 7 个新文件 1671 行 + 43 行（35.1：局部有限支撑的 PL 修改、同胚塔极限、实心环面邻域） | **活的，但无人接手。** `Moise351` 在 integration 里仍是未证假设，P1 消费它，新路线没有绕开 35.1。尾部多为基础设施与 `…_model` 存在性例子，不是 `Moise351` 的 producer。注意 A2 摘要 P1："35.1 的任意输出不能冻结后宣称满足 (G)"——接手前先做一次只读 scoping，确认 `Moise351` 的陈述是否要改成受控版本 |
| `codex/moise-smoothing` | `HalfSpaceGeneralPosition.lean` +265、`HalfSpacePerturbation.lean` +323/−47 | **活的，且与新车道 H 正在做的事重叠。** 新增 `exists_small_homeomorph_generalPosition_off_polyhedron_in_halfSpace`、`…_with_chart_displacements`、`…_with_local_conjugates`、`exists_lipschitz_displacement_extending_vertex_perturbation_fixing_polyhedron_in_halfSpace`、`IsPiecewiseAffineOn.exists_polyhedron_lipschitz_displacement`——正是"半空间内、固定一个多面体的相对扰动"。对象是环境同胚而非奇异映射，但顶点扰动 + Lipschitz 延拓的引擎相同 |

**对车道 H 的指令（H0，先于 B4–B6）：** 读 `git show codex/moise-smoothing:…/HalfSpacePerturbation.lean` 与
`HalfSpaceGeneralPosition.lean` 的上述声明，报告哪些可直接复用于相对一般位置（替代你们新写的
`GeneralPositionInDoubleRelativeHalfSpace`/`…RelativePerturbation` 中的重复部分）；可复用的，作为对这两个已提交
文件的 append-only 批次交验收（检查 + 审计 + lint 日志）。这些尾部都只有作者自检，未经独立审计。

### 已合并：`codex/moise-304` 与 `codex/moise-h`（2026-09-20 夜，owner 指示；commit `daafbf482`、`13cbe0459`）

真正的 git merge，两条分支现在是 integration 的祖先。根聚合**没有**用 git 的文本合并结果（它会重复 34 条
import：车道在自己的位置登记过的模块，integration 已在末尾登记），而是 integration 自己的版本 + 末尾追加
26 条新 import。`PHASE3_APPROXIMATION_PLAN.md` 的唯一冲突是两边在同一处追加，两边都保留。

**状态：已合并，未重放。** lead 没有 compiler lease。合并时做过的源码级核对：26 个新模块 + 6 个被改的已提交
文件（`SurfaceEssentialDisk`、`FundamentalGroup/CollaredClosedCover`、四个 `TrivalentDualCell*`）的 import 闭包共
976 个模块，其中 integration 自 merge-base 以来只改过 `GeneralPosition`、`HeightProjection`、
`SingularGeneralPosition`，而被合并的模块没有引用那里签名变过的 21 个声明中的任何一个；无公开重名；无
`sorry`/`axiom`/`nolint`/`maxHeartbeats`/`set_option`/`native_decide`。车道自己的记录是"私有检查零诊断、13 项
linter、公理闭包合规"。这 6 个文件的反向闭包只有 `SurfaceCutKernel`、`SphericalShellCompression`、
`LemmaTwoSpine`、`LemmaTwoEndpoint`、`LemmaTwoBuffered`；四条在跑的车道的工作文件都不依赖它们，但这 11 个模块在
共享 build 里的 olean 现在相对源码是 stale 的。

**重放任务 R（任何持有 granted lease 的车道，空闲时做；不阻塞 F/H/S/E3 的砖）：** 对下列模块跑聚焦检查 +
审计 + lint，日志存 `.lake/scratch/{Check,Audit,Lint}ReplayM304H.log`，失败的逐条报告：
`Connected/{CollaredCover,RelativeClosedCover}`、`FundamentalGroup/{CollaredClosedCover,CollaredCut,CommutativeCover,Torus}`、
`Homology/{FieldCycles,PathConcatenation,PathHomotopy,HurewiczOne,FieldHurewiczOne,FundamentalGroupRank}`、
`Manifold/CylinderImage`、`PL/{SurfaceEssentialDisk,SurfaceIncompressibility,SurfaceEulerParity,ToroidalShell,
ToroidalShellFundamentalGroup,ToroidalShellSphere,ToroidalShellCompression,ToroidalShellHomology}`、
`PL/{TrivalentDualCellNeighborhoodModel,TrivalentDualCellPerturbationModel,TrivalentDualCellCompatibleTriangulation,
TrivalentDualCellTransportedNeighborhoods,TrivalentDualCellSolidTorusNeighborhoods,
TrivalentDualCellLocallyFiniteModification,LocallyFiniteHomeomorphTower,LocallyFiniteSupportedModification,
LocallyFiniteSolidTorusModification,SolidTorusOpenNeighborhood,CommonCircleSolidTorusTransport}`，以及下游
`SurfaceCutKernel`、`SphericalShellCompression`。这些模块的**陈述尚未经 lead 逐条阅读**（不在主链上）；谁要
消费其中任何一条，先按今晚的空洞检查读它的假设。

### Prompt D 的答复已回（`consult/D-answer-digest.md`）——四处空洞全部确认，三条车道的指令据此更新

**车道 E3（E3.6′ 的目标形状，取代上面的草案）：**
- 不要塔。终端装配 = **局部有限带标签 PL 胞腔装配定理**：同一分次面偏序集上的两族紧 PL 球 `(P_λ)`、`(P'_λ)`
  （维数 ≤ 3），边界 = 真面之并，`P_λ ∩ P_μ = ⋃_{ν ≤ λ, μ} P_ν`（两侧都成立），在各自并集内局部有限 ⇒ 存在把每个
  `P_λ` 映到 `P'_λ` 的 PL 同胚（按维数 1、2、3 归纳，每个球延拓只选一次；用局部有限闭粘合同时得到映射**和逆**）。
  这是 E3.4 `UniformBallExtension` + E3.3 的直接消费者，E1–E7 就是它的各行。
- `Section34FinalDiagram D η` := 上述源/靶胞腔数据（源并 = `U`）+ (C1) `h(C_v) ∪ V_v ⊂ H_v`、`h(Q_t) ∪ R_t ⊂ H_t`，
  **不含任何"存在映射"的字段**。端点：`(∀ D η, Nonempty (Section34FinalDiagram D η)) → Moise352Open 3`，误差由
  (C0c)+(C1)。
- P0 的控制条款：载体按单形 `α` 编号，控制支集 `S_α = ⋃_{v ∈ α} |St̄ v|`；(C0a) `h(S_α) ⊂ Int H_α`、`H_α ⊂ h(U)`；
  (C0b) `(H_α)` 在**子空间 `h(U)`** 内局部有限；(C0c) `∀ x ∈ S_α, ∀ y z ∈ H_α, dist y z < η x`。
  **P0 不得冻结 `N`**：P0 只定三角剖分、载体、缓冲与对源邻域的约束；`N, f₁` 由 P1 联合选取（或把 P0、P1 合并）。
- 各 P_i 的产出是**块与关联式**（表见摘要）；`h σ ⊂ Int C_σ` 压缩后不保留。
- 非空洞夹具：`h = id` + 足够细的标准三角剖分给出匹配的源/靶图；P4 的测试要另外引入一个可消去的 bigon / 边界指。

**车道 F：**
- 单弧引理用更强的形式：`P₁` 只需 `range P₁ ⊆ range P₀`，不需单射、不需值域相等
  （`P₁ = P₀ ∘ r`，`H (s,t) = P₀ ((1−s) r t + s t)`）；正向、反向各一条。
- 类型纪律：`τ₀ : q → u` 与 `σ₀ : p → q` 在源圆周里**不能拼接**（`u ≠ p`）；逐弧在源里比较 → 过 `f` → 才在 `X` 里拼。
  候选的证书按弧记录：落在哪条源弧、源端点的有序对（符号）、在该弧上与 `ρ ∘ f` 的逐点等式。
- `IsBoundarySurgeryCell.pullback` 是集合论选取，**不连续**，别拿它当连续映射用；direct 候选也走逐弧的连续 PL 映射。
- `Nonempty (BoundaryWordWitness G ρ w) ↔ Nonempty (… (w ∘ r))`（`r` 为反射）可把方向二分收成一条引理。
- **F10 结论强度缺口（已核对 `BoundarySurgeryCellPredicate.lean:339` 对 `LemmaTwoSpine.lean:124`）：** 边界情形
  组装只给出 surgery + 避开正规子群；`DescentStepStatement` 还要 `MapsTo Sg.cell … C`（侧）与边界缓冲
  `∀ z ∈ range Sg.cell.boundary, B ∈ 𝓝[Bd] z`。需要管子 producer 提供 `闭柱 ⊂ C`、`端盘 ⊂ Int_{Bd} B`，组装的结论
  据此加强（append-only 新定理）。
- **F11 联合夹具（D 答复称"下一个决定性的非空洞测试"）：** 一个定理同时实例化真实的正规边界支、它的 direct 与
  cross 候选、边界相对的 PL 管、PL 读法和两个边界词 witness。模型：preserving——`ℓ` 过
  `(2,0),(−1,0),(−2,−2),(0,−1),(0,2)`，`D (s,t) = (ℓ s, t)`，唯一二重点 `ℓ (2/3) = ℓ (10/3)`；reversing——
  `ℝ³/((x,y,z) ∼ (x+1,y,1−z))` 里 `D (s,t) = [s, |s − 1/2|, t]`。排在 F7/F8 之后。

**车道 S：** `IsCrossSeamTubeProducer` 缺 `[T2Space M]`，请在真实的 double 上陈述；Lemma C 的产出必须含
`闭柱 ⊂ C` 与 `端盘 ⊂ Int_{Bd} B`（F10 要消费）。

**四条车道共用的新纪律（加进验收）：** (a) 对**同一个共享元组**测试全部假设的合取，并带 `Nondegenerate` 子句
（非零复杂度 / 正误差 / 非 PL 的 `h`）；(b) 常备 `∀ γ : Path x x, ¬ Function.Injective γ`；(c) 容差探针：固定当前
界、令下一个界 → 0，以及粗容差 + 不可延拓嵌入；(d) 局部有限探针：指标类型、环境/子空间、对递增族查点有限；
(e) `∃ d, H d`、`∀ d, H d → ∃ o, C d o`、`∃ o, C d₀ o` 三者互不替代；恒等特化（如 `exists_of_twoArcMatch_self`）
不是居留者。

---

## 车道 C — 闭支（Moise p. 185，Case 1 / Case 2）；lead 于 2026-09-20 夜做的只读 scoping

**书上说的（PDF p. 195，已对页）：** Case 1：`Γ` 的完整原像是**一个**多边形 `J`，`D|J` 恰为二对一；取 `Γ` 的正则邻域
作柱形图，端面粘合 `(x,y,0) ∼ (y,x,1)`，把两张矩形换成 `x − y = ±1` 两个平面的截面，得到环带 `A'`，重定义
`D|A`。Case 2：原像是**两个**不交多边形 `J₁, J₂`；取 `J₁` inmost（它围的 2-胞腔里没有别的原像多边形），则 `Γ` 围出
`|D|` 里的嵌入 2-胞腔 `Δ₁`；把 `J₂` 的内部同胚地映到 `Δ₁`，再"推离 `Δ₁` 的一个邻域"。书里**只有这几句**。

**树里已有：** 选择定理 `NormalSingularCellData.exists_innermost_cleanDisk_of_exists_not_boundaryBranch`
（`LoopTheorem/InnermostCleanDisk.lean:221`）已经给出干净盘 `Q`（`frontier Q = J`，
`doublePointPreimage ∩ Q = J`，`D '' interior Q` 无二重点）**以及二分**：`branchPreimage c = J`（Case 1）或
`= J ∪ T`、`Disjoint J T`、`InjOn D Q`（Case 2）。还有：球的边界同胚延拓 `exists_isPLHomeomorphOn_of_frontier`
（`BallFrontier.lean:102`）；`DescendingSurgery.ofBranchInjection`（`LoopTheorem/BranchInjection.lean:301`）；
`SingularTwoCell.nonempty_normalSingularCellData_of_fields`（H1：`singularSet` 由五个字段推出）；模型层
`CylinderSplice`、`ClosedSeamResolution`、`ClosedBranchOrientability`。**缺的：** 从真实闭支到 `DescendingSurgery`
的一切；闭支目前没有任何 surgery 构造子。

**三个子情形，难度差别很大：**

| 子情形 | 需要什么 | 判断 |
| --- | --- | --- |
| **2a 嵌套**（`Q ⊂ interior E₂`，`E₂` 为 `T` 围的盘） | 只在源里剪贴：`G = D` 于 `E₂` 外，`G = D ∘ k` 于 `E₂`，`k : E₂ → Q` 延拓 `T → J` 的识别。**不需要管子，也不需要推离**（`J` 连同它外侧的一圈都在 `E₂` 里被覆盖掉了）。边界附近 `G = D`，三条不变量（侧、缓冲、避开子群）逐字继承 | **现在就能做**，约 0.8–1.5k 行 |
| **2b 不交**（`Q ∩ E₂ = ∅`） | 直接覆盖会让 `Δ₁` 整张盘成为二重点，必须沿平行曲线 cap off：取 `Δ₁` 的正则邻域球 `N`，`∂N ∩ |D|` 是三条平行圆（`X_out`、`Y_out`、`Y_in` 各一条），`∂N` 上由 `Y_out` 那条圆围出、不含另两条的盘 `Δ'` 满足 `Δ' ∩ |D| = ∂Δ'`；把 `E₂` 外扩到该圆的原像，映到 `Δ'` | 中等，约 1.5–3k 行；先 scoping：`SpanningDiskBallNeighborhood`、`SpanningDiskPrism`、`BicollarEmbedding` 能复用多少 |
| **Case 1**（连通二重覆盖） | 扭转圆盘丛管子：车道 S 的 S3（内部标记锥）+ S6（绕圆周闭合的链）+ S8（cross-disk 同痕，**不是**共轭到 `Prod.swap`）+ 映射环面等价，然后 `ClosedSeamResolution` | **现在做不了**，排在车道 S 之后 |

**砖块（每块先反驳后证明；每条强假设按 D 答复的纪律在端点/极端处取值）：**
- **C1 嵌套替换 cell。** 输入：选择定理的 Case 2 输出 + `E₂`（`IsPLBall 2 E₂`、`frontier E₂ = T`、
  `Q ⊆ interior E₂`）+ 识别 `g : T → J`（`IsPLHomeomorphOn`，`EqOn D (D ∘ g) T`——先查 `branchPreimage` 的 API 里
  有没有这条识别；没有就从 `InjOn D J`、`InjOn D T`、`D '' J = D '' T` 造）。产出 `G`：`G.domain = D.domain`、
  `EqOn G D (D.domain \ interior E₂)`、`EqOn G (D ∘ k) E₂`。**∀G 陷阱：** 用谓词 `IsNestedDiskReplacementCell hD c G`
  = 这个 producer 的**完整**结论（固定 `G`），不要只记几条性质。
- **C2 弯折处的局部单射。** `G` 在 `T` 的点处局部单射：`crossing` 字段给出 `Γ` 处四张半页只沿 `Γ` 相交；`G` 在 `T`
  两侧分别是 `Y_out`（`T` 外侧）与 `X_in = D(Q)`。**接点检验：** `T` 上 `D = D ∘ g` 保证连续；`E₂` 内部
  `G = D ∘ k` 单射（`InjOn D Q`）。
- **C3 二重点集 = 整支的并。** 每条别的支的每个原像分量连通且与 `J ∪ T` 不交，又不在 `Q` 里（干净），所以**整个**
  落在环带 `E₂ \ Q`（被覆盖掉）或整个在 `E₂` 外（保留）；`D '' interior Q` 无二重点 ⇒ 新映射不产生新二重点。故
  `doublePointSet G` 是若干**整条**旧支之并且不含 `c` ⇒ origin 单射、错过 `c` ⇒ `ofBranchInjection`。（对照
  `BranchDescent` 的警告：严格包含本身不够，这里靠的是"整支"。）纤维 ≤ 2 同理。
- **C4 2a 的组装：** `∃ Sg : hD.DescendingSurgery, MapsTo … C ∧ 缓冲 ∧ 避开子群`——后三条因 `G` 在
  `frontier D.domain` 的一个邻域上等于 `D` 而逐字继承（`c`、`δ` 原样可用）。结论形状直接对齐
  `DescentStepStatement`（`LemmaTwoSpine.lean:124`），别重蹈 F10 的覆辙。
- **C5 2b 的 scoping（只读）**，然后 C6 2b 的证明。
- **C7 Case 1**：等 S3/S6/S8。
- **非空洞夹具：** 2a——平面里一条自交一次的闭曲线上方的"帽子"模型，或直接取 `D(s,t)` 为一张盘与一个嵌套的浅碗相交
  成一个圆；要求复杂度 ≥ 1 且 Case 2a 的全部假设在**同一个**元组上成立。

**需要 owner 拍板的一点（会改变 Case 1 的工作量，但动公共陈述）：** `Moise252`（`MoiseChain.lean:36`）**本来就带**
`IsOrientable 3 K`，而 `LemmaTwoStatement` / `DescentStepStatement` 不带。在可定向的 `M` 里 Case 1 **不会发生**：给 `Δ`、
`M`、`J` 定向，对 `Γ` 上一点的有序原像对 `(a,b)` 取标架 `(t, n_a, n_b)` 的符号 `σ(a,b) = −σ(b,a) ≠ 0`；绕 `Γ` 一圈
`(a,b) ↦ (b,a)`，连续性给 `σ(a,b) = σ(b,a)`，矛盾。这个排除**不需要管子**（现有的
`IsCylindricalDiagram.not_closedBranchCase1` 需要先有柱形图）。若把可定向性沿塔传下去（可定向流形的覆盖仍可定向），
Case 1 整块可以删掉，闭支只剩 2a + 2b。代价：`NormalSystem` 世界的几条已证归约要带着这个假设重过一遍。
