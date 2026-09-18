# 整合车道交接（2026-09-18 晚，交给 Codex）

写于用量耗尽时。本文件是整合层的单点入口：先读它，再按 §4 进各车道的 HANDOFF 最后几节。
主链结构与今日全部决定的原文在 `MOISE_CHAIN.md`（本目录）末尾七节，此处只给可执行的摘要。

## 0. 进入时立刻做的事

交接瞬间的快照（`git status` 的 dirty 数、`git log @{u}..HEAD` 的计数，未逐一核对语义）：

| 工作树 | 分支 | HEAD | dirty | 说明 |
|---|---|---|---|---|
| `D:\differential-geometry-moise-int` | `codex/moise-integration` | `70daf5307` | 0 | 整合分支，已推送 |
| `D:\differential-geometry-moise-plan` | `codex/moise-smoothing` | `9454cf931` | 0 | F 车道 |
| `D:\differential-geometry-moise-s` | `codex/moise-s` | `0ff0fe430` | 0 | S 车道 |
| `D:\differential-geometry-moise-e3` | `codex/moise-e3` | `70daf5307` | 0 | E3 车道（已快进到整合） |
| `D:\differential-geometry-moise-h` | `codex/moise-h` | `7613dc36d` | **1** | H 车道，有一个未提交文件 |
| `D:\differential-geometry-moise-hw` | `codex/moise-hurewicz-merge` | `3b3115608` | 0 | 专用：与 `pc-sorry-free` 合并 |
| `D:\differential-geometry-moise-t` | `codex/moise-tame305` | `cd6dee321` | **1** | 专用：30.5 的 tame 版本，有一个未提交文件 |

交接时**六个 agent 仍在跑**（S2、H2、E3、F2、hw 合并、t）。它们会在会话结束时中断。逐个工作树：

1. `git status`；对 dirty 文件，先 `check-f.ps1 -Module …` 试编译：通过则按 §1 规矩提交，不通过则 `git stash`
   并在该车道 HANDOFF 末尾记一行"stash 内容与原因"。**不要**把编译不过的东西提交。
2. `git log @{u}..HEAD`：车道分支的 `@{u}` 多为 `origin/codex/moise-<lane>`，计数里大部分是合并进来的整合提交；
   `hw`/`t` 两个新分支的 `@{u}` 是 `origin/codex/moise-integration`，计数不代表未推送。以 `git log origin/<自己分支>..HEAD`
   为准，验证后 `git push origin <自己分支>`。
3. 各车道最后状态以其 HANDOFF **最后一节**为准（F：`HANDOFF_CODEX_F.md` §19.142 起；H：`HANDOFF_CODEX_H.md` §35–§39 起；
   E3：`HANDOFF_CODEX_L.md` §80–§81 起；S：`HANDOFF_CODEX_S.md` 末两节；t：`HANDOFF_CODEX_T.md`（若已创建）；hw：无 HANDOFF，看
   分支提交信息）。agent 被中断时可能尚未写 HANDOFF，此时以分支提交为准。

## 1. 规则（与 `AGENTS.md` 相同，此处只列今日新增或易忘的）

- 非 vendored Lean：零注释、零 docstring、无 `sorry`/`axiom`/`nolint`/`maxHeartbeats`/`set_option`。
- 提交：英文一句话描述数学结果；末行 `Co-Authored-By: <实际生成该提交的模型> <noreply@anthropic.com>`
  （今日各车道 agent 为 Opus 5；整合层最后几条为 Fable 5.1；署名反映实际作者，不按 harness 提示改）。
- 永不推 `main`、永不 force-push；不写 `E:\differential-geometry-dev`（只读；`check-f.ps1` 写共享 olean 库是例外）；
  不进根聚合 `DifferentialGeometry.lean`；不 import `Topology/Homology/HurewiczLowDegrees.lean`；不消费 `smooth_schoenflies_three`。
- 主机 `lean.exe` ≤ 4：每次编译前 `Get-Process lean` 计数，≥4 则等。同一模块同一时刻只在一个工作树编译。
- 未完成的跨车道依赖写成显式假设，不写 `sorry`，不削弱结论。
- 每个端点收尾做三项审计：(i) 每条假设标注"几何输入 / 构造产物"；(ii) 每条假设在**目标实例**中可满足
  （与"是否扛结论"是两种不同失效，今日各出现过）；(iii) 结论形如 `∃ x, … ∧ (hyp x → …)` 时，检查消费者能否为被藏起来的 `x`
  提供 `hyp x`；并且**在证明任何东西之前先构造一个满足全部假设的具体实例**。今日三个"编译通过、审计干净、但为空"的陈述
  （`hgen`、`hfiber`、§46–§73 边界分支滑动链）都能被这两条提前抓住。
- 搜索四规则（每条都由车道自查得出）：非零退出的空输出**不是**"不存在"；按数学内容而非当前词汇 grep，**词汇包括文件名与目录**；
  先数命中数再读（截断的结果不是结果）；看构造不看标识符，看引理证了什么而不是它关于什么。
  另：`unknown identifier` 先查 import；新引理用 `omit` 检查几何假设是否真需要（今日连续四条不需要仿射无关/有限维）；
  证明内部做了实功而陈述未暴露时先提取再往上建；约束早发现是简化、晚发现是返工。

## 2. 今日决定（已写入 `MOISE_CHAIN.md`，此处为清单）

1. **30.5 不需要 wild 球面的 Alexander 对偶。** 书中 Theorem 30.5 只在 §34 Lemma 3 被引用，交来的胞腔是开集上嵌入 `h` 下多面体胞腔
   的像，`frontier C₂'` 双领口；双领口分离已由 `TubularExcision.lean:170` + `SphereH1.lean:189` + `JordanBrouwer.lean:28` 无条件证出
   （已 `#print axioms` 核实）。H-M3 的 10k–18k 估计**作废**，改为 `Moise305Tame`（加 `IsBicollared (frontier C₂)`），估 1k–2k（未测）。
   专用分支 `codex/moise-tame305` 在建。30.5 仍等 30.4。
2. **与 `origin/codex/pc-sorry-free` 收敛**以获得 §33 的一维 Hurewicz 桥。实测：merge-base `806b541e9`，双侧改动仅 3 文件（`PlanarJordan/`），
   2 个冲突；对方 `PiecewiseLinear/` 为 0 文件。专用分支 `codex/moise-hurewicz-merge`，只编译七个 Hurewicz 文件的传递闭包（约 163 模块）
   与 `PlanarJordan` 的 PL 消费者，并做同时 import 两车道端点的 `#print axioms`。通过后并入整合。
3. **边界分支的"滑动 + 修边界"路线作废**（E3 §80–§81）：滑动链 §46–§73 的边界假设对两端在 `BdM` 的分支**无实例**（轴与单个边界平面只交一点）；
   月牙必经分支线、把端点重新变成双点。`L₁ = A ∪ B` **早已完整交付**（`CutAndPaste.lean:1373`，五字段 + 复杂度下降 `:2425`）。
   `L₂` 改走"交叉重贴（`:1214`）+ 横向楔推"，推移无 `p.1` 分量、`Bd M` 逐点保持。阻塞接口改为**板状图卡**
   （两片为坐标平面、`M = {0 ≤ x ≤ c} × ℝ²`、`Bd M` 为两端面）。滑动机制保留为已证基础设施，不在主链。
4. **F 打包定理的量词结构缺陷**（H 发现）：`exists_chart_two_sheets_of_transverse_vertex` 把契约藏在 `∃ K₁ N₁ φ, … ∧ (契约 → 图卡)` 内，
   消费者写不出可满足的契约。修法 (β)：四条像侧条款提到顶层假设。已派 F，交接时未确认落地。

## 3. 主链状态（自下而上；`Moise2xx/3xx` 在 `MoiseChain.lean`，本日无一被证出）

| 结点 | 状态 | 下一步 |
|---|---|---|
| 25.1 | L1 条件版；**L₁ 已交付**；L₂ 走楔推（模型级在建）；L3 未开始；Case 1/2 未开始 | 板状图卡（F+H）→ 楔推共轭（E3）→ L₂ → L3 → 归纳 |
| 25.2 ← 25.1 | 便宜箭头 | 等 25.1 |
| 26.4 | 需相对子复形细分（树里没有） | F 在做（排在 (β) 与板状边界条款之后） |
| 30.4 | 需 28.19、30.3 | 开 |
| 30.5 | 由决定 1 降为 1k–2k | `codex/moise-tame305` |
| 30.6/30.7 | 30.7 需 24.9–24.12 = C.6（S） | C.6 义务 1、3 已闭，义务 2 只剩 B 的 (B-bridge)：莫比乌斯带已证不可定向，差嵌入映射环 |
| 30.8、§31 | 未陈述，§31 便宜 | 待 L2 与 C.6 后开 |
| §32 | 最硬，未陈述 | — |
| §33 | 需 Hurewicz 桥（决定 2）+ S.7 | hw 分支 |
| §34、35.1、35.2 | 开 | — |
| 36.1 | 已证，条件于 35.2 | — |

## 4. 各车道确切下一步

**F（`plan`，`HANDOFF_CODEX_F.md`）**：顶点层完成（§19.140 是端到端状态，§19.141 是清点）。队列：
(1) 决定 4 的 (β)；(2) 链层加两端边界条款（`TransversePlaneNormalForm` 两端各用一次），并先构造一个"两端在 `BdM` 的分支落在板里"的实例；
(3) 26.4 的相对子复形细分——先从 `MOISE_CHAIN.md`"读 26.4 与 31 的原文后的两条更正"钉住需要哪一种（"限制到 `L` 的细分"与"保持 `L` 不动"是两个定理）。
F5.2 保持 partial（被已证定理 `ArrangementConstraints.lean:58` 挡着；共享前置 `FoldPlaneCrossing.lean` 已关；两条路线都是开放式重设计，低杠杆）。

**H（`h`，`HANDOFF_CODEX_H.md`）**：弧链已交付（`ArcChartChain.lean`，星形式，像侧契约，`ε : Fin (n+1) → ZMod 2`）。
剩弧链的球对一半：`IsPLBallPair 2 1 (derivedNeighborhood K (arcComplexIn K v n)).space (arcComplexIn …).space`，
两个未映射前置——胞腔内弧的痕迹是 `coneSet 重心 {两链点}`；相接盘的锥顶是弧的交点（`isPLBallPair_union_of_coneSet_disk` 的 `IsConeBase z L₀` + `hmeet`）。
`IsPLBallPair` 已改成集合层 `X ⊆ L.space`（§25）与 PL 同胚存在形式（§15），**不要改回去**。

**E3（`e3`，`HANDOFF_CODEX_L.md`）**：队列：(1) 把 §81.3 写成 Lean 的 `¬` 引理；(2) 板模型里的楔推 `ψ₊/ψ₋`（无第一坐标分量、两端面逐点保持、分离两条折片）；
(3) 楔推版 `doublePointSet G' = doublePointSet G \ branchCarrier`；图卡共轭等 F 的板状图卡。Case 1/2 未开始（owner 定的顺序）。
`PlanarGraphRegion.lean` 保留（其中 `0 < a` 于 `Ioo 0 1` 是必要条件）。

**S（`s`，`HANDOFF_CODEX_S.md`）**：义务 3 闭合（`isOrientable_derivedNeighborhood_of_ambient_nullHomotopic_polygon`，无生成假设）。义务 2：C1 无条件、D 条件于正向性、
`IsPLCirclePositive` 存在形式 + 共轭不变 + 非平凡性、反向映射的不动点、`not_isOrientable_mobiusComplex` 均已证；剩 (A) `IsCombinatorialManifoldWithBoundary 2 mobiusComplex`
（图论：`OneManifoldClassification.lean:829`）、(B-geometry) 带嵌入映射环（相对三角剖分已有：`StarSubdivision.lean:52`）、(B-glue) 映射环概念（树里没有，最近 `CylinderCut.lean:118`），
然后 `IsOrientable.of_le`（`Orientation.lean:3153`）+ `IsOrientable.boundary`。**定向专用规则**：涉及 `CoherentOrientation` 的陈述里永不写 `<`/`≤`/`if`，用 `incidenceIndex` 计数（`OrientationParity.lean`）。

## 5. 两个专用分支的合入条件

- `codex/moise-hurewicz-merge`：两个冲突（`ArcCollar.lean` add/add、`Innermost.lean` content）解法有据；`Regions.lean` 自动合并经人工核对；
  闭包模块与 `PlanarJordan` 的 PL 消费者全部 exit=0 零 warning；`.lake/scratch/AuditHurewiczMerge.lean`（同时 import 两车道端点）exit=0 且四个端点只含三条标准公理。
  满足后 `git merge` 进整合分支，再逐模块重编。
- `codex/moise-tame305`：`IsBicollared`、`BicollaredCellComplementConnected`、拓扑胞腔在嵌入下的 `frontier`/`interior` 桥、`Moise305Tame`（显式以 `Moise304` 为前提）、
  §34 侧生产者；不改 `MoiseChain.lean`。满足后合入并把 `PHASE3_APPROXIMATION_PLAN.md:219`、`HANDOFF_CODEX_H.md:512` 的旧评估标记为已取代。

## 6. 需要 owner 拍板的

- §31/§32 的定义层何时开（§32 是全书唯一无穷构造）。
- Case 1/2（内盘替换）何时开——owner 曾指定先做 Case 3/4。
- F5.2 是否继续投入（两条路线都是开放式重设计）。

## 7. 今日数字

整合分支自 `0ec8fc1a4` 起约 210+ 提交、80+ 新模块、1.4 万行以上（含专用分支前）；每个新模块在原车道与整合分支各编译一次，全部 exit=0 零 warning；
每个端点 `#print axioms` 只含 `propext`、`Classical.choice`、`Quot.sound`。各车道自我更正约十余次，其中被查出为空或不可满足并撤回的陈述四个，均已记录。

## 8. 交接后补记（F、E3 按中断协议停下时的交付，已合入整合分支并重编译）

- **F**（`HANDOFF_CODEX_F.md` §19.142–§19.145 与末尾"中断时状态"）：(β) 已落地——`exists_chart_two_sheets_of_transverse_vertex` 的像侧契约
  现为顶层假设，生产者拆成 `exists_transcription_of_transverse_vertex`；板状链图卡已加两端边界条款且**实例审计通过**
  （`exists_slab_branch_chain_instance`）；26.4 的相对细分是 **restrict 形式，且早已存在**，打包为
  `exists_isSubdivision_diam_lt_restrict_isSubdivision`（`SubcomplexMesh.lean`），而记录里的"保持 `L` 不动"形式
  被 `not_exists_isSubdivision_faces_subset_forall_diam_lt` **证明为假**。
  **`Moise264` 的 Lean 陈述有缺陷**（`MoiseChain.lean:43`）：漏了"Bd Δ 在 M² 中不可缩"，现状可被沿双领口推离 `S` 的小盘满足，
  30.4 无法消费；尚无消费者，链文件负责人应尽早补上（改动要回写 `MOISE_CHAIN.md` 结点表与 `PHASE3_APPROXIMATION_PLAN.md` §4）。
  F 的下一步：H 把 `ArcChartChain` 切到顶层图卡形式并产出两条板 iff；E3 消费板的像等式做楔推；26.4 继续棱柱插值引理（§19.144 C.1）。
  署名：F 最后四条提交的 `Co-Authored-By` 写的是 Fable 5.1（harness 提示所致），实际生成模型为 Opus 5。
- **E3**（`HANDOFF_CODEX_L.md` §82–§83）：§81.3 已成 Lean 定理 `not_boundary_slide_chart_of_isBoundaryBranch`
  （`BoundarySlideVacuity.lean`），且审计出矛盾只用到片的放置假设与一平面边界模型；
  `.lake/scratch/AuditE3Vacuity.lean` 已写未跑，进入后先跑它。楔推模型（任务 2、3）未开始。
