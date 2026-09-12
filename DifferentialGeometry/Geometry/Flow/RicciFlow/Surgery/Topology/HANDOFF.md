# Topology and Comparison Maps across Surgery — 合作者交接

## 1. 范围与基线

请接手 `master05b.tex` 的 **`ch:rfs-topology`**，完成全部陈述、全部子结论及真实生产证明。此包在用户明确停止本轮证明推进后整理；没有再启动证明检查，也没有向合作者发送或启动新任务。

基线是 `E:/differential-geometry-dev`，分支 `codex/gradient-ricci-solitons`，提交 `804e9a8a7289f3b4de293aa34fffb5f52fb7d812`，Lean `4.33.1`。新文件和最后候选包含在快照中，不全在该提交里。逐文件 SHA256、直接证明债、注册状态和依赖见 [Inventory.md](Handoff/Inventory.md) 与 [Manifest.json](Handoff/Manifest.json)。

这是依赖完整仓库基线的工作包，不是自带 Mathlib 的独立 Lake 工程。把 ZIP 解压到空的审阅目录，先比较基线与接收分支；不要直接覆盖共享 checkout。包内的外部依赖、配置及旧树材料只供复核，不转移文件所有权。根书源摘录是 [BookSource.tex](Handoff/BookSource.tex)，包含本章完整正文、证明和状态说明；六项外部引用原文在 [ExternalInputs.tex](Handoff/ExternalInputs.tex)。保留原书宏，未承诺摘录能单独编译 LaTeX。引用始终使用 label。

## 2. 当前真实进度

- **17 个数学节点**：6 definition、5 lemma、4 proposition、2 theorem。主 crosswalk 为 **0 verified、16 conditional、1 not stated**。这是完整书节点状态；其中已经有许多完成的真实证明。
- **30 个已注册正式 Lean 文件，50 处直接 `sorry`**。数量来自去除注释、字符串后的源码扫描；不是传递公理审计、最小阻塞集合或工作量估计。完整清单在 inventory。
- 另有 `LinearOrientation.lean` 和 `ChartOrientation.lean` 两个未注册文件。前者独立 focused check 和具名 lint 构建通过，尚未做单独公理审计；后者最后修订版尚未检查。二者均未提交。
- 五个指定出口都已准确陈述，但仍有直接或传递的 `sorryAx`。本轮没有消除原 `Homology.lean` 的四项直接证明债，也没有升级书节点状态。
- 已完成的底层工作包括真实两开覆盖 SvK、带符号单形链和相对棱柱、同一坐标图内半径不变性、指定六单形 cubical Hurewicz 映射的边界/同伦/可加性，以及实际有限祖先递归与 observation restriction。应接续这些证明，不重建同义层级。

历史验收以同名 `.md` 中与源码 SHA 一致的最终 checkpoint 为依据。包内保留本轮检查及 Homology 最近一次审计的原日志；旧检查不等于接收方修改后的验证。当前所有工人已停止，REPL 正常关闭，本批普通文件 claims 已释放，原独占窗口已提前归还。

## 3. 五个指定出口

命名空间是 `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology`。下表说明验收重点；**完整量词、section hypotheses 和 Lean 签名以包内原 `.lean` 为准，不按摘要重写目标。**

| 书 label | 原生声明与文件 | 必须保持的内容及未完成部分 |
|---|---|---|
| `thm:rfs-child-comparison` | `Comparison.lean` · `rfs_child_comparison` | 全父 carrier 上固定的连续 degree +1 映射；所有 retained children 共用趋于 1 的 incoming modulus；core 上同一实际映射、晚时刻 Lipschitz、空子集情形。五项实际 exterior/support/pasting/degree/modulus 生产证明仍缺。 |
| `thm:rfs-finite-ancestry` | `Ancestry.lean` · `rfs_finite_ancestry`；`HistoryAncestry.lean`、`ObservationTower.lean` | 同一真实有限历史的唯一祖先链、定向与简单连通、指定 α/β 的输运与非零、原历史索引下的 restriction 相容。递归和实际 restriction 已有证明；仍依赖 parent/capping/class 生产结果。 |
| `prop:rfs-free-loop-class` | `FreeLoopClass.lean` · `rfs_free_loop_class`、`positiveFreeLoopClass_*`、`positiveFreeContractibleClass` | compact-open 自由环空间的连通/简单连通，指定 π₃→π₂Ω→π₂Λ，自由定向类、基点无关、非零及 degree +1 自然性。adjunction、evaluation/basepoint 等生产证明仍缺。 |
| `prop:rfs-homotopy-groups` | `LoopClass.lean` · `rfs_homotopy_groups`、`positiveHurewiczEquiv`；`Homology.lean` | closed connected simply connected oriented smooth 3-manifold 的 π₂=0、指定 π₃→H₃ 同构、实际定向正生成元。Hurewicz/duality 和四项 local/global orientation-class 生产证明仍缺。 |
| `prop:rfs-capped-simply-connected` | `CutCap.lean` · `rfs_capped_simply_connected`、`rfs_retained_capped_simply_connected` | 有限不交嵌入球面 cut/cap 后每个 component 简单连通，包含任意 retained 子集。真实球面分离、collar/cap 的 SvK 适配与有限归纳未闭合；不能假设一侧已经是球。 |

## 4. 文件责任与依赖边界

| 工作簇 | 文件 | 下一步 |
|---|---|---|
| 定向、同调、Hurewicz | `Background`, `Homology`, `Cohomology`, `LoopClass`, `OrientationDegree`；新 `LinearOrientation`、候选 `ChartOrientation` | 先接完局部定向类比较，再处理 local generator、global fundamental class、duality 和指定 Hurewicz 的复用桥。 |
| 基点与自由环 | `BasedTransport`, `LoopModel`, `FreeLoopClass`, `SphereSmash` | 真实路径输运、compact-open adjunction/evaluation、保定向 smash 与符号；下游 class 消费者保留。 |
| 切帽与 comparison | `VanKampen`, `CutCap`, `ChildParent`, `Comparison`, `WeakLength` | 实际球面分离、有限 cap、exterior/support、连续粘合与 local degree，最后 uniform incoming modulus。 |
| 真实历史 | `Descendants`, `AncestryCore`, `Ancestry`, `History*`, `ObservationTower` | 复用已经完成的递归、presentation、observation/restriction；按生产依赖消除传递债。 |
| 上游记录适配 | `StaticCap`, `EventData`, `GeometricCutoff`, `Recenter`, `Backward` | 保持 supplied record 的逐项实际对象及映射。手术几何主干的构造由另一车道负责；这里不假定本章输出。 |

工作范围为 `Surgery/Topology/`。`Extinction/Width/` 已独立交给合作者，`CurveShortening/`、`Families/` 及其他车道保持只读；不得让拓扑反向 import 宽度或灭绝。书中指向 `ch:rfs-disk-width`、`thm:rfs-width-lipschitz` 等是后续用途，不变成当前证明前提。

主要外部 supplied-record 边界是 `def:ssc-static-cap-witness`、`lem:rfs-weak-length`、`def:rfs-geometric-cutoff-record`。另有 `lem:rfs-cap-component-bijection`、`lem:svk-simply-connected-sphere-separates`、`cor:svk-sphere-sides` 的经典拓扑义务。输入记录的 native 流形/度量/映射和全量字段必须保持。不能用任意 parent function 或把五个出口塞进新 `Prop`/structure 参数代替它们的生产证明。

不修改 Shi、CanonicalNeighborhood、KappaSolutions、Compactness 等其他车道；不提交他人的工作区改动。根聚合和主 crosswalk 的集成由负责人处理。原有记录允许在明确指派的文件中填充 `sorry`，不允许改弱公开语义。

## 5. 立即接续的精确候选

### A. 正行列式线性同伦：已检查，但未完整验收

`LinearOrientation.lean` 的 `positive_linear_homotopy` 输入实际 `OrthonormalBasis (Fin 3) ℝ E`、`L : E ≃L[ℝ] E`、正行列式，输出从 L 到 identity 的真实连续同伦，且所有中间映射保持非零向量非零。路线是 Gram–Schmidt 的正三角变形，加上正等距映射的零次/两次非零反射分解。

精确 SHA256：`2B0C1C74D3F41EB094B5531DA5C0138A9B08E0CC20A2301BD01B1641481F70EB`。THIRD 独立 focused check 16.1 秒通过，具名 lint/artifact build 2397 jobs、目标 14 秒通过，无诊断或 style 警告。**尚未 `#print axioms`，也未注册/提交。**不要因失败证明曾出现 unused-variable 警告而删除公开 `[FiniteDimensional ℝ E]`；保留原签名。

### B. 不同正向坐标图比较：最后修订未检查

`ChartOrientation.lean` 精确 SHA256：`9DA2D099740896AACB9EDB57C32AEA2946ED9EF4C8B7472ADAC3207ABFB3C39F`。目标为 `OrientedChartSimplex.localClass_eq_of_positive_charts`，从而消除**原** `exists_unique_localOrientationClass` 的 `sorry`。这是最后 source-written 候选，没有任何通过声明。

路线：实际 centered chart transition 的中心导数 → 从非线性映射到导数的避零 blend → 共同缩小半径控制整个紧参数 GL 同伦 → 两个真实单形族 → 已证明的相对棱柱和同图半径不变性。控制的是整个 `H(t,z)` 族，不能把一般 GL 同伦误当作齐次映射。

FIRST warm 检查出现 11 个错误；最后版本修正了局部切空间实例、导数的坐标化简、membership、同伦端点和 lambda continuity，但用户在复检前停止。准确 FIRST 请求/错误和 pre-target setup 已保存在 Evidence。没有 SECOND 检查，没有成功/错误证明对照，也没有独立 saved-file 验收。

**避免循环：**候选为开发而 import `Homology`，不能让 `Homology` 再 import 它。成功后将必要证明块迁到原 `Homology.lean` 的 uniqueness 声明之前，仅 import 较低的 `LinearOrientation` 等模块，保留原 theorem header。不能使用原 uniqueness、它选出的 `localOrientationClass` 或其 generator 来证明自身。保留现有 `OrientedChartSimplex` 的任意 actual `OpenPartialHomeomorph`、仅中心可微和可逆导数；不得暗中加强到光滑 chart。

最后证明真正移入原位置并独立检查后，才允许把 Homology 四项直接债减为三项。接续三项是 `localOrientationClass_generator`、`exists_unique_fundamentalClass`、`fundamentalClass_generator`。

### C. 旧抽象 ancestry restriction：保留诊断，优先级低于生产证明

`AncestryRestrictionCandidate.pending.txt` SHA256：`47A79E766F47F3558BF3577AD1A69C9CF63FAE47F6170B3173D4F424DEDAC5D4`，未验证。原 `Ancestry.lean` 完全未改。

精确义务：仅从 retained stage 等式和 transition `HEq`，传递实际 `childParent`；record 没有 discarded/capped stage 等式。现有 full-presentation congruence 有后两项数据，不能直接套用；泛型 dependent elimination 的失败有原始记录。可研究不依赖额外参数的 trace projection congruence，但这不是已证明的不可能性，也没有获准加强原 record。实际 `ObservedHistory.finite_ancestry_restrict` 和 observation tower 路线已证明，且不消费这个旧 `sorry`，不要为它阻塞真实出口。

## 6. Hurewicz 复用

[Background.md](Background.md) 保留先前的逐项复用审计。包内 `Handoff/ReuseReference/` 提供旧 `E:/testdifferential-geometry-t1-433` 中的窄 `T1Provider`、接口及说明，保留源码头部的许可信息，标为 **只读参考**；没有移入 native import 树或宣称在 4.33.1 编译成功。旧树为 Lean 4.33.0，其 artifact 与历史公理审计只证明旧树的相应对象。

关键入口是 `Mathoverflow1973.SecondHurewicz.SimplyConnected.hurewiczPi2Equiv`、`Mathoverflow1973.ThirdHurewicz.hurewiczPi3Equiv` 和 `ThirdHurewicz.CubeSubdivision.cubeChain_eq_sum_tetrahedra`。后者的六个带符号单形与当前 LoopClass 的 staircase 顺序相符，是比较**指定** Hurewicz 映射的入口；不能只选择一个同型群之间的任意同构。

旧 provider 限制 `X : Type`、`ModuleCat.{0} ℤ`、系数 `ℤ`；当前公开空间 universe-polymorphic，实际系数是 `ULift.{u} ℤ`。仍需泛化必要证明链，或证明真实 smallness/homeomorphism，再证明 coefficient-chain-homology 传递的自然性与 simplex generator 作用。Type-0 wrapper 不能完成当前目标。旧 `Poincare/Targets.lean` 的 `h2_zero`、`h3_ne_zero` 仍有直接债，不能将旧 README 的完成描述当作 manifold duality 或本项目端点完成。

不要为了 SvK 引入整条 6000 多声明的 toolbox；本树 `VanKampen.lean` 已有可用证明。`PendingProofSources/` 与 `LinearOrientationCandidates.md` 是保留的旧试稿和失败路线，新的 A/B checkpoint 优先，不重新搭建已经通过的线性同伦。

## 7. 语义、验证与报告

定向公开对象是 owner 已采用的真实切空间定向截面，坐标平凡化中局部常值；不能改成全局 oriented chart 或任意抽象符号。基本类与 degree 仍需真实证明。保持 `T_alg`、`T_deg`、`T_map` 中尚未陈述的经典背景义务可见；当前没有授权把整个 classical input 当作新增 imported axiom。

连续 degree +1 map 不推出 homotopy equivalence。全父比较映射必须处理 loop 进入新 cap 和 shortest path 离开 terminal regular region 的情形；环境 a.e. 微分控制不意味着每条曲线上 a.e. 控制。局部 fundamental-class rule 不要求整个 map 光滑。验收覆盖 no-cut、total disappearance、多 child、多 boundary sphere、horizon event、非 identity presentation，以及指定 basepoint/path 和符号。

可以保留准确 `theorem ... := by sorry` 显式记债，但不能把未证目标变成新的结论型假设。禁止新增数学 axiom、`nolint`、`maxHeartbeats`、`maxRecDepth`、`skipKernelTC` 或削弱原语句。公开数学语义、竞争性基础层级和接受 classical input 为 imported 是 owner 决策；常规局部 helper 不需要额外许可。

先读接收 checkout 的 `CLAUDE.md`、`WORKING_STATUS.md` 和实际锁状态。dev 当前缺少本地 `scripts/lake-locked.ps1`；本轮从 dev cwd 调用 `E:/testdifferential-geometry/scripts/lake-locked.ps1`，它按当前 Git root 管理锁。接收方重新核对路径。本机每次启动 Lean 前检查进程，已有至少 3 个 Lean 时等待；本任务默认一个 compiler、2 threads。先 claim，再 focused check；任何 artifact refresh/lint build 先协调独占窗口。

```powershell
# 从确认后的目标 checkout 执行，保存 claim 返回的 token。
$topologyWrapper = 'E:/testdifferential-geometry/scripts/lake-locked.ps1'
& $topologyWrapper status
& $topologyWrapper claim -Files DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Topology/Homology.lean
& $topologyWrapper check -Token '<returned-token>' -Files DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Topology/Homology.lean -NoLakeLock -LeanThreads 2
# 只有在已协调的独占窗口中：
& $topologyWrapper build -NoLakeLock -LeanThreads 2 +DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology
& $topologyWrapper release -Token '<returned-token>'
```

Warm REPL 只能复用目标之前的环境，不 import 目标模块，不使用已含目标证明的环境；prefix/import/artifact/toolchain 改变就失效。不能和独立 Lean/Lake 检查重叠。热会话不代替最终保存文件的独立检查、窄 lint build 和 scratch `#print axioms`。新导出先刷新必要上游 artifact，再检查下游；不要启动全根 build。标准公理只允许 `propext`、`Classical.choice`、`Quot.sound`；有 `sorryAx` 的输出逐项列出来源。

路线明确的证明实现用 high；机械修复、检索、文档和协调用 medium；实际数学瓶颈再单项升档。每个 worker 最多一个待验证主候选，避免堆积。返回报告包含基线、变更文件 SHA、label→完整声明及子结论、实际消除的 producer、仍缺的精确义务、focused/lint/axiom 日志与未检候选状态。交付隔离分支 commit 或明确 patch，由负责人独立复核、仅注册/暂存自己的根 import hunk，并在集成 commit 末尾加 `Co-Authored-By: Claude`。不要自行 push 或发送他人的改动。

## 8. 可直接转发的 brief

请接手 `ch:rfs-topology`（Topology and Comparison Maps across Surgery）的全部 Lean 形式化，先读本 HANDOFF、完整 BookSource、Inventory 和五项出口的原始签名。在固定基线上接续 30 个正式文件，保留已批准的真实切空间定向、指定 Hurewicz/自由环类、实际 cut/cap 与 finite history 对象。首先核验最后的 ChartOrientation 候选，完成 LinearOrientation 的公理验收，并把无循环的实际比较证明迁回原 Homology uniqueness；再按依赖完成基本类/Hurewicz、球面 cut/cap、comparison 与 loop-class 生产证明。旧 T1 Hurewicz 材料是可复用证明源，仍需 universe/coefficient/指定映射桥；不接受 Type-0 或任意同构替代。不要改其他车道，保持所有证明债显式，按当前 claims/编译名额规则验证，逐 label 报告实际端点与传递依赖，由负责人集成。
