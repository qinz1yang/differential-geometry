# Skeleton fill log

## 1 IsPLHomeomorphInto.mono_of_isPLCellOn — CLOSED
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/IsPLHomeomorphIntoMonoOfIsPLCellOn.lean
- import 行：import DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphIntoMonoOfIsPLCellOn
- 新公共名：DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.mono_of_isPLCellOn
- 编译：`Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\IsPLHomeomorphIntoMonoOfIsPLCellOn.lean with no diagnostics; shared outputs unchanged.`
  （2026-09-21 21:09:57 -07:00）
- 公理审计：13 项 linter 均通过；全部模块声明的公理闭包均包含于
  `propext`、`Classical.choice`、`Quot.sound`；`exitCode=0`，`diagnosticLines=0`
  （2026-09-21 21:13:31 -07:00）。
- 证明路线：先在欧氏模型紧胞腔上把 PL 单射升级为局部可逆 PL 嵌入，再沿胞腔参数化
  及其局部逆传递该结构。
- 用时：约 6 分钟；编译次数：3 次模块检查、2 次审计检查。

## 2 exists_splitDisk_src_eq_inter_vertexBall — FALSE
- 文件：无
- import 行：无
- 新公共名：无
- 编译：未运行；反驳在冻结的 `Section34CutFrame` 字段层完成。
- 公理审计：不适用。
- 反例：取 `𝒦'` 的两个不相邻图顶点 `w ≠ w'`，让两个源三胞腔的交恰为一个
  以 `faceDisk s` 标记的闭 PL 二胞腔 `F`，并令所有实际边的 `splitDisk` 都取为与
  `F` 不同的二胞腔。这样的正则 PL 胞腔图满足每个标签的胞腔和边界并公式：在
  `src (.vertexBall w) ∩ src (.vertexBall w')` 的共同下方面恰放入
  `faceDisk s` 及其边界标签。`Section34CutFrame` 的第 24 个字段只给出
  `∀ e, ∃ w w', src (splitDisk e) = src (vertexBall w) ∩ src (vertexBall w')`，没有反向的
  覆盖或排他性字段；其交集展开字段也允许该 `faceDisk s` 同时包含于两个顶点胞腔。
  因而 `hmeet` 成立而不存在任何 `e` 的 splitting disk 等于 `F`。这也正是
  `Section34Frame.lean` 模块说明第 76--78 行所记录的缺口。
- 用时：约 12 分钟；编译次数：0 次。

## 3 separates_of_locally_eventually_eq — CLOSED
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/SeparatesOfLocallyEventuallyEq.lean
- import 行：import DifferentialGeometry.Topology.PiecewiseLinear.SeparatesOfLocallyEventuallyEq
- 新公共名：DifferentialGeometry.Topology.PiecewiseLinear.separates_of_locally_eventually_eq
- 编译：`Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\SeparatesOfLocallyEventuallyEq.lean with no diagnostics; shared outputs unchanged.`
  （2026-09-21 21:22:57 -07:00）
- 公理审计：13 项 linter 均通过；全部模块声明的公理闭包均包含于
  `propext`、`Classical.choice`、`Quot.sound`；`exitCode=0`，`diagnosticLines=0`
  （2026-09-21 21:25:53 -07:00）。
- 证明路线：若极限集不分离，取其补中的连接路径；路径像紧且避开中心，局部最终相等
  由有限覆盖统一为同一阶段，从而给出某个 `M n` 补中的连接路径，矛盾于该阶段分离。
- 用时：约 15 分钟；编译次数：2 次模块检查、2 次审计检查。

## 4 isTopologicalSphere_image_splitRim — CLOSED
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/IsTopologicalSphereImageSplitRim.lean
- import 行：import DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSphereImageSplitRim
- 新公共名：DifferentialGeometry.Topology.PiecewiseLinear.isTopologicalSphere_image_splitRim
- 编译：`Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\IsTopologicalSphereImageSplitRim.lean with no diagnostics; shared outputs unchanged.`
  （2026-09-21 21:31:06 -07:00）
- 公理审计：13 项 linter 均通过；全部模块声明的公理闭包均包含于
  `propext`、`Classical.choice`、`Quot.sound`；`exitCode=0`，`diagnosticLines=0`
  （2026-09-21 21:32:18 -07:00）。
- 证明路线：由有限闭对偶胞腔之并先得 `N` 闭，从而边界圆周位于嵌入域；将分裂盘的
  PL 边界圆周经该限制嵌入送到像中，再与标准圆周的参数化复合。
- 用时：约 11 分钟；编译次数：2 次模块检查、1 次审计检查。

## 5 section33_tube_product — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/Section33TubeProduct.lean.wip
- import 行：无（未闭合）。
- 新公共名：无。
- 编译：未通过；第二次模块检查在
  `Section33TubeProduct.lean:26:2` 报 `Type mismatch: hN has type
  N = (derivedNeighborhood A K).space but is expected to have type Nonempty
  (↑(frontier (derivedNeighborhood A K).space) × ↑(Ioo 0 1) ≃ₜ
  ↑(interior N' \\ h '' K.space))`（2026-09-21 21:42:18 -07:00）。
- 公理审计：不适用。
- 卡住的目标与错误：`IsTube.spaceEq` 已给出 `N = (derivedNeighborhood A K).space`，但全树
  没有从有限三维组合流形中的一维子复形导出
  `frontier (derivedNeighborhood A K).space × Ioo 0 1 ≃ₜ
  interior (derivedNeighborhood A K).space \\ K.space` 的正规邻域去核乘积定理。
  `derivedNeighborhoodStrongDeformationRetract` 仅给出收缩，
  `IsCombinatorialManifoldWithBoundary.exists_collar` 仅给出边界的局部 collar，二者均不能
  构造全补集的双射。还须把任意嵌入 `h|N` 的源端内部精确送到 `interior (h '' N)`；现有
  `IsPLHomeomorphOn.image_interior` 不适用，因为 `IsTube.isEmbedding` 只假设拓扑嵌入。
- 已试路线：通过 `ht.spaceEq` 化为源端导出邻域，检索 DerivedNeighborhood、RegularNeighborhood、
  Collar 及全部 PL 乘积 API；没有可消费的定理。需要先补一个真正的正规邻域乘积生产者，
  以及其在紧致嵌入像下的 interior-complement transport。
- 用时：约 12 分钟；编译次数：2 次模块检查。

## 2 exists_splitDisk_src_eq_inter_vertexBall — CLOSED
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/Section34SplitDiskIntersection.lean
  （lead-owned；本车道此前的 FALSE 条目由本更正覆盖。）
- import 行：import DifferentialGeometry.Topology.PiecewiseLinear.Section34SplitDiskIntersection
- 新公共名：DifferentialGeometry.Topology.PiecewiseLinear.exists_splitDisk_src_eq_inter_vertexBall
- 编译：lead 已在提交 `284ccc052` 中完成独立审计和集成。
- 公理审计：由 lead 的独立验收覆盖。
- 证明路线：此前的反例不成立。`faceDisk ⊆ vertexBall` 会迫使关联的
  `faceArc = faceDisk`，这与严格维数下降矛盾；故相交的两个不同 dual ball
  必由 split disk 给出。
- 用时：更正记录；本车道不再保留该叶子的独立源码或编译计数。

## 6 boundaryComplex_space_of_isPLCellAttachmentWith_zero — CLOSED
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/BoundaryComplexPLCellAttachmentZero.lean
- import 行：import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryComplexPLCellAttachmentZero
- 新公共名：DifferentialGeometry.Topology.PiecewiseLinear.
  boundaryComplex_space_of_isPLCellAttachmentWith_zero
- 编译：`Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\BoundaryComplexPLCellAttachmentZero.lean with no diagnostics; shared outputs unchanged.`
  （2026-09-21 21:58:05 -07:00）
- 公理审计：13 项 linter 均通过；全部模块声明的公理闭包均包含于
  `propext`、`Classical.choice`、`Quot.sound`；`exitCode=0`，`diagnosticLines=0`
  （2026-09-21 22:02:25 -07:00）。
- 证明路线：由零边界附着的逐点锚定先导出 `N'.space = L.space ∪ C` 和二者不交；
  将 `C` 三角化为 PL 3-ball，再在相对邻域中逐点将 `L` 与该 ball 的组合边界
  同 `N'` 的组合边界等同，最后用标准单形边界的 PL 参数化识别 `C` 的边界像。
  当前模块以同定义的私有 `IsPLCellAttachmentWith` 重演骨架接口；lead 将该定义
  提升至公共模块后须以公共常量重验端点。
- 用时：约 48 分钟；编译次数：7 次模块检查、1 次公理/linter 审计。

## 7 boundaryComplex_space_of_isPLCellAttachmentWith_three — STUCK
- 文件：`DifferentialGeometry/Topology/PiecewiseLinear/BoundaryComplexPLCellAttachmentThree.lean.wip`
- import 行：无（未闭合）。
- 新公共名：无。
- 编译：`Verification failed; see C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\DifferentialGeometry\Topology\PiecewiseLinear\BoundaryComplexPLCellAttachmentThree.log and .json`
  （2026-09-21 22:24:54 -07:00；末端未解目标为
  `(boundaryComplex 3 N').space = (boundaryComplex 3 L).space \ g '' stdSimplexBoundary 3`。）
- 公理审计：未运行；模块未闭合。
- 卡住的目标与错误：已由 `hN`、`hCL`、局部邻域转移证明接缝外的边界等价。余下需要
  `Disjoint (g '' stdSimplexBoundary 3) (boundaryComplex 3 N').space`，即完整附着球面在
  `N'` 中成为内部。现有 `BoundaryGluing` 只覆盖双方全部边界恰为交集的无边界粘合；
  `BoundaryInvariance` 和 `SubcomplexNhdsWithin` 没有“边界三球沿完整边界球面粘合”的局部
  邻域/边界消失引理。`NeighborhoodEmbedding.lean` 源码中可导出接缝在旧边界的相对开性，
  但该声明不在本租约的已编译环境中，且仍不足以产生所需的双侧局部三球。
- 用时：约 22 分钟；编译次数：6。

## 8 isSmoothHandleStage_adjunction_zero — CLOSED
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/IsSmoothHandleStageAdjunctionZero.lean
- import 行：import DifferentialGeometry.Topology.PiecewiseLinear.IsSmoothHandleStageAdjunctionZero
- 新公共名：DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_zero
- 编译：Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\IsSmoothHandleStageAdjunctionZero.lean with no diagnostics; shared outputs unchanged.
  （2026-09-21 22:41:54 -07:00）。
- 公理审计：13 项 linter 均通过；全部本模块声明的公理闭包均包含于
  propext、Classical.choice、Quot.sound；xitCode=0，diagnosticLines=0
  （2026-09-21 22:41:54 -07:00）。
- 证明路线：空附着关系没有生成元，故商空间显式同胚于标准三单形与原流形的不交并；
  再经标准单形到闭三球的坐标同胚，使用不交并流形实例、闭三球边界球面公式和
  不交并边界公式给出精确边界对应。
- 用时：约 47 分钟；编译次数：8 次模块检查、2 次公理/linter 审计。
- 记录更正：编译成功行原文为 `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\IsSmoothHandleStageAdjunctionZero.lean with no diagnostics; shared outputs unchanged.`
  公理审计结果为：13 项 linter 均通过，公理闭包仅含 `propext`、`Classical.choice`、`Quot.sound`，
  `exitCode=0`，`diagnosticLines=0`。

## 9 revolutionOf_cellInterior_subset_interior — CLOSED
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/RevolutionOfCellInteriorSubsetInterior.lean
- import 行：`import DifferentialGeometry.Topology.PiecewiseLinear.RevolutionOfCellInteriorSubsetInterior`
- 新公共名：DifferentialGeometry.Topology.PiecewiseLinear.
  revolutionOf_cellInterior_subset_interior。
- 编译：`Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\RevolutionOfCellInteriorSubsetInterior.lean with no diagnostics; shared outputs unchanged.`
  （2026-09-21 22:53:45 -07:00）。
- 公理审计：13 项 linter 均通过；全部模块声明的公理闭包均包含于
  `propext`、`Classical.choice`、`Quot.sound`；`exitCode=0`，`diagnosticLines=0`
  （2026-09-21 22:55:33 -07:00）。
- 反例检查：严格半平面条件排除了旋转轴，未找到反例。
- 证明路线：将闭圆盘参数化经闭球收缩延拓到整个平面；其平面坐标投影在开单位
  球上单射，域不变性给出开像。径向坐标的逆像是三维开邻域，并逐点落入旋转像。
- 用时：约 30 分钟；编译次数：4 次模块检查、1 次成功公理/linter 审计。

## 10 exists_isTopologicalCellWithInterior_union_consecutive — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/
  ExistsIsTopologicalCellWithInteriorUnionConsecutive.lean.wip
- import 行：无（未闭合）。
- 新公共名：无。
- 编译：`Verification failed`（2026-09-21 22:58:58 -07:00）；最小尝试在提取
  两个闭圆盘参数化和交集闭圆盘参数化后，留下完整目标：
  `∃ Eint, IsTopologicalCellWithInterior 2 (D j.castSucc ∪ D j.succ) Eint ∧ ...`。
- 公理审计：未运行；模块未闭合。
- 反例检查：未找到反例。严格平面条件将三集合都限制在同一二维仿射平面内。
- 卡住的目标与错误：当前库和已导入的 Schoenflies API 均没有“两个嵌入平面闭盘的
  交是闭盘，则并是闭盘，且各参数化开盘都落入新开盘”的粘合定理。现有
  PlanarJordan.ClosedInterior 只从已知 Jordan 前沿构造一个闭盘，不能从三个任意闭盘
  参数化导出并集前沿为 Jordan 曲线；直接 `aesop` 的精确未解目标已保留在 WIP。
- 用时：约 15 分钟；编译次数：1。
## 11 separates_initialSurface — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/SeparatesInitialSurface.lean.wip
- import 行：无（未闭合）。
- 新公共名：无。
- 编译：Verification failed；在 SeparatesInitialSurface.lean:58:10 的精确未解目标为
  IsClosed (Subtype.val ⁻¹' initialSurface S'' T'' P')（时间：2026-09-21 23:06:24 -07:00）。
- 公理审计：未运行；模块未闭合。
- 反例检查：未找到反例。havoid 结合每个配置的 innerSubset 会排除顶点落在
  各个 T'' 上；h 在 tube 上的嵌入性也排除了 P' = h u 或 P' = h v 的退化。
- 卡住的目标与错误：IsCanonicalTower、initialSurface 仍只定义在不可导入的
  Skeleton/Section32PseudoCell.lean 中，真实库没有同名公共词汇；为得到上述实际目标，
  WIP 暂时复制了逐字的私有接口。更深的缺口是只有每个有限配置的
  IsCombinatorialSolidTorus、塔的 locallyFinite（针对 φ '' S i）和
  IsTube.splitSeparates，没有将交错的 T''-并及奇数项的删除操作证明为闭集并传递
  分离性的公开引理。现有 LocallyFinite.isClosed_iUnion 只能处理已给出的局部有限闭族，
  不能产生该族或完成交错面替换。
- 已试路线：检索 initialSurface、IsCanonicalTower、splitSeparates、局部有限闭并、
  canonical configuration 和所有非 Skeleton 的 Section 32 API；没有可消费的
  tower-to-separator 生产者。需要先把词汇提升到真实模块，并补 Lemmas 1/3 的
  canonical tower 初始交错面闭且分离导出。
- 用时：约 22 分钟；编译次数：1 次模块检查。
## 12 section33_faceEulerChar_handlePiece — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/Section33FaceEulerCharHandlePiece.lean.wip
- import 行：无（未闭合）。
- 新公共名：无。
- 编译：Verification failed；首批精确错误为
  Unknown identifier IsPolyhedralTubeNeighborhood、
  Unknown identifier HasSinglePolygonTraces、Unknown identifier HasConnectedHandlePieces、
  Unknown identifier edgesAt（时间：2026-09-21 23:08:20 -07:00）。
- 公理审计：未运行；模块未闭合。
- 反例检查：未找到反例。已核对 AI 摘要的计数是 2 − deg v，且导出的组件边界恰是
  incident trace polygons；没有把 AA 的旧 off-by-one 读法带入本陈述。
- 卡住的目标与错误：四个输入/结论词汇仍只存在于
  Skeleton/Section33Approximation.lean，故真实模块不能逐字重述冻结端点。
  即使局部复制它们，现有公开 API 仅给二维组合流形的 Euler-Betti 公式和单个
  SurfaceSplit 的 Euler 公式；没有从 tube 的 handle-piece 分解、所有 trace 圆周及
  frontier-to-complement 的 π1 双射导出逐顶点 capped-surface Euler 等式的生产者。
  该缺口正是摘要所谓 global Euler identity plus capping bounds，并非单一
  faceEulerChar 化简。
- 已试路线：检索 faceEulerChar、边界 Euler、SurfaceSplitEuler、曲面可定向性、
  π1 映射和 handle decomposition；可见一般 Euler 公式，但没有将本结构的
  boundaryComplex 等式接到 capping/global 计数的引理。需要先提升四个词汇并补
  handle-piece capping/global Euler bridge。
- 用时：约 19 分钟；编译次数：1 次模块检查。
## 13 isCombinatorialManifold_of_locallyFinitePLPieceIn — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/IsCombinatorialManifoldOfLocallyFinitePLPieceIn.lean.wip
- import 行：无（未闭合）。
- 新公共名：无。
- 编译：Verification failed；展开组合流形定义后的精确首个目标为
  IsPLSphere 2 (SimplicialComplex.geometricLink 𝒦.complex {s}).space，
  其中 s : Ea 且 {s} ∈ 𝒦.complex.faces（时间：2026-09-21 23:10:11 -07:00）。
- 公理审计：未运行；模块未闭合。
- 反例检查：未找到反例。U 的开性和 𝒦.bijOn/isEmbedding 排除了边界 link 与额外分支；
  这正是 AF Part 1 所确认的局部 PL 欧氏模型情形。
- 卡住的目标与错误：真实库有 LocallyFinitePLPieceIn 及其局部有限 link 有限性，
  但没有从该结构的 chartwise IsPiecewiseAffineOn、局部嵌入和开像推出顶点
  geometricLink 为 PL 2-sphere 的定理。现有 isPLSphere_link 只从已经给出的
  IsCombinatorialManifold 反向推出 link 球面，BallSphereLink 的传输定理也要求
  先有 PL ball/sphere 或 subdivision；不能闭合这个方向。
- 已试路线：展开 IsCombinatorialManifold 得到顶点 link 目标，检索所有
  geometricLink、piecewiseAffine、local PL 和 manifold API；仅找到从组合流形
  到 link 的单向链。需要先补“局部有限 PL 三角剖分的开 PL 三维流形具有 PL 球 link”
  的基本生产者。
- 用时：约 20 分钟；编译次数：1 次模块检查。
## 14a boundaryComplex_space_of_isPLCellAttachmentWith_one — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/BoundaryComplexPLCellAttachmentOne.lean.wip
- import 行：无（未闭合）。
- 新公共名：无。
- 编译：Verification failed；精确目标为
  Bd N' = (Bd L  g '' ((Δ²  ∂Δ²) × {0,1})) ∪ g '' (∂Δ² × [0,1])
  的 Lean 集合等式（时间：2026-09-21 23:13:23 -07:00）。
- 公理审计：未运行；模块未闭合。
- 反例检查：未找到反例。AN 的审阅确认两端圆盘的相对内部消失、端圆周保留、侧环加入。
- 卡住的目标与错误：真实库没有 IsPLCellAttachmentWith；WIP 只能临时复制私有定义。
  更实质地，BoundaryGluing 仅处理两边完整边界相等的闭合粘合，而本叶需要在两个
  attaching disk 的相对内部把 L 和新三胞腔的半空间邻域拼成内部点，同时保留边界圆周。
  mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin 只适用于某一个子复形已是
  环境中的邻域，恰在拼接接缝处不可用。
- 已试路线：复用 zero/three 模块的 quotient-union 及局部边界 transfer，检索
  BoundaryGluing、BoundaryInvariance、SubcomplexNhdsWithin；没有相对 disk gluing 的
  双侧局部三球/边界消失引理。
- 用时：约 18 分钟；编译次数：1 次模块检查。

## 14b boundaryComplex_space_of_isPLCellAttachmentWith_two — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/BoundaryComplexPLCellAttachmentTwo.lean.wip
- import 行：无（未闭合）。
- 新公共名：无。
- 编译：Verification failed；精确目标为
  Bd N' = (Bd L  g '' (∂Δ² × (0,1))) ∪ g '' (Δ² × {0,1})
  的 Lean 集合等式（时间：2026-09-21 23:13:23 -07:00）。
- 公理审计：未运行；模块未闭合。
- 反例检查：未找到反例。AN 的审阅确认仅侧环的相对内部消失，两个端圆盘应保留。
- 卡住的目标与错误：与 14a 同一未提升接口问题；更具体地需要相对 annulus glue
  的局部 collar 定理，既证明侧环内部在 N' 中成为内部，又证明两个端盘保持为边界。
  现有完整边界 BoundaryGluing 和单子复形的 nhdsWithin transfer 都不能给出该
  mixed seam 的双侧/单侧局部模型。
- 已试路线：对照 k=3 的现有 WIP、k=0 的闭合证明和 AN 的精确 relative-interior
  读法；没有可消费的 annulus collar / boundary trace API。
- 用时：约 17 分钟；编译次数：1 次模块检查。

## 15 hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock — STUCK
- 文件：DifferentialGeometry\Topology\PiecewiseLinear\HasPLNormalDoubleCrossingAtOfIsStableCrossingBlock.lean.wip
- import 行：无；骨架私有词汇尚未导出，真实模块不能形成该接口
- 新公共名：无
- 编译成功行原文 + 时间；公理审计结果：无；第 2 次聚焦检查于 2026-09-21 23:12 PDT 失败，未运行审计
- 卡住的目标与错误：真实模块逐字写入端点时，checker 报 Unknown identifier IsStableCrossingBlock 和 Unknown identifier innerChartBlock。二者仅定义在 Skeleton/GeneralPositionInDouble.lean；Skeleton 不能被真实模块导入，且私有同名复制不会与骨架端点同一命题。即使词汇被提取，尚缺将两张带收缩余量的 PL 图像推出 HasPLCrossingAt 的公共 graph-crossing 引理；现有 SingularGeneralPosition 只从横截单形复形产生该结论。反例检查：旧 AABB 重配对曲线不满足各源片在 inner block 的邻域字段和投影 PL 同胚字段，未构成此冻结陈述的反例。
- 用时：约 18 分钟；编译次数：2

## 16 isSpine_revolutionOf_of_mem_cellInterior — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/IsSpineRevolutionOfOfMemCellInterior.lean.wip
- import 行：无；本轮未闭合
- 新公共名：无
- 编译成功行原文 + 时间；公理审计结果：无；第 12 次聚焦检查于 2026-09-21 23:42 PDT 失败，未运行审计
- 卡住的目标与错误：显式旋转映射 `D × S¹ → revolutionOf D` 的连续性、双射性和
  `revolutionOf {p}` 的圆周值域刻画均已通过。最后拼接闭圆盘参数化时，checker 的唯一
  证明错误为第 270 行 `hu : u ∈ {q | ‖↑q‖ < 1}` 未被
  `simpa only [mem_ball, dist_zero_right]` 展开为 `‖↑u‖ < 1`；另有第 255 行
  `letI : CompactSpace D := φ.compactSpace` 的 `haveILetI` linter 警告。预期修复是将
  `hu` 先 `change ‖(u : EuclideanSpace ℝ (Fin 2))‖ < 1 at hu`，并把该局部实例改为
  `let _ : CompactSpace D := φ.compactSpace` 后复检。源中其余最后等式已写成从纤维像到
  单点旋转圆周的双向值域证明。
- 用时：约 58 分钟；编译次数：12
## 5 section33_tube_product — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/Section33TubeProduct.lean.wip
- import 行：无（第二轮未闭合）
- 新公共名：无
- 编译成功行原文 + 时间；公理审计结果：无；第二轮未启动 Lean，因为接口检索仍缺失结论所需的唯一生产者
- 卡住的目标与错误：第二轮重新核对 `IsTube.derivedModel`、`DerivedNeighborhood.lean`、
  `DerivedNeighborhoodRetraction.lean`、`RegularNeighborhood.lean` 及新加入的
  `OpenEmbeddingFrontier.lean`。新模块可把紧致嵌入像的内部精确传输，因而解决了旧记录的
  像端辅助问题；但源端仍没有
  `frontier (derivedNeighborhood A K).space × Ioo 0 1 ≃ₜ
  interior (derivedNeighborhood A K).space \ K.space`。现有
  `derivedNeighborhoodStrongDeformationRetract` 只给收缩和基本群等价，不能给该补集的
  同胚。`regularNeighborhood` 也只定义邻域并给包含/邻域性质。故冻结结论尚缺正规邻域
  去核乘积生产者，不能从现有 API 合法拼出。
- 用时：约 19 分钟；编译次数：0（第二轮）
## 7 boundaryComplex_space_of_isPLCellAttachmentWith_three — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/BoundaryComplexPLCellAttachmentThree.lean.wip
- import 行：无（第二轮未闭合）
- 新公共名：无
- 编译成功行原文 + 时间；公理审计结果：无；第二轮未启动 Lean，因为精确骨架接口仍非公共常量
- 卡住的目标与错误：第二轮确认真实库仍没有 `IsPLCellAttachmentWith`；该名称只在
  `Skeleton/PLSmoothingCompact.lean`，现有 WIP 的私有复制不能形成冻结端点。即使暂以复制
  继续，旧检查已将证明化为“完整附着球面在 `N'` 的组合边界中消失”。重新检索
  `BoundaryGluing`、`BoundaryComplement`、`ManifoldSubcomplexBoundary` 与
  `SubcomplexNhdsWithin` 后，仍只有整个边界粘合或接缝外邻域转移，没有把一枚 PL 三球
  沿完整 2-球附着后该接缝成为内部的局部双侧引理。故需先公开 attachment 结构并生产
  完整球面接缝的相对边界消失定理。
- 用时：约 14 分钟；编译次数：0（第二轮）
## 10 exists_isTopologicalCellWithInterior_union_consecutive — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/ExistsIsTopologicalCellWithInteriorUnionConsecutive.lean.wip
- import 行：无（第二轮未闭合）
- 新公共名：无
- 编译成功行原文 + 时间；公理审计结果：无；第二轮未启动 Lean，因所需 planar-gluing 生产者仍不存在
- 卡住的目标与错误：第二轮核对 `CanonicalConfiguration`、所有非 Skeleton 的
  `IsTopologicalCellWithInterior`、PlanarJordan/ClosedInterior 及 `Moise314` 的消费者。没有
  可重用的定理把两个嵌入平面闭圆盘、其闭圆盘交集，提升为它们并的闭圆盘参数化，并同时将
  两个既有开盘像包含在新内点集合。`Moise314` 正是该叶子的消费者，不能倒用；现有
  Jordan API 从已知 Jordan 前沿生产盘，不能从三份盘参数化识别并的前沿。声明未发现反例，
  但缺少这条平面圆盘粘合桥接。
- 用时：约 16 分钟；编译次数：0（第二轮）
## 11 separates_initialSurface — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/SeparatesInitialSurface.lean.wip
- import 行：无（第二轮未闭合）
- 新公共名：无
- 编译成功行原文 + 时间；公理审计结果：无；第二轮未启动 Lean，因为端点参数结构仍未导出
- 卡住的目标与错误：第二轮确认 `IsCanonicalTower` 与 `initialSurface` 仍只定义于
  `Skeleton/Section32PseudoCell.lean`。WIP 的私有复制不能交付冻结端点。进一步核对
  `IsTube.splitSeparates` 与 tower 字段：它只给单个 splitting disk 对两个顶点的分离；要得到
  交错 `T''` 并、删除奇数 torus 内部和极限点 `{P'}` 后的闭性与分离，仍缺“局部最终恒等
  的分离子极限”及完整的 closed-union transport。`havoid` 已修复顶点落在表面的反例，
  但不生产这些闭性/分离结论。
- 用时：约 13 分钟；编译次数：0（第二轮）
## 12 section33_faceEulerChar_handlePiece — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/Section33FaceEulerCharHandlePiece.lean.wip
- import 行：无（第二轮未闭合）
- 新公共名：无
- 编译成功行原文 + 时间；公理审计结果：无；第二轮未启动 Lean，因为冻结参数结构仍未导出
- 卡住的目标与错误：第二轮确认 `IsPolyhedralTubeNeighborhood`、`HasSinglePolygonTraces`、`HasConnectedHandlePieces` 和 `edgesAt` 仍仅在 `Skeleton/Section33Approximation.lean`，外部模块无法逐字形成端点。`SurfaceInvariants`、`SurfaceCappingBetti` 和 `SurfaceSphereRecognition` 提供闭曲面的 Euler/球面识别，但没有从 `IsHandleDecompositionOfTube` 的 `Cpp`、各 trace 多边形和 `AK v` 导出 capping 后的全局 Euler 恒等式或分量归属。因此尚缺将 handle-piece 数据接到该 Euler 链的生产者。
- 用时：约 15 分钟；编译次数：0（第二轮）
## 13 isCombinatorialManifold_of_locallyFinitePLPieceIn — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/IsCombinatorialManifoldOfLocallyFinitePLPieceIn.lean.wip
- import 行：无（第二轮未闭合）
- 新公共名：无
- 编译成功行原文 + 时间；公理审计结果：无；第二轮未启动 Lean，因为现有公开 API 尚不能关闭首个顶点 link 目标
- 卡住的目标与错误：反驳检查未找到反例；digest AF Part 1 的局部 PL 欧氏模型论证与冻结陈述一致。`LocallyFinitePLPieceIn.geometricLink_faces_finite` 已由真实局部有限性给出 link 的有限面集，但第一个目标仍是 `IsPLSphere 2 (SimplicialComplex.geometricLink 𝒦.complex {s}).space`。现有 `LocallyFinitePLPieceIn.isPLSphere_geometricLink` 以 `IsCombinatorialManifold` 为前提，不能倒用；全树没有把开放 PL 图卡中的嵌入三角剖分提升为顶点 link PL 球面的定理。缺少的生产者是“局部双向逐片仿射 3-流形图卡 + 局部有限复形 ⇒ 每个 vertex geometricLink 为 PL 2-sphere”。
- 用时：约 18 分钟；编译次数：0（第二轮）
## 14a boundaryComplex_space_of_isPLCellAttachmentWith_one — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/BoundaryComplexPLCellAttachmentOne.lean.wip
- import 行：无（第二轮未闭合）
- 新公共名：无
- 编译成功行原文 + 时间；公理审计结果：无；第二轮未启动 Lean，因为冻结假设接口未导出
- 卡住的目标与错误：反驳检查未找到满足附件参数化和 adjunction 同胚字段的反例。`IsPLCellAttachmentWith` 及其从 `IsPLCellAttachment` 选择 `g` 的 producer 仍只在 Skeleton；外部模块不能逐字引用冻结 `hatt`。即使使用 WIP 中的私有逐字段副本，现有公开 API 也只给空 attaching region 的不交并边界式；缺少任意 PL 3-ball 沿两张闭盘粘合后，已粘圆盘的相对内部从 `boundaryComplex` 消失、侧面补入的相对边界公式。
- 用时：约 14 分钟；编译次数：0（第二轮）

## 14b boundaryComplex_space_of_isPLCellAttachmentWith_two — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/BoundaryComplexPLCellAttachmentTwo.lean.wip
- import 行：无（第二轮未闭合）
- 新公共名：无
- 编译成功行原文 + 时间；公理审计结果：无；第二轮未启动 Lean，因为冻结假设接口未导出
- 卡住的目标与错误：反驳检查未找到反例。冻结 `IsPLCellAttachmentWith` 仍为 Skeleton 私有词汇，故真实模块无法逐字声明端点。私有副本下还缺相应的 annulus collar 边界追踪：须证明 `stdSimplexBoundary 2 × Ioo 0 1` 的像从旧边界删除，而 `stdSimplex 2 × {0,1}` 的像进入新边界；`BoundaryInvariance`、`DerivedNeighborhoodCellBoundary` 和现有 gluing API 未提供任意 adjunction 的这条相对公式。
- 用时：约 14 分钟；编译次数：0（第二轮）
## 15 hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/HasPLNormalDoubleCrossingAtOfIsStableCrossingBlock.lean.wip
- import 行：无（第二轮未闭合）
- 新公共名：无
- 编译成功行原文 + 时间；公理审计结果：无；第二轮未启动 Lean，因为两个冻结核心定义仍未导出
- 卡住的目标与错误：反驳检查未找到满足完整源片邻域、严格 margin 和 PL 图投影字段的反例；review V 所述的退化 AABB 重配对已被这些字段排除。`IsStableCrossingBlock` 与 `innerChartBlock` 仍只在 `Skeleton/GeneralPositionInDouble.lean`，外部模块不能逐字组成端点。公开库有 `HasPLNormalDoubleCrossingAt` 的局部性、前后复合和 source 传输 API，却没有“稳定双 graph block ⇒ normal double crossing”的桥接定理；这一桥必须从 block 的两张源片、graph equations 与 margin 构造局部图卡见证，不能以现有 normality 结论倒推。
- 用时：约 16 分钟；编译次数：0（第二轮）
## 16 isSpine_revolutionOf_of_mem_cellInterior — CLOSED
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/IsSpineRevolutionOfOfMemCellInterior.lean
- import 行：import DifferentialGeometry.Topology.PiecewiseLinear.IsSpineRevolutionOfOfMemCellInterior
- 新公共名：isSpine_revolutionOf_of_mem_cellInterior
- 编译成功行原文 + 时间；公理审计结果：Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\IsSpineRevolutionOfOfMemCellInterior.lean with no diagnostics; shared outputs unchanged.（2026-09-21 23:53 PDT）；最终审计 exitCode 0、diagnosticLines 0、sharedArtifactsModified false（2026-09-22 00:01 PDT），本模块所有声明的公理闭包只含 propext、Classical.choice、Quot.sound，13 个环境 linter 全部通过。
- 证明路线：显式旋转给出 `D × S¹ ≃ₜ revolutionOf D`；以闭盘参数化与之取积，再由内点参数的纤维像正好为 `revolutionOf {p}`。
- 用时：第二轮约 27 分钟；聚焦编译次数 1（累计 13 次）

## 总表

| 状态 | 队列条数 |
| --- | ---: |
| CLOSED | 8 |
| FALSE | 0 |
| STUCK | 8 |

按 `FILL_QUEUE.md` 的 16 个编号条目计数；第 14 条的两个端点为同一队列条目，首轮的第 2 条反例记录已由 lead 修复并以 CLOSED 计入。

## 15 hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/HasPLNormalDoubleCrossingAtOfIsStableCrossingBlock.lean.wip
- import 行：无（本轮未闭合）
- 新公共名：无
- source hash：SHA256 787521FDD86EE0304271E1352C7E378163DD71567522BFC416D89FD65F8BBD37
- 编译成功行原文 + 时间；公理审计结果：无；本轮未启动 Lean，阻塞在首个几何构造前。
- 反例：未找到满足 `IsStableCrossingBlock` 全部字段的反例；两张完整源片的相对邻域和
  `IsPLHomeomorphOn` 投影排除了 AABB 重配对。
- 卡住的目标与错误：由 `u = a (v,t)`、`v = b (u,t)`、`La * Lb ≤ 1 - η`、两张源片的
  投影局部满射和共同 `t` 参数，构造一个局部逐片仿射环境自同胚，将两张像同时送到两张
  横截坐标平面（边界支还须保留 `t = 0` 半空间）。`isPLHomeomorphOn_id_add_of_lipschitz`
  只处理某个欧氏范数下 Lipschitz 常数小于一的整体位移；本接口只给乘积小于一，以及对
  `t` 不受控的分片仿射依赖，不能直接套用。全树没有该加权/逐纤维图像正规化引理，且
  `HasPLNormalDoubleCrossingAt`、`HasPLCrossingAt` 的传输定理均以后者为输入，不能倒推。
  需要生产者：共同参数的两张 PL 图像在乘积收缩条件下的局部双平面正规化，含 `tlo = 0`
  的半空间相对版本。
- 用时：约 24 分钟；编译次数：0

## 13 isCombinatorialManifold_of_locallyFinitePLPieceIn — CLOSED
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/IsCombinatorialManifoldOfLocallyFinitePLPieceIn.lean
- import 行：import DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldOfLocallyFinitePLPieceIn
- 新公共名：LocallyFinitePLPieceIn.starComplex_faces_finite；
  LocallyFinitePLPieceIn.closedStar_mem_nhdsWithin；
  isCombinatorialManifold_of_locallyFinitePLPieceIn
- source hash：SHA256 F3AA957F521185BE7E0B0E742B48B46576F0FC02B46727441D186560F97F1E1B
- 编译成功行原文 + 时间；公理审计结果：Verified
  D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\
  IsCombinatorialManifoldOfLocallyFinitePLPieceIn.lean with no diagnostics; shared outputs
  unchanged.（2026-09-22 03:32 PDT）。Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\
  AuditIsCombinatorialManifoldOfLocallyFinitePLPieceIn.lean with no diagnostics; shared outputs
  unchanged.（2026-09-22 03:32 PDT）。端点与两个新增辅助引理的公理闭包只含 propext、
  Classical.choice、Quot.sound；13 个环境 linter 全部通过。
- 反例：未找到满足局部有限、双向逐片仿射图卡、嵌入和开放像的反例。
- 证明路线：局部有限的 coface 集控制顶点星的面；其余不含该顶点的闭单形族局部有限，
  所以其并闭，从而闭星在复形载体内是邻域。嵌入将此邻域送到像的相对邻域，`hU` 将它
  提升为环境邻域。随后把有限星限制为有限 PL piece，细分使顶点闭星落入一个图卡，
  用有限图卡 link 定理，再经细分与星的 geometric link 同一性送回原复形。
- 用时：约 70 分钟；聚焦编译次数：5；公理/linter 审计次数：2（首轮仅发现并修复了
  `HasGroupoid` 的 unusedArguments 与辅助引理中多余的 FiniteDimensional 参数）。
## 7 boundaryComplex_space_of_isPLCellAttachmentWith_three — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/BoundaryComplexPLCellAttachmentThree.lean.wip
- import 行：无（本轮未闭合）
- 新公共名：无
- source hash：SHA256 B393E77BDB10F50281E145CE35C16AB5BEB3DB04E97CC9E347F7D089F4896D50
- 编译成功行原文 + 时间；公理审计结果：无。第 1 次检查于 2026-09-22 PDT 失败：
  `error: unsolved goals`，目标为
  `(boundaryComplex 3 N').space = (boundaryComplex 3 L).space \ g '' stdSimplexBoundary 3`；
  同时 `aesop: failed to prove the goal after exhaustive search.`
- 反例：未找到满足 `IsPLCellAttachmentWith` 的反例；`hgB` 将完整附着球面精确送到
  `C ∩ L.space`，而 adjunction 同胚排除了额外的粘合点。
- 卡住的目标与错误：已从 adjunction 同胚推出 `N'.space = L.space ∪ C`，从 `hgB` 推出
  `C ∩ L.space = g '' stdSimplexBoundary 3`，并证明接缝以外的 boundaryComplex 判定可由
  `mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin` 转移。剩余正是证明完整接缝
  `g '' stdSimplexBoundary 3` 在 `N'.space` 中成为内点，因此不属于
  `(boundaryComplex 3 N').space`。`BoundaryGluing` 只处理两个复形的整个边界相同，不能
  处理 `L` 的一个边界分支；现有局部边界转移也只适用于接缝外。需要生产者：PL 三球沿
  `IsClosedEmbedding` 的完整边界球附着到三维组合流形的一个边界分支时，接缝的相对
  boundaryComplex 消失，以及其余边界的不变性。
- 用时：约 31 分钟；编译次数：1
## 14a boundaryComplex_space_of_isPLCellAttachmentWith_one — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/BoundaryComplexPLCellAttachmentOne.lean.wip
- import 行：无（本轮未闭合）
- 新公共名：无
- source hash：SHA256 91DE8C6B424D4073651A8DDFA5A36DC18A9A22F6CE1647C7C7BC56FC95F7E354
- 编译成功行原文 + 时间；公理审计结果：无；本轮未启动 Lean，因第 7 条已定位到同一缺失的
  相对边界粘合生产者，且本 WIP 的首个未解决目标就是其一手实例。
- 反例：未找到满足 `IsPLCellAttachmentWith` 的反例；端盘区域由 `hgB` 精确识别为
  `C ∩ L.space`，侧环的内部不与旧阶段相交。
- 卡住的目标与错误：需要证明两张端盘的相对内部从旧 `boundaryComplex` 消失，侧环
  `g '' (stdSimplexBoundary 2 ×ˢ Icc 0 1)` 全部进入新 `boundaryComplex`，并在其余点转移
  旧边界。公开 `CellAttachment` 现在可逐字形成冻结假设，但只给 adjunction 坐标等式；
  `BoundaryGluing` 只覆盖全边界粘合，不能给两闭盘附着的相对边界公式。需要第 7 条记录的
  相对 PL 附着边界生产者的 disk-pair 特例。
- 用时：约 12 分钟；编译次数：0

## 14b boundaryComplex_space_of_isPLCellAttachmentWith_two — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/BoundaryComplexPLCellAttachmentTwo.lean.wip
- import 行：无（本轮未闭合）
- 新公共名：无
- source hash：SHA256 57B80F0D2A2BF6CD7A29A608B8C8E01185C8973E1CAA8E20A8E55960F275680C
- 编译成功行原文 + 时间；公理审计结果：无；本轮未启动 Lean，因第 7 条已定位到同一缺失的
  相对边界粘合生产者，且本 WIP 的首个未解决目标就是其一手实例。
- 反例：未找到满足 `IsPLCellAttachmentWith` 的反例；附着侧环的相对内部应变为内点，两个
  未附着端盘保持在新边界。
- 卡住的目标与错误：需要证明
  `g '' (stdSimplexBoundary 2 ×ˢ Ioo 0 1)` 从旧边界删除、
  `g '' (stdSimplex ℝ (Fin 3) ×ˢ ({0,1} : Set ℝ))` 加入新边界，并保留接缝外的旧边界。
  这正是任意附着区域为环带时的 relative boundary-complex gluing；公开 API 未提供它，
  且不能由整个边界的 `BoundaryGluing` 推出。需要第 7 条记录的相对 PL 附着边界生产者的
  annulus 特例。
- 用时：约 12 分钟；编译次数：0
## 11 separates_initialSurface — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/SeparatesInitialSurface.lean.wip
- import 行：无（本轮未闭合）
- 新公共名：无
- source hash：SHA256 DCC97D4C8DAAC9488CF2608FA6F70F1319AFF2E7302094A96D063B4377C837C3
- 编译成功行原文 + 时间；公理审计结果：无；本轮未启动 Lean，公开 `PseudoCell` 与
  `separates_of_locally_eventually_eq` 已可直接引用，但首个缺口是几何构造而非命名或实例。
- 反例：未找到满足全部 `IsCanonicalTower` 字段和 `havoid` 的反例；已核对 `havoid` 经每个
  `config.innerSubset` 排除两个顶点落在任何 `S'' i` 或其边界上。
- 卡住的目标与错误：`separates_of_locally_eventually_eq` 需要一个自然数索引的闭分离子列，
  每项分离两个顶点，并在 `P'` 外局部最终等于 `initialSurface`。`IsCanonicalTower` 只给
  三重 canonical configurations、远离二步的外 torus 不交、两个尾部的 closure 方程和
  外 torus 的局部有限性；没有公开引理把每个三重配置的 annuli/solid tori 拼成上述闭分离子，
  也没有从这些字段导出对 `T''` 与删去偶数 `interior S''` 的局部最终稳定。`IsTube.splitSeparates`
  只给原 splitting disk 的分离，不能把它运送到交错 `initialSurface`。需要生产者：
  canonical tower 的 Lemma 1/Lemma 3 型有限截断 separator 及其在 `P'` 外的局部稳定性。
- 用时：约 28 分钟；编译次数：0
## 10 exists_isTopologicalCellWithInterior_union_consecutive — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/ExistsIsTopologicalCellWithInteriorUnionConsecutive.lean.wip
- import 行：无（本轮未闭合）
- 新公共名：无
- source hash：SHA256 7C592B41E36B6C2A0F6C67167B4EF7222F939E49D85C330173794EC953913294
- 编译成功行原文 + 时间；公理审计结果：无；本轮未启动 Lean，`CanonicalConfiguration` 已直接
  提供所有冻结词汇，首个缺口是新的平面粘合定理。
- 反例：未找到满足 `IsPlanarCellChain` 全部字段的反例；两盘交集由 `hc.overlap j` 为二维
  topological cell，且两个指定 intrinsic interior 包含各自连接段。
- 卡住的目标与错误：从两份 `IsTopologicalCellWithInterior 2` 参数化和
  `IsTopologicalCell 2 (D j.castSucc ∩ D j.succ)`，构造
  `IsTopologicalCellWithInterior 2 (D j.castSucc ∪ D j.succ) Eint`，并证明两个旧
  intrinsic interior 均包含于 `Eint`。全树没有 `IsTopologicalCellWithInterior` 的 union/
  planar gluing 定理；已有 Jordan/Schoenflies API 从已知前沿产生盘，不能从三份盘参数化
  推导并的盘参数化和内点包含。需要生产者：平面嵌入闭二胞腔沿闭二胞腔交集的并胞腔定理。
- 用时：约 18 分钟；编译次数：0
## 12 section33_faceEulerChar_handlePiece — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/Section33FaceEulerCharHandlePiece.lean.wip
- import 行：无（本轮未闭合）
- 新公共名：无
- source hash：SHA256 7EBD6D8450016F8D9AE96A8B80DB8A192A8C3C001139F95503538F62B81C54A4
- 编译成功行原文 + 时间；公理审计结果：无；本轮未启动 Lean，公开
  `PolyhedralTubeNeighborhood` 已提供所有四个输入谓词，首个缺口是 global capping/Euler
  construction。
- 反例：未找到满足 `HasConnectedHandlePieces`、single-polygon trace 和 `hiso` 的反例；
  `AK v` 的边界确实由 incident trace polygons 的并精确给定。
- 卡住的目标与错误：`h56` 给出 `AK v` 是连通的二维组合流形带边界，且边界等于 incident
  polygon traces；`h34` 给每一条 trace 一个盘；现有 `SurfaceCapping`/`CapComplex` 可在
  已给出切开/封帽复形后计算 Euler characteristic。然而没有从 `h2`,`h34`,`h56`,`hiso`
  构造这些盘的同时封帽、证明所得闭曲面为球面，或把所有 `AK v` 的 capped pieces 接到
  一个全局 Euler 恒等式。`hiso` 是基本群同构，却没有可直接消费的“boundary inclusion
  isomorphism implies capped piece sphere”引理。需要生产者：incident traces 的相容封帽与
  global handle-piece Euler/capping bridge，结论为每个 `AK v` 的 Euler 数 `2 - deg(v)`。
- 用时：约 24 分钟；编译次数：0

## 5 section33_tube_product — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/Section33TubeProduct.lean.wip
- import 行：无（本轮未闭合）
- 新公共名：无
- source hash：SHA256 552DDAD27B722B2C58A4588B5E1A63F6880BA4CF8FDB735DB93A28D9C901C85B
- 编译成功行原文 + 时间；公理审计结果：无；本轮未启动 Lean（2026-09-22 03:37:26 -07:00），因为首个缺口是尚未形式化的源端正规邻域乘积定理，而非可由现有声明消解的 elaboration 错误。
- 反例：未找到满足 `IsTube` 全部字段的反例。`isNeighborhood` 将图核置于 `N` 的内部；`isEmbedding` 与 `imageEq` 足以使既有 `OpenEmbeddingFrontier` 接口处理像端的内部传输。问题在于源端生产者缺失。
- 卡住的目标与错误：由 `IsTube.derivedModel`、`unionEq` 可将源端化为有限三维组合带边流形 `A` 中一维子复形 `K` 的导出邻域，但全树没有定理
  `frontier (derivedNeighborhood A K).space × Set.Ioo (0 : ℝ) 1 ≃ₜ
  interior (derivedNeighborhood A K).space \\ K.space`。
  `derivedNeighborhoodStrongDeformationRetract` 只给到 `K.space` 的强变形收缩及基本群等价；它既不控制补集，也不能构造所需三维乘积同胚。`NeighborhoodCylinder` 只覆盖连通 PL 圆周的特殊情形，不能应用于冻结的任意一维 `K`。需要先补“有限三维组合带边流形中的有限一维子复形，其导出邻域去核为边界乘开区间”的生产者；随后再经 `h` 和 `OpenEmbeddingFrontier` 搬运。
- 用时：约 14 分钟；编译次数：0

## 本轮总表

| 状态 | 叶子数 |
| --- | ---: |
| CLOSED | 1 |
| FALSE | 0 |
| STUCK | 8 |

按本轮 9 个冻结叶子计，14a 与 14b 分别计数。

## 10 exists_isTopologicalCellWithInterior_union_consecutive — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/ExistsIsTopologicalCellWithInteriorUnionConsecutive.lean.wip
- import 行：无（冻结端点尚未闭合）
- 新公共名：IsTopologicalCellWithInterior.interior_eq
- source hash：TopologicalCellInterior.lean SHA256 CF4529B964071B01615A406FFF0DB00A9471644EFC9432274A31E56A1F717C34
- 编译成功行原文 + 时间；公理审计结果：2026-09-22 04:14:50 -07:00；Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\TopologicalCellInterior.lean with no diagnostics; shared outputs unchanged.；审计 AuditTopologicalCellInterior.lean 同样为 Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTopologicalCellInterior.lean with no diagnostics; shared outputs unchanged.，模块全部声明只含 propext、Classical.choice、Quot.sound，13 个标准 linter 均为零。
- 反例：未找到满足 IsPlanarCellChain 全部字段的反例。hc.cell、hc.overlap 分别给两枚闭二胞腔及其闭二胞腔交集；hc.halfPlane 将它们约束在同一嵌入平面。
- 卡住的目标与错误：已证明二维欧氏环境中 IsTopologicalCellWithInterior 的指定内部等于环境 interior。要完成冻结端点仍须从两枚平面嵌入闭二胞腔及其闭二胞腔交集构造并集的闭二胞腔参数化，并证明其边界为 Jordan 曲线（或等价地构造相对闭盘粘合）。现有 PlanarJordan/Schoenflies API 只能从给定 Jordan 前沿或给定 crosscut 构造闭盘；DiskUnion/BallGluingTwo 只覆盖 PL 且沿一维边界弧粘合，不能消费此处任意 topological 2-cell 交集。
- 用时：约 70 分钟；编译次数：5 次外部探针、1 次模块检查、1 次审计。

## 15 hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/HasPLNormalDoubleCrossingAtOfIsStableCrossingBlock.lean.wip
- import 行：无（冻结端点尚未闭合）
- 新公共名：无
- source hash：SHA256 787521FDD86EE0304271E1352C7E378163DD71567522BFC416D89FD65F8BBD37
- 编译成功行原文 + 时间；公理审计结果：`Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\F15Scratch24.lean with no diagnostics; shared outputs unchanged.`（2026-09-22 05:45:11 -07:00）。该回执只验证外部私有辅助构造，冻结端点未闭合，故未运行端点公理审计或 linter。
- 反例：未找到满足 `IsStableCrossingBlock` 全部字段的反例。两张完整源片的相对邻域、投影的 `IsPLHomeomorphOn`、共同 `t` 参数及严格 margin 排除了 AABB 重配对；`StableCrossingBlock.lean` 现已公开七个定义和五个辅助引理。
- 卡住的目标与错误：已验证共同参数的全局图像正规化：先将第一张图像剪切为第一坐标平面，再以收缩映射沿第二坐标剪切，所得 PL 环境自同胚保持 `t`，并把两张完整 graph image 分别送到两张横截坐标平面。冻结端点尚须把此全局图像等式限制到两张源片的多面体相对邻域，组装两个 `IsPLHomeomorphOn` 见证、由稳定 block 的完整 preimage 等式给出二点纤维的最终覆盖，并在 `tlo = 0` 支中把 `t = 0` 半空间送入 `HasPLBoundaryCrossingAt`；最后再以 `exists_crossing_chart_mem_atlas` 更换图卡。尚无声明错误或数学反例；本条已累计运行 `F15Scratch2` 至 `F15Scratch24` 共 23 次外部 Lean 探针，超过每叶 12 次编译上限，按队列规则停止，不能继续检查该组装。
- 用时：约 54 分钟；编译次数：23 次外部探针，0 次本轮命名模块检查。

## 本轮收尾总表

| 状态 | 队列条数 |
| --- | ---: |
| CLOSED | 8 |
| FALSE | 0 |
| STUCK | 8 |

按 `FILL_QUEUE.md` 的 16 个编号条目计数；第 15 条仍为既有 STUCK，未重复计数。本轮优先处理的第 10、15 条均已记录；其余建议条目没有新的构造路线，依队列要求停止。

## 15 hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock — STUCK
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/StableCrossingNormalizer.lean（已闭合支持模块）；冻结端点没有新 .lean，既有 HasPLNormalDoubleCrossingAtOfIsStableCrossingBlock.lean.wip 未修改。
- import 行：import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingNormalizer
- 新公共名：exists_pl_homeomorph_two_graphs_to_coordinate_planes_of_lipschitz
- source hash：StableCrossingNormalizer.lean SHA256 D8A07126B81EAA68E88FB3D42B8E58807C150FFAE237E1FC5CCAEECB470B08D1
- 编译成功行原文 + 时间；公理审计结果：2026-09-22 06:47:35 -07:00；Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\StableCrossingNormalizer.lean with no diagnostics; shared outputs unchanged.；全声明审计 AuditStableCrossingNormalizer.lean 为 Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditStableCrossingNormalizer.lean with no diagnostics; shared outputs unchanged.，全部声明公理闭包只含 propext、Classical.choice、Quot.sound，13 个标准 linter 均为零。
- 证明路线：支持模块先以 (u,v,t) ↦ (u - a(v,t),v,t) 将第一完整 graph image 送到第一坐标平面；再用 La * Lb < 1 的纤维收缩构造第二个保持共同 	 参数的 PL 自同胚。两张完整 graph image 分别精确送到两张坐标平面。
- 卡住的目标与错误：冻结端点要求最后调用 xists_crossing_chart_mem_atlas。该定理有未满足的隐式实例 [HasGroupoid M (plGroupoid 3)]；冻结陈述只给 [TopologicalSpace M]、[ChartedSpace ... M] 和局部 hec : ec ∈ (plGroupoid 3).maximalAtlas M。外部探针 F15AtlasProbe.lean:19:8 的原文为 rror(lean.synthInstanceFailed): failed to synthesize instance of type class HasGroupoid M (plGroupoid 3)。hec 只能控制与 c 重叠的转移，不能构造全图册的 HasGroupoid。这不是冻结结论的反例：可在自然主题中新加局部输运版，令目标图卡为 chartAt ... y，并以 (plGroupoid 3).subset_maximalAtlas (chart_mem_atlas _ y) 供给 HasPLNormalDoubleCrossingAt.of_mem_maximalAtlas；但这将绕开指定的现有封装定理并新增公共 API，按本轮遇到 API 缺口即停止的规则留给 lead 决定。
- 用时：约 35 分钟；编译次数：4 次 Lean 调用（命名模块检查、两次全声明审计、一次外部接口探针；另有一次 checker 参数错误，未启动 Lean）。

## 本轮总表（第 15 条有界重试）

| 状态 | 冻结叶子数 |
| --- | ---: |
| CLOSED | 0 |
| FALSE | 0 |
| STUCK | 1 |

支持模块 CLOSED 1；队列累计总表仍为 CLOSED 8 / FALSE 0 / STUCK 8。

## 15 hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock — STUCK (corrected receipt)
- 文件：DifferentialGeometry/Topology/PiecewiseLinear/StableCrossingNormalizer.lean (closed supporting module); the frozen endpoint has no new .lean file, and the existing HasPLNormalDoubleCrossingAtOfIsStableCrossingBlock.lean.wip was not modified.
- import 行：import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingNormalizer
- 新公共名：exists_pl_homeomorph_two_graphs_to_coordinate_planes_of_lipschitz
- source hash：StableCrossingNormalizer.lean SHA256 D8A07126B81EAA68E88FB3D42B8E58807C150FFAE237E1FC5CCAEECB470B08D1
- 编译成功行原文 + 时间；公理审计结果：2026-09-22 06:48:09 -07:00；Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\StableCrossingNormalizer.lean with no diagnostics; shared outputs unchanged.；全声明审计 AuditStableCrossingNormalizer.lean 为 Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditStableCrossingNormalizer.lean with no diagnostics; shared outputs unchanged.，全部声明公理闭包只含 propext、Classical.choice、Quot.sound，13 个标准 linter 均为零。
- 证明路线：支持模块先以 (u,v,t) mapsto (u - a(v,t),v,t) 将第一完整 graph image 送到第一坐标平面；再用 La * Lb < 1 的纤维收缩构造第二个保持共同 t 参数的 PL 自同胚。两张完整 graph image 分别精确送到两张坐标平面。
- 卡住的目标与错误：冻结端点要求最后调用 exists_crossing_chart_mem_atlas。该定理有未满足的隐式实例 [HasGroupoid M (plGroupoid 3)]；冻结陈述只给 [TopologicalSpace M]、[ChartedSpace ... M] 和局部 hec : ec ∈ (plGroupoid 3).maximalAtlas M。外部探针 F15AtlasProbe.lean:19:8 的原文为 error(lean.synthInstanceFailed): failed to synthesize instance of type class HasGroupoid M (plGroupoid 3)。hec 只能控制与 ec 重叠的转移，不能构造全图册的 HasGroupoid。这不是冻结结论的反例：可在自然主题中新加局部输运版，令目标图卡为 chartAt ... y，并以 (plGroupoid 3).subset_maximalAtlas (chart_mem_atlas _ y) 供给 HasPLNormalDoubleCrossingAt.of_mem_maximalAtlas；但这将绕开指定的现有封装定理并新增公共 API，按本轮遇到 API 缺口即停止的规则留给 lead 决定。
- 用时：约 35 分钟；编译次数：4 次 Lean 调用（命名模块检查、两次全声明审计、一次外部接口探针；另有一次 checker 参数错误，未启动 Lean）。

上一节的反引号被 PowerShell 字符串转义损坏；本 corrected receipt 是本轮权威记录。

## 本轮总表（第 15 条有界重试）

| 状态 | 冻结叶子数 |
| --- | ---: |
| CLOSED | 0 |
| FALSE | 0 |
| STUCK | 1 |

支持模块 CLOSED 1；队列累计总表仍为 CLOSED 8 / FALSE 0 / STUCK 8。

## 15 hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock — FALSE

- 文件：无新 Lean 模块；冻结陈述位于 `DifferentialGeometry/Topology/PiecewiseLinear/Skeleton/GeneralPositionInDouble.lean:1463`。既有 `.lean.wip` 未修改。
- import 行：不适用。
- 新公共名：无。冻结陈述 SHA256 `AF3D17C8D284A0028E3967173AFFB1299F09A81AA365269DA772789120A9EB38`（2026-09-22）。
- 编译成功行原文 + 时间；公理审计结果：本轮没有编译端点；反例是对冻结陈述的语义否定，故端点公理审计和 linter 不适用。此前已验证的 `NormalCrossingTransport` 与 `StableCrossingNormalizer` 支持模块不受影响。
- 反例的环境：令 `H = {z : ℝ³ | z₂ < 0}`，令 `M` 为两份 `ℝ³` 沿 `H` 按恒等映射粘合的非 Hausdorff 商。记两份开嵌入为 `i₀,i₁`；在 `H` 上 `i₀ z = i₁ z`，而两个零点 `o₀=i₀ 0`、`o₁=i₁ 0` 不相等，且不可由不交邻域分开。两份逆图卡给出 `ChartedSpace (EuclideanSpace ℝ (Fin 3)) M`；重叠转移恒等，故 `ec=i₀⁻¹` 属于 `(plGroupoid 3).maximalAtlas M`。这个实例无需 `T2Space M`，而冻结陈述确实没有该实例。
- 取 `ℓ(u,v,t)=t`、`A(u,v,t)=(u,v,t)`、`BdM=i₀({t=0})`、`r=1`、`tlo=0`、`a=b=0`、`La=Lb=0`、`η=1`。于是 `ℓ≠0`，且在 `ec.source` 内 `x∈BdM ↔ ℓ(ec x)=0`。`chartBlock ec A 1 0 = i₀([-1,1]²×[0,1])` 在 `M` 中闭且紧；它的闭包仍是自身，包含于 `ec.source`。特别是 `o₁` 没有落入该闭包：它在第二份图卡中的小邻域只有负高度的公共点和第二份正高度点，与盒子不交。
- 源域取矩形 `S=[-5,5]×[0,3]`，是一个 PL 2-ball。未修改的映射为 `(x,s)↦i₀(g(x),s)`，其中 `g(x)=(0,x+3)`（`x≤-1`）、`g(x)=(-2(x+1),2)`（`-1≤x≤0`）、`g(x)=(-2,2-2x)`（`0≤x≤1`）、`g(x)=(x-3,0)`（`x≥1`）。它在接点一致。只在 `(0,2)` 附近一个小方块内作如下 PL 修改：在内层小多边形边界取常值 `c=(-2,2,-1)`，用有限三角剖分在外边界原值与 `c` 之间线性插值；在内层由边界向中心 `w=(0,2)` 作锥，边界值为 `i₁(c)`、中心值为 `D(w)=o₁`。锥上除中心外的值为 `i₁(λc)=i₀(λc)`（`λ>0`），在公共负半空间中。外层修改区域可选得全部满足 `u<-3/2` 或 `v>3/2`，所以始终避开 `chartBlock`；锥也避开盒子，因为高度为负。所得 `D` 在第一图卡的其余源点及第二图卡的中心附近逐片仿射，故 `D.isPLOn`，并构成 `SingularTwoCell M`。域外值任取。
- 所有稳定块字段同时成立：`SA=[-4,-2]×[0,1]`、`SB=[2,4]×[0,1]`，且 `S∩D⁻¹(chartBlock ec A 1 0)=SA∪SB`，两片不交。在 `SA` 上图像恰为 `(0,x+3,s)`，在 `SB` 上恰为 `(x-3,0,s)`；因此两个 graph 方程为零函数，`blockSheetProjA`、`blockSheetProjB` 分别是 `(x,s)↦(x+3,s)`、`(x,s)↦(x-3,s)`，均为矩形之间的仿射 PL 同胚。`SA/SB` 与相应投影矩形在各自内盒原像点处是相对邻域；投影矩形 `[-1,1]×[0,1]` 在 `blockHalfPlane 0={t≥0}` 中覆盖所需相对邻域。对 `SA∪SB` 中每一点，`x∈frontier S ↔ s=0 ↔ ℓ(ec(Dx))=0`。取 `tlo=0` 支，`A` 的高度坐标就是 `ℓ`；`0<r,0<η,0≤La,Lb,La·Lb≤1-η`、两条 Lipschitz 条件及两个零函数的逐片仿射条件也成立。
- 令 `y=o₀`。`D⁻¹{y}∩S` 恰有 `p=(-3,0)`、`q=(3,0)` 两点，故 `hy : y∈doublePointSet D S`；`y∈innerChartBlock ec A 1 0`。取锥上一列 `w_n→w` 且锥参数 `λ_n↓0`、`λ_n>0`，则 `D(w_n)=i₀(λ_n c)→y`，但 `D(w)=o₁≠y`，并且这些点不在稳定盒原像里。
- 结论失败的确切 Lean 条款：任意在 `y` 处的 atlas 图卡 `e` 的开源域不能同时包含 `o₁`，否则其源域（同胚于欧氏开集）包含不可分的两点。可是 `D(w_n)→y`，所以最终 `w_n∈P_e:=S∩D⁻¹(e.source)` 且 `(e∘D)(w_n)→e y`。`y∈e''(e.source∩BdM)`，故 `HasPLNormalDoubleCrossingAt` 只能走 `HasPLBoundaryDoubleCrossingAt` 支；该定义的见证 `a,b,A',B'` 满足 `a∈A'`、`b∈B'`、两者映到 `e y`、`A',B'⊆P_e`、各自的 `IsPLHomeomorphOn`，并有 `∀ᶠ z in 𝓝(e y), P_e∩(e∘D)⁻¹'{z}⊆A'∪B'`。图卡单射及上面的精确纤维给出 `{a,b}={p,q}`。`IsPLHomeomorphOn.homeomorph` 保证每片的逆映射在 `e y` 连续；取源中包含 `p,q` 而闭包避开 `w` 的小邻域，其两片逆像在 `e y` 附近都必须落入该邻域。纤维覆盖则把足够大的 `w_n` 放进 `A'∪B'`，与 `w_n→w` 矛盾。普通 `HasPLDoubleCrossingAt` 支也有同样的逆连续与覆盖条款。
- 根因及接口决定：`IsStableCrossingBlock` 的紧致盒是闭半盒，并非 `y` 的环境邻域；负高度一侧的另一份图卡允许额外源分支的像趋向 `y`，而其极限源点不映到 `y`。增加 `[T2Space M]` 可排除此反例，但是否以及如何修改冻结端点属于 lead 决定；本车道不更改骨架，也不继续证明假的原陈述。直接依赖者是同骨架的 `exists_normalCrossing_of_hasWallProductBlocks`。
- 用时、编译次数：本轮语义核对约 20 分钟；Lean 编译 0 次。此 FALSE 记录取代此前第 15 条 STUCK 记录作为当前判断，不改变其他队列条目。

## 本轮总表（F15 反例，待 lead 独立验收）

| 状态 | 本轮 F15 | 队列累计当前判断 |
| --- | ---: | ---: |
| CLOSED | 0 | 8 |
| FALSE | 1 | 1 |
| STUCK | 0 | 7 |

## Codex queue Q3 — checked first layer (2026-09-22 evening)

Worker evidence only; independent lead acceptance, aggregate registration and commits remain
with the lead. Work used the owner-authorized `codex-moise-recon` private lane. No frozen
statement, existing proof module, aggregate, lease, acceptance ledger or Git state was edited.

### Existing Q1 and Q2

The live queue marks Q1 withdrawn. Current `ChartImagePLCell` and `PLSphereLocallyPlanar`
are already registered. Q2 is also already implemented as `DiskMeetsGraph`, imported by
`Section33Approximation` and registered by the lead. A private audit of
`IsPLCellOn.isPLBall_image_chart`, `IsPLSphere.exists_isOpen_inter_homeomorph_of_two`
and `section33_disk_meets_graph` found only `propext`, `Classical.choice`, `Quot.sound`.
The last theorem retains its explicit `Moise324` input.
Receipt: `queue-existing-20260922.json/.log` under the private root below; Lean exit 0,
source stable, nine expected axiom-print lines, no shared artifact changes.
These are existing results, not new Codex closures.

### New checked modules

All names below are in `DifferentialGeometry.Topology.PiecewiseLinear`.

1. `import DifferentialGeometry.Topology.PiecewiseLinear.CyclicBallUnion`
   - `isCombinatorialSolidTorus_union_of_inter_eq_disjoint_disks`
   - `isCombinatorialSolidTorus_iUnion_of_cycle`
   - SHA256: `398402A484516B31431D12564C51A8435FB827D053E7415F4B56B36606A481E2`.
   - Two PL 3-balls in E3 whose exact intersection is two disjoint PL 2-disks form a
     CST. A cyclic family of length at least three reduces to this case: consecutive
     intersections are PL disks, nonneighbors are disjoint, distinct triple intersections
     are empty. The proof derives the boundary placement and the global combinatorial
     manifold condition from local ball neighborhoods; neither is an extra endpoint input.
   - The E3 cylindrical-diagram bridge supplies orientability. This does not claim the
     analogous abstract or higher-dimensional twisted cycle is a solid torus.
   - Eight source theorems (two public, six private); imported declarations audited.
   - Module receipt ended `2026-09-23T05:32:19.0552225Z`.
     Audit: `queue-cycle-audit-20260922.json/.log`, ended `2026-09-23T05:33:44.5111436Z`.

2. `import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryCollarExtension`
   - `exists_isPLHomeomorphOn_annulus_of_isPLCirclePositive`
   - `exists_isPLHomeomorphOn_of_circle_collars`
   - `IsPLHomeomorphOn.exists_extension_of_positive_boundary_corrections`
   - SHA256: `4EBBFDD71FB5CC36E7782EF8237557EF3C8140CBCFF307EF017FB44DDB74CC2D`.
   - Positive circle corrections extend over specified pairwise disjoint PL product
     collars, simultaneously, fixing a polyhedral remainder meeting only the fixed ends.
     The reference-map corollary preserves the reference on the remainder.
   - Positivity concerns the correction relative to the reference. A globally reversing
     reference is allowed; this is not a demand that every absolute boundary map be positive.
   - Three declarations audited.
   - Module receipt ended `2026-09-23T05:26:58.1246516Z`.
     Audit: `queue-collar-audit-20260922.json/.log`, ended `2026-09-23T05:31:48.3329593Z`.

3. `import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskFamilyMove`
   - `IsPLBall.isConnected_compl` (planar PL 2-disks)
   - `isPreconnected_sdiff_iUnion_of_disjoint_isPLBall_two`
   - `exists_isPLHomeomorphOn_map_disk_family_eqOn_compl`
   - `exists_isPLHomeomorphOn_holed_disk_eqOn_outer_boundary`
   - SHA256: `AFB0C5B87B30416D6C65CC9CF459E84C1254F23F5283B747C136D154948D7802`.
   - Finite labelled planar disk families are matched by an ambient PL homeomorphism
     supported in any connected open set containing them. Every insertion correction
     fixes all previously matched target disks pointwise. Empty families are included.
   - The holed-disk theorem prescribes the outer boundary map, matches all labelled inner
     disks and their frontiers, and supplies the actual PL map of
     `D \ ⋃ i, interior (A i)` onto `D' \ ⋃ i, interior (B i)`.
     Inner boundary maps at this stage are those induced by the produced reference.
   - Five source theorems (four public, one private); imported declarations audited.
   - Module receipt ended `2026-09-23T05:35:58.7403799Z`.
     Audit: `queue-disk-family-audit-20260922.json/.log`, ended `2026-09-23T05:37:37.1534242Z`.

For each of these three modules the checker success line had the form
`Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\<Module>.lean with no diagnostics; shared outputs unchanged.`
All module and audit receipts have `exitCode = 0`, `diagnosticLines = 0`,
`sourceStable = true`, `sharedArtifactsModified = false`.
All sixteen source theorem declarations have only the approved foundational axiom closure;
all thirteen standard environment linters pass (excluding only docBlame/docBlameThm).
No sorry, axiom, inline comments, declaration docstrings, resource overrides or linter suppression.

Private root: `C:\Users\liao9\AppData\Local\Temp\codex-moise-recon`.
Named-module receipts are under its corresponding `DifferentialGeometry/Topology/PiecewiseLinear/`
directory. Before each named check, the current import closure was prepared with
`claude-moise-shared/prepare-private-root.py`; checks used PowerShell
`claude-moise-shared/checker.ps1 -Checkout D:/differential-geometry-moise-int
-Token codex-moise-recon-20260922 -OutputRoot C:/Users/liao9/AppData/Local/Temp/codex-moise-recon
-Module DifferentialGeometry.Topology.PiecewiseLinear.<Module>`.

Q3(ii) is delivered as a checked reusable brick. Full Q3(i) still needs actual compatible
one-sided collar production and the final prescribed-inner-boundary assembly; its first
collar producer is in progress. These results do not close CGN edge matching or supply the
orientation-character bridge around arbitrary graph cycles. Root imports are intentionally
left to the lead under the queue's new-files-only rule.

## Codex queue Q3 — final checked delivery (2026-09-22 evening)

This section supersedes the first-layer Q3(i) pending status and the old
`PlanarDiskFamilyMove` source hash. No frozen CGN endpoint is claimed closed.

### Delivered endpoints and orientation condition

- Q3(ii): `isCombinatorialSolidTorus_iUnion_of_cycle` and the two-ball/two-disk theorem
  in `CyclicBallUnion` are checked real E3 producers.
- Q3(i), planar model: `HoledDiskBoundaryExtension` now extends all prescribed boundary
  maps under the explicit relative orientation condition. Its
  `exists_isPLHomeomorphOn_holed_disk_with_boundary_extension` first produces a labelled
  reference map from the prescribed outer map, independently of the inner prescribed maps.
  It then quantifies arbitrary inner PL circle maps and requires their corrections against
  that reference to satisfy the existing `IsPLCirclePositive` increasing-lift predicate.
  The output maps the actual closed holed regions and agrees with every prescribed circle map.
  The reference may reverse orientation. No extension witness is assumed.
- The main reusable relative theorem is
  `IsPLHomeomorphOn.exists_holed_disk_extension_of_positive_boundary_corrections`.
  `exists_boundary_collars_holed_disk` in `PlanarHoledCollars` produces all one-sided
  collars and the actual polyhedral closed remainder.
  `exists_isPLHomeomorphOn_holed_disk_of_positive_boundary_maps` consumes them.

The finite producer uses `Option.none` for the outer boundary. It chooses disjoint neighborhoods
of the outer complement and all closed inner disks, constructs an inward outer collar and
outward collars for the holes, and sets the remaining region to the actual complement closure.
Each local closed remainder contains that global remainder, proving the seam-only contact.
Thus neither the collar system nor its overlap equations were promoted to endpoint assumptions.
The empty hole family is included.

Still separate: identifying compatibility directly from an ambient degree/orientation character
without the reference map, transporting the planar model into arbitrary sphere charts, and
the CGN graph-cycle compatibility supplied by the original embedding. The E3 cyclic-ball
result alone does not prove these facts. The original CGN matching/removal leaves are untouched.

### Final import list

All eight imports are ready for the lead's registration; this worker did not edit the aggregate.

```lean
import DifferentialGeometry.Topology.PiecewiseLinear.BallComplementFamily
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryCollarExtension
import DifferentialGeometry.Topology.PiecewiseLinear.CyclicBallUnion
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarBoundaryCollars
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskFamilyMove
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarOuterCollar
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarHoledCollars
import DifferentialGeometry.Topology.PiecewiseLinear.HoledDiskBoundaryExtension
```

Additional public names:

- `IsPolyhedron.sdiff_iUnion_interior_of_isPLBall`: finite full-dimensional ball interiors
  may be removed from a polyhedron. Both new consumers share this proof in
  `BallComplementFamily`; the private duplicate was removed from `PlanarDiskFamilyMove`.
- `IsPLHomeomorphOn.exists_disk_boundary_collar`: a small inward collar in a prescribed
  relative neighborhood, with pointwise boundary fixing, exact seam and a remaining PL disk.
- `IsPLBall.exists_outer_boundary_collar`: a small collar on the outside of an inner planar
  disk, with the exact complement, polyhedral remainder, seam, neighborhood and annulus frontier.

### Final source identity and verification

| Module | SHA256 | Zero-diagnostic module check ended (UTC) |
|---|---|---|
| CyclicBallUnion | `398402A484516B31431D12564C51A8435FB827D053E7415F4B56B36606A481E2` | 2026-09-23 05:32:19 |
| BoundaryCollarExtension | `4EBBFDD71FB5CC36E7782EF8237557EF3C8140CBCFF307EF017FB44DDB74CC2D` | 2026-09-23 05:26:58 |
| PlanarDiskFamilyMove | `F8E2905CAD14CD18DAC79BB2F6ABAD4786231589DEC096C8E71604756F8127DE` | 2026-09-23 05:47:14 |
| BallComplementFamily | `9F7EA14D0C06244461DFC7677FA22C2501C624F0837B79549C0B8505CD122565` | 2026-09-23 05:46:31 |
| PlanarBoundaryCollars | `353C4456B4681DE621C318BBB6B0B35AC7C2D42EBEC0AAA3A3E23CA9EC23B436` | 2026-09-23 05:41:32 |
| PlanarOuterCollar | `F56D7F7C39AD77D40FF42E757103BB1125CBE25C710D1CB610DCC8B45282BFE5` | 2026-09-23 05:48:43 |
| PlanarHoledCollars | `AF67495708399D19652B4B2D758BC3D2A21047041A1E881FEC8051200A9C81A6` | 2026-09-23 05:49:12 |
| HoledDiskBoundaryExtension | `071C89CACAE7FF82A753A8FF24E81916B6ACDDF288A309F3FED8BC4035905AA3` | 2026-09-23 05:50:04 |

All eight module receipts have Lean exit 0, zero diagnostics, stable source hashes and unchanged
shared outputs. The final source manifest was compared against every current file and receipt.

The final six-module boundary-suite audit passed at `2026-09-23T05:55:47.2042307Z` with
zero diagnostics, only `propext`/`Classical.choice`/`Quot.sound` in every axiom closure, and
all thirteen environment linters passing. It enumerated seventeen declarations: thirteen
source theorems/private lemmas plus four local-notation declarations. The count was read from
Lean's environment, not inferred from source theorem lines. Together with the unchanged
cycle and collar-extension audits above, all eight modules are covered. The final source
contains 24 mathematical declarations: 16 public theorems and 8 private helpers.

Evidence under the private root from the preceding entry:

- `queue-q3-source-manifest-20260922.json`
- `queue-boundary-suite-audit-20260922.json/.log`
- `queue-boundary-declarations.txt`
- `queue-boundary-suite-audit-source-20260922.txt` (exact replayable audit text; scratch Lean file removed)
- The unchanged `queue-cycle-audit-20260922` and `queue-collar-audit-20260922` receipts.

Source review found no sorry, axiom, unsafe proof escape, resource override, linter suppression,
declaration docstring, inline comment or long Lean line. Only required headers/module docstrings
remain. Owned-path `git diff --check` passed. No Git write, mirror write, existing proof-module
edit, frozen-signature edit, aggregate edit or acceptance-ledger edit was performed.

Queue accounting: Q1/Q2 were already completed by other lanes and only reverified here.
Q3 has these checked reusable deliveries. Q4 remains as the earlier reconnaissance files:
the descent-sequence and protected-circle-removal assemblies are still explicitly partial.
Q5/Q6 were not started in this batch. The lead still owns integration and independent acceptance.

## Codex overnight Q3(i) — chart transport and graph-cycle probe (2026-09-23)

Status: PARTIAL. The planar prescribed-boundary extension has been transported through arbitrary
PL charts of closed complementary surface disks in E3. The real module
SphereHoledBoundaryExtension.lean proves
IsPLHomeomorphOn.exists_holed_surface_extension_of_planar_charts and
IsPLHomeomorphOn.exists_holed_surface_extension_of_prescribed_boundary_maps. The latter
takes actual prescribed E3 boundary maps, proves a PL map of the charted holed regions,
and agrees with every prescribed boundary map. Its reference disk map and positive
relative circle corrections are explicit inputs. It does not claim that the frozen CGN
geometry has produced those inputs or that its edge matching leaf is closed.

Checker success line:
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\SphereHoledBoundaryExtension.lean with no diagnostics; shared outputs unchanged.

SHA-256:
- SphereHoledBoundaryExtension.lean: 59EF30F80DE9B86880212474B44D9A53482449B1BBBD3138CBA3D9654A51A49B
- Skeleton/OrientationCharacterBridge.md: F3E5317A44BA291B4B4FB7BCDCA7BAB9CADC39F9D37F1E55E8CFD208EADCB00B

The private checker receipt has Lean exit 0, zero diagnostics, stable source, and unchanged
shared outputs. The two theorem axiom closures contain only propext, Classical.choice and
Quot.sound. The external audit's raw Lean exit was 0; its scratch source produced only
long-line warnings on the two diagnostic commands, not on the module source.

Sub-leaves still required for the frozen CGN assembly (exact scopes in
Skeleton/OrientationCharacterBridge.md):
1. exists_planar_chart_of_spherical_complement, including intrinsic rim transport;
2. exists_marked_sphere_reference_maps, jointly across shared disks;
3. relative_orientation_character_cycle_zero from the original embedding, with no
   global-orientability assumption;
4. exists_vertex_signs_of_cycle_zero for the finite incidence graph;
5. positive_boundary_corrections_of_vertex_signs;
6. exists_joint_boundary_matching_of_orientation_character, preserving all four
   boundary-map and overlap equations.

The graph-cycle equality is stated as an output obligation in the probe, not added as a
hypothesis to a frozen endpoint. No Opus-owned file, frozen statement, aggregate, or Git state
was changed.

## Codex overnight Q2 — canonical-tower probe recheck and centered disk (2026-09-23)

Status: PARTIAL. The exact existing Skeleton/CanonicalTowerReduction.lean source was checked
against a fresh private import closure: Lean exit 0, source stable, two expected sorry warnings
at its geometric child leaves, and no other diagnostic. The lead's three errors from its
22:00 recheck (two omega and one simp mismatch) did not reproduce. The probe source was not
changed. The wrapper cannot emit a no-diagnostics success line for a probe containing the
two explicitly retained sorry warnings; its raw Lean result is the compiler evidence.

A real bounded sub-leaf was extracted as SplitDiskCenter.lean. For any IsTube edge, it
constructs a PL parametrization of its actual splitting disk that sends the standard
simplex center to the graph edge centroid and retains the intrinsic rim. This proves the
marked-disk part of the relative cylinder-coordinate construction, not the whole cylinder.

Checker success line:
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\SplitDiskCenter.lean with no diagnostics; shared outputs unchanged.

SHA-256:
- SplitDiskCenter.lean: 750D3A737447A11D386B6F4C0A52ECAECE2F78593D81FBC0DFCD7E13497BBD14
- Skeleton/CanonicalTowerReduction.lean (unchanged): F402C9CDB20349317716D909D765AB0D78A77F335502A1DA3FF1A123786A6190

SplitDiskCenter's private receipt has Lean exit 0, zero diagnostics, stable source and
unchanged shared outputs. Its axiom closure is propext, Classical.choice and Quot.sound.

Exact remaining child leaves of the tower probe:
1. exists_splitDisk_cylinder_coordinates: the center and intrinsic rim are now handled by
   SplitDiskCenter; still build compatible maps on both PL 3-ball halves, then transport a
   round-cylinder model to their union and through the tube embedding.
2. exists_controlled_revolved_tower: construct the joint bi-infinite radial exhaustion with
   exact two tail closures, W containment, Z avoidance, and local finiteness. This is the
   substantial geometric producer and still has sorryAx.

The conditional single-torus supply, even/odd GP choice, triple restriction, and tower
assembly remain elaborated but cannot be called axiom-free while the two leaves are open.
No Opus-owned module, frozen declaration, aggregate, or Git state was changed.

## Codex overnight review checks 0b and 0 (BH/BI; 2026-09-23)

Scope: due-diligence notes only, as explicitly requested. The two new notes are
`consult/BH-compression-codex-check.md` and `consult/BI-branch-tube-codex-check.md`.
Neither frozen leaf nor its interface was edited or proved. The reviewer's geometric
fixture remains outside the checkout; the notes distinguish source checks from paper claims.

SHA-256:
- BH-compression-codex-check.md: F17E7E3C1A099004FCF10577FA9229BDEE32AFE03E43841FC71BE884FF1D665D
- BI-branch-tube-codex-check.md: FA5A7FF76674C6007CB9ACA7332FDFB029D0B55DB49CFFEA3FCCFAF05BA2E4C0

Checker success line: not applicable to Markdown due-diligence notes. A proposed BI Lean
interface probe was rejected by automatic approval review before execution because the user's
BH/BI scope was read as notes only; no such probe file was created. Source search confirms
that the actual transport theorem uses its full-ray equality only at t=0 and t=1.

Open sub-leaves recorded for BH: controlled thin PL shell; an arc in interior N avoiding rim
and obstacles; a sufficiently small regular tube whose shell complement is a PL 3-ball;
field-by-field invariants and exact trace/crossing counts; two-tetrahedra exterior escape.
Open sub-leaves recorded for BI: actual endpoint-restricted interface edit and cone rebuild
by the lead; construction of a derived marked tube and endpoint matching; a joint non-vacuity
fixture. No completion claim is made for either review leaf.

## Codex overnight Q4 — solid-torus interior H1 injection (2026-09-23)

Status: CLOSED as a reusable theorem in the new real module
`SolidTorusInteriorHomology.lean`. The radial disk-factor homotopy gives a left inverse on
integral first homology to the inclusion `interior S -> S`, for every
`IsTopologicalSolidTorus S`. The statement is the actual map, not a packaged hypothesis.
It supplies both the SpineCarrier and TorusLinking interior-inclusion leaf shapes by
unfolding their local `firstHomologyInclusion` definitions; those existing skeletons remain
unchanged and are not claimed fully closed.

Checker success line:
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\SolidTorusInteriorHomology.lean with no diagnostics; shared outputs unchanged.

SHA-256:
- SolidTorusInteriorHomology.lean: 0BEC8C765610756824814D6E14F4064428B4658C652CE672294A0808A1E6F38E

Sub-leaf list: the two interior-inclusion injection shapes above are proved by this one
canonical theorem. The other Q4 leaves (`exists_maximal_firstHomology_image_of_disjoint_polygons`,
`hurewiczOne_injective_of_isTopologicalSolidTorus`, and
`face_rim_subset_interior_deleted_family`) remain for separate work. The private receipt
has Lean exit 0, zero diagnostics, stable source and unchanged shared outputs.

## Codex overnight Q4 — solid-torus degree-one Hurewicz injection (2026-09-23)

Status: CLOSED in the new real module `SolidTorusHurewiczOne.lean`. It builds the actual
fundamental-group and H1 equivalences with ℤ, obtains Hurewicz surjectivity from path
connectedness, and proves a surjective additive endomorphism of ℤ is injective. No
fundamental-group conclusion was added as a hypothesis.

Checker success line:
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\SolidTorusHurewiczOne.lean with no diagnostics; shared outputs unchanged.

SHA-256:
- SolidTorusHurewiczOne.lean: 5D476B2F5CA7DD0065EF112E5E82A16317233D6BC0B4E532E64419062E058D24

Sub-leaf list: `hurewiczOne_injective_of_isTopologicalSolidTorus` is proved as
`IsTopologicalSolidTorus.hurewiczOne_injective`. Remaining Q4 items are maximal image
among disjoint polygons and face-rim localization. Private checker receipt: Lean exit 0,
zero diagnostics, source stable, shared outputs unchanged.

## Codex overnight Q4 — face-rim localization (2026-09-23)

Status: CLOSED as a stronger, smaller-input theorem in the new real module
`FaceRimInteriorDeletedFamily.lean`. It proves a general local-finite closed-subfamily
lemma, shows a face rim lies in the graph skeleton, then restricts the neighborhood of
the whole Dv family to vertices incident to the chosen face. The actual conclusion is
`h '' simplexRim 𝒦 s.1 ⊆ interior (section34FaceTorus Dv s)`; it needs only `hQsep`,
`hQlf`, `htor`, `hDv`, `hDvQ` and `hDnbhd` from the larger skeleton leaf.

Checker success line:
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\FaceRimInteriorDeletedFamily.lean with no diagnostics; shared outputs unchanged.

SHA-256:
- FaceRimInteriorDeletedFamily.lean: 706080191302970488215C1625D702279211DBE2CF5651ED86C9BF76AA5853E9

Sub-leaf list: `face_rim_subset_interior_deleted_family` is proved under fewer natural
inputs; only the disjoint-polygon maximal-image Q4 leaf remains in this queue. The
private checker receipt has Lean exit 0, zero diagnostics, stable source and unchanged
shared outputs. No frozen skeleton statement was edited.

Q4 axiom audit (private root `q4-axioms-audit.json/.log`): raw Lean exit 0,
stable scratch source, unchanged shared outputs. Each of the three public theorem closures
contains exactly `propext`, `Classical.choice`, and `Quot.sound`; none contains `sorryAx`.
The audit wrapper reports nonzero because `#print axioms` emits informational lines, while
each module's separate delivery checker above has a zero-diagnostic success line.

## Codex overnight remaining gates — Q4 maximal image, Q6 fixtures, Q5 condition

Q4 maximal image remains OPEN. The required proof is not merely finite selection of
subgroups of ℤ: images 2ℤ and 3ℤ are incomparable. It needs the torus-specific fact that
disjoint nonseparating PL circles have equal inclusion-image subgroups, and that a
separating circle has zero image. Opus-a's in-flight `TorusCircleHomology.lean` reports
exactly those range theorems in `OPUS_FILL_LOG_A.md`, but there is no final worker report
and this lease has not imported, edited or claimed that file. Once the lead accepts it,
the remaining child is a finite nonempty selection and range comparison for the actual
`G : Fin (n+1) -> Set E3` family.

Q6 fixtures remain OPEN; no misleading empty or conditional inhabitant was added.
For `IsHandleDecompositionOfTube`, `exists_isTube` supplies a genuine edge, two dual
balls and a splitting disk. A fixture still has to turn each image disk into a marked
`IsPseudoCell`, prove exact rim/frontier and graph intersection, and identify each
handle piece as the closure of the corresponding component of the complement of all
pseudo-cells. For `Section34VertexPreparation`, a fixture must jointly realize the
nonempty vertex and edge indices, PL balls, nested solid tori, annuli, collars, local
finiteness and all distance-margin clauses of the actual preparation predicate.
For `IsCanonicalTower`, the finite standard configuration in the §31 skeleton is
conditional on `Moise307` and other open inputs; it does not supply the bi-infinite
compatible tower, its two exact tail closures or local finiteness. These are the exact
remaining construction sub-leaves, not extra hypotheses to any requested inhabitant.

Q5 gate is now met for reconnaissance: `OPUS_FILL_LOG_D.md` Batch 8 reports the smooth
disk taming leaf verified and the smooth annulus leaf STUCK with an exact remaining goal.
That goal is a compactly supported isotopy of an embedded essential annulus core to a
smooth core inside a prescribed open set, followed by a smooth bicollar. The current
pointwise surface-chart smoothing result does not supply an isotopy of an entire
essential circle. No new Q5 theorem was claimed or worker-owned file touched.

Checker success line and SHA-256: none for these still-open construction items; no new
Lean module or probe was created for them. The completed Q3/Q2/Q4 modules and their
checker lines, hashes and child lists are recorded above.

Consumer-audit limit for the interior-H1 theorem: the checker deliberately excludes
private `.olean` imports whose receipts have diagnostics. The two skeleton probes still
contain `sorry` warnings, so an external scratch consumer importing them could not be
compiled through that checker. The claimed fit to their leaves is source-level unfolding
of the two displayed `firstHomologyInclusion` definitions; it is not a checked edit to
either skeleton. The standalone producer theorem and its axiom closure were checked above.

## Codex day queue item 1 — maximal polygon image (2026-09-23)

Status: CLOSED in new real module `MaximalPolygonHomologyImage.lean`, importing the
accepted `TorusCircleHomology` and solid-torus frontier PL-torus producer. For a
nonempty finite family `G : Fin (n+1) → Set E3`, choose any nonseparating circle
if one exists. Every other nonseparating circle has the same actual inclusion
image in `H₁(S)` by `IsPLTorus.range_integralSingularHomologyMap_eq_of_disjoint`;
every separating circle has zero image by the companion theorem. If all
circles separate, choose index zero. The theorem has the exact skeleton inputs
and conclusion, with the inclusion map unfolded; the frozen probe was not edited.

Checker success line:
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\MaximalPolygonHomologyImage.lean with no diagnostics; shared outputs unchanged.

SHA-256:
- MaximalPolygonHomologyImage.lean: 08C157F63FFA604374FE8EC8A7935B34A586E0946DBBAB85D5DEB588D9CCA0EC

Sub-leaf list: finite nonempty selection; separating-circle zero range;
disjoint nonseparating-circle equal ranges; transport of `id '' G i` to the
actual inclusion `G i → S`. All four are closed, the last three by the cited
accepted theorem or a proof-independent set equality. A private axiom audit
reported only `propext`, `Classical.choice`, and `Quot.sound`, no `sorryAx`.
The audit wrapper returns nonzero only because `#print axioms` emits information;
the module checker above has zero diagnostics. `TorusCircleHomology` was
refreshed in this lease's private output with zero diagnostics; shared outputs
were unchanged.

## Codex day queue item 1b — compact source face order (2026-09-23)

Read `consult/BM-section34-compact-source-face-cut-order-review-digest.md`
before the probe. The new `Skeleton/CompactSourceFaceOrderReduction.lean` leaves
exactly four named proof frontiers: (1) a codimension-one facet between every
proper pair of nested source cells (the pure-dimensional boundary tiling),
(2) exactly two one-cells at a marked boundary point of a split disk,
(3) exactly two two-cells at a one-cell of a vertex-ball boundary, and
(4) classification of each codimension-one containment by the existing
`Section34CompactCutStep` constructors. From (1) and (4), the probe proves
containment implies cut order by strong induction on dimension; from (4) and
the real step-dimension lemma it proves cut order implies containment by
relation induction. These are directional reductions, not a restatement or
edit of the frozen `compactSourceFace_iff_cutLe` declaration. No frame clause
was added. The existing `Section34CompactSplitDiskIntersection` gives the
intersection control needed inside frontier (4).

Probe checker receipt: raw Lean exit 0, source stable, zero errors, exactly
four warnings (`declaration uses sorry`, one at each named frontier). The
zero-diagnostic checker success line is unavailable because this explicitly
authorized probe contains four `sorry`s; the wrapper accordingly reports
`Verification failed` solely for those diagnostics. Probe SHA-256:
- Skeleton/CompactSourceFaceOrderReduction.lean: E93D2EDF12A1F1F056BABC1332E7A91185FD75CA9F646F905D67E9E48EB91BA3

The new real module `Section34CompactFacePoset.lean` closes four elementary
sub-leaves: each `CutStep` raises dimension by one; intrinsic source boundary
lies in the source cell; the boundary of a three-cell equals its ambient
frontier; equal source cells have equal labels (using `IsPLCellOn.dim_eq` and
the existing frame dimension clause). The probe imports this module.

Checker success line:
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\Section34CompactFacePoset.lean with no diagnostics; shared outputs unchanged.

SHA-256:
- Section34CompactFacePoset.lean: F451F33329CC345DA9020B0E93EF8F078995BADB1873BDCE8C5AFE0DA1C17572

All four real theorem axiom closures contain only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. The private axiom
audit wrapper returns nonzero only for the informational `#print axioms`
lines. The accepted `Section34CompactVocabulary` and
`Section34CompactSplitDiskIntersection` dependencies were refreshed into this
lease's private output with zero diagnostics; shared outputs were unchanged.

## Codex day queue item 2 — spine chain cut and polygon resolution (2026-09-23)

The `integralFirstHomology_interior_injective` probe leaf is exactly
`IsTopologicalSolidTorus.integralSingularHomologyMap_interior_injective` from
`SolidTorusInteriorHomology` after unfolding its local
`firstHomologyInclusion`; it was not re-proved.

Status of `exists_frontier_cycle_of_boundary_in_open`: PARTIAL. The new real
general-topology module `Topology/Homology/RelativeChainCut.lean` proves
`exists_interface_cycle_of_boundary_difference`: if two closed integral
1-cycles on the two sides of an open cover differ by the boundary of a
2-chain, a cycle on the overlap is homologous to the first through a chain
supported on its side. The proof subdivides the actual bounding chain,
splits the small chain, and checks both support and boundary identities.
This is the open-cover chain step, not the exact PL-frontier cut.

Checker success line:
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\Homology\RelativeChainCut.lean with no diagnostics; shared outputs unchanged.

SHA-256:
- Topology/Homology/RelativeChainCut.lean: 34F8078BD555656C15458F9518E28B52A9BF3B1E2321354521CF539C005FEFFE

Sub-leaf list for the exact skeleton chain cut: (1) open-cover relative
boundary cut, CLOSED in the module above; (2) choose the two open sides of a
PL frontier with the needed compact-support margin in `A`, OPEN; (3) retract
the resulting overlap cycle to `frontier S ∩ A` and keep its bounding chain
inside `S`, OPEN. The existing bicollar producer gives local topology but
no checked chain homotopy with these simultaneous support controls.

Status of `exists_disjoint_oriented_polygons_of_cycle`: OPEN. Its independent
sub-leaves are (1) a finite PL representative of the supported class within
the relatively open surface patch, preserving its image in `H₁(S)`;
(2) oriented edge-cycle resolution at vertices; (3) disjoint PL circle
extraction inside the same patch, with each circle's integral generator
cycle and the weighted class equation. Existing polygonal-cycle theorems
start from an already simplicial cycle or 2-regular graph and do not supply
the support-preserving singular-to-PL step. No misleading direct producer
was added. The real open-cover theorem's axiom closure contains only
`propext`, `Classical.choice`, and `Quot.sound`, no `sorryAx`; the private
axiom audit wrapper returns nonzero solely for its informational line.

## Codex day queue item 3 — torus linking sub-leaves (2026-09-23)

The three frozen `Skeleton/TorusLinkingReduction.lean` leaves remain OPEN, in
the requested order. Two reusable, zero-`sorry` preliminaries now compile.

1. `subsingleton_firstHomology_complement_of_isPLBall`: the needed
   decomposition is a PL regular 3-ball neighbourhood `N ≅ D² × [-1,1]` of
   the embedded disk `Δ`, followed by Mayer–Vietoris for `ℝ³ \ Δ` between
   the exterior of `N` and its two disk sides. The exterior has zero `H₁`,
   each side has zero `H₁`, and the `H₀` incidence map of the two components
   of the overlap must be injective. The current `IsPLBall 2 Δ` provides a
   parametrization of `Δ` but not this ambient neighbourhood and its
   complement deformation maps. OPEN.
2. `exists_integer_linking_equiv_of_isPLSphere`: choose a PL solid-torus
   regular neighbourhood `N` of the arbitrary possibly knotted circle `G`.
   Mayer–Vietoris on `ℝ³ = Int(N) ∪ Ext(N)` needs the actual maps from the
   boundary torus (`H₁ ≅ ℤ²`) to `N` (`H₁ ≅ ℤ`) and the exterior, plus
   `H₁(ℝ³)=H₂(ℝ³)=0`. The meridian is a primitive kernel generator, giving
   the exterior and hence `Gᶜ` an integral `H₁ ≅ ℤ`; a type-level rank
   calculation alone does not identify this map. OPEN.
3. `surjective_firstHomologyInclusion_complement_of_null_meridian`: from a
   nonseparating boundary circle, prove its primitive slope on `∂S`; the
   given null map to `π₁(S)` makes it the meridian of the *actual* solid
   torus `S`. The inclusion `Int S → Gᶜ` must then be shown to have linking
   degree `±1`, using a collar/regular-neighbourhood Mayer–Vietoris diagram
   and naturality. No unknotted ambient model may be assumed. OPEN.

`Topology/Homology/EuclideanThreePunctureFirstHomology.lean` proves that
`H₁(ℝ³ \ {p}; ℤ)=0` by radial retraction to `S²` and its checked sphere
homology. `Topology/Homology/ComplementHomeomorphHomology.lean` proves the
actual complement homeomorphism induced by an ambient homeomorphism and its
integral homology equivalence, with a subsingleton transport iff. The latter
cannot be applied to a PL disk's own parametrization without an ambient
extension theorem.

Checker success lines:

Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\Homology\EuclideanThreePunctureFirstHomology.lean with no diagnostics; shared outputs unchanged.

Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\Homology\ComplementHomeomorphHomology.lean with no diagnostics; shared outputs unchanged.

SHA-256:
- EuclideanThreePunctureFirstHomology.lean: 177D7FA15A3BD88FBAB6198E51334F4FC54E0E88D7B4EFC832BFC72813AF89A9
- ComplementHomeomorphHomology.lean: 19A87CA38099B1D187B23AE7A243DB0270847723DEF87524C13C2FD2DDD3AD71

Private `#print axioms` checks of all four new declarations report only
`propext`, `Classical.choice`, `Quot.sound` and no `sorryAx`; the audit
wrapper reports failure solely because the requested `#print axioms`
commands emit information. No general Alexander-duality statement is used.

## Codex day queue item 4 — split-disk cylinder coordinates (2026-09-23)

`exists_splitDisk_cylinder_coordinates` remains PARTIAL. The new real module
`TubeCenteredPrismCoordinates.lean` closes the common-disk and compatible
three-ball-half portion. It applies `SplitDiskCenter` to select one PL disk
parametrization carrying `stdCenter 1` to the edge centroid, uses the actual
`IsTube.interEdge` equality and both `splitDisk_subset_frontier` facts, and
extends that *same* disk map over both dual PL 3-balls. The resulting prism
map is a PL homeomorphism onto `C u ∪ C v`; its middle disk and intrinsic rim
have the exact `D {u,v}` and `Dbd {u,v}` images, its center is the centroid,
and its two half-prisms map to `C u` and `C v` separately. A fourth theorem
shows the tube map `h` is an embedding on this pair of balls.

Remaining sub-leaf list: (1) a homeomorphism between the queue's *round*
`Skeleton/CanonicalTowerReduction.cylinder` and the triangular prism that
identifies the round middle disk/rim with the simplex middle disk/rim and
sends the round origin to `stdCenter 1`; the available simplex-to-ball
homeomorphism has no checked center equation, so its mark must be adjusted;
(2) compose that model map, the proved prism map, and the tube embedding,
then verify all five fields of `DiskCoordinates` for the exact images under
`h`. No new premise is needed from `IsTube`; this is model-coordinate and
transport work, not a new ball-gluing theorem. The frozen skeleton leaf was
not changed.

Checker success line:

Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\TubeCenteredPrismCoordinates.lean with no diagnostics; shared outputs unchanged.

SHA-256:
- TubeCenteredPrismCoordinates.lean: E3C383931184ACECF702CEB7E6BCBE8339CF0680ADE8E30CDB7483FF83B7BCD6

Sub-leaf proof list: generic PL ball-pair prism gluing; centered split-disk
extension; exact middle disk/rim and half images; restricted tube embedding.
All four axiom closures contain only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`. The scratch axiom audit emitted one scratch
line-length warning and four informational `#print axioms` lines; the real
module checker was zero-diagnostic.

## Codex day queue item 5 — Section 32 reconnaissance (2026-09-23)

The three frozen leaves in `Skeleton/Section32PseudoCell.lean` were not edited.
Three new probe modules elaborate with raw Lean exit code 0. The private
checker intentionally does not print a success line for them: it rejects the
named `sorry` warnings. Receipts report stable source and no shared artifact
changes. Exact remaining `sorry` counts are 3, 2, and 2 respectively; the
assembly theorem in each probe has no `sorry`.

`Section32AnnularChainProbe.lean` splits
`isOpenTopologicalCell_annularChain` into (1) the two-ended open-cell
compactification, OPEN; (2) local polyhedrality off the center, CLOSED by
`IsAnnularChain.locallyPolyhedral_off_center`; (3) closure adding exactly the
intrinsic split-disk rim, OPEN; (4) the local pair of PL 3-balls meeting in a
PL disk, OPEN. The center-free annulus pieces and their containment in the
tube-pair interior are also real lemmas. Local finiteness of the canonical
tower reduces each neighborhood to finitely many half/bridge annuli.

`Section32GeneralPositionProbe.lean` splits
`exists_generalPosition_ball_pseudoCell` into (1) a small PL ball whose
frontier has a finite transverse polygon trace and crosses the pseudo-cell,
OPEN; (2) a topological subdisk of `Eint` absorbing the ball's trace inside
the same metric ball, OPEN. A positive radius and the given pseudo-cell do
not themselves provide general-position perturbation.

`Section32ReducedDiskProbe.lean` splits
`exists_reducedDisk_of_crossesPseudoCell` into (1) outermost PL disk
selection with its intrinsic simplex rim, ambient neighborhood control and
the exact intersection `Δbd = Δ ∩ Ec`, OPEN; (2) a topological subdisk of
`Ec` bounded by that rim and containing the center in its intrinsic
interior, OPEN. The latter is a Jordan/innermost-disk step, not a PL
structure assertion at the potentially wild center.

Checker success line for the real module:

Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\AnnularChainLocalPolyhedral.lean with no diagnostics; shared outputs unchanged.

SHA-256:
- AnnularChainLocalPolyhedral.lean: 462CBAF389AB47D8E54E94F4C34F4028466DE2E1685048ECED91E547A41D227F
- Section32AnnularChainProbe.lean: 6BFEB4766F2F2664615262A51FC330DEBD30C9EE14C8C6FA06794ABE791BC6BE
- Section32GeneralPositionProbe.lean: DD252A8A163CEDBEE984676F6F6C8337FBCFCB76BEC4AE70B3B6439D940BA95B
- Section32ReducedDiskProbe.lean: C4182F7A4FEAF090BCF60F64335CFAD1E76A9939EAA1B430F4619DC4F61025E1

The real module's five declaration axiom closures contain only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. Its `#print axioms`
audit exited 0; the wrapper treated the five intentional information lines
as diagnostics. Probe receipts each have Lean exit 0 and only the named
`sorry` warnings (3/2/2); hence there is no zero-diagnostic checker success
line to claim for a probe.

## Codex day queue item 6 — Q6 fixtures (2026-09-23, in progress)

The IsHandleDecompositionOfTube fixture is CLOSED as a genuine nonempty
exists_isHandleDecompositionOfTube theorem. Its witness has a real edge,
uses the identity embedding of an actual derived-neighborhood tube, and takes
each edge pseudo-cell to be the PL splitting disk, with intrinsic open disk
and rim. The handle pieces are the actual dual 3-balls. The proof identifies
each with the closure of the corresponding connected component after every
splitting disk is removed; thus componentClosure is proved, not bypassed.
All fields of IsHandleDecompositionOfTube elaborate directly.

Reusable sub-leaf list, all CLOSED: (1) the intrinsic interior of a
topological cell is an open cell and its complementary rim is a sphere;
(2) a marked PL disk is a pseudo-cell; (3) all splitting disks in a genuine
tube are centered pseudo-cells, including an identity-embedding instance;
(4) each dual 3-ball minus all splitting disks is connected and dense;
(5) the resulting connected-component closure is exactly that dual ball;
(6) assembly of the nonempty handle decomposition.

Checker success lines:

Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\TopologicalCellInteriorOpen.lean with no diagnostics; shared outputs unchanged.

Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\PLDiskPseudoCell.lean with no diagnostics; shared outputs unchanged.

Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\SplitDiskPseudoCellFamily.lean with no diagnostics; shared outputs unchanged.

Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\TubeSplitDiskComponents.lean with no diagnostics; shared outputs unchanged.

Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\HandleDecompositionTubeFixture.lean with no diagnostics; shared outputs unchanged.

SHA-256:
- TopologicalCellInteriorOpen.lean: 0D19BB6FD60200FD11F5D2B1C0B153799A627E8FFBF3D50A510B1A34F87ABE11
- PLDiskPseudoCell.lean: F661C6C755C7E58AC090390DF73EB2A8F78B1502A76BDA072590CAB056D61F80
- SplitDiskPseudoCellFamily.lean: EB7D642742F75B274B95E3466336828D25B5FBDD7CCE79756DA47C3638E58392
- TubeSplitDiskComponents.lean: 23EF90595A7AEE528C541EFF1DC67E628E7B753FEC6DEA7C4E45BEA2981BD73E
- HandleDecompositionTubeFixture.lean: 2EB5E85B356BB8DAF22755BF4E68F2AB7FF8215A548D26C1AF5F34D2A9C15D37

The private axiom audits of the new declarations and of the
handle-decomposition fixture report only propext, Classical.choice,
Quot.sound, with no sorryAx. The audit wrapper reports nonzero only
because the requested #print axioms commands emit information; the real
module checker lines above are zero-diagnostic.

The other two Q6 fixtures remain OPEN after checking their exact on-disk
predicates. No empty-index or conditional theorem was presented as an
inhabitant.

Section34VertexPreparation sub-leaf list: (1) construct an actual
LocallyFinitePLPieceIn source pair with nonempty Section34VertexIndex and
Section34EdgeIndex, and a compatible cut label source; OPEN. The current
Section34CutFrame has no proved nonempty inhabitant. (2) For each edge,
realize two nested regular-neighborhood solid tori around the piercing
circle, three annuli with their marked end circles, and the required
fundamental-group generator maps; OPEN. (3) Choose pierced/enlarged PL
3-cells and compact graph cores, then a common positive tolerance satisfying
all one-sided and sum-distance clauses, the stability scale and overlap
conditions; OPEN. The frozen exists_section34VertexPreparation is a sorry
producer, so importing it would not audit as a fixture.

IsCanonicalTower sub-leaf list: (1) construct a genuine bi-infinite
compatible IsRevolvedTorusChain family, not the finite three-cell standard
configuration; OPEN. (2) Map it through a marked splitting-disk cylinder
with the exact annulus image and two distinct tail closures, one at the
center and one at the rim, plus local finiteness away from the center; OPEN.
(3) Supply nested fitted PL solid tori and adjacent general position for
every integer window without the unproved global Moise307 input; OPEN.
ControlledRevolvedTower.exists_canonicalTower is a checked conditional
consumer of Moise307, while exists_controlled_revolved_tower itself is an
open frozen leaf. Neither certifies a standalone fixture. No checker success
line or SHA-256 exists for these two uncreated fixtures.


## Codex item 7 — CGN edge matching, checked partial layer (2026-09-23 14:40 UTC)

Worker: Codex, owner-authorized lease codex-moise-recon, token codex-moise-recon-20260922, private output root C:\Users\liao9\AppData\Local\Temp\codex-moise-recon. The host guard was checked before every compile; the count was below four each time. Only new Lean files were written. No frozen source, Opus-owned source, root aggregate, lease, or Git state was edited.

Sub-leaf accounting, in queue order:

1. exists_vertex_signs_of_cycle_zero is CLOSED in GraphCoboundary. Its edgeBoundary counts both endpoints over ZMod 2; a loop contributes zero, while parallel edges remain separate edge labels. The proof works for arbitrary vertex and edge types via finite-support chains, derives the annihilator condition from every finite mod-two cycle, and uses linear duality to produce the vertex signs.
2. The planar-chart input layer is checked. Section34SplitDisksDisjoint proves distinct source splitting disks disjoint from the cut-frame vertex-incidence clause. PLCellPullback transports intrinsic disk coordinates into a vertex-cell model. PLCellBoundaryHoledChart gives a planar chart of the complementary sphere disk with the other marked disks in its planar interior and intrinsic rims on planar frontiers. Section34BoundaryDiskFamilies verifies the exact source and target incident-disk premises from the frozen clauses. A single theorem choosing a marked incident edge at every vertex is still OPEN: the generic chart theorem takes a chosen disk, and the nonempty incident-edge choice has not been exported from the cut frame.
3. The simultaneous edge-disk choice is CLOSED. PLCellPairMap maps two genuine PL cells and their intrinsic boundaries; Section34SharedDiskMaps chooses one map φ e for each edge, used at both endpoints, with exact disk and rim images. The stronger item-2 reference sphere maps agreeing pointwise on all incident disks remain OPEN. HoledSphereExtension yields a reference holed-sphere map from one outer rim map and sends the other labelled rims to their target sets, but pointwise agreement with the selected φ e on those other rims needs positive corrections. This is the orientation-character work of items 3–5, not supplied by independent reference choices.
4. Item 3 remains OPEN. The proposed whole-cell closeness route cannot be read from the frozen leaf: exists_section34PiercingPackage separately returns ∀ w x ∈ Cc w, dist (G w x) (h x) < ε w, but Section34PiercingConditions has no such field, and frozen exists_section34EdgeMatching receives only hpack after protected removal. The call site has hcore₂ and hDmark from prior work but does not pass either to this leaf. This does not prove the leaf false. An alternative anchor is now checked: LocallyFiniteClosedCover plus Section34VertexMarkerInterior derive h '' simplexBody 𝒦' w.1 ⊆ interior (Dv w) from the frozen neighborhood, separation and local-finiteness clauses. PLCellInteriorImage and Section34VertexInteriorOverlap then prove (h '' interior (src (.vertexBall w)) ∩ interior (Dv w)).Nonempty at every vertex. The remaining producer must relate these anchored local degrees across each shared splitting disk and every mod-two edge cycle, using the actual h paths and target disk placements. No orientation-cycle equality or edge sign has been claimed.
5. Positive corrections, joint boundary matching, nested torus, and the frozen endpoint remain OPEN; queue order was respected.

Named-module checker success lines (each receipt: Lean exit 0, diagnosticLines = 0, stable source hash, shared outputs unchanged):

Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\Combinatorics\GraphCoboundary.lean with no diagnostics; shared outputs unchanged.
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\Section34SplitDisksDisjoint.lean with no diagnostics; shared outputs unchanged.
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\PLCellPullback.lean with no diagnostics; shared outputs unchanged.
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\PLCellBoundaryHoledChart.lean with no diagnostics; shared outputs unchanged.
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\Section34BoundaryDiskFamilies.lean with no diagnostics; shared outputs unchanged.
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\PLCellPairMap.lean with no diagnostics; shared outputs unchanged.
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\Section34SharedDiskMaps.lean with no diagnostics; shared outputs unchanged.
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\Compactness\LocallyFiniteClosedCover.lean with no diagnostics; shared outputs unchanged.
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\Section34VertexMarkerInterior.lean with no diagnostics; shared outputs unchanged.
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\PLCellInteriorImage.lean with no diagnostics; shared outputs unchanged.
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\Section34VertexInteriorOverlap.lean with no diagnostics; shared outputs unchanged.

SHA-256:

- GraphCoboundary.lean: 111AA1B8247ADCBC6D90F4CCD0C7146937E693D0901E3B462966E366DA8F32F3
- Section34SplitDisksDisjoint.lean: 1F032CD2B4BB073F8022F8BA7BE691ACA803C3A3AD37A923348EB96682C3FD98
- PLCellPullback.lean: 4076669D7D5A37E73B6CBE6B42CDF560F5068BA6591FBB9F0E448CEBD9D3C0EF
- PLCellBoundaryHoledChart.lean: 10FC5D3923377A0C138428D4EDEF9122FE554950E9C02495326FE80B372DBFBD
- Section34BoundaryDiskFamilies.lean: F68F282F9D244873E2F33C57A38CCEED1D860DE885C23D791EF001BDDFC5E537
- PLCellPairMap.lean: E63E1DBCB51FCBC03A95FB4D915FE260357F026A1395A647764497457C1CC0F5
- Section34SharedDiskMaps.lean: A5BBE221D58713445B71D57A5C9CF9A47120132DA3AD511DF7C48883D4AD9ED2
- LocallyFiniteClosedCover.lean: 6B0B29D9B99F199CC13D87CD5EB56E31A21802978F2C7B8D02FFB5EE06A24198
- Section34VertexMarkerInterior.lean: 7D5E2FFE55C3EE027DA76503D441DC55B1DB9CFA29F1E9F82D68E170CEAC6A71
- PLCellInteriorImage.lean: 048C376FA85C08EBE7766E92CECBCC39EDBBDA4F5388AF257273D034FB665FBE
- Section34VertexInteriorOverlap.lean: 7F23553F1A9111A0FA89CAD02030B39B266763355B62822EF1552B98D5AAFB22

External #print axioms audits of the new public endpoints all exited 0 and found only propext, Classical.choice, and Quot.sound, with no sorryAx. The wrapper reports the intentional information lines as diagnostics. PLCellBoundaryHoledChart imports the Opus-b HoledSphereExtension at source SHA-256 EA8F04D298CD020434EC22EEDD4EC777FDFDEBD0644B13D015D3FC690D7914D7; the worker's CLOSED receipt has the same bytes. It was only read and imported. The lead still owns acceptance, aggregate registration and commit.

## Codex C1 surface trace - local subcomplex trace check (
2026-09-23T14:42:53.9105134Z
)

Module: DerivedCellSurfaceTrace.lean. Checker exit: 
1
.
SHA-256: 
088A2AE5BF06617BDB08ADD22C3E6E22161F8AEFF21EDFACC711F12A710D9394
Sub-leaf list: derived cell base intersection with a subcomplex; PL ball trace for a boundary face of a manifold with boundary. The branch surface producer and frozen endpoint remain OPEN.

Checker output:
```text
D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\DerivedCellSurfaceTrace.lean:35:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  coneSet (Finset.centroid ℝ s id) (upperLink (barycentricSubdivision L) {Finset.centroid ℝ s id}).space
in the target expression
  x ∈ coneSet (Finset.centroid ℝ s id) (derivedNeighborhoodCellBase L s).space

E : Type u_1
inst✝¹ : NormedAddCommGroup E
inst✝ : NormedSpace ℝ E
K L : Geometry.SimplicialComplex ℝ E
hLK : L.faces ⊆ K.faces
s : Finset E
hs : s ∈ L.faces
hsub : (derivedNeighborhoodCellBase L s).space ⊆ (derivedNeighborhoodCellBase K s).space
hcone :
  coneSet (Finset.centroid ℝ s id) (upperLink (barycentricSubdivision K) {Finset.centroid ℝ s id}).space ∩ L.space =
    coneSet (Finset.centroid ℝ s id) (upperLink (barycentricSubdivision L) {Finset.centroid ℝ s id}).space
hrad : IsConeBase (Finset.centroid ℝ s id) (upperLink (barycentricSubdivision K) {Finset.centroid ℝ s id})
x : E
hxS : x ∈ (derivedNeighborhoodCellBase K s).space
hxL : x ∈ L.space
⊢ x ∈ coneSet (Finset.centroid ℝ s id) (derivedNeighborhoodCellBase L s).space
D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\DerivedCellSurfaceTrace.lean:40:18: error: Type mismatch
  hz
has type
  z ∈ (derivedNeighborhoodCellBase L s).space
but is expected to have type
  Finset.centroid ℝ s id + t • (Finset.centroid ℝ s id + t • (z - Finset.centroid ℝ s id) - Finset.centroid ℝ s id) ∈
    (derivedNeighborhoodCellBase L s).space
D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\DerivedCellSurfaceTrace.lean:45:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  coneSet (Finset.centroid ℝ s id) (upperLink (barycentricSubdivision L) {Finset.centroid ℝ s id}).space
in the target expression
  x ∈ coneSet (Finset.centroid ℝ s id) (derivedNeighborhoodCellBase L s).space

case h₂
E : Type u_1
inst✝¹ : NormedAddCommGroup E
inst✝ : NormedSpace ℝ E
K L : Geometry.SimplicialComplex ℝ E
hLK : L.faces ⊆ K.faces
s : Finset E
hs : s ∈ L.faces
hsub : (derivedNeighborhoodCellBase L s).space ⊆ (derivedNeighborhoodCellBase K s).space
hcone :
  coneSet (Finset.centroid ℝ s id) (upperLink (barycentricSubdivision K) {Finset.centroid ℝ s id}).space ∩ L.space =
    coneSet (Finset.centroid ℝ s id) (upperLink (barycentricSubdivision L) {Finset.centroid ℝ s id}).space
hrad : IsConeBase (Finset.centroid ℝ s id) (upperLink (barycentricSubdivision K) {Finset.centroid ℝ s id})
x : E
hx : x ∈ (derivedNeighborhoodCellBase L s).space
hxC : x ∈ coneSet (Finset.centroid ℝ s id) (derivedNeighborhoodCellBase L s).space
⊢ x ∈ L.space
Verification failed; see C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\DifferentialGeometry\Topology\Piecewise
Linear\DerivedCellSurfaceTrace.log and .json
At C:\Users\liao9\AppData\Local\Temp\claude-moise-shared\checker.ps1:121 char:76
+ ... skStable) { throw "Verification failed; see $taskBase.log and .json"  ...
+                 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    + CategoryInfo          : OperationStopped: (Verification fa...e.log and .json:String) [], RuntimeException
    + FullyQualifiedErrorId : Verification failed; see C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\Differen 
   tialGeometry\Topology\PiecewiseLinear\DerivedCellSurfaceTrace.log and .json
 
```


## Codex C1 surface trace check (2026-09-23T14:44:46.7826708Z)

Module: DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellSurfaceTrace. Checker exit: 0.
SHA-256: 0118F3309E14599577478E6ADDAB28534FE4F29C66AF56006340621EDD963087
Sub-leaf list: Derived cell base intersection with a subcomplex; PL ball trace for a boundary face of a manifold with boundary.
The branch surface producer and frozen endpoint remain OPEN.

Checker output:
```text
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\DerivedCellSurfaceTrace.lean with no diagnostics; shared outputs unchanged.
```


## Codex C1 surface trace check (2026-09-23T14:48:42.3431292Z)

Module: DifferentialGeometry.Topology.PiecewiseLinear.UpperLinkSubcomplex. Checker exit: 1.
SHA-256: 43F0875972C5D46FEC9C879F34DEFA2C8410BA5254240B3F095A4EC0FDED9C68
Sub-leaf list: The upper link of any face intersects a subcomplex exactly in the upper link calculated in that subcomplex.
The branch surface producer and frozen endpoint remain OPEN.

Checker output:
```text
D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\UpperLinkSubcomplex.lean:23:4: error(lean.unknownIdentifier): Unknown identifier `barycentricSubdivision_faces_subset`
D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\UpperLinkSubcomplex.lean:40:12: error(lean.unknownIdentifier): Unknown identifier `mem_faces_of_mem_openSimplex_of_mem_space`
D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\UpperLinkSubcomplex.lean:42:10: error: No goals to be solved
D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\UpperLinkSubcomplex.lean:48:6: error: Tactic `apply` failed: could not unify the type of `space_mono_of_faces_subset ?m.333 ?m.335`
  ?m.334 ∈ (upperLink L e).space
with the goal
  x ∈ (upperLink K e).space

case h₂.left
E : Type u_1
inst✝¹ : NormedAddCommGroup E
inst✝ : NormedSpace ℝ E
K L : Geometry.SimplicialComplex ℝ E
hLK : L.faces ⊆ K.faces
e : Finset E
hLbK : (barycentricSubdivision L).faces ⊆ (barycentricSubdivision K).faces
x : E
hx : x ∈ (upperLink L e).space
⊢ x ∈ (upperLink K e).space
D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\UpperLinkSubcomplex.lean:48:84: error: Application type mismatch: The argument
  hx
has type
  x ∈ (upperLink L e).space
but is expected to have type
  ?m.334 ∈ (upperLink K e).space
in the application
  space_mono_of_faces_subset ?m.333 hx
Verification failed; see C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\DifferentialGeometry\Topology\Piecewise
Linear\UpperLinkSubcomplex.log and .json
At C:\Users\liao9\AppData\Local\Temp\claude-moise-shared\checker.ps1:121 char:76
+ ... skStable) { throw "Verification failed; see $taskBase.log and .json"  ...
+                 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    + CategoryInfo          : OperationStopped: (Verification fa...x.log and .json:String) [], RuntimeException
    + FullyQualifiedErrorId : Verification failed; see C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\Differen 
   tialGeometry\Topology\PiecewiseLinear\UpperLinkSubcomplex.log and .json
 
```


## Codex C1 surface trace check (2026-09-23T14:50:00.6753927Z)

Module: DifferentialGeometry.Topology.PiecewiseLinear.UpperLinkSubcomplex. Checker exit: 0.
SHA-256: D6AD532D83C30D2D1D5832636C8690B49397037AAD9F5B528EE798360317CDC3
Sub-leaf list: The upper link of any face intersects a subcomplex exactly in the upper link calculated in that subcomplex.
The branch surface producer and frozen endpoint remain OPEN.

Checker output:
```text
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\UpperLinkSubcomplex.lean with no diagnostics; shared outputs unchanged.
```


## Codex C1 surface trace check (2026-09-23T14:51:08.5883781Z)

Module: DifferentialGeometry.Topology.PiecewiseLinear.UpperLinkBoundary. Checker exit: 0.
SHA-256: 7ED3E4FA57FE40F813589E37D3DABE05855665C1EA1CECD085EE71223F8C321B
Sub-leaf list: Geometric link after barycentric subdivision; boundary commutes with barycentric subdivision; intrinsic boundary of a vertex upper link; intrinsic boundary of a derived cell base.
The branch surface producer and frozen endpoint remain OPEN.

Checker output:
```text
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\UpperLinkBoundary.lean with no diagnostics; shared outputs unchanged.
```


## Codex C1 surface trace check (2026-09-23T14:53:35.8532985Z)

Module: DifferentialGeometry.Topology.PiecewiseLinear.DerivedSurfaceArc. Checker exit: 0.
SHA-256: 7DC4DABDCA66BF912D5F5A729522F9CBAA871F854CF6C804958C76F268815224
Sub-leaf list: A surface with boundary cuts out a PL arc on a derived cell base; its parametrization has the prescribed two boundary-trace points as endpoints.
The branch surface producer and frozen endpoint remain OPEN.

Checker output:
```text
Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\DerivedSurfaceArc.lean with no diagnostics; shared outputs unchanged.
```

