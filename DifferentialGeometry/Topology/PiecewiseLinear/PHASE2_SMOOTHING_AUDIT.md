# Phase 2（`PLSmoothingModel 3`）光滑化输入审计

审计日期 2026-09-11/12。审计基线：分支 `codex/moise-smoothing@182f9e343`（本文件所在分支
`codex/moise-phase2-audit` 自该提交创建）。本文件只记录事实：读到的声明原文、假设、结论、公理状态，
以及尚无生产者的缺口。路径省略 `DifferentialGeometry/` 前缀时指本库源码树；`ℝⁿ := EuclideanSpace ℝ (Fin n)`。
目标接口见 `MOISE_PLAN.md` §4.2 B′：

```lean
def PLSmoothingModel (n : ℕ) : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    (C : ChartedSpace (EuclideanSpace ℝ (Fin n)) X),
    (letI := C; HasGroupoid X (plGroupoid n)) →
    ∃ (N : Type u) (_ : TopologicalSpace N) (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N),
      IsManifold (𝓡 n) ∞ N ∧ Nonempty (X ≃ₜ N)
```
（`Topology/PiecewiseLinear/Smoothing.lean`；`plSmoothing_of_plSmoothingModel` 已证 B′ → B，公理审计干净，见 §0.2。）
注意 `PLSmoothingModel` 不要求 `CompactSpace X`；Phase 2 实际只需紧致情形，若最终只证紧致情形，需要把
`CompactSpace` 加进接口或另立紧致版本（见 §2.9）。

## 0. 审计方法与证据边界

### 0.1 源码检查

- 逐文件读取或提取签名（`theorem/def/structure` 到 `:=`）的目录：`Topology/Handle/`、`Topology/Morse/Attachment/`、
  `Topology/Manifold/{Sphere*,EmbeddedBall*,Collar*,SmoothBicollar,SmoothTwoSidedCollar,PlanarChartGermIsotopy,
  RelativeSquareIsotopy,CompactPlanarIsotopy,Diffeomorph*,HomeomorphAtlas,Homeomorph/Transport,BallDiffeomorphExtension,
  CompactBicollar,EmbeddedHypersurface/NormalTriviality,CodimensionOneImmersion,Orientation/SurfaceFrame}`、
  `Topology/ClosedBall/`、`Topology/Collar/`、`Topology/SphereSeparation/{Defs,Schoenflies,SchoenfliesSides,StandardSphere,
  TwoSphereDomain,SourceTheorems}`、`Topology/ThreeManifold/{StandardSphere,SmoothSchoenflies,schoenflies,Closed,
  ConnectedSum/*,StandardFactors}`、`Topology/Embedding/`、`Topology/SimplicialComplex/{EulerCharacteristic,
  GeometricEulerCharacteristic,GeometricManifoldLinks,GeometricManifoldFaceLinks,GeometricManifoldDimension,
  GeometricRealizationHomeomorphism,GeometricLink}`、`Topology/Homology/{EulerCharacteristic,ManifoldEulerParity,
  SphereEuler,ClosedManifold,Manifold,ManifoldDoubleEuler,HurewiczLowDegrees}`、`Topology/Ehresmann/{SphereBoundary,
  SphereBoundaryDegree,BoundaryMatching}`、`Topology/Attachment/Defs.lean`、`Topology/Cell/Coordinates.lean`、
  `Topology/Double/SmoothAtlas.lean`、`Topology/PiecewiseLinear/*`。
- `sorry`/`admit`/`axiom` 全文 grep（`Handle Morse/Attachment Manifold ClosedBall Collar SphereSeparation ThreeManifold
  Embedding SimplicialComplex Homology Diffeomorph PiecewiseLinear`）命中列表（全部）：
  `Manifold/Components.lean:115`、`Manifold/ProductOrientation.lean:39`、`Manifold/SphereOrientation.lean:28`、
  `Manifold/ULift.lean:96`、`ThreeManifold/ConnectedSum/Construction.lean:92,95,102,133`、
  `ThreeManifold/ConnectedSum/Finite.lean:34,40,46,53,64,70`、`ThreeManifold/SmoothSchoenflies.lean:14`、
  `ThreeManifold/StandardFactors.lean:86`、`Homology/HurewiczLowDegrees.lean:32,44`。其它被审计文件源码无 `sorry`。
  `Analysis/ODE/Flow/Planar/`、`Analysis/Calculus/Interpolation/`、`Geometry/VectorField/ConstantPushforward.lean`、
  `Manifold/RectangleFieldDeformation.lean`（球面同痕链的分析依赖）grep 亦无 `sorry`/`axiom`。

### 0.2 公理审计（`#print axioms`）

- 本工作树（`.claude/worktrees/agent-…`）无 `.lake`；共享检出 `E:\differential-geometry-dev\.lake` 有 2026-09-11 构建的
  olean。`git diff --stat 806b541e9 182f9e343 -- DifferentialGeometry` 显示分支相对基线只新增
  `Topology/Manifold/PartialAtlas.lean` 与 `Topology/PiecewiseLinear/*`（其余为 `.md`），因此被审计的非 PL 源文件与
  olean 构建时一致。
- 探针：临时文件（在 scratch 目录，未入库）import 32 个已有 olean 的模块，对 50 个声明 `#print axioms`；
  以 `LEAN_PATH` 指向共享检出的 `build/lib/lean` 与各 package 的 `.lake/build/lib/lean`，直接调用
  `~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean.exe`（不经 `lake`，不写任何构件；单进程，13 秒，退出码 0）。
- 结果：下表标 **标准** 的声明全部只依赖 `propext`、`Classical.choice`、`Quot.sound`。对照组
  `DifferentialGeometry.Topology.standardThreeSphere` 与 `DifferentialGeometry.sphereOrientation` 报告含 `sorryAx`
  （与源码 grep 一致），说明探针能检出 `sorry`。
- **未审计**（共享检出当时无 olean；根构建尚在进行；源码 grep 无 `sorry`）：`Manifold/SphereDiffeomorphDegree`、
  `SphereOrientationIsotopy`、`SphereRelativeIsotopy`、`SphereChartIsotopy`、`CompactPlanarIsotopy`、
  `ChartSupportedIsotopy`、`RelativeSquareIsotopy`、`SquareFlowIsotopy`。下表标 **未审计**。
- 根聚合 `DifferentialGeometry.lean` 注册状态：`Topology.PiecewiseLinear.{Smoothing,Polyhedron,ApproximationManifold}`
  **未注册**（`MOISE_PLAN.md` §6 已说明待根构建结束后登记）；`Topology.Manifold.{SphereDiffeomorphDegree,
  CompactPlanarIsotopy,SphereOrientationIsotopy,SmoothBicollar}`、`ThreeManifold.{SmoothSchoenflies,schoenflies}`、
  `Morse.Attachment.{ManifoldHandle,SublevelTransport}`、`Handle.Gluing`、`SphereSeparation.Schoenflies` 已注册。

### 0.3 Mathlib（`v4.33.1`，`.lake/packages/mathlib`）

| 声明 | 文件 | 内容 | 用途 |
|---|---|---|---|
| `EuclideanSpace.instChartedSpaceSphere`, `EuclideanSpace.instIsManifoldSphere`, `instance : IsManifold (𝓡 n) ω (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)`, `stereographic'`, `contMDiff_coe_sphere`, `ContMDiff.codRestrict_sphere`, `contMDiff_neg_sphere`, `mfderiv_coe_sphere_injective` | `Geometry/Manifold/Instances/Sphere.lean` | 单位球面的解析（含 `∞`）流形结构与球极投影图卡 | (ii) 的目标 `S²`；3-柄的 `CellBoundary 3` 与球面比较 |
| `instance : ChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle`, `IsManifold (𝓡 1) ω Circle`, `LieGroup (𝓡 1) ω Circle`, `contMDiff_circleExp` | 同上 | `Circle` 的流形/李群结构 | (i) 中 `S¹` 模型的候选（本库柄层用 `CellBoundary 2`） |
| `Diffeomorph`（`M ≃ₘ^n⟮I, I'⟯ M'`）、`toHomeomorph`、`trans/symm`、`contMDiff_comp_diffeomorph_iff` 等 | `Geometry/Manifold/Diffeomorph.lean` | 微分同胚 API | 全部光滑粘接 |
| `IsSmoothEmbedding`（结构）、`IsImmersion`/`IsImmersionAt`/`IsImmersionAtOfComplement` | `SmoothEmbedding.lean`, `Immersion.lean` | 光滑嵌入/浸入 | 贴附映射的光滑性 |
| `IsLocalDiffeomorph*`, `PartialDiffeomorph` | `LocalDiffeomorph.lean` | 局部微分同胚 | 图卡搬运 |
| `WhitneyEmbedding.lean` | — | Whitney 嵌入（紧致情形） | 不直接需要 |
| `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere` | `PoincareConjecture.lean` | 仅定义（`Prop`） | 无 |
| `SingularManifold` | `Bordism.lean` | 奇异流形 | 无 |
| `EuclideanHalfSpace`, `modelWithCornersEuclideanHalfSpace`（`𝓡∂ n`）, `Icc` 的流形结构 | `Instances/Real.lean` | 带边模型 | 柄与领 |

Mathlib 中**没有**：同痕（`isotop` 在 `Geometry`/`Topology` 下零命中）、管状邻域（`tubular` 零命中）、
`Diff(S¹)`/`Diff(S²)` 的连通性、曲面分类、任何 PL 结构。

## 1. 可复用声明表

列说明：假设只列关键项（完整变量块见文件）；"公理"为 §0.2 探针结果（标准 = 仅 `propext/Classical.choice/Quot.sound`；
未审计 = 无 olean，源码无 `sorry`；`sorryAx` = 探针或源码确认含 `sorry`）；"服务于"指 (i)/(i-b)/(ii)/(ii′)/柄粘接（H）/
装配（A）。

### 1.A PL 侧接口（Phase 1 已有，`Topology/PiecewiseLinear/`）

| 声明 | 文件 | 假设 | 结论 | 公理 | 服务于 |
|---|---|---|---|---|---|
| `PLSmoothingModel n`, `PLSmoothing n` | `Smoothing.lean` | `Prop` 定义 | 见文首 | 定义 | A（目标） |
| `plSmoothing_of_plSmoothingModel (h : PLSmoothingModel.{u} n) : PLSmoothing.{u} n` | `Smoothing.lean` | — | 用 `pullbackChartedSpace` 把光滑模型拉回同一 carrier | 标准 | A |
| `exists_isManifold_three_of_plApproximation_of_plSmoothing (hA : PLApproximation.{u} 3) (hB : PLSmoothing.{u} 3)` | `Smoothing.lean` | `[T2Space M] [CompactSpace M] [ChartedSpace ℝ³ M]` | `∃ C, IsManifold (𝓡 3) ∞ M` | 标准 | A（书中接口） |
| `PLTriangulation n X`（结构：`ambientDim`, `complex : Geometry.SimplicialComplex ℝ ℝ^ambientDim`, `finite_faces`, `map`, `bijOn : BijOn map complex.space univ`, `continuousOn`, `isPiecewiseAffineOn_chart`, `isPiecewiseAffineOn_chart_symm`） | `Polyhedron.lean` | `[ChartedSpace ℝⁿ X]` | 有限几何复形 + 逐图卡逐块仿射的 PL 同胚 | 定义 | H1 输入 |
| `PLManifoldTriangulation n : Prop`（T2） | `Polyhedron.lean` | 紧致 T2 第二可数 PL `n`-流形 | `∃ T : PLTriangulation n X, IsCombinatorialManifold n T.complex` | `Prop` 接口（无证明） | H1 输入（条件） |
| `IsCombinatorialManifold n K`（顶点 link 是 `IsPLSphere (n-1)`；`n = 0` 时 link 空） | `Polyhedron.lean` | — | — | 定义 | H1 |
| `IsPLBall n P`, `IsPLSphere n P`, `IsPLHomeomorphOn f P Q`, `isPLBall_stdSimplex` | `Polyhedron.lean` | — | 与 `stdSimplex`/`stdSimplexBoundary` 的 PL 同胚 | `isPLBall_stdSimplex` 标准（§6 记录） | H1 |
| `CombinatorialManifoldPLStructure n : Prop`（T1） | `Polyhedron.lean` | 有限组合流形 `K` | `K.space` 上的 PL 图册且与线性结构逐块仿射相容 | `Prop` 接口 | H1（若经组合流形） |
| `IsPL n m f`, `IsPLAt/IsPLOn/IsPLWithinAt`, `isPLAt_iff_of_mem_maximalAtlas`, `isPL_id`, `isPL_symm_of_homeomorph` | `Manifold.lean` | `[HasGroupoid _ (plGroupoid _)]` | PL 流形间的 PL 映射（`LiftProp`） | `isPL_symm_of_homeomorph` 标准 | H1、(i) 的 PL 侧陈述 |
| `plGroupoid n`, `mem_plGroupoid_iff`, `ClosedUnderRestriction` | `Groupoid.lean` | — | — | 标准（§6） | 全部 |
| `IsHPolytope`, `IsPiecewiseAffineOn`, `.comp/.symm/.congr` | `Polytope.lean`, `PiecewiseAffine.lean` | 见 `MOISE_PLAN.md` §4.1 | — | 标准（§6） | 全部 |
| `plApproximation_of_plApproximationManifold` | `ApproximationManifold.lean` | — | A′ → A | 标准 | Phase 3 |

### 1.B 光滑结构运输

| 声明 | 文件 | 假设 | 结论 | 公理 | 服务于 |
|---|---|---|---|---|---|
| `exists_smoothAtlas_of_homeomorph (h : M ≃ₜ N)` | `Manifold/HomeomorphAtlas.lean` | `[ChartedSpace H M] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]` | `∃ C : ChartedSpace E N, IsManifold 𝓘(ℝ, E) ∞ N ∧ ∃ d : Diffeomorph I 𝓘(ℝ, E) M N ∞, (d : M → N) = h` | 标准 | A（沿同胚运输，**注意目标模型变为 `𝓘(ℝ, E)`，且要求无边**） |
| `pullbackChartedSpace (h : X ≃ₜ M)`, `instHasGroupoidPullback`, `instIsManifoldPullback`, `pullbackDiffeomorph`, `contMDiff_pullback` | `Manifold/Homeomorph/Transport.lean` | `[ChartedSpace H M]`，任意群胚/模型 | `X` 上拉回的图卡空间、群胚、`IsManifold`，`h` 成为微分同胚 | `instIsManifoldPullback` 标准 | A（任意模型，含带边/PL） |
| `chartedSpaceOfHomeomorph`, `isManifoldOfHomeomorph`, `contMDiff_homeomorph_of_chartedSpaceOfHomeomorph` | `Handle/Manifold.lean:20-190` | — | 同上的柄层本地版本 | `chartedSpaceOfHomeomorph` 经 `closedCellChartedSpace` 被已探针的 `contMDiff_cell_of_contMDiff` 使用（标准）；其余未单独探针 | H |
| `adjunctionChartedSpace φ (h : AdjunctionSpace k l φ ≃ₜ Y)`, `adjunctionIsManifold`, `contMDiff_adjunctionHomeomorph(_symm)`, `contMDiff_lower_of_contMDiff`, `contMDiff_cell_of_contMDiff`, `handleAdjunctionDiffeomorph` | `Handle/Gluing.lean:173-336` | `[ChartedSpace H Y] [IsManifold I n Y]`；`cell` 版需 `[Fact (k = (k-1)+1)] [Fact (l = (l-1)+1)]` 与 `standardHandleChartedSpace` | 把 `Y` 的光滑结构搬到粘接空间；`lower`/`cell` 光滑性由复合判定；两个粘接空间的微分同胚（给定 `h : X ≃ₜ X'`, `hφ : ∀ a, h (φ a) = φ' a`, `hcomm`） | 标准 | H、A |
| `uliftDiffeomorph I M`（`Manifold/ULift.lean`） | `Manifold/ULift.lean` | — | `M ≃ₘ⟮I, I⟯ ULift M` | 文件含 1 个 `sorry`（`uliftTangentOrientation_locally_constant`，定向部分）；微分同胚本身未单独审计 | A（宇宙提升，见 §2.9） |

### 1.C 标准柄/胞腔的拓扑与光滑结构（`Topology/Handle/`, `Topology/Attachment/Defs.lean`, `Topology/Cell/`）

| 声明 | 文件 | 假设 | 结论 | 公理 | 服务于 |
|---|---|---|---|---|---|
| `ClosedCell n := {x : ℝⁿ // ‖x‖ ≤ 1}`, `CellBoundary n := {x // ‖x‖ = 1}`, `cellBoundaryInclusion`, `closedCellCenter`, `CellAdjunctionSpace n φ := AdjunctionSpace (cellBoundaryInclusion n) φ`（`Quot`） | `Attachment/Defs.lean` | — | 圆胞腔模型 | 定义 | H |
| `StandardHandle k l := ClosedCell k × ClosedCell l`, `AttachingRegion k l := CellBoundary k × ClosedCell l`, `BeltRegion`, `Corner`, `attachingInclusion`, `coreDisk`, `attachingSphere`, `toAmbient`, `AdjunctionSpace k l φ`, `lower`, `cell` | `Handle/Defs.lean` | — | 柄模型与粘接空间 | 定义 | H |
| `continuous_*`, `injective_*`, `isClosedEmbedding_*`, `range_*`, `mem_*` 系列 | `Handle/Basic.lean` | — | 各包含映射为闭嵌入等 | 未探针 | H |
| `frontier_handleSet`, `range_toAmbient`, `toAmbient_attachingRegion/beltRegion/corner`, `attachingSet_inter_beltSet` | `Handle/Boundary.lean` | — | `toAmbient` 像为 `closedBall ×ˢ closedBall`，边界 = 贴附区 ∪ 带区 | 未探针 | H |
| `attachingCollar k l : (AttachingRegion k l × Ico 0 1) ≃ₜ {p // p ∉ cocoreDisk k l}`, `beltCollar`, `bicollar`, `*_zero/_apply/_symm_apply/_range`, `isOpen_attachingCollarSet` | `Handle/Collar.lean` | — | 贴附区/带区/角的拓扑领（径向） | 未探针 | H（角光滑化） |
| `swap k l : StandardHandle k l ≃ₜ StandardHandle l k` 及 `swap_*` | `Handle/Duality.lean` | — | 柄对偶 | 未探针 | H |
| `coreRetract`, `cocoreRetract`, `attachingSphereRetract`, `beltSphereRetract` | `Handle/Retraction.lean` | — | 强形变收缩 | 未探针 | 同伦层（非必需） |
| `closedCellChartedSpaceSucc m`, `closedCellHasGroupoid`, `closedCellIsManifold m : IsManifold (modelWithCornersEuclideanHalfSpace (m+1)) ⊤ (ClosedCell (m+1))` | `Handle/Manifold.lean:897-1610` | — | 闭胞腔是带边光滑流形（模型 `EuclideanHalfSpace`） | 标准 | H |
| `cellBoundaryChartedSpace k`, `cellBoundaryIsManifold k : IsManifold (𝓡 (k-1)) ⊤ (CellBoundary k)`, `cellBoundaryInclusion_contMDiff` | `Handle/Manifold.lean:2229-2330` | `[Fact (finrank ℝ ℝᵏ = (k-1)+1)]` | 胞腔边界是无边光滑流形 | 标准 | H、(ii) |
| `standardHandleChartedSpaceSucc`, `standardHandleIsManifold m n`, `standardHandleChartedSpace k l`（`@[reducible]`，模型 `ModelProd (EuclideanHalfSpace ((k-1)+1)) (EuclideanHalfSpace ((l-1)+1))`），`standardHandleZeroChartedSpace`, `standardHandleTopChartedSpace`, `standardHandleTopSubChartedSpace` | `Handle/Manifold.lean:2139-2555` | `[Fact (k = (k-1)+1)] [Fact (l = (l-1)+1)]`（由 `[NeZero k]` 实例给出） | 标准柄是带角光滑流形 | 标准 | H |
| `attachingRegionChartedSpace k l`（实例 `attachingRegionChartedSpaceInst`），`attachingRegionIsManifold`（实例） | `Handle/Manifold.lean:2792-2846` | 同上 | 贴附区是带边光滑流形，模型 `ModelProd ℝ^(k-1) (EuclideanHalfSpace ((l-1)+1))` | 图卡空间被已探针的 `attachingRegionInclusion_isSmoothEmbedding` 使用（标准）；`attachingRegionIsManifold` 未探针 | H、(i-b) |
| `cellBoundarySphereHomeomorph k : CellBoundary k ≃ₜ sphere 0 1`, `cellBoundarySphereDiffeomorph : Diffeomorph (𝓡 (k-1)) (𝓡 (k-1)) (CellBoundary k) (sphere (0 : ℝᵏ) 1) ∞` | `Handle/Manifold.lean:2174`, `Handle/Embedding.lean:54` | — | 胞腔边界 ≅ Mathlib 单位球面 | 标准 | (ii)、3-柄 |
| `closedCellInclusion_isSmoothEmbedding : IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace (m+1)) (𝓡 (m+1)) ∞ (Subtype.val : ClosedCell (m+1) → ℝ^(m+1))`, `isSmoothEmbedding_coe_cellBoundary`, `isSmoothEmbedding_coe_closedCell`, `attachingRegionInclusion_isSmoothEmbedding k l [NeZero k] [NeZero l]`, `exists_closedCellChart_extension` | `Handle/Embedding.lean` | — | 胞腔/贴附区到欧氏空间的包含为光滑嵌入 | 标准 | H |
| `stdSimplexClosedCellHomeomorph n : stdSimplex ℝ (Fin (n+1)) ≃ₜ ClosedCell n`, `stdSimplexCellBoundaryHomeomorph` | `Cell/Coordinates.lean` | — | 单形 ≅ 圆胞腔（径向） | 未探针 | H1（PL 模型 ↔ 圆模型） |

### 1.D 拓扑柄粘接（`Topology/Handle/Attachment/`, `Handle/Gluing.lean`）

| 声明 | 文件 | 假设 | 结论 | 公理 | 服务于 |
|---|---|---|---|---|---|
| `adjunction_coherence`, `continuous_lower`, `continuous_cell`, `cell_lower_coverage` | `Handle/Attachment/Basic.lean` | — | 粘接空间基本性质 | 未单独探针（`adjunctionHomeomorphUnionImage` 标准） | H |
| `adjunctionHomeomorphUnionImage φ c hφ hc hcont hmeet hclosed : AdjunctionSpace k l φ ≃ₜ {y : Y // y ∈ X₀ ∪ range c}` | `Handle/Attachment/Basic.lean:62` | `[T2Space Y]`, `φ : AttachingRegion k l → X₀`, `c : StandardHandle k l → Y` 连续单射, `hφ : ∀ a, (φ a : Y) = c (attachingInclusion k l a)`, `hmeet : Disjoint (c '' (univ \ attachingRegion k l)) X₀`, `hclosed : IsClosed X₀` | 抽象粘接 = 环境空间中的并集 | 标准 | H（把 `Quot` 粘接空间识别为子空间） |
| `adjunctionMap`, `adjunctionCongr (h : X ≃ₜ Y) (hφ : ∀ a, h (φ a) = φ' a) : AdjunctionSpace k l φ ≃ₜ AdjunctionSpace k l φ'`, `adjunctionCongr_lower/_cell` | `Handle/Gluing.lean:14-170` | — | 沿底空间同胚搬运粘接 | `adjunctionCongr` 被已探针的 `handleAdjunctionDiffeomorph` 使用（标准）；其余未单独探针 | H、(i-c) |
| `coreProjectionAttachingMap`, `inverseMetricContraction`, `thicken`, `thickenCollapseHomotopy`, `handleCellAdjunctionHomotopyEquivUnder` | `Handle/Attachment/Comparison.lean` | — | 柄粘接 ≃ 胞腔粘接（同伦等价，相对下层） | 标准 | 同伦层 |
| `not_simplyConnectedSpace_adjunction_of_joined_feet` | `Handle/SimplyConnected.lean` | 1-柄两脚连通 | 粘接后非单连通 | 未探针 | 无 |

### 1.E 光滑柄粘接——Morse 路线（`Topology/Morse/`）

所有定理的流形变量为 `{M : Type}`（**宇宙 0**），模型 `I : ModelWithCorners ℝ (MorseModel (m+1)) H`
（`MorseModel n` 见 `Morse/NormalForm/Local.lean:173`），带边模型为 `morseModelWithCornersHalfSpace m :
ModelWithCorners ℝ (MorseModel (m+1)) (MorseHalfSpace m)`（`Morse/RegularLevel/LevelSet.lean:918,970`），**不是**
`modelWithCornersEuclideanHalfSpace`；见 §4 警告。

| 声明 | 文件 | 假设 | 结论 | 公理 | 服务于 |
|---|---|---|---|---|---|
| `MorseChart n k hk c I f`（结构：`p R smoothRadius ε χ`, `map_zero`, `normalForm_on : ∀ y, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y`, `closedBall_subset_source`, `contMDiffOn`, `symm_contMDiffOn`），`morseChart I f hf p c k hk hnd hindex hfp`（由 `morse_lemma` 构造） | `Morse/Attachment/ManifoldHandle.lean:121-198` | `[I.Boundaryless] [IsManifold I ⊤ M]`, 非退化临界点, 指标 `k` | Morse 图卡 | 定义/构造 | H |
| `exists_morse_function [T2Space M] [CompactSpace M] : ∃ f, ContMDiff I 𝓘(ℝ,ℝ) ∞ f ∧ ∀ x, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x`；`exists_excellent_morse_function`（另加 `InjOn f (criticalPoints I f)`） | `Morse/Existence.lean:253`, `Morse/CriticalValues.lean:215` | `[FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] [T2Space M]` | 紧致无边光滑流形上的 Morse/优 Morse 函数 | 标准 | (ii) |
| `morse_smooth_handle_attachment hk c ε r δ I f hf data hε hr hδ hεr hRltR' hreg v hv hsupp hcomplete hdfOn hrate [NeZero k] [NeZero (m+1-k)]` | `ManifoldHandle.lean:2828` | 见原文：Morse 图卡 `data`, `0 < ε`, `r ≠ 0`, `r²/2 < δ`, `√(2ε+2r²) ≤ data.R < data.smoothRadius`, `c-ε` 正则, 完备紧支撑梯度型向量场 `v` | `∃ φ = handleEmbedding …`：标准柄到 `M` 的 `ContMDiff`（模型 `standardHandleChartedSpace k (m+1-k)`）闭嵌入，`f ∘ φ = morseNormalForm ∘ modelHandleMap`，贴附区落在 `sublevel f (c-ε)`，`handleCollarMap` 闭嵌入且高度公式 | 标准 | H |
| `morse_smooth_handle_attachment_zero`（`k = 0`，`StandardHandle 0 (m+1)`），`morse_smooth_handle_attachment_top`（`k = m+1`，`ClosedCell (m+1)`） | `ManifoldHandle.lean:2901,2949` | 同上（少梯度场假设） | 0-柄 / 顶柄的光滑嵌入 | 标准 | H（0-柄、3-柄） |
| `morseAttachedSpace`, `morseAttachedChartedSpace`, `morseAttachedIsManifold`, `morseAttachedDiffeomorphUpper`, `morseAttachedDiffeomorphModifiedSublevel`, `morseAttachedNaturalDiffeomorphUpper` | `ManifoldHandle.lean:3371-4222` | 模型层参数 | 模型柄粘接空间是带边流形，微分同胚于上水平集 | `morseAttachedIsManifold` 标准 | H |
| `exists_morseHandleAdjunction_diffeomorph_upperSublevel_of_morseChart hk c a data hf ha haR hRR' hcompact hunique [NeZero k] [NeZero (m+1-k)]` | `Morse/Attachment/SublevelTransport.lean:1033` | `[T2Space M] [SigmaCompactSpace M] [I.Boundaryless] [IsManifold I ⊤ M]`, `0 < a ≤ data.R²/16`, `data.R < data.smoothRadius`, `IsCompact (f ⁻¹' Icc (c-a) (c+a))`, 带内唯一临界点 | `∃ ε>0, r, η>0, c±ε 正则, hcs : ChartedSpace (MorseHalfSpace m) (Handle.AdjunctionSpace k (m+1-k) (morseAttachingEmbedding …)), e : Diffeomorph … (AdjunctionSpace) (SublevelSpace f (c+ε)) ⊤`，两侧 `IsManifold`，`Handle.lower` 与 `Handle.cell` `ContMDiff`（`cell` 用 `standardHandleChartedSpace`），`e` 在 `f ≤ c-ε-η` 处为恒同 | 标准 | H（**本库已有的"沿 Morse 贴附映射光滑粘一个柄"定理**） |
| `…_of_morseChart_zero`, `…_of_morseChart_top` | 同上 `:1172,1309` | — | 0-柄/顶柄版本 | 标准 | H |
| `one_critical_point_cell_attachment` | `Morse/Attachment/SmoothHandle.lean:932` | 单临界点带 | 上水平集 ≃ 下水平集 ∪ `k`-胞腔（`HomotopyEquivUnder`） | 标准 | 同伦层 |
| `exists_contMDiff_isClosedEmbedding_attachingRegion` | `SmoothHandle.lean:959` | 同上 `[NeZero k] [NeZero (m+1-k)]` | `∃ ε, φ : AttachingRegion k (m+1-k) → SublevelSpace f (c-ε)` 闭嵌入且 `φ₀` 到水平集 `LevelSetSpace f (c-ε)` 光滑闭嵌入 | 标准 | H、(i-b)（水平集中的光滑贴附环） |
| `sublevelTransport_diffeomorph_of_setImage` | `SmoothHandle.lean:381` | 全局微分同胚 `Φ` 把 `sublevel g a` 送到 `sublevel f b` | 两个下水平集流形微分同胚 | 未探针 | H |
| `exists_isotopy_cocoreAttachingEmbedding` | `Morse/HandleIsotopy.lean:70` | 模型空间 | 贴附嵌入沿高度的紧支撑同痕 | 标准 | H |
| `exists_isSmoothEmbedding_cocore_collar` | `Morse/HandleCollar.lean:610` | `r ≠ 0, 0 < ε, √(2ε+2r²) < data.R, < data.smoothRadius` | 贴附区 × 区间的光滑嵌入（余核领） | 未探针 | H |
| `exists_morseHandleAdjunction_homeomorph_roundedSublevel_on_set` | `Morse/RelativeHandleAttachment.lean:194` | 见原文 | 相对版本：粘接空间 ≃ₜ 圆化下水平集（`D` 上） | 标准 | H |
| `exists_morse_eulerChar`（`Morse/ClosedEulerCharacteristic.lean:16`），`exists_relative_morse_eulerChar` | `Morse/…` | — | Euler 数 = 临界点交错和 | 未探针 | (ii) |

### 1.F 领、双领、管状邻域

| 声明 | 文件 | 假设 | 结论 | 公理 | 服务于 |
|---|---|---|---|---|---|
| `SmoothTwoSidedCollar I J e`（结构：`radius`, `neighborhood : Opens M`, `toDiffeomorph : Diffeomorph (I.prod 𝓘(ℝ,ℝ)) J (S × symmetricOpenInterval radius) neighborhood ∞`, `zero_eq`），`toFun`, `isOpenEmbedding_toFun`, `transAmbientModel` | `Manifold/SmoothTwoSidedCollar.lean` | — | 余维 1 光滑嵌入的双侧领 = 管状邻域 | 定义 | (i-b)、H |
| `exists_smoothTwoSidedCollar_of_coorientedAtlas (C : CoorientedSmoothEmbeddingRealNormalAtlas I J ∞ f) (hf : Injective f) (hdim : finrank F = finrank E + 1)` | `Manifold/SmoothBicollar.lean:21` | `[CompactSpace B] [I.Boundaryless] [J.Boundaryless]` 等 | `Nonempty (SmoothTwoSidedCollar I J f)` | 标准 | (i-b) |
| `exists_smoothTwoSidedCollar_of_smoothSphereEmbedding (e : SphereTwo → M) (he : IsSmoothEmbedding 𝓘(ℝ,ℝ²) 𝓘(ℝ,ℝ³) ∞ e)` | 同上 `:47` | `[ChartedSpace ℝ³ M] [IsManifold 𝓘(ℝ,ℝ³) ∞ M] [T2Space M]` | `Nonempty (SmoothTwoSidedCollar …)`（`S²` 在 3-流形中自动双侧） | 标准 | 3-柄 |
| `nonempty_smoothTwoSidedCollar_of_normalTrivialization (he : IsSmoothEmbedding I J ∞ e) (hK : IsCompact (range e)) (t : Trivialization ℝ (normalSpace I J e 的投影)) [t.IsLinear ℝ] (ht : t.baseSet = univ)` | `Manifold/EmbeddedHypersurface/NormalTriviality.lean:86` | `[T2Space M] [SigmaCompactSpace M]` | `Nonempty (SmoothTwoSidedCollar I J e)` | 未探针（源码无 sorry） | (i-b)（框架 = 法丛平凡化） |
| `exists_smoothTwoSidedCollar_of_localDiffeomorphAt_zero (he : Injective e) (Φ : B × ℝ → A) (hΦ) (hzero) (hloc : ∀ x, IsLocalDiffeomorphAt (I.prod 𝓘(ℝ,ℝ)) J ∞ Φ (x,0))` | `Manifold/CompactBicollar.lean:20` | `[CompactSpace B] [T2Space A]` | `Nonempty (SmoothTwoSidedCollar I J e)` | 未探针 | (i-b) |
| `exists_smoothTwoSidedCollar_of_compact_regularLevel_manifold (hf) (a) (hK : IsCompact {x | f x = a}) (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ,ℝ) f x ≠ 0)` | `Manifold/RegularLevel/Collar/ManifoldSmooth.lean:17` | — | 正则水平集的双侧领 | 未探针 | H |
| `exists_boundary_collar_diffeomorph (hK : IsCompact ((𝓡∂ (n+1)).boundary M))` | `Manifold/BoundaryCollar/Diffeomorph.lean:76` | `[ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M] [T2Space M] [SigmaCompactSpace M]` | `∃ ε>0, …`（边界的光滑领微分同胚；结论续行未全文引用） | 未探针 | H、(i-c) |
| `exists_attachment_homeomorph (f : C(B,X)) … (c : C(B × Icc 0 ε, X)) (hc : IsEmbedding c) (hzero) (hopen)` | `Collar/Attachment.lean:12` | `2a < δ ≤ ε` | `∃ h : MappingCylinder f ≃ₜ X`，`h` 在原空间为 `rescale`，在柱体为 `c` | 未探针 | H（拓扑） |
| `exists_smooth_attachment_realization … (e : Diffeomorph (J.prod (𝓡∂ 1)) I ⟨{q | q.2.val < δ}, _⟩ Y ∞) (he)` | `Manifold/Collar/Attachment.lean:11` | `[CompactSpace B] [T2Space M]`, `c` 光滑嵌入且在 `δ`-带内为微分同胚 | `∃ a σ d, … ∃ h : MappingCylinder f ≃ₜ M`，原空间侧与柱体侧的映射均 `ContMDiff` | 标准 | H（沿光滑领粘映射柱） |
| `exists_attachmentSeam_diffeomorph`, `exists_attachmentSeam_boundary_diffeomorph` | `Manifold/Collar/SeamDiffeomorph.lean:72,154` | `[IsManifold I ∞ M]`，同上数据 | 缝处（`B × Icc (-1) 1`）在 `pullbackChartedSpace h` 下为微分同胚 | `exists_attachmentSeam_diffeomorph` 标准 | H（缝光滑性） |
| `rescale`, `continuous_rescale`, `isClosedEmbedding_rescale`, `range_rescale`, `exists_homeomorph_superlevel_of_collar` | `Collar/Rescaling.lean`, `Collar/Superlevel.lean` | `[CompactSpace B] [T2Space X]` | 领内重标度 | `exists_homeomorph_superlevel_of_collar` 标准 | H |
| `Diffeomorph.exists_isotopy_eq_collar (Φ : OpenPartialHomeomorph (N × ℝ) E) (hΦ) (hi) (hA : IsCompact A) (hε) (hw)` | `Diffeomorph/Collar.lean:84` | `[IsManifold J 1 N] [FiniteDimensional ℝ E]` | 紧支撑同痕 `H : ℝ → E ≃ₘ[ℝ] E` 沿领方向平移 `A` | 标准 | (i-c)、H |
| `exists_smoothAtlas_double_of_collar` | `Double/SmoothAtlas.lean:10` | `{M … : Type}`（宇宙 0），紧致 `M`，边界 `B` 有领 `c` 与微分同胚 `d` | `Double B` 上的光滑结构，两半与缝均光滑 | 未探针 | Heegaard 路线的"沿恒同粘合"；沿一般微分同胚粘合需推广 |

### 1.G 球面、球体、微分同胚与同痕（`Topology/Manifold/`, `Topology/Diffeomorph/`, `Topology/ThreeManifold/schoenflies.lean`）

| 声明 | 文件 | 假设 | 结论 | 公理 | 服务于 |
|---|---|---|---|---|---|
| `exists_diffeomorph_image_sphere (c) (hr : 0 < r) : ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' sphere 0 1 = sphere c r` | `ThreeManifold/schoenflies.lean:26` | — | 圆球面由仿射微分同胚给出 | 标准 | 3-柄（仅圆球面） |
| `exists_smooth_ball_filling_round_sphere (c) (hr) : ∃ b : ClosedCell 3 → ℝ³, IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace 3) (𝓡 3) ∞ b ∧ range (b ∘ cellBoundaryInclusion 3) = sphere c r` | 同上 `:47` | — | 圆球面的光滑填充 | 标准 | 3-柄（仅圆球面） |
| `exists_diffeomorph_eqOn_of_partialDiffeomorph_closedBall (φ : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) E E ∞) (hr) (hrs : closedBall 0 r ⊆ φ.source) : ∃ D : Diffeomorph …, EqOn D φ (closedBall 0 r)` | `Manifold/BallDiffeomorphExtension.lean:12` | — | 球上的局部微分同胚延拓为全局 | 标准 | H |
| `exists_diffeomorph_straightening_embedded_closedBall (φ) (hr) (hrs) (hV) (himage)` | `Manifold/EmbeddedBallStraightening.lean:14` | `E` 有限维 | `∃ A ε F`, `F ∘ φ` 在球上仿射，`F` 紧支撑 | 标准 | H（把嵌入球拉直） |
| `exists_diffeomorphs_contracting_embedded_closedBall (φ : PartialDiffeomorph 𝓘(ℝ,E) I E M ∞) (hr) (hrs) (hV) (himage)` | `Manifold/EmbeddedBallContraction.lean:17` | — | 紧支撑同痕 `J` 收缩嵌入球 | 标准 | H |
| `exists_smooth_embeddedBallShell_parametrization` | `Manifold/EmbeddedBallShell.lean:24` | `[Fact (finrank ℝ E = n+1)]` | `closedBall 0 R \ φ '' ball 0 r ≅ sphere × unitInterval`（光滑） | 标准 | H |
| `sphereRadialExtension f`, `contDiffOn_sphereRadialExtension`, `sphereRadialDiffeomorph f : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) E E ∞`, `det_fderiv_sphereRadialExtension_pos_iff` | `Manifold/SphereRadialExtension.lean`, `SphereRadialDiffeomorph.lean` | `[Fact (finrank ℝ E = n+1)]` | 球面微分同胚的径向延拓 | `sphereRadialDiffeomorph` 标准 | (ii) |
| `sphereDiffeomorphDegree f : ℤ`, `sphereDiffeomorphDegree_eq_sign`, `sphereDiffeomorphDegree_eq_one_iff_isotopy : sphereDiffeomorphDegree f = 1 ↔ ∃ J : ℝ → Diffeomorph (𝓡 2) (𝓡 2) S² S² ∞, ContMDiff … J ∧ ContMDiff … J.symm ∧ J 0 = f ∧ J 1 = refl` | `Manifold/SphereDiffeomorphDegree.lean:62-92` | `f : Diffeomorph (𝓡 2) (𝓡 2) (sphere (0:ℝ³) 1) (sphere (0:ℝ³) 1) ∞` | **`S²` 的保向微分同胚光滑同痕于恒同（Smale 1959 的 π₀ 部分，即 Γ₂ = 0 的核心）** | 未审计 | (ii)、(ii′)、3-柄唯一性 |
| `sphere_isotopy_iff_positive_radial_derivative`, `exists_sphere_isotopy_of_positive_chart_derivative`, `exists_sphere_isotopy_of_positive_fixed_point_chart`, `exists_sphere_isotopy_of_identity_near_point`, `exists_sphere_isotopy_moving_point`, `det_radial_pos_iff_det_chart_pos`, `sphereDiffeomorphDegree_eq_of_cylinder` | `Manifold/SphereOrientationIsotopy.lean`, `SphereChartIsotopy.lean`, `SphereFixedPointIsotopy.lean`, `SphereRelativeIsotopy.lean`, `SpherePointIsotopy.lean`, `SphereRadialChartSign.lean`, `SphereCylinderDegree.lean` | `S² = sphere (0:ℝ³) 1` | 上述 Smale 链的各步 | `exists_sphere_isotopy_moving_point` 标准；其余未审计 | (ii) |
| `exists_compactly_supported_planar_isotopy (f : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ℂ ℂ ∞) (hf : HasCompactSupport (fun z ↦ f z - z))` | `Manifold/CompactPlanarIsotopy.lean:10` | — | 紧支撑同痕到恒同（经 `exists_relative_square_isotopy` → `exists_relative_isotopy_of_square_flow`：常向量场的推前 + 矩形形变 + 平面流；纯分析证明，依赖 `Analysis/ODE/Flow/Planar/*`） | 未审计 | (ii)、(ii′)、(i) |
| `exists_relative_square_isotopy`, `exists_relative_isotopy_of_square_flow`, `exists_isotopy_of_support_in_planar_chart`, `exists_isotopy_realizing_positive_chart_germ` | `Manifold/RelativeSquareIsotopy.lean`, `SquareFlowIsotopy.lean`, `ChartSupportedIsotopy.lean`, `PlanarChartGermIsotopy.lean` | 平面图卡 `e : OpenPartialHomeomorph M ℂ`，`e.target = univ` | 图卡支撑的同痕 | `exists_isotopy_realizing_positive_chart_germ` 标准；其余未审计 | (ii)、(i) |
| `Diffeomorph.extend`, `Diffeomorph.exists_extension_of_isCompact (e : P → Diffeomorph I I U U n) (he) (hi) (hK : IsCompact K) (hfix)`, `exists_extension_conjugate_of_isCompact` | `Diffeomorph/Extension.lean` | `[T2Space M]`, `U : Opens M` | 开集上紧支撑的微分同胚族延拓到 `M` | 标准 | (i)、(ii)、H |
| `addLipschitz`, `addLipschitzIsotopy`, `exists_isCompact_eqOn_addLipschitzIsotopy` | `Diffeomorph/Perturbation.lean` | `LipschitzWith C f`, `C < 1` | 小扰动是微分同胚且同痕于恒同 | 未探针 | (i)（光滑逼近后修正） |
| `diffeomorphList`, `contMDiff_diffeomorphList`, `isLocalDiffeomorphAt_diffeomorphList_of_basis` | `Manifold/DiffeomorphFamily.lean` | — | 有限个同痕的复合族 | 未探针 | (ii) |
| `isotopyTrackDiffeomorph`, `endpointCorrectedProduct`, `exists_endpoint_flat_corrected_product` | `Ehresmann/SphereBoundary.lean` | `Hprod : Diffeomorph (IF.prod (𝓡∂ 1)) IW (F × Icc 0 1) W ∞`，同痕 `A` | 用同痕修正积结构的端点 | `exists_endpoint_flat_corrected_product` 标准 | H（沿同痕改贴附） |
| `exists_prescribed_sphere_boundary_matching_of_degree_one`, `prescribed_sphere_boundary_matching_iff_degree_one`, `exists_prescribed_boundary_matching_of_isotopy` | `Ehresmann/SphereBoundaryDegree.lean`, `BoundaryMatching.lean` | `[HasSmoothBoundary E H I]`，`u` 边界取值 `a/b` | 度 1 的球面边界匹配 | 未探针 | 3-柄 |
| `IsSmoothEmbedding.diffeomorph_comp`, `.comp_diffeomorph`, `Diffeomorph.isSmoothEmbedding`, `IsImmersion.isLocalDiffeomorphOn_comp*` | `Embedding/Diffeomorph.lean`, `Embedding/LocalDiffeomorph.lean` | — | 光滑嵌入与微分同胚复合 | `diffeomorph_comp` 被已探针的 `exists_smooth_ball_filling_round_sphere` 使用（标准）；其余未单独探针 | H |
| `isSmoothEmbedding_coe_sphere : IsSmoothEmbedding (𝓡 n) 𝓘(ℝ,E) ∞ Subtype.val` | `Embedding/Sphere.lean:94` | `[Fact (finrank ℝ E = n+1)]` | 球面包含为光滑嵌入 | 未探针 | (ii) |
| `retraction`, `extension`（连续延拓） | `ClosedBall/Retraction.lean`, `Extension.lean` | — | 闭球收缩/连续函数延拓（**非同胚延拓**） | 未探针 | 无（Alexander trick 仍缺） |

### 1.H 球面分离 / Schoenflies（`Topology/SphereSeparation/`, `ThreeManifold/`）

| 声明 | 文件 | 假设 | 结论 | 公理 | 服务于 |
|---|---|---|---|---|---|
| `SphereSides S`（结构：两侧开连通、并为 `Sᶜ`、紧侧闭包紧、边界为 `S` 等） | `SphereSeparation/Defs.lean` | — | 分离数据 | 定义 | 无（Phase 2 不需要拓扑 Schoenflies） |
| `smoothSchoenfliesThree : Prop := ∀ e : sphere (0:ℝ³) 1 → ℝ³, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e → ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) ℝ³ ℝ³ ∞, closedBall 0 1 ⊆ Φ.source ∧ Φ '' sphere 0 1 = range e` | `SphereSeparation/Schoenflies.lean:10` | — | **`Prop` 接口** | 定义 | 无 |
| `smooth_schoenflies_three (e : S² → ℝ³) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) : ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' sphere 0 1 = range e` | `ThreeManifold/SmoothSchoenflies.lean:11` | — | 光滑 Schoenflies | **`sorry`**（他人负责，`MOISE_PLAN.md` §3） | 无（Phase 2 路线不依赖） |
| `exists_global_diffeomorph_of_smoothSchoenflies (hSch : smoothSchoenfliesThree) …`, `exists_ball_sphereSides_of_smoothSchoenflies` | `SphereSeparation/SchoenfliesSides.lean` | 显式假设 `hSch` | 条件性 | 标准（条件由假设表达） | 无 |
| `standardUnitSphereSides`, `standardUnitSphereComplementComponents`, `jordanBrouwer_openThreeSpace`（`SourceTheorems.lean`） | `StandardSphere.lean`, `SourceTheorems.lean` | 光滑嵌入 | Jordan–Brouwer（光滑 `S² ⊂ ℝ³`） | 未探针 | 无 |
| `exists_nested_ball_shell_of_two_spherical_boundaries (hSch : smoothSchoenfliesThree) …` | `TwoSphereDomain.lean` | 显式 `hSch` | 条件性 | 未探针 | 无 |

### 1.I Euler 特征、单纯复形、曲面

| 声明 | 文件 | 假设 | 结论 | 公理 | 服务于 |
|---|---|---|---|---|---|
| `eulerChar k X`, `finiteHomologyType`, `eulerChar_eq_of_homeomorph`, `eulerChar_eq_of_homotopyEquiv`, `eulerChar_eq_sum` | `Homology/EulerCharacteristic.lean` | `k` 域 | 奇异同调 Euler 数 | 未探针 | (ii) |
| `eulerChar_euclideanSphere n : eulerChar k (TopCat.of (sphere (0 : ℝ^(n+1)) 1)) = 1 + (-1)^n`, `finiteHomologyType_euclideanSphere` | `Homology/SphereEuler.lean:53,58` | — | `χ(Sⁿ)` | 标准 | (ii)（`χ = 2` 判据） |
| `finiteHomologyType_of_compact_boundaryless_manifold`, `eulerChar_eq_of_compact_boundaryless_manifold` | `Homology/ClosedManifold.lean` | 紧致无边光滑流形 | 有限型；与系数域无关 | 未探针 | (ii) |
| `eulerChar_eq_zero_of_odd_compact_boundaryless_manifold (hdim : Odd (finrank ℝ E)) : eulerChar K (TopCat.of M) = 0` | `Homology/ManifoldEulerParity.lean:94` | 紧致无边 | 奇维 `χ = 0` | 标准 | 无（3 维一致性检查） |
| `finiteHomologyType_and_eulerChar_intrinsicDouble` | `Homology/ManifoldDoubleEuler.lean` | 紧致带边 | `χ(DM) = 2χ(M) − χ(∂M)` | 未探针 | 无 |
| `faceEulerChar K`, `faceEulerChar_eq_of_card_le_three`, `faceEulerChar_sup_add_faceEulerChar_inf`, `eulerChar_geometricSpace_eq_faceEulerChar` | `SimplicialComplex/EulerCharacteristic.lean`, `GeometricEulerCharacteristic.lean` | 有限复形 | 组合 Euler 数 = 拓扑 Euler 数 | 未探针 | (ii)（三角剖分曲面 `V−E+F`） |
| `faceEulerChar_vertexLink_of_interior … = 1 − (−1)^n`, `faceEulerChar_vertexLink_three_interior … = 2`, `faceEulerChar_edgeLink_three_interior … = 0`, `faceEulerChar_triangleLink_three_interior … = 2`, `face_card_le_of_manifold_homeomorph` | `SimplicialComplex/GeometricManifoldLinks.lean`, `GeometricManifoldFaceLinks.lean`, `GeometricManifoldDimension.lean` | 复形空间同胚于流形 | link 的 Euler 数（**不是** link 是球面） | `faceEulerChar_vertexLink_three_interior` 标准 | H1（弱于 `IsCombinatorialManifold`） |
| `geometricRealizationHomeomorphism K : SSet.toTop.obj (orderedSimplicialSet K) ≃ₜ K.space`, `geometricLink K s`, `mem_geometricLink_singleton` | `SimplicialComplex/GeometricRealizationHomeomorphism.lean`, `GeometricLink.lean` | `[Finite K.faces]` | 实现同胚；link | 未探针 | H1 |
| `SurfaceOrientation I M`, `SurfaceOrientation.frame_orientation_eq_of_loop` | `Manifold/Orientation/SurfaceFrame.lean` | 2 维 | 曲面定向与沿环路的标架 | 未探针 | (i-b)（可定向情形的框架） |
| `isImmersionOfComplement_real_of_isSmoothEmbedding_finrank_succ`, `realNormalFormPartialHomeomorph` | `Manifold/CodimensionOneImmersion.lean` | 余维 1 | 余维 1 嵌入的实法向标准形 | 未探针 | (i-b) |

### 1.J 三维流形层（`Topology/ThreeManifold/`）

| 声明 | 文件 | 假设 | 结论 | 公理 | 服务于 |
|---|---|---|---|---|---|
| `isClosedThreeManifold : Prop := CompactSpace M ∧ ConnectedSpace M ∧ I.Boundaryless ∧ finrank ℝ E = 3` | `Closed.lean` | — | 定义 | 定义 | A（可作最终陈述的词汇） |
| `standardThreeSphere : ConnectedClosedOrientedManifold.{0} 3`（carrier `sphere (0:ℝ⁴) 1`，`orientation := sphereOrientation 3 _`） | `StandardSphere.lean` | — | 标准 `S³` | **`sorryAx`**（经 `exists_unique_sphere_orientation`） | 无；Phase 2 直接用 Mathlib 的 `sphere (0 : ℝ⁴) 1` |
| `BallChart n I M`（`chart : PartialDiffeomorph 𝓘(ℝ,ℝⁿ) I ℝⁿ M ∞`, `closedBall 0 2 ⊆ chart.source`） | `ConnectedSum/Quotient.lean:41` | — | 光滑球图卡 | 定义 | 0-柄/3-柄的词汇 |
| `exists_oriented_ball_chart`, `exists_boundary_attachment`, `exists_smooth_connected_sum`, `connectedSum_choice_independent`, `connectedSum_sphere_right/left`, `finiteConnectedSum_*` | `ConnectedSum/Construction.lean`, `Finite.lean` | — | 连通和 | **`sorry`** | 无 |
| `exists_smooth_quotient`（`StandardFactors.lean:86`） | `StandardFactors.lean` | — | — | **`sorry`** | 无 |

## 2. 缺口与建议的 Lean 陈述

### 2.0 两条候选路线与各自的缺口

- **路线 R-H（柄归纳，`MOISE_PLAN.md` §5 Phase 2 所述）**：`PLManifoldTriangulation 3` → PL 柄分解（H1）→ 逐柄建光滑模型
  `N_j` 与同胚 `N_j ≃ₜ X_j`：0-柄用 `ClosedCell 3`；1-柄贴附区 `AttachingRegion 1 2 = S⁰ × D²`，贴附映射经 (i) 的
  0 维类比（两个圆盘的光滑化；由 `exists_diffeomorph_straightening_embedded_closedBall` 类工具处理）；2-柄贴附区
  `AttachingRegion 2 1 = S¹ × D¹` 需 (i)；3-柄需 (ii) 与 Alexander 锥延拓（2.8）。每步还需 H2（沿任意光滑贴附嵌入粘柄）
  与 (i-c)（同痕贴附给出同胚的粘接空间）。
- **路线 R-Hg（Heegaard）**：`PLManifoldTriangulation 3` → Heegaard 分裂（H1′）→ PL 柄体唯一性（PL 层，Phase 3 词汇）
  → 两个标准光滑柄体沿 (ii′) 得到的微分同胚粘合（需把 `exists_smoothAtlas_double_of_collar` 推广到沿微分同胚粘合）。
  只用一次 2 维输入 (ii′)，但 (ii′) 对任意亏格曲面成立的证明成本高于 (ii)。

两条路线都没有现成的 H1/H1′；R-H 的 2 维输入 (i)、(ii) 本库均无生产者；R-Hg 的 (ii′) 亦无。下面给出每个缺口的建议陈述。
所有陈述用本库现有词汇，`待定义` 标记的辅助定义需先落地。

### 2.1 H1：PL 柄分解（无生产者）

本库没有任何 `HandleDecomposition`/`Heegaard` 声明（全库 grep `genus|heegaard|HandleDecomposition` 零命中）。
建议以立方体为 PL 柄模型（`IsPiecewiseAffineOn` 以 H-多面体覆盖 `𝓝[s] x`，**圆球 `ClosedCell` 不是多面体**，
在其曲边界处该定义退化；圆模型与立方模型经 `stdSimplexClosedCellHomeomorph`/径向同胚互换）：

```lean
namespace DifferentialGeometry.Topology.PiecewiseLinear

def cube (k : ℕ) : Set (EuclideanSpace ℝ (Fin k)) := {x | ∀ i, |x i| ≤ 1}   -- 待定义；IsHPolytope
def cubeBoundary (k : ℕ) : Set (EuclideanSpace ℝ (Fin k)) := {x | x ∈ cube k ∧ ∃ i, |x i| = 1}

structure PLHandleDecomposition (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] where
  count : ℕ
  index : Fin count → ℕ
  index_le : ∀ i, index i ≤ n
  handle : (i : Fin count) →
    EuclideanSpace ℝ (Fin (index i)) × EuclideanSpace ℝ (Fin (n - index i)) → X
  injOn : ∀ i, Set.InjOn (handle i) (cube (index i) ×ˢ cube (n - index i))
  continuousOn : ∀ i, ContinuousOn (handle i) (cube (index i) ×ˢ cube (n - index i))
  isPiecewiseAffineOn_chart : ∀ i, ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (e ∘ handle i)
      ((cube (index i) ×ˢ cube (n - index i)) ∩ handle i ⁻¹' e.source)
  cover : (⋃ i, handle i '' (cube (index i) ×ˢ cube (n - index i))) = Set.univ
  attaching : ∀ i, handle i '' (cubeBoundary (index i) ×ˢ cube (n - index i)) ⊆
    ⋃ j : {j // j < i}, handle j '' (cube (index j) ×ˢ cube (n - index j))
  disjoint_interiors : ∀ i j, i ≠ j →
    Disjoint (handle i '' (interior (cube (index i) ×ˢ cube (n - index i))))
      (handle j '' (cube (index j) ×ˢ cube (n - index j)))
  monotone_index : Monotone index

theorem exists_plHandleDecomposition_of_plTriangulation
    {X : Type u} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [HasGroupoid X (plGroupoid 3)]
    (T : PLTriangulation 3 X) (hT : IsCombinatorialManifold 3 T.complex) :
    Nonempty (PLHandleDecomposition 3 X)
```

`attaching` 字段还应要求贴附区落在前面柄之并的**边界**上（可用 `frontier (⋃ j<i, …)`），并要求 `n`-柄的贴附区为整个边界球面。
经典来源：Rourke–Sanderson, *Introduction to PL Topology*, Thm 6.9（三角剖分的二次导出细分给出柄分解）；
Moise GTM 47 §23（三角剖分）。**Heegaard 形式**（H1′）需先定义 PL 柄体模型
`PLHandlebody g`（立方体贴 `g` 个 1-柄），其陈述 `∃ g (h₁ h₂ : PLHandlebody g → X), …` 依赖 PL 柄体唯一性，属 Phase 3 的
PL 正则邻域理论（Rourke–Sanderson Ch. 3）。

### 2.2 H2：沿给定光滑贴附嵌入粘一个光滑柄（无直接生产者）

已有的是 Morse 版本：`exists_morseHandleAdjunction_diffeomorph_upperSublevel_of_morseChart` 在贴附映射为
`morseAttachingEmbedding hk c ε r data hε h.2`、下层为 `SublevelSpace f (c - ε)`、模型为 `MorseHalfSpace m` 时给出
粘接空间的 `ChartedSpace`/`IsManifold` 及 `Handle.lower`/`Handle.cell` 的光滑性。Phase 2 需要的是：下层是任意紧致带边光滑
3-流形 `N`（模型 `𝓡∂ 3`，与 `closedCellChartedSpace`/`standardHandleChartedSpace` 同一模型族），贴附映射是任意光滑嵌入
（带角处理）。建议陈述（结论形状复制 Morse 版本）：

```lean
open DifferentialGeometry.Topology.Handle in
theorem exists_smooth_handle_adjunction
    {N : Type u} [TopologicalSpace N] [T2Space N] [CompactSpace N]
    [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold (𝓡∂ 3) ∞ N]
    {k : ℕ} (hk : k ≤ 3) [NeZero k] [NeZero (3 - k)]
    (φ : AttachingRegion k (3 - k) → N)
    (hφ : Manifold.IsSmoothEmbedding
      ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((3 - k - 1) + 1))) (𝓡∂ 3) ∞ φ)
    (hbd : ∀ p, (𝓡∂ 3).IsBoundaryPoint (φ p)) :
    ∃ hcs : ChartedSpace (EuclideanHalfSpace 3) (AdjunctionSpace k (3 - k) φ),
      @IsManifold ℝ _ (EuclideanSpace ℝ (Fin 3)) _ _ (EuclideanHalfSpace 3) _ (𝓡∂ 3) ∞
        (AdjunctionSpace k (3 - k) φ) _ hcs ∧
      T2Space (AdjunctionSpace k (3 - k) φ) ∧ CompactSpace (AdjunctionSpace k (3 - k) φ) ∧
      @ContMDiff ℝ _ (EuclideanSpace ℝ (Fin 3)) _ _ (EuclideanHalfSpace 3) _ (𝓡∂ 3) N _ _
        (EuclideanSpace ℝ (Fin 3)) _ _ (EuclideanHalfSpace 3) _ (𝓡∂ 3)
        (AdjunctionSpace k (3 - k) φ) _ hcs ∞ (lower φ) ∧
      @ContMDiff ℝ _ (EuclideanSpace ℝ (Fin ((k - 1) + 1)) × EuclideanSpace ℝ (Fin ((3 - k - 1) + 1))) _ _
        (ModelProd (EuclideanHalfSpace ((k - 1) + 1)) (EuclideanHalfSpace ((3 - k - 1) + 1))) _
        ((modelWithCornersEuclideanHalfSpace ((k - 1) + 1)).prod
          (modelWithCornersEuclideanHalfSpace ((3 - k - 1) + 1)))
        (StandardHandle k (3 - k)) _ (standardHandleChartedSpace k (3 - k))
        (EuclideanSpace ℝ (Fin 3)) _ _ (EuclideanHalfSpace 3) _ (𝓡∂ 3)
        (AdjunctionSpace k (3 - k) φ) _ hcs ∞ (cell φ)
```

两条实现路径：(a) 由 `φ` 与 `exists_boundary_collar_diffeomorph` 构造一个把 `N` 变成 Morse 下水平集、把 `φ` 变成
`morseAttachingEmbedding` 的 Morse 函数，然后调用现成定理（需 `MorseHalfSpace m` ↔ `EuclideanHalfSpace 3` 的模型转换，见 §4）；
(b) 直接用 `Manifold.Collar.exists_smooth_attachment_realization`（映射柱）与 `handleAdjunctionDiffeomorph`。
经典来源：Hirsch, *Differential Topology*, Ch. 8 §2（角光滑化与沿边界粘合）；Milnor, *Lectures on the h-cobordism
theorem* §3。规模：中到大（角光滑化是主要成本）。

### 2.3 (i)：光滑曲面中的 PL 圆周/环带可同痕到光滑的（无生产者）

全库没有 `S¹`（`Circle`、`CellBoundary 2`、`𝓡 1`）到曲面的嵌入的任何定理（grep `Diffeomorph (𝓡 1)|IsSmoothEmbedding (𝓡 1)|Circle ≃ₘ`
仅命中 `StandardFactors.lean:133` 的类型）。柄粘接消费的是环带嵌入，建议直接陈述环带版本：

```lean
open DifferentialGeometry.Topology.Handle in
theorem exists_smooth_attaching_annulus_isotopic_of_pl
    {S : Type u} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    (T : PLTriangulation 2 S) (hT : T.IsSmooth)              -- 待定义，见下
    (φ : AttachingRegion 2 1 → S) (hφ : Topology.IsEmbedding φ)
    (hPL : IsPLAttachingMap T φ)                               -- 待定义，见下
    : ∃ (ψ : AttachingRegion 2 1 → S) (H : ℝ → S ≃ₜ S),
      Manifold.IsSmoothEmbedding ((𝓡 1).prod (modelWithCornersEuclideanHalfSpace 1)) (𝓡 2) ∞ ψ ∧
      Continuous (fun q : ℝ × S ↦ H q.1 q.2) ∧ Continuous (fun q : ℝ × S ↦ (H q.1).symm q.2) ∧
      H 0 = Homeomorph.refl S ∧ ∀ p, H 1 (φ p) = ψ p
```

其中 `ψ` 的光滑性用 `attachingRegionChartedSpaceInst 2 1`（模型 `ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)`）。
待定义：`PLTriangulation.IsSmooth`（Whitehead 意义的光滑三角剖分：`∀ s ∈ T.complex.faces, ContMDiffOn 𝓘(ℝ, ℝ^T.ambientDim) (𝓡 2) ∞ T.map (convexHull ℝ ↑s)` 且在每个面上为浸入）与 `IsPLAttachingMap T φ`（`φ` 经 `T.map⁻¹` 与 `AttachingRegion 2 1` 上的标准 PL 结构逐块仿射；`AttachingRegion` 的 PL 结构需经 `stdSimplexCellBoundaryHomeomorph 1` 或改用立方模型）。
只有核心圆周的版本（`γ : sphere (0 : ℝ²) 1 → S` 光滑嵌入，`H 1 '' (T.map '' C.space) = range γ`，`C ≤ T.complex`，`IsPLSphere 1 C.space`）
更短，但随后需 (i-b)。经典来源：Moise GTM 47 §6–8（平面/曲面上的 PL 逼近与 Schoenflies）、Munkres, *Elementary
Differential Topology* §8–10（光滑化 PD 同胚，维数 2）、Hirsch Ch. 8 §1（曲线的光滑逼近与同痕）。规模：大。

### 2.4 (i-b)：框架（法丛平凡化）

若 (i) 只给出核心圆周，需要 `SmoothTwoSidedCollar (𝓡 1) (𝓡 2) γ`：`nonempty_smoothTwoSidedCollar_of_normalTrivialization`
把它归结为 `normalSpace (𝓡 1) (𝓡 2) γ` 的线性平凡化（`Trivialization ℝ …` 且 `baseSet = univ`）。缺口是从 PL 环带（贴附区
`AttachingRegion 2 1` 的像）得到该平凡化：

```lean
theorem exists_normal_trivialization_of_two_sided
    {S : Type u} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    (γ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → S) (hγ : Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ)
    (Φ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Icc (-1 : ℝ) 1 → S) (hΦ : Topology.IsEmbedding Φ)
    (hΦ0 : ∀ z, Φ (z, ⟨0, by norm_num⟩) = γ z) :
    ∃ t : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (normalSpace (𝓡 1) (𝓡 2) γ) → _),
      t.IsLinear ℝ ∧ t.baseSet = Set.univ
```

若采用 2.3 的环带版本，此项被吸收（`ψ` 本身给出光滑环带）。规模：小到中。

### 2.5 (i-c)：同痕的贴附映射给出同胚的粘接空间

`adjunctionCongr φ φ' h hφ` 已把"底空间同胚 `h : X ≃ₜ X'` 且 `h ∘ φ = φ'`"变成粘接空间同胚。缺的是把边界上的
同痕终点 `H 1 : ∂N ≃ₜ ∂N` 延拓为 `N ≃ₜ N`（领技巧）：

```lean
theorem exists_homeomorph_extension_of_boundary_isotopy
    {N : Type u} [TopologicalSpace N] [T2Space N] [CompactSpace N]
    [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold (𝓡∂ 3) ∞ N]
    (H : ℝ → ((𝓡∂ 3).boundary N) ≃ₜ ((𝓡∂ 3).boundary N))
    (hH : Continuous (fun q : ℝ × (𝓡∂ 3).boundary N ↦ H q.1 q.2))
    (hH' : Continuous (fun q : ℝ × (𝓡∂ 3).boundary N ↦ (H q.1).symm q.2))
    (h0 : H 0 = Homeomorph.refl _) :
    ∃ G : N ≃ₜ N, ∀ x : (𝓡∂ 3).boundary N, G x = H 1 x
```

输入：`exists_boundary_collar_diffeomorph`（边界领）。规模：小。经典来源：Hirsch Ch. 8 §2（collaring 与同痕延拓到领）。

### 2.6 (ii)：同胚于 `S²` 的光滑闭曲面微分同胚于 `S²`（无生产者）

```lean
theorem exists_diffeomorph_sphere_of_homeomorph_sphere
    {S : Type u} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    (h : S ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Nonempty (S ≃ₘ⟮𝓡 2, 𝓡 2⟯ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
```

可用输入：`eulerChar_eq_of_homeomorph` + `eulerChar_euclideanSphere 2`（`χ(S) = 2`）；`exists_excellent_morse_function`；
`exists_morse_eulerChar`；`exists_morseHandleAdjunction_diffeomorph_upperSublevel_of_morseChart(_zero/_top)`（2 维柄）；
`sphereDiffeomorphDegree_eq_one_iff_isotopy`（`S²` 的微分同胚，未审计）。仍缺的子砖：

- (ii-a) `Diff(S¹)` 连通性（Γ₁ = 0）：
  ```lean
  theorem exists_circle_isotopy_to_rotation
      (f : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₘ⟮𝓡 1, 𝓡 1⟯ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
      ∃ (J : ℝ → sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₘ⟮𝓡 1, 𝓡 1⟯ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)),
        ContMDiff (𝓘(ℝ).prod (𝓡 1)) (𝓡 1) ∞ (fun q : ℝ × _ ↦ J q.1 q.2) ∧
        ContMDiff (𝓘(ℝ).prod (𝓡 1)) (𝓡 1) ∞ (fun q : ℝ × _ ↦ (J q.1).symm q.2) ∧
        J 0 = f ∧ ∀ z, ((J 1 z : _) : EuclideanSpace ℝ (Fin 2)) = A z
  ```
  经典来源：Munkres, *Elementary Differential Topology* §? / Hirsch Ch. 8 Thm 3.? （`Diff(S¹) ≃ O(2)`），证明经
  `Circle.exp` 提升与单调性；本库 `Circle/Logarithm.lean` 仅有"无连续对数"。规模：中。
- (ii-b) 两个圆盘沿 `S¹` 的微分同胚粘合微分同胚于 `S²`（Reeb 型），依赖 (ii-a) 与 H2 的 2 维版本。规模：中。
- (ii-c) 由 `χ(S) = 2` 与优 Morse 函数得到恰有两个临界点的 Morse 函数（临界点消去，Milnor h-cobordism §5 的 2 维情形）
  或直接走曲面分类（Hirsch Ch. 9）。规模：大。这是 (ii) 的主要成本。

### 2.7 (ii′)：闭曲面的 PL 同胚同痕于微分同胚（无生产者；R-Hg 路线）

```lean
theorem exists_diffeomorph_isotopic_of_pl_homeomorph_surface
    {S : Type u} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    (T : PLTriangulation 2 S) (hT : T.IsSmooth)
    (f : S ≃ₜ S) (hf : IsPL 2 2 f)      -- 相对 T 诱导的 PL 结构，需先由 T 造 HasGroupoid S (plGroupoid 2)
    : ∃ (g : S ≃ₘ⟮𝓡 2, 𝓡 2⟯ S) (H : ℝ → S ≃ₜ S),
      Continuous (fun q : ℝ × S ↦ H q.1 q.2) ∧ Continuous (fun q : ℝ × S ↦ (H q.1).symm q.2) ∧
      H 0 = f ∧ H 1 = g.toHomeomorph
```

经典来源：Munkres 1960（Ann. Math. 72）与 *Elementary Differential Topology* 的 PD 同胚光滑化；Whitehead 1961。
规模：大（大于 (ii)）。仅在 R-Hg 路线需要。

### 2.8 Alexander 锥延拓（3-柄的拓扑侧；无生产者）

`ClosedBall/Extension.lean` 只有连续函数延拓，无同胚延拓：

```lean
theorem exists_closedCell_homeomorph_extension (n : ℕ)
    (f : CellBoundary n ≃ₜ CellBoundary n) :
    ∃ F : ClosedCell n ≃ₜ ClosedCell n, ∀ x, F (cellBoundaryInclusion n x) = cellBoundaryInclusion n (f x)
```

用途：`N₂ ∪_f D³ ≃ₜ X₂ ∪_g D³` 只需 `g ∘ h ∘ f⁻¹ : S² ≃ₜ S²` 的锥延拓，不需要 Smale 定理。规模：小。

### 2.9 装配与宇宙/模型对接（无生产者）

- `PLSmoothingModel.{u}` 要求 `N : Type u`；Morse/柄层定理全在 `Type`（宇宙 0）。若在 `Type` 中造模型再 `ULift`，需
  `ULift` 的 `ChartedSpace`/`IsManifold` 运输（`Manifold/ULift.lean` 有 `uliftDiffeomorph`，该文件的 `sorry` 只在定向部分；
  需单独审计），或把柄层定理推广到 `Type u`。
- 目标 `IsManifold (𝓡 3) ∞ N` 是**无边**模型；柄归纳中间对象是带边模型 `𝓡∂ 3`。最后一步 3-柄贴附后需"无边流形的
  `𝓡∂ 3` 结构 ⇒ `𝓡 3` 结构"的转换（`I.Boundaryless`/内点图卡），本库无现成声明；建议：
  ```lean
  theorem exists_chartedSpace_euclidean_of_boundary_empty
      {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold (𝓡∂ 3) ∞ N]
      (h : (𝓡∂ 3).boundary N = ∅) :
      ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 3)) N, letI := C; IsManifold (𝓡 3) ∞ N ∧
        Nonempty (N ≃ₘ⟮𝓡∂ 3, 𝓡 3⟯ N)
  ```
- 紧致性：`PLSmoothingModel` 未含 `CompactSpace X`；Phase 2 只证紧致情形时应新增
  `PLSmoothingModelCompact`（同定义加 `[CompactSpace X]`）并证明它足以支持 `exists_isManifold_three_of_plApproximation_of_plSmoothing`
  的紧致消费者（该定理已假设 `[CompactSpace M]`）。

## 3. 建议的砖块顺序（R-H 路线）

| 序 | 砖块 | 规模（估） | 依赖 | 经典来源 |
|---|---|---|---|---|
| B0 | 2.8 锥延拓；2.5 边界同痕延拓（领技巧）；2.9 的无边转换与紧致接口 | 各 100–300 行 | `exists_boundary_collar_diffeomorph`, `adjunctionCongr` | Hirsch Ch. 8 §2 |
| B1 | 2.2 H2：沿光滑贴附嵌入粘柄 + 角光滑化（`k = 0,1,2,3`，3 维） | 1500–4000 行 | 1.E Morse 粘接、1.F 领、1.C 标准柄 | Hirsch Ch. 8; Milnor h-cobordism §3 |
| B2 | 2.1 H1：立方 PL 柄模型、`PLHandleDecomposition`、由 `PLTriangulation` 的二次导出细分得到分解 | 2000–5000 行 | 1.A、`SimplicialComplex/*`、Phase 3 的细分 | Rourke–Sanderson Thm 6.9; Moise §23 |
| B3 | 2.3/2.4 (i)：曲面中 PL 环带同痕到光滑环带（含 1-柄的圆盘情形） | 3000–6000 行 | 1.G 平面同痕、`Diffeomorph/Extension`, `Perturbation` | Moise §6–8; Munkres EDT; Hirsch Ch. 8 §1 |
| B4 | 2.6 (ii)：(ii-a) `Diff(S¹)`；(ii-b) 两圆盘粘合 ≅ `S²`；(ii-c) `χ = 2 ⇒` 两临界点 | (ii-a) 500–1000；(ii-b) 500–1500；(ii-c) 3000–8000 行 | 1.E、1.G、1.I | Munkres EDT; Milnor h-cobordism §5; Hirsch Ch. 9 |
| B5 | 装配：对 `PLHandleDecomposition` 归纳，维护 `N_j`（`𝓡∂ 3`）与 `N_j ≃ₜ X_j`，末步用 B0 得 `PLSmoothingModelCompact 3` | 1000–2000 行 | B0–B4 | — |

若改走 R-Hg：B2 换成 Heegaard 分裂 + PL 柄体唯一性（Phase 3 的 PL 正则邻域、PL Schoenflies §17），B3+B4 换成 2.7 (ii′)
与"沿微分同胚粘合两个带边流形"（推广 `exists_smoothAtlas_double_of_collar`）。总成本预计不低于 R-H，且 (ii′) 无本库输入；
R-H 已有 `S²` 微分同胚链（1.G）与 Morse 柄粘接可复用。建议 R-H。

## 4. 警告：名称相近但条件性或含 `sorry` 的声明

- `ThreeManifold/SmoothSchoenflies.lean: smooth_schoenflies_three`：**直接 `sorry`**（他人负责）。
  `SphereSeparation/Schoenflies.lean: smoothSchoenfliesThree` 是 `Prop`；`exists_global_diffeomorph_of_smoothSchoenflies`、
  `exists_ball_sphereSides_of_smoothSchoenflies`、`exists_nested_ball_shell_of_two_spherical_boundaries` 都显式带 `hSch`
  假设，公理审计干净但**条件性**。Phase 2 路线不需要它们。
- `Manifold/SphereOrientation.lean: exists_unique_sphere_orientation`：`sorry`；由此 `sphereOrientation`、
  `ThreeManifold/StandardSphere.lean: standardThreeSphere/standardThreeSphereLift`、`ConnectedSum/*`、`StandardFactors`、
  `PoincareStandard` 的公理闭包含 `sorryAx`（探针确认 `standardThreeSphere`、`sphereOrientation`）。标准 `S³` 请直接用
  Mathlib 的 `sphere (0 : EuclideanSpace ℝ (Fin 4)) 1`。
- `Manifold/Components.lean:115`、`Manifold/ProductOrientation.lean:39`、`Manifold/ULift.lean:96`（定向局部常值性）、
  `Homology/HurewiczLowDegrees.lean:32,44`（Hurewicz 2/3 维）：`sorry`。`ULift.lean` 的非定向部分若用于 2.9 需单独审计。
- `ConnectedSum/Construction.lean` 的 `exists_oriented_ball_chart`、`exists_boundary_attachment`、`exists_smooth_connected_sum`、
  `connectedSum_choice_independent` 与 `ConnectedSum/Finite.lean` 全部定理：`sorry`。名称暗示"光滑粘合球面边界"，不可复用。
- `Manifold/SphereDiffeomorphDegree.lean` 等 8 个球面/平面同痕模块（§0.2 列表）：源码无 `sorry`，但审计时共享检出无 olean，
  **未做公理审计**；使用前需在根构建完成后 `#print axioms sphereDiffeomorphDegree_eq_one_iff_isotopy`。
- `Topology/PiecewiseLinear/Polyhedron.lean` 的 `CombinatorialManifoldPLStructure`、`PLManifoldTriangulation` 与
  `Approximation.lean`/`Smoothing.lean` 的 `PLApproximation`、`PLSmoothing(Model)` 都是 **`Prop` 接口**；以它们为假设的
  定理必须报告为条件性，且不得用经典定理名（`NAMING.md` §3）。
- `SimplicialComplex/GeometricManifoldLinks.lean` 的 `faceEulerChar_vertexLink_*` 只给 link 的 **Euler 数**，不是
  `IsCombinatorialManifold`（link 是 PL 球面）；不能替代 T2。
- Morse 柄粘接定理（1.E）：流形在 **`Type`**（宇宙 0）；带边模型是 `MorseHalfSpace m`/`morseModelWithCornersHalfSpace m`，
  与 `Handle/Manifold.lean` 的 `EuclideanHalfSpace`/`modelWithCornersEuclideanHalfSpace` 不同，直接组合需要模型转换；
  贴附映射固定为 `morseAttachingEmbedding`，不是任意光滑嵌入（见 2.2）。
- `exists_smoothAtlas_of_homeomorph` 要求源流形 **无边**（`[I.Boundaryless]`）且目标模型改为 `𝓘(ℝ, E)`；带边中间对象请用
  `pullbackChartedSpace`（任意模型）。
- `Handle.AdjunctionSpace` 是 `Quot`，`T2Space`/`CompactSpace` 不自动成立；`adjunctionHomeomorphUnionImage` 需要
  `[T2Space Y]`、`IsClosed X₀`、`c` 连续单射与 `Disjoint (c '' (univ \ attachingRegion)) X₀`。
- `IsPiecewiseAffineOn` 以有限 H-多面体覆盖 `𝓝[s] x`；在**圆**胞腔 `ClosedCell`/`AttachingRegion` 的曲边界处该定义退化，
  PL 柄模型应取立方体/单形（2.1），再经 `stdSimplexClosedCellHomeomorph` 与圆模型互换。
- `exists_smoothAtlas_double_of_collar` 仅沿恒同（double）粘合，且在 `Type`；沿一般微分同胚粘合需推广。
- `ClosedBall/Extension.lean: extension` 是连续函数延拓（经 `retraction`），不是同胚延拓；Alexander 锥延拓仍缺（2.8）。
