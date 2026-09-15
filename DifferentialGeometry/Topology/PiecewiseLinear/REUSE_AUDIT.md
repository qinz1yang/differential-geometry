# 可复用形式化的公理审计与复用决定（2026-09-15）

另一会话整理了本机可复用的现成形式化（vendored `External/Schoenflies`、`Topology/PlanarJordan`、
`Topology/FundamentalGroup`、`Topology/VanKampen`、`Topology/SphereSeparation`、`Topology/Homology`、Phase 2 工具、
Bennett 的 `origin/Moise`）。本文件记录本方对其中关键声明的独立 `#print axioms` 审计与复用决定。各车道在其 handoff 中引用本文件即可。

## 1. 已审计声明（审计文件 `.lake/scratch/AuditClaudeReuse.lean`，全部只含 `propext`、`Classical.choice`、`Quot.sound`）

| 声明 | 模块 | 可供 |
|---|---|---|
| `Schoenflies.jordan_schoenflies_homeomorph`（Jordan 曲线间同胚延拓为平面同胚） | `External/Schoenflies/JordanSchoenflies` | P.4（10.8 驯顺）、P.5 |
| `Schoenflies.jordan_curve_theorem` | `External/Schoenflies/JordanClosed` | 已被 P.1 原生证明消费 |
| `PlanarJordan.exists_regions_of_simple_closed_curve`、`closure_inside_union_of_isCrosscut`、`eq_or_eq_of_isArcBetween_subset_isCutPair`、`nonempty_homeomorph_closedBall_closure` | `Topology/PlanarJordan/{Regions,ClosedInterior}` | P.5（4.4 任意弧、Problem 4.1、θ 曲线） |
| `fundamentalGroupCircleEquivInt`、`fundamentalGroupProdEquiv`、`fundamentalGroupProdCircleEquivIntOfSimplyConnected`、`fundamentalGroupMulEquivOfHomotopyEquiv` | `Topology/FundamentalGroup/{Circle,Product,HomotopyEquiv}` | L.2 第 2 砖、I.7（30.8）、D.3（27.3）、T.* |
| `VanKampen.freeProductToFundamentalGroup`、`VanKampen.simplyConnectedSpace_of_open_cover` | `Topology/VanKampen/{FreeProduct,SimplyConnectedUnion}` | L.2、I.5（30.6） |
| `SphereSeparation.connectedComponents_equiv_fin_two_of_reducedSingularH0_iso_int`、`subspaceMayerVietoris_exact_at_middle`、`hasTwoComplementComponents_of_alexanderDualityH0Certificate` | `Topology/SphereSeparation/{ReducedH0,CochainMayerVietoris,JordanBrouwer}` | I.1/I.2 的工具；`JordanBrouwer` 只在 H₀ 证书假设下成立，不能替代 B.6/I.4 |
| `Manifold.sphereDiffeomorphDegree_eq_one_iff_isotopy` | `Topology/Manifold/SphereDiffeomorphDegree` | Phase 2 B4(ii) |
| `Homology.eulerChar_eq_of_homeomorph` | `Topology/Homology/EulerCharacteristic` | H 车道（已在用） |

`External/Schoenflies` 中 `sorry`/`axiom` 的文本命中都在注释里；上表两个端点的公理闭包证明它们不依赖任何额外公理。

## 2. 复用决定

- P.4（10.8）、P.5：S 车道若需要，直接消费 `External/Schoenflies` 与 `Topology/PlanarJordan`（拓扑 Schoenflies + PL 逼近，
  而不是原生证驯顺）。先核对陈述与假设；不改这些文件。是否需要 10.8 由 S.3/S.4 的接口清单决定。
- Bennett `origin/Moise`（38 个模块，其接口他自审为标准公理）：建议只择取同调与覆盖 transfer 部分
  `Topology/Homology/{ChangeOfRings, Coefficients, CoveringTransfer, CoveringTransferExact, CoveringTransferNaturality,
  CoveringTransferSequence, Reduced/MayerVietorisCoefficients, Reduced/PointClasses}`、`Topology/Covering/LiftEnumeration`、
  `Topology/Manifold/{CoveringAtlas, CoveringStructomorph}`（连同它们引用的 `Tensor/LinearAlgebra/Finsupp/FiniteFibers`、
  `Topology/Manifold/GroupoidPullback` 若非基线），**不取** `Topology/Manifold/PiecewiseAffine.lean`（与 `plGroupoid` 竞争的
  第二套 PL 层级）与他对根聚合 `DifferentialGeometry.lean` 的改动。择取后在整合分支上逐模块聚焦检查与审计。
  消费者：C.5（`H₁ ↠ ℤ₂`）、H.5（`b₁ > 0`）、H 的 ℚ 系数。
  **已执行（2026-09-15，用户批准「只取同调/covering」）**：整合分支提交 `9379160dd`（作者 Bennett Chow）择取了十个新文件
  `Tensor/LinearAlgebra/Finsupp/FiniteFibers`、`Topology/Covering/LiftEnumeration`、`Topology/Homology/{ChangeOfRings,
  Coefficients, CoveringTransfer, CoveringTransferExact, CoveringTransferNaturality, CoveringTransferSequence,
  Reduced/MayerVietorisCoefficients, Reduced/PointClasses}`（共 1289 行，只依赖基线的 `Covering/Lifting`、
  `Homology/Algebra/Augment`、`Homology/Reduced`、`Homology/Reduced/MayerVietorisNaturality`）。未取他对基线
  `Topology/Manifold/CoveringAtlas.lean` 的重构（删除 `coveringChart`、`coveringChartedSpace` 等，会破坏消费者）及依赖它的
  `CoveringStructomorph`、`GroupoidPullback`。十个模块逐个聚焦检查 exit 0，`AuditClaudeBennett.lean` 的 69 项声明只含标准三公理。
  各车道下次合并整合分支即可 `import`。
- H.4：维持不整体 vendor 上游 classification-of-surfaces（只有拓扑存在性，无 χ/H₁/π₁ 与标准形互异）。

## 3. 不可用

- `Topology/Homology/HurewiczLowDegrees.lean`：2、3 维版本含 `sorry`，任何车道不得引用；一维 Hurewicz（`H₁ ≅ π₁^ab`）本库没有。
- `sphere-six-complex`：含 `public axiom`。
- `smooth_schoenflies_three`：`sorry`，有负责人，不得消费或复制。
- 上游 `LocallyFiniteTriangulation`、`LocallyFiniteControlledApproximation`、`ChartInduction`：平面专用类型，只能作设计模板。
