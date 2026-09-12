# `ch:rfs-topology` — 固定交接库存

快照时间：`2026-09-09T00:32:17.570097+00:00`。基线：`804e9a8a7289f3b4de293aa34fffb5f52fb7d812`。主计划仍是 `Extinction/EXTINCTION_PLAN.md`；本文件只描述包内固定字节。

## 书节点 crosswalk

17 个数学节点，0 verified、16 conditional、1 not stated。已证明 helper 和消费者不等于完整书节点闭合。

### `ch:rfs-topology`

| 书节点 | 原文标题 | 拟定树声明 | 负责人 | 状态 |
|---|---|---|---|---|
| `def:rfs-comparison-background` | Background used by the comparison and class arguments | `Surgery/Topology/Background.lean`, `Homology.lean` · `TangentOrientationSection`, `IntegralHomology`, `RelativeIntegralHomology`, `fundamentalClass`, `orientedDegree` | W-A | not stated · actual orientation and relative-chain layer checked; fundamental class/degree conditional; full duality/Hurewicz/mapping background pending |
| `prop:rfs-capped-simply-connected` | Simple connectivity after spherical cutting and capping | `Surgery/Topology/CutCap.lean` · `rfs_capped_simply_connected`, `rfs_retained_capped_simply_connected` | W-A | conditional · actual full cut/cap target checked/lint/audit; sphere separation and cap induction deferred |
| `prop:rfs-homotopy-groups` | Second and third homotopy groups | `Surgery/Topology/LoopClass.lean`, `Homology.lean` · `rfs_homotopy_groups`, `positiveHurewiczEquiv`, `fundamentalClass_generator` | W-A | conditional · actual signed cubical Hurewicz and oriented H3 generator checked/lint/audit; actual cubical additivity and relative-simplex-family invariance proved; Hurewicz and four local/global orientation-class producer debts remain |
| `def:rfs-child-parent` | Child core and parent at an actual event | `Surgery/Topology/ChildParent.lean`, `CutCap.lean` · `childParent`, `childCoreComponent`, `childCoreInclusion`, `componentOrientation`, `core_compact` | W-A | conditional · actual orientation and literal core compactness proved/check/lint/audit without sorryAx; full restricted cap embeddings checked; capping producer debts remain |
| `lem:rfs-actual-descendants` | Parenthood and simple connectivity on a history | `Surgery/Topology/Descendants.lean`, `Ancestry.lean`, `ObservationTower.lean` · `rfs_actual_descendants`, `childParent_unique`, `rfs_simply_connected_history`, `ObservationTower.observe_simplyConnected` | W-A | conditional · actual finite histories and compatible real observations checked/lint/audit; literal initial component identification and initial simple-connectivity transport proved; capping and child simple-connectivity producers retain sorryAx |
| `lem:rfs-exterior-branches` | One exterior region for each boundary sphere | `Surgery/Topology/Comparison.lean` · `rfs_exterior_branches` | W-A | conditional · actual exterior regions and complete boundaryless case checked/lint/audit; explicit topological debt |
| `lem:rfs-comparison-support` | A compact region containing every nonconstant piece | `Surgery/Topology/Comparison.lean` · `rfs_comparison_support` | W-A | conditional · same actual core/collars/terminal domain and exterior decomposition checked/lint/audit; producer debt |
| `def:rfs-whole-parent-map` | The whole-parent collapse map | `Surgery/Topology/Comparison.lean` · `rfs_whole_parent_map` | W-A | conditional · actual unique finite pasting with all three exact formulas checked/lint/audit; continuity/uniqueness producer debt |
| `lem:rfs-collapse-degree` | Continuity, local length control, and degree | `Surgery/Topology/Comparison.lean` · `rfs_collapse_degree` | W-A | conditional · actual fundamental-class equation, full-core agreement, support constancy and local length control checked/lint/audit; producer debt |
| `lem:rfs-local-to-global-length` | From local length estimates to ambient distances | `Surgery/Topology/WeakLength.lean` · `rfs_local_to_global_length` | W-A | conditional · exact all-rectifiable-curve target checked/lint/audit; explicit sorry |
| `thm:rfs-child-comparison` | Actual child maps with a uniform incoming-time modulus | `Surgery/Topology/Comparison.lean` · `rfs_child_comparison` | W-A | conditional · actual event maps for all retained children, degree one and one common incoming modulus checked/lint/audit; five geometric/topological producer debts |
| `def:rfs-positive-homotopy-class` | The orientation class with a specified basepoint | `Surgery/Topology/LoopClass.lean`, `BasedTransport.lean` · `positiveHomotopyClass`, `positiveHomotopyClass_infiniteOrder` | W-A | conditional · actual positive Hurewicz generator, infinite order and specified path transport checked/lint/audit; explicit topological producer debts |
| `prop:rfs-degree-class-transport` | Degree and canonical basepoint transport | `Surgery/Topology/LoopClass.lean`, `BasedTransport.lean` · `rfs_degree_class_transport` | W-A | conditional · full degree-power, actual path/basepoint, composition, naturality and independence clauses checked/lint/audit; consumers proved, path/Hurewicz producers deferred |
| `def:rfs-continuous-loop-model` | Continuous loop spaces and the adjunction convention | `Surgery/Topology/LoopModel.lean`, `FreeLoopClass.lean`, `SphereSmash.lean` · `BasedContinuousLoop`, `cubeAdjunct`, `basedLoopAdjunctionEquiv`, `sphereCubeParameter`, `standardSmashHomeomorph` | W-A | conditional · actual compact-open spaces, ordered cube adjunction, exact sphere-circle smash homeomorphism and outward-normal sign certificates checked/lint/audit; five explicit smash/parameter debts and prior adjunction producers remain |
| `prop:rfs-free-loop-class` | The free-loop orientation class and its naturality | `Surgery/Topology/FreeLoopClass.lean` · `rfs_free_loop_class`, `positiveFreeLoopClass_eq`, `positiveFreeLoopClass_nontrivial`, `positiveFreeLoopClass_natural`, `positiveFreeContractibleClass` | W-A | conditional · full connectivity/natural adjunction/basepoint independence/nonzero/degree-one clauses checked/lint/audit; nonzero and contractible-subspace consumers proved, topological producers deferred |
| `def:rfs-finite-ancestor-chain` | The ancestor chain of an observed component | `Surgery/Topology/AncestryCore.lean` · `FiniteAncestorChain`, `ancestorComponent`, `rfs_finite_ancestor_chain`, `exists_unique_finiteAncestorChain` | W-A | conditional · actual reverse finite recursion and uniqueness proved/check/lint/audit; zero local sorry, upstream actual parent construction debts remain |
| `thm:rfs-finite-ancestry` | Finite ancestry and transport in the same history | `Surgery/Topology/Ancestry.lean`, `HistoryAncestry.lean`, `ObservationTower.lean` · `rfs_finite_ancestry`, `ObservationTower.observe_finite_ancestry`, `observe_ancestry_restrict` | W-A | conditional · full actual alpha/beta transport, compatible observations and original-index ancestry restriction checked/lint/audit; tower restriction has a proof; geometric producers still retain sorryAx |

## 正式文件与候选

30 个已注册文件有 50 处直接 `sorry`；另两个未注册文件分开报告。完整文件包含原始 signatures、namespace、section hypotheses 和证明；这里不以摘要替代公开目标。

| 文件 | 身份 | 直接 sorry | SHA256 |
|---|---|---:|---|
| `Ancestry.lean` | 已注册正式文件 | 1 | `8caed7abb4ceaccb1d057d1ae4b9b1e9cda9b198ced7d0999f731750722820c1` |
| `AncestryCore.lean` | 已注册正式文件 | 0 | `6bf7e765dcf88d953429404347dbb37bc73be8aef5e892e17e436ed5381baa2c` |
| `Background.lean` | 已注册正式文件 | 0 | `81915ade4f200f900222bb21c318128d2a384700ffb10764b08d592ff6bdf281` |
| `Backward.lean` | 已注册正式文件 | 0 | `5641dedfc5893a6fa0bcf76b21e9c5522b8b67160dc8198b72a2e005711a0bf6` |
| `BasedTransport.lean` | 已注册正式文件 | 10 | `e2616cf2038ce173d641fe8ee389d931794641aa11808ec62350972f3014ddbe` |
| `ChartOrientation.lean` | 最后修订未检查，未注册 | 0 | `9da2d099740896aacb9edb57c32aea2946ed9ef4c8b7472adac3207abfb3c39f` |
| `ChildParent.lean` | 已注册正式文件 | 1 | `9eb5aa39570527e1d58cc98dac126c7718abe517fbda0a36480afd38ad7d3031` |
| `Cohomology.lean` | 已注册正式文件 | 0 | `62345b29baddf845417b0dd11243409ff44f5d916542a4de11ce4b4bd1a762f4` |
| `Comparison.lean` | 已注册正式文件 | 5 | `6ab7eb4015d0ed6dc0df869ff484b893c927adb67adce8ea5c3c210c4c0da286` |
| `CutCap.lean` | 已注册正式文件 | 2 | `5c8b037e2748fb08cea892dc2e9730fd53a9f09693ece2ca1fe4c257cd22fa8f` |
| `Descendants.lean` | 已注册正式文件 | 0 | `b321b690433eea62dd104e8b4a62672481111fc6a9146558acebbb6fc605f98b` |
| `EventData.lean` | 已注册正式文件 | 2 | `83030bce43f479ab62c366a9a3e5cdfc05eaeb367cadf5a18b7d178b9a5402f9` |
| `FreeLoopClass.lean` | 已注册正式文件 | 13 | `d7299fef961f4a314dd1e0e5c6916488f83fde9a920629a4ade92735907f9bf1` |
| `GeometricCutoff.lean` | 已注册正式文件 | 1 | `d238a45ac4139b1e97f470d5ace94e6343ea5d675f870f57d34067c6bb95aea0` |
| `History.lean` | 已注册正式文件 | 0 | `07e0e989787329088de29f642beb12b14324ebb7e064244f65afead85d47c7c2` |
| `HistoryAncestry.lean` | 已注册正式文件 | 0 | `bd38f63c25726387608e1d3f28ff1aaaf8e97b2ac45ec0b297e5b3f20d167a10` |
| `HistoryCompatibility.lean` | 已注册正式文件 | 0 | `643254ca4a53de0f40a07440fad34748375691b831d7034d5d46b751809e7ed8` |
| `HistoryIdentities.lean` | 已注册正式文件 | 0 | `bcda60e5e153477306a2f8d712c05234567fb9ef13c297382418498a863f956d` |
| `HistoryPresentation.lean` | 已注册正式文件 | 0 | `4b4a5ef57cdc2773b86cad0feb339c595a78a49aafde3f573657bf521bd2f69b` |
| `HistoryRestriction.lean` | 已注册正式文件 | 0 | `d472a91b27935f2f4c9ec7d3818a3de507ecb622922fdbc61ad036e63e19fb84` |
| `HistorySlices.lean` | 已注册正式文件 | 0 | `77f2d3396884fe6dfcd4cc7185b7e0d729214ed21602341c2a943b63f9ff3219` |
| `Homology.lean` | 已注册正式文件 | 4 | `4287489181806c2a17c49402b1c4dccac3cac8ace0badd4e3a71fc55cad6d998` |
| `LinearOrientation.lean` | focused/lint 通过，未单独公理审计、未注册 | 0 | `2b0c1c74d3f41eb094b5531da5c0138a9b08e0cc20a2301bd01b1641481f70eb` |
| `LoopClass.lean` | 已注册正式文件 | 1 | `299d9052a28497f3a24d38aebdd7dd899848fc7fabe48ba85e31d06a9111721c` |
| `LoopModel.lean` | 已注册正式文件 | 0 | `0e401a31083c84293e3397814d9a71916bf65792ee651b9bb766f1fd2fe78b19` |
| `ObservationTower.lean` | 已注册正式文件 | 0 | `4caa19364bce6682ca9ca0f24c65fba952a0d824eca9335c0a6e763d09cf1ecf` |
| `OrientationDegree.lean` | 已注册正式文件 | 0 | `5ae2beed1f4339794f8e56b49e76737a316b3ec1b3f19f8f5bae39fc6cc61e16` |
| `Recenter.lean` | 已注册正式文件 | 1 | `1cdb02a0afc24b47ba8ffbaf211432463918cd279058c9c4cba19aeb460097f0` |
| `SphereSmash.lean` | 已注册正式文件 | 5 | `dd18be6c19edd0a586d85d8408cae111b604145ed5f18943cad86e796c9e3b14` |
| `StaticCap.lean` | 已注册正式文件 | 2 | `033a73ca7f75197acfa50a008aef1e6946d3518943a4ed8d6e2a06bcd362b32a` |
| `VanKampen.lean` | 已注册正式文件 | 0 | `87ee617c5507aecf158b6a98b77ba2ef60329eb4feafb1c43fd5d4507faec7a8` |
| `WeakLength.lean` | 已注册正式文件 | 2 | `eb9bc22f98140f120c01d7a387e6c20f1751889951feb9a6eedcf6fd8aac88ea` |

## 直接证明债

词法扫描剔除嵌套注释、行注释和字符串后计数。下列是直接 `sorry` 所属声明；没有传递公理审计含义，也不能据此判断某条路线已被阻塞。书引用只使用 label。

| 文件 | 原始声明 |
|---|---|
| `Ancestry.lean` | `rfs_finite_ancestry_restrict` |
| `BasedTransport.lean` | `exists_unique_pathTransportClass` |
| `BasedTransport.lean` | `pathTransportClass_homotopic` |
| `BasedTransport.lean` | `pathTransport_one` |
| `BasedTransport.lean` | `pathTransport_mul` |
| `BasedTransport.lean` | `pathTransport_bijective` |
| `BasedTransport.lean` | `pathTransport_refl` |
| `BasedTransport.lean` | `pathTransport_trans` |
| `BasedTransport.lean` | `pathTransport_natural` |
| `BasedTransport.lean` | `pathTransport_independent` |
| `BasedTransport.lean` | `hurewiczThree_pathTransport` |
| `ChildParent.lean` | `child_simplyConnected` |
| `Comparison.lean` | `rfs_exterior_branches` |
| `Comparison.lean` | `rfs_comparison_support` |
| `Comparison.lean` | `exists_unique_wholeParentMap` |
| `Comparison.lean` | `rfs_collapse_degree` |
| `Comparison.lean` | `rfs_child_comparison` |
| `CutCap.lean` | `rfs_cap_component_bijection` |
| `CutCap.lean` | `rfs_capped_simply_connected` |
| `EventData.lean` | `exists_unique_standardCapMetric` |
| `EventData.lean` | `standardCapConformalCoordinate_bijective` |
| `FreeLoopClass.lean` | `sphereCubeVector_continuous` |
| `FreeLoopClass.lean` | `exists_unique_sphereFactor` |
| `FreeLoopClass.lean` | `sphereFactor_homotopic` |
| `FreeLoopClass.lean` | `exists_unique_cubeAdjunct` |
| `FreeLoopClass.lean` | `cubeAdjunct_homotopic` |
| `FreeLoopClass.lean` | `basedLoopAdjunction_bijective` |
| `FreeLoopClass.lean` | `basedLoopAdjunction_one` |
| `FreeLoopClass.lean` | `basedLoopAdjunction_mul` |
| `FreeLoopClass.lean` | `freeLoopAdjunction_natural` |
| `FreeLoopClass.lean` | `rfs_free_loop_class` |
| `FreeLoopClass.lean` | `positiveFreeLoopClass_eq` |
| `FreeLoopClass.lean` | `every_continuousLoop_contractible` |
| `FreeLoopClass.lean` | `positiveFreeLoopClass_natural` |
| `GeometricCutoff.lean` | `IncomingBackwardNeck.metric_smooth_up_to` |
| `Homology.lean` | `exists_unique_localOrientationClass` |
| `Homology.lean` | `localOrientationClass_generator` |
| `Homology.lean` | `exists_unique_fundamentalClass` |
| `Homology.lean` | `fundamentalClass_generator` |
| `LoopClass.lean` | `rfs_homotopy_groups` |
| `Recenter.lean` | `exists_universal_neck_recenter_constants` |
| `SphereSmash.lean` | `sphereThreeCubeVector_norm` |
| `SphereSmash.lean` | `sphereThreeCubeVector_continuous` |
| `SphereSmash.lean` | `exists_unique_standardSmashHomeomorph` |
| `SphereSmash.lean` | `sphereTwo_parameter_positive` |
| `SphereSmash.lean` | `standardSmash_parameter_positive` |
| `StaticCap.lean` | `exists_unique_shrinkingCylinderMetric` |
| `StaticCap.lean` | `standardCap_edist_zero` |
| `WeakLength.lean` | `rfs_local_to_global_length` |
| `WeakLength.lean` | `rfs_weak_length` |

## Imports 与源码边界

下列逐文件 imports 直接从源码读取。Topology 以外的原生直接依赖作为只读快照打包；更深依赖和 Mathlib 仍须使用完整基线工程。候选的 Homology import 只用于开发，迁移时必须避免反向循环。

### `Ancestry.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncestryCore`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Comparison`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FreeLoopClass`

### `AncestryCore.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent`

### `Background.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel`
- `Mathlib.LinearAlgebra.Orientation`
- `Mathlib.Geometry.Manifold.ContMDiffMFDeriv`

### `Backward.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData`

### `BasedTransport.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopClass`

### `ChartOrientation.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LinearOrientation`
- `Mathlib.Analysis.Calculus.FDeriv.OfCompLeft`
- `Mathlib.Analysis.Normed.Module.Convex`

### `ChildParent.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData`
- `Mathlib.Analysis.Convex.PathConnected`
- `Mathlib.Geometry.Manifold.MFDeriv.Atlas`
- `Mathlib.LinearAlgebra.Dimension.Constructions`

### `Cohomology.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology`
- `Mathlib.CategoryTheory.Abelian.Ext`
- `Mathlib.Algebra.Homology.Opposite`

### `Comparison.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff`

### `CutCap.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel`
- `Mathlib.Topology.Connected.TotallyDisconnected`
- `Mathlib.Topology.Connected.LocallyConnected`
- `Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected`
- `Mathlib.Geometry.Manifold.Diffeomorph`

### `Descendants.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent`
- `Mathlib.Topology.Connected.Clopen`

### `EventData.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCap`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WeakLength`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic`
- `DifferentialGeometry.Geometry.Metric.OpenSubtype`
- `DifferentialGeometry.Geometry.Compactness.CheegerGromov.Convergence.Metric`
- `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`
- `Mathlib.Geometry.Manifold.Instances.Real`
- `Mathlib.Geometry.Manifold.Instances.Sphere`
- `Mathlib.Geometry.Manifold.SmoothEmbedding`

### `FreeLoopClass.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopClass`

### `GeometricCutoff.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap`
- `DifferentialGeometry.Geometry.Curvature.DimensionThree.AlgebraicCurvatureOperatorMetric`
- `Mathlib.Analysis.Calculus.IteratedDeriv.Defs`

### `History.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData`

### `HistoryAncestry.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Ancestry`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPresentation`

### `HistoryCompatibility.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryIdentities`

### `HistoryIdentities.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPresentation`

### `HistoryPresentation.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction`

### `HistoryRestriction.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.History`
- `Mathlib.Data.Finset.Max`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction`

### `HistorySlices.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction`

### `Homology.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background`
- `Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance`
- `Mathlib.AlgebraicTopology.SimplicialSet.TopAdj`
- `Mathlib.Algebra.Category.ModuleCat.Abelian`
- `Mathlib.Algebra.Category.ModuleCat.Colimits`
- `Mathlib.Algebra.Module.ULift`
- `Mathlib.Algebra.Homology.HomologicalComplexAbelian`
- `Mathlib.Geometry.Manifold.MFDeriv.Atlas`
- `Mathlib.Geometry.Manifold.MFDeriv.FDeriv`
- `Mathlib.Topology.Algebra.Module.FiniteDimension`
- `Mathlib.Analysis.Normed.Group.Bounded`

### `LinearOrientation.lean`

- `Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional`
- `Mathlib.Analysis.Normed.Module.Connected`
- `Mathlib.Topology.Homotopy.Basic`
- `Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho`
- `Mathlib.LinearAlgebra.Matrix.Block`
- `Mathlib.LinearAlgebra.Determinant`
- `Mathlib.LinearAlgebra.Orientation`
- `Mathlib.Tactic.NormNum`

### `LoopClass.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology`
- `Mathlib.AlgebraicTopology.SimplicialSet.TopAdj`
- `Mathlib.Topology.Homotopy.HomotopyGroup`
- `Mathlib.GroupTheory.Perm.Sign`
- `Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected`
- `Mathlib.Topology.CompactOpen`
- `Mathlib.Tactic.FinCases`
- `Mathlib.Data.Fin.VecNotation`

### `LoopModel.lean`

- `Mathlib.Topology.Instances.AddCircle.Real`
- `Mathlib.Geometry.Manifold.Instances.Sphere`
- `Mathlib.Topology.Homotopy.Basic`

### `ObservationTower.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.OrientationDegree`
- `DifferentialGeometry.Topology.Manifold.PartialDiffeomorphOpens`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryCompatibility`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAncestry`
- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Descendants`
- `Mathlib.Algebra.Order.Archimedean.Real.Basic`

### `OrientationDegree.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology`
- `Mathlib.Geometry.Manifold.Diffeomorph`
- `Mathlib.AlgebraicTopology.SimplicialSet.TopAdj`

### `Recenter.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap`

### `SphereSmash.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FreeLoopClass`
- `Mathlib.Analysis.Calculus.FDeriv.Basic`
- `Mathlib.Data.Fin.VecNotation`

### `StaticCap.lean`

- `DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData`
- `DifferentialGeometry.Geometry.Curvature.Metric`
- `Mathlib.Topology.Constructions`

### `VanKampen.lean`

- `Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected`
- `Mathlib.Topology.Sets.Opens`
- `Mathlib.Topology.Subpath`
- `Mathlib.Topology.UnitInterval`

### `WeakLength.lean`

- `DifferentialGeometry.Geometry.Metric.DistanceScaling`
- `DifferentialGeometry.Analysis.Integration.Measure.Invariance`
- `Mathlib.Topology.EMetricSpace.BoundedVariation`

## 原文引用清单

保留全部 `ref`/`eqref` 名称以供审阅。内部复用、外部输入和后续用途必须按原证明区分；机械出现一个 ref 不构成证明依赖。

`ch:rfs-disk-width`, `cor:svk-sphere-sides`, `def:rfs-child-parent`, `def:rfs-comparison-background`, `def:rfs-geometric-cutoff-record`, `def:rfs-positive-homotopy-class`, `def:rfs-whole-parent-map`, `def:ssc-static-cap-witness`, `lem:rfs-actual-descendants`, `lem:rfs-cap-component-bijection`, `lem:rfs-collapse-degree`, `lem:rfs-composed-family-regularization`, `lem:rfs-exterior-branches`, `lem:rfs-local-to-global-length`, `lem:rfs-weak-length`, `lem:svk-simply-connected-sphere-separates`, `prop:rfs-capped-simply-connected`, `prop:rfs-degree-class-transport`, `prop:rfs-free-loop-class`, `prop:rfs-homotopy-groups`, `prop:rfs-regular-class-correspondence`, `thm:rfs-child-comparison`, `thm:rfs-width-lipschitz`

## 验证和候选状态

- `LinearOrientation.lean`：独立 focused check 和具名 lint/artifact build 通过；未单独审计、注册或提交。
- `ChartOrientation.lean`：最后修订仅写入源码；FIRST 的 11 个错误日志与最后修订分别保存，不能称复检通过。
- `AncestryRestrictionCandidate.pending.txt`：保留精确 HEq 传递诊断，未验证；原公开 record/theorem 未改。
- `PendingProofSources/`：旧试稿，不属于正式源或本轮验收。
- 原 Homology 源 SHA 与历史完整审计 checkpoint 一致，四项直接债不变。本包没有启动新的 Lean/Lake/REPL 或公理审计。

