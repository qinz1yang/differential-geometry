# Moise 光滑化（拓扑三维流形 → 兼容光滑结构）阶段计划

统一记录本任务的目标、复用审计、证明路线、阶段与验证。其他文档只引用本文件，不另开状态表。
日期均为绝对日期。路径省略 `DifferentialGeometry/` 前缀时指本库源码树。

## 1. 目标与接口

- 数学目标：Hausdorff、第二可数的紧致无边界拓扑三维流形 `M`，在同一 carrier、同一拓扑上存在光滑结构。
  只要存在性；不要求唯一性、Hauptvermutung、完整 Pachner 定理，也不重做 Ricci flow。
- 书中消费者接口（`master05a.tex` `thm:moise-smoothability`，节点 `PC-DI-SMOOTHABILITY` / `FND-SMOOTHABILITY`）：

  ```lean
  theorem ... [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [CompactSpace M] :
      ∃ s : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M, letI := s; IsManifold (𝓡 3) ∞ M
  ```

  `TopologicalSpace M` 固定不变，只对 `ChartedSpace` 存在量化。唯一消费者是拓扑版 Poincaré 装配
  (`thm:pc-topological-assembly`)，它只需要紧致情形。截至 2026-09-11 库中还没有该接口的 Lean 消费者声明。
- 初始假设只允许拓扑流形条件（`ChartedSpace ℝ³ M` 只提供拓扑图卡；不得要求给定图卡已是 PL/光滑）。

## 2. 基线与工作区（2026-09-11）

- 共享检出 `E:\differential-geometry-dev`，按负责人指示 `main` 已重置到 `origin/main@806b541e9`
  （旧本地 `main@9cdb3d0cc` 保存在分支 `backup/main-local-20260911`，204 个未跟踪文件另存
  `E:\dg-local-backup-20260911` 并原地保留）。本任务分支：`codex/moise-smoothing`（自 806b541e9）。
- 工具链 Lean/Mathlib `v4.33.1`。完整 `lake build DifferentialGeometry` 在该检出运行
  （`LEAN_NUM_THREADS=2`，日志 `.lake/build-main.log`，内存看门狗）；孤儿构件已清理，
  缺失构件以只读方式从 `D:\differential-geometry-candidate` 的暂停构建播种。
- 当前 `AGENTS.md`（Codex 版）是工作流权威：非 vendored Lean 源零注释、零 docstring；
  按模块名构建；新叶子登记到 `DifferentialGeometry.lean`；重要端点做 `#print axioms`。

## 3. 复用清单（源码审计快照，未重新构建外部项目）

| 来源 / 提交 | 实际声明 | 假设 | 结论 | 额外公理 / sorry | 维数 | 适配成本 / 结论 |
|---|---|---|---|---|---|---|
| Mathlib v4.33.1 | `ChartedSpace`, `StructureGroupoid`, `Pregroupoid`, `Pregroupoid.groupoid`, `HasGroupoid`, `ClosedUnderRestriction`, `Opens.instChartedSpace/instHasGroupoid`, `Homeomorph.chartedSpace`, `StructureGroupoid.LocalInvariantProp` | 任意模型空间 | 图卡/群胚框架 | 无 | 任意 | 直接使用：PL 结构 = `HasGroupoid M (plGroupoid n)` |
| Mathlib v4.33.1 | `Geometry.SimplicialComplex 𝕜 E`, `PreAbstractSimplicialComplex`, `AbstractSimplicialComplex` | 向量空间中的几何复形 | 面、`space`、交面条件 | 无 | 任意 | 后续三角剖分层使用；不另造平行体系 |
| Mathlib v4.33.1 | `metrizableSpace_of_t3_secondCountable`, `ChartedSpace.secondCountable_of_sigmaCompact`, `ChartedSpace.locallyCompactSpace`, `Metric.infDist`/`continuous_infDist_pt`, `IsClosed.notMem_iff_infDist_pos`, `Continuous.homeoOfEquivCompactToT2`, `AffineMap.continuous_of_finiteDimensional` | — | 点集/度量工具 | 无 | — | Phase 1 直接使用 |
| 本库 `Topology/Manifold/HomeomorphAtlas.lean` | `exists_smoothAtlas_of_homeomorph (h : M ≃ₜ N)` | `M` 无边界光滑流形 | `∃ C : ChartedSpace E N, IsManifold 𝓘(ℝ,E) ∞ N ∧ ∃ d : Diffeomorph ..., d = h` | 标准 | 任意 | 路线第 3 步“沿同胚运输光滑结构”已有生产者 |
| 本库 `Topology/Manifold/Homeomorph/Transport.lean` | `pullbackChartedSpace`, `instHasGroupoidPullback (h : X ≃ₜ M) (G)` | `HasGroupoid M G` | `HasGroupoid X G` | 标准 | 任意 | 任意群胚结构沿同胚拉回；PL 结构运输可直接复用 |
| 本库 `Topology/Manifold/SmoothOpenCover.lean`, `Atlas.lean` | `exists_smoothAtlas_of_openCover`, `isManifold_of_contMDiffOn` | 光滑相容开覆盖 | `ChartedSpace` + `IsManifold` | 标准 | 任意 | 光滑侧装配模板 |
| 本库 `Topology/SimplicialComplex/*` | `geometricRealizationHomeomorphism`（有限 `Geometry.SimplicialComplex ℝ E`）、`geometricLink`、`faceEulerChar`、`GeometricManifoldLinks` 等 | 有限几何复形 | 实现同胚、link、Euler 数 | 未审计 | 任意 | 三角剖分层可复用；不重造 |
| 本库 `Topology/Homology/*`, `Topology/SphereSeparation/*` | 局部同调、Jordan–Brouwer、Alexander 对偶、`isOpen_range_of_isImmersion`（光滑） | — | — | 未审计 | — | 拓扑不变域定理**尚无原生声明**；若后续需要可由此推出 |
| 本库 `External/Schoenflies/`（alonamaloh/schoenflies-lean@05a43d2） | 平面 Jordan–Schoenflies | 平面 | 平面 | 见其 README | 2 | 仅平面；对三维 Moise 只在 2D 模型章节有用 |
| 本库 `Topology/ThreeManifold/SmoothSchoenflies.lean`（分支 `origin/codex/smooth-schoenflies-three`，有负责人） | `smooth_schoenflies_three (e : S² → ℝ³) (he : IsSmoothEmbedding ...) : ∃ Φ : ℝ³ ≃ₘ ℝ³, Φ '' S² = range e` | **光滑**嵌入 | 光滑 Schoenflies | 直接 `sorry` | 3 | 与 Moise 需要的 **PL** Schoenflies（Alexander，Moise GTM47 §17：PL 2-球面界定 PL 3-胞腔）是不同定理；互不推出（需 PL/光滑比较）。不重复其证明；本路线不依赖它。书中 `FND-SCHOENFLIES` 卡片允许该负责人反过来经 PL 链得到光滑版 |
| mccorvie/classification-of-surfaces@e3c7230 (Lean 4.32.0, Apache-2.0) | `moise_triangulation : Nonempty (GeometricTriangulation S)`，`moise_triangulation_explicit`；链 `Moise.moise_triangulation_of_boundaries`→`ChartInduction.lean`(5815 行) | `[T2Space S] [ConnectedSpace S] [CompactSpace S] [ChartedSpace (EuclideanHalfSpace 2) S] [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]` | 有限顶点集、三顶点面族、重心实现 `GeometricRealization V F ≃ₜ S` | 源码无 `sorry`（`JordanCurve/Main.lean` 的匹配只是 docstring 文字）；未本机审计公理 | 2 | 其 PL 机器类型为平面专用（`Plane`, `TriangleMesh`, `PlaneComplex`, `FinitePLHomeomorphOn`, 直线公共细分, `PolygonalSchoenflies`）；维数无关部分只有重心实现 `GeometricRealization V F ⊆ (V → ℝ)` 与重标号，且与本库 `Geometry.SimplicialComplex` 实现重叠。**不能改 2 为 3**；其 2D 图卡归纳是 Moise GTM47 §8 的实现，对应本路线的“拼接桥”在 2D 的实例。其 `Topology/InvarianceOfDomain.lean`（813 行，`invariance_of_domain_open_map`，维数无关的解析证明）是 Phase 3 的单文件移植候选；其 `classification_of_surfaces`（拓扑版，依赖 142k 行）不整体移植 |
| not-gary/pachner@df9ad40 (Lean 4.21.0-rc3, Apache-2.0) | `AbstractSimplicialComplex E`（faces : Set (Finset E)），`StellarSubdivision`, `StellarMove/StellarEquiv`, link/star/join/cone，`stellarSubdivision_simplicialIso` 等 | 抽象复形 | 星形细分与 link/join 关系 | 0 `sorry`（14.6k 行） | 任意 | 与 Mathlib `PreAbstractSimplicialComplex` 同构；组合流形定义/细分层（Phase ≥3）可移植；**无**流形三角剖分存在定理，完整 Pachner 定理未完成 |
| deancureton/sphere-six-complex@9bf61f6 (Lean 4.34.0-rc1) | `SmoothManifold.finiteCWModel`, `ManifoldWithCorners.relativeCWComplex` | 已有 C¹ 光滑结构 | 有限 CW 同伦模型 | **`public axiom`** | 任意 | 不可作已证存在定理移植；与目标方向相反（假设光滑） |
| TauCeti Roadmap | — | — | — | — | — | 路线图，非证明 |
| 数学来源 | Moise, *Geometric Topology in Dimensions 2 and 3* (GTM 47)，本机 `D:\数学文档\拓扑\...Moise...pdf`：§5–8（2D 模型；定理 8.4 开集逼近形式）、§17 PL Schoenflies、§23 三角剖分 3-流形、§24–27 覆盖/环定理/Dehn、§30–34 多面体插值与 PLH 逼近、§35 定理 35.2/35.3、§36 定理 36.1；Bing 1959；Shalen 1984；用户 `Moise_Theorem.zip` 的 `main04.tex`（仅章节合同，无证明） | | | | | 本路线以 Moise §35–36（Shalen 式）为 A 的经典来源 |

## 4. 证明路线

记 `ℝⁿ := EuclideanSpace ℝ (Fin n)`。

1. **R1（TOP → PL）**：紧致拓扑 `n`-流形 `X` 的有限图卡覆盖 `U₁,…,U_k`，每个 `Uᵢ` 带由图卡运输的欧氏 PL 结构；
   按 Moise §8/§35 的图卡归纳逐个并入：设 `U` 已有 PL 图册 `A`，`V` 有 `B`，`O = U ∩ V`。
   对 `id_O : (O, A|O) → (O, B|O)` 用**逼近定理 A** 得 PL 同胚 `f : O → O` 且
   `dist (f x) x < ½·infDist x Oᶜ`；把 `f` 用恒同延拓成
   `F : X ≃ₜ X`（边界处连续性由该控制给出，双射由 `f(O) = O` 给出，不需要不变域定理），
   `F(U) = U, F(V) = V`；把 `A` 沿 `F` 运输后与 `B` 在 `O` 上逐图卡 PL 相容，取并得 `U ∪ V` 的 PL 图册。
   有限归纳后得 `∃ C : ChartedSpace ℝⁿ X, HasGroupoid X (plGroupoid n)`。除 A 外维数无关。
2. **R2（PL → DIFF）**：`n = 3` 时每个 PL 3-流形有兼容光滑结构（Moise/Whitehead/Munkres；
   障碍群 `Γ₁ = Γ₂ = 0`）。作为**光滑化接口 B** 显式陈述：同一 carrier、同一拓扑上由 `HasGroupoid X (plGroupoid 3)`
   得 `∃ C' : ChartedSpace ℝ³ X, IsManifold (𝓡 3) ∞ X`。
3. **R3（接入原生接口）**：B 直接给出书中接口形式；若 B 以“光滑模型 + 同胚”形式证明，则用
   `exists_smoothAtlas_of_homeomorph` 或 `pullbackChartedSpace` 运输。

### 4.1 PL 的原生表示

- `IsHPolytope C`：有限个闭仿射半空间之交且有界（紧）；对仿射映射原像、仿射等价像、有限交封闭；
  有限维空间中每点在任一开集内有 H-多面体邻域（坐标立方体）。
- `IsPiecewiseAffineWithinAt f s x`：存在有限个 H-多面体 `Cᵢ ⊆ s`，`⋃ Cᵢ ∈ 𝓝[s] x`，`f` 在每个 `Cᵢ` 上与一个仿射映射相等；
  `IsPiecewiseAffineOn f s := ∀ x ∈ s, IsPiecewiseAffineWithinAt f s x`。用 `𝓝[s] x` 而非 `𝓝 x`，
  使同一定义既适用于开集（此时二者相同）也适用于多面体（Rourke–Sanderson / Moise 意义下的多面体上 PL 映射）。
  与“对某个三角剖分逐单形仿射”等价（胞腔复形的单纯细分定理），需要时另证。
  已证性质：恒同、限制（`inter_of_mem_nhds`/`of_inter_of_mem_nhds`）、局部性、congr、复合
  （用 `Cᵢ ∩ Aᵢ⁻¹(Dⱼ)`，不需公共细分）、集合内连续、同胚的逆（先舍去内部为空的多面体——它们无处稠密——再用仿射等价像）。
- `piecewiseAffineProperty n m` 是 `plGroupoid n`/`plGroupoid m` 的 `StructureGroupoid.LocalInvariantProp`
  （`Manifold.lean`），由此 PL 流形之间的映射 `IsPLWithinAt/IsPLAt/IsPLOn/IsPL n m f` 通过 Mathlib 的
  `ChartedSpace.LiftProp*` 定义，并自动得到图卡无关性（`isPLAt_iff_of_mem_maximalAtlas`）、恒同与图卡为 PL。
- 多面体层（`Polyhedron.lean`）：`IsPLHomeomorphOn f P Q`（`BijOn` + 双向逐块仿射）、`IsPLBall n`/`IsPLSphere n`
  （与标准单形 / 其边界 PL 同胚）、`IsCombinatorialManifold n K`（Moise 定义：顶点 link 是 PL `(n-1)`-球面；
  `n = 0` 时 link 为空）、`PLTriangulation n X`（有限几何复形 + 与 `X` 的 PL 同胚，逐图卡逐块仿射）。
- `plPregroupoid n : Pregroupoid ℝⁿ`，`plGroupoid n := (plPregroupoid n).groupoid`，`ClosedUnderRestriction`。
  PL 流形 = `[ChartedSpace ℝⁿ M] [HasGroupoid M (plGroupoid n)]`；流形间 PL 映射逐图卡定义。
- 开子集上的部分图册 `AtlasOn G U`（`G` 任意结构群胚，`U : Set X`）：图卡为 `OpenPartialHomeomorph X ℝⁿ`，
  source ⊆ U 且覆盖 `U`，两两转移在 `G` 中。运算：限制、沿 `X ≃ₜ X` 运输、相容并、`AtlasOn G univ → ChartedSpace + HasGroupoid`。

### 4.2 显式上游接口（无负责人，本任务自有；下游结果一律报告为条件性）

- **A `PLApproximation n : Prop`**（Moise GTM47 定理 36.1 / Shalen；书中 `thm:boundaryless-approx-main04` 无相对项版本）：
  对 T2 第二可数空间 `X₁`、带度量的第二可数空间 `X₂`、开集 `O₁ O₂`、其上的 PL 图册 `A B`、同胚 `h : O₁ → O₂`
  （`OpenPartialHomeomorph X₁ X₂`，source/target 恰为 `O₁ O₂`）以及在 `O₁` 上连续且为正的控制函数 `φ : X₁ → ℝ`，
  存在同胚 `f : O₁ → O₂`，`∀ x ∈ O₁, dist (f x) (h x) < φ x`，且对 `A` 的每个图卡 `e`、`B` 的每个图卡 `e'`，
  `e.symm ≫ₕ f ≫ₕ e' ∈ plGroupoid n`（即 `f` 及其逆逐图卡分段仿射，也就是 Moise 的 PLH）。
  这正是 Moise 36.1 的 φ-逼近形式（Moise 的“强正函数”被连续正函数取代，二者在此等价：连续正函数强正；
  强正函数在局部紧可分空间上有连续正下界）。目标空间的度量任意，与 Moise 一致。该命题在 `n ≤ 3` 为真
  （`n = 2` 即 Moise 定理 8.4，`n = 3` 即定理 36.1），`n ≥ 4` 为假；因此条件定理不隐藏目标。
  拼接桥只用 `X₁ = X₂ = X`、`h = id_O`、`φ x = ½·infDist x Oᶜ` 的特例。
  流形语言的同一陈述 **A′ `PLApproximationManifold n`**（`Manifold.lean`：PL `n`-流形 `M₁ M₂`、同胚 `h`、
  连续正 `φ`，存在同胚 `f` 满足 `IsPL n n f` 并 φ-逼近 `h`；逆映射自动 PL：`isPL_symm_of_homeomorph`）
  是未来经典证明的自然目标；
  `A′ → A` 的归约已证：`plApproximation_of_plApproximationManifold`（`ApproximationManifold.lean`；
  `AtlasOn.subtypeChartedSpace` 把开集上的图册变成子类型上的图卡空间并继承群胚，
  `OpenPartialHomeomorph` 与子类型同胚互换，再用 `isPLAt_iff_of_mem_maximalAtlas` 转回逐图卡群胚条件）。
  因此未来只需在流形语言中证明 A′（`n = 3`）。
- **B `PLSmoothing n : Prop`**：同一 carrier/拓扑上 `HasGroupoid X (plGroupoid n) → ∃ C', IsManifold (𝓡 n) ∞ X`。
  `n ≤ 7` 为真（`n = 3` 经典），`n = 8` 为假。更弱的 **B′ `PLSmoothingModel n`**（只要求存在与 `X` 同胚的光滑模型）
  已证蕴含 B（`plSmoothing_of_plSmoothingModel`，用本库 `pullbackChartedSpace`），所以 Phase 2 只需证 B′。
- **T1 `CombinatorialManifoldPLStructure n`**：有限组合 `n`-流形 `K` 的实现 `K.space` 有 PL 图册，且图卡与 `K` 的线性结构
  逐块仿射相容。**T2 `PLManifoldTriangulation n`**：紧致 PL `n`-流形有 `PLTriangulation`，其复形是组合流形。
  两者是 A、B 的经典证明与图册模型之间的桥（Moise §7 定理 5–6、§23；Rourke–Sanderson 第 3 章）。
- 两者都以 `Prop` 定义 + 显式假设出现在定理签名中，**不引入 `sorry`/`axiom`**；条件定理不使用经典定理名
  （NAMING.md §3：不得靠命题假设获得经典名）。

## 5. 阶段

### Phase 1（进行中，2026-09-11 起）：PL 基础 + 图卡拼接桥 + 条件性端点

文件（新目录 `Topology/PiecewiseLinear/`，均登记到根聚合）：

1. `Polytope.lean` — `IsHPolytope` 及其封闭性、立方体邻域。
2. `PiecewiseAffine.lean` — `IsPiecewiseAffineOn`：id、congr、限制、局部性、复合、连续性、同胚之逆。
3. `Groupoid.lean` — `plPregroupoid`, `plGroupoid`, `ClosedUnderRestriction`，模型空间 `HasGroupoid`。
4. `Topology/Manifold/PartialAtlas.lean` — `AtlasOn G U` 与运算（群胚通用）。
5. `Approximation.lean` — `PLApproximation n` 的定义。
6. `ChartGluing.lean` — 两集合拼接桥（度量控制 → 全局同胚 `F` → 运输 + 并），有限图卡归纳：
   `PLApproximation n → ∀ 紧致 T2 [ChartedSpace ℝⁿ X], ∃ C, HasGroupoid X (plGroupoid n)`。
7. `Smoothing.lean` — `PLSmoothing n` 定义；端点
   `PLApproximation n → PLSmoothing n → ∃ C : ChartedSpace ℝⁿ X, IsManifold (𝓡 n) ∞ X`，
   并给出 `n = 3` 的书中接口形式。

8. `Manifold.lean` — PL 群胚的局部不变性质与 PL 流形间映射 `IsPL* n m`。
9. `Polyhedron.lean` — PL 同胚、PL 球/球面、组合流形、`PLTriangulation`，以及桥接口 T1、T2 的陈述。
10. `ApproximationManifold.lean` — 开集图册的子类型图卡空间；`plApproximation_of_plApproximationManifold`。

验收：每个模块按模块名构建通过、零警告；端点 `#print axioms` 只含标准公理；条件性由签名显式表达。
已证生产者：1–4、6 的桥与归纳、7 的装配。条件性消费者：6、7 的端点（依赖 A、B）。

### Phase 2（候选，待 Phase 1 验收后定）：B′ `PLSmoothingModel 3`（蕴含 B）

路线：PL 3-流形的柄分解（来自三角剖分的二次导出细分）+ 本库光滑柄粘接
（`Topology/Handle/*`, `Topology/Morse/Attachment/*`）；0/1-柄直接光滑，2-柄需光滑曲面中 PL 圆周的光滑化与框架，
3-柄需“同胚于 S² 的光滑闭曲面微分同胚于 S²”（`Γ₂ = 0` 型 2D 输入）。这些 2D 输入是 B 的真实数学成本，须先审计
本库 `Topology/Manifold/Sphere*`、`ClosedBall`、`Morse` 现有生产者。B 也需要 Phase 3 的“PL 图册 ⇔ 组合三角剖分”桥。

### Phase 3：A′ `PLApproximationManifold 3` 的经典链（Moise §17, §21–28, §30–36）

具体计划（分章定理清单、拟定 Lean 陈述、车道、验收）在 `PHASE3_APPROXIMATION_PLAN.md`（2026-09-12 起草，
通读 Moise §2–5、§7–8、§17、§21–28、§30–36 后写成）。要点：

- 终点只有一条定理 `plApproximationManifold_three : PLApproximationManifold.{u} 3`；A′ → A → 拼接桥 → 图册已证，
  Phase 3 结束时补两条无条件推论 `plApproximation_three`、`exists_chartedSpace_hasGroupoid_plGroupoid_three` 并做公理审计。
- A′ 是 Moise 36.1 取 `U = M₁` 的情形，必须覆盖非紧致 `M₁`；推导顺序 35.1 → 35.2 → 36.1（穷竭 + 不变域）。
- 六条车道：F 基础（多面体/细分/公共细分/PL 映射单纯化/link 唯一性/正则邻域/一般位置/穷竭/T1、T2）、
  H 同调与曲面（§21–22、23.14–19、28.11）、S Schoenflies（2D 输入 3.3/3.6/5.3/5.4/10.8 → §17 → 23.9–11）、
  C 覆盖/环定理/环带/实心环面（§24–28 关键子集；27.5 Dehn 引理与 28.5, 28.12–18 不在关键路径）、
  I 插值与逼近（§30–34）、E 终局（不变域移植、§35–36、端点）。
- 规模重估：约 200k–330k 行（早先 110k–210k 的估计在通读 §24–35 之前给出）；4 车道并行约 6–9 个月。
- 拓扑不变域定理按 classification-of-surfaces 的 `Topology/InvarianceOfDomain.lean`（813 行，维数无关）单文件移植。
- 与光滑 Schoenflies 负责人的接口见该文件 §7：本链自证 PL 版（§17），其证明确实依赖平面多边形 Schoenflies（3.6）；
  不消费光滑版；光滑版若要经 PL 版导出需 Phase 2 级别的 PL/光滑比较。

## 6. 验证记录

- 2026-09-12（Phase 3 车道 F 首轮，工作树 `D:\differential-geometry-moise-plan`，分支 `codex/moise-smoothing`）：新增五个模块
  `Polyhedra.lean`（`IsPolyhedron`、单形是 H-多面体、有限复形的底空间是多面体）、`Barycentric.lean`（重心权唯一性、
  `openSimplex`、载体面、面的极端性、复形中开面不交、`weights` 及其仿射性）、`Subdivision.lean`（`IsSubdivision`，
  粗复形的单形是所含细单形之并）、`Derived.lean`（旗、任意内点的导出细分 `derived` 是 `Geometry.SimplicialComplex`，
  `barycentricSubdivision`，`IsSubdivision`）、`Mesh.lean`（重心细分网格 ≤ N/(N+1)，迭代得任意细的细分
  `exists_isSubdivision_diam_lt`）。每个模块用 Phase 1 配方在共享检出的构件上逐模块检查（`lean` 直接调用，
  LEAN_PATH 取共享检出的包与构建库，新 olean 写入共享构建库，脚本 `check-f.ps1`），零错误零警告；
  十个端点（含 `derived_isSubdivision`、`barycentricSubdivision_isSubdivision`、`exists_isSubdivision_diam_lt`）
  `#print axioms` 只含标准公理。未登记根聚合（整合仍按负责人指示推迟）。
  同日第二批：`Star.lean`（有限复形中闭星是底空间内的邻域 `closedStar_mem_nhdsWithin`；逐单形仿射的映射分段仿射
  `isPiecewiseAffineOn_space_of_forall_face`；仿射无关集上的赋值延拓为仿射映射）、`SimplicialMap.lean`
  （载体面 `carrierFace`、顶点映射的单纯延拓 `simplicialMap`、单纯同构给出 PL 同胚 `isPLHomeomorphOn_simplicialMap`）、
  `RegularNeighborhood.lean`（`regularNeighborhoodIn`、二次重心细分 `secondDerived`、`regularNeighborhood K A`
  及其邻域性质 `regularNeighborhood_mem_nhdsWithin`）、`SimplexBall.lean`（仿射无关有限集的凸包是 PL 球
  `isPLBall_convexHull_of_affineIndependent`）。同样逐模块检查零错误零警告，十七个端点公理审计只含标准公理。
  推送至 `origin/codex/moise-smoothing`。
- 2026-09-12（车道 F 第三批，胞腔复形）：`Arrangement.lean`（有限族仿射泛函的符号向量胞腔：开/闭胞腔、符号序 `SignLE`、
  吸收引理 `combo_mem_openCell`、边界点的严格坐标、闭胞腔闭且凸、沿开胞腔点的线段延伸、射线出口点存在
  `exists_exit_of_mem_openCell` 与唯一 `exit_unique`）、`CellComplex.lean`（紧致"胞腔闭"集 `P` 的胞腔族、
  胞腔旗、`cellDerived l P` 是 `Geometry.SimplicialComplex`（仿射无关性由顶胞腔的严格坐标给出；交集公理由
  "过一点的旗唯一"给出，其顶系数由射线出口点唯一性决定）；`space_cellDerived`；胞腔闭子集是单形之并）、
  `Triangulation.lean`（任意有限族 H-多面体被同一个复形三角剖分且各为子复形之并
  `exists_simplicialComplex_of_forall_isHPolytope`；F1.2 `IsPolyhedron.exists_simplicialComplex`；
  F2.3 `exists_isSubdivision_subcomplexes`；公共细分 `exists_common_subdivision`）、
  `PiecewiseAffineSimplicial.lean`（F3.1 正命题：有限复形上的分片仿射映射在某细分的每个单形上仿射
  `IsPiecewiseAffineOn.exists_isSubdivision_affineOn_faces`）。逐模块检查零错误零警告；
  `#print axioms` 仅 `propext`、`Classical.choice`、`Quot.sound`。

- 2026-09-13（车道 F 第四批，link 唯一性 F3.3）：`PLHomeomorph.lean`（PL 同胚复合/逆/转移）、`Cone.lean`（径向投影、锥底、
  顶点 link 的径向单射性）、`SimplicialImage.lean`（单纯映射像复形）、`RadialProjection.lean`（伪径向投影是 PL 同胚
  `exists_isPLHomeomorphOn_of_radial`）、`LinkSubdivision.lean`（顶点 link 在细分下 PL 不变）、`SimplexBoundary.lean`
  （单形边界复形、`isPLSphere_biUnion_erase`、任意小单形邻域）、`LinkEuclidean.lean`
  （`isPLSphere_geometricLink_of_mem_nhds`：`finrank E = n+1` 且 `K.space ∈ 𝓝 p` ⟹ 顶点 link 是 PL `n`-球面）。
  逐模块检查零错误零警告；九个端点 `#print axioms` 仅标准公理（`.lake/scratch/AuditF5.lean`）。

- 2026-09-13（车道 F 第五批，锥与锥延拓 F3.4）：`ConeComplex.lean`（锥复形 `coneComplex`、`closedStar_eq_coneComplex_space`）、
  `ConeBase.lean`（`affineIndependent_insert_iff`、锥底在细分下稳定、`isConeBase_simplexBoundary`）、`ConeExtension.lean`
  （`exists_isPLHomeomorphOn_coneComplex`：锥底间 PL 同胚的锥延拓，保射线）、`StdSimplexCone.lean`
  （标准单形是中心对边界的锥；`IsConeBase.isPLBall_of_isPLSphere`、`isPLBall_closedStar`、
  `IsCombinatorialManifold.isPLBall_closedStar`）。逐模块检查零错误零警告；七个端点 `#print axioms` 仅标准公理
  （`.lake/scratch/AuditF6.lean`）。

- 2026-09-13（车道 F 第六批，T1 组合流形的 PL 图册）：`OpenStar.lean`（顶点开星、锥描述、相对开性、
  星同胚 `exists_starHomeo`）、`StdChart.lean`（标准单形开单形与 `EuclideanSpace ℝ (Fin (n+1))` 中开集
  `stdTarget` 之间的仿射投影/提升）、`VertexChart.lean`（顶点图卡 `vertexChart`、图册 `combinatorialChartedSpace`、
  `HasGroupoid _ (plGroupoid (n+1))`、图卡与逆图卡在环境坐标下分片仿射；`combinatorialManifoldPLStructure_succ`）、
  `CombinatorialZero.lean`（`n = 0`；`combinatorialManifoldPLStructure : ∀ n, CombinatorialManifoldPLStructure n`）。
  逐模块检查零错误零警告；`#print axioms` 仅标准公理（`.lake/scratch/AuditF7.lean`、`AuditF8.lean`）。
  这样 Phase 1 的 T1、T2 接口都已由 Phase 3 车道 F 证明：`combinatorialManifoldPLStructure : ∀ n, CombinatorialManifoldPLStructure n` 与 `plManifoldTriangulation : ∀ n, PLManifoldTriangulation n`（`Gluing`/`ChartPiece`/`Subcomplex`/`SubdivisionTransport`/`ChartGlue`/`TriangulationExistence`/`StarComplex`/`Combinatorial`，2026-09-13）；`PLManifoldTriangulation n` 增加了 `[Nonempty X]`（空流形没有 `PLTriangulation`，因 `map : ℝ^N → X`）。

- 2026-09-11（Phase 1 第二轮，负责人指示不等完整构建）：`IsPiecewiseAffineOn` 改为基于 `IsPiecewiseAffineWithinAt`
  （`𝓝[s] x`）的定义并重跑整条链；新增 `Manifold.lean`、`Polyhedron.lean`，以及 `Smoothing.lean` 中的
  `PLSmoothingModel`/`plSmoothing_of_plSmoothingModel`。九个模块逐个 `lake env lean` 加 lakefile 选项检查零错误零警告；
  端点与主要引理（含 `plSmoothing_of_plSmoothingModel`、`piecewiseAffineProperty_localInvariantProp`、`isPL_id`、
  `isPLAt_iff_of_mem_maximalAtlas`、`isPLBall_stdSimplex`）`#print axioms` 均只含标准公理。
- 2026-09-11（深夜）：`ApproximationManifold.lean` 通过检查；`plApproximation_of_plApproximationManifold`
  与 `AtlasOn.subtypeChartedSpace_hasGroupoid`、`AtlasOn.subtypeRestr_mem_maximalAtlas` 公理审计只含标准公理。

- 2026-09-11：源码审计与路线固定。
- 2026-09-11（Phase 1 首轮）：以下七个模块在本检出用 `lake env lean` 加 lakefile 选项
  （`autoImplicit=false`、`weak.linter.mathlibStandardSet=true` 等）逐个检查，零错误零警告；
  完整根构建仍在进行，故尚未登记到 `DifferentialGeometry.lean`（构建结束后登记并做增量根构建）。
  - `Topology.PiecewiseLinear.Polytope`：`IsHPolytope` 及 `inter`、`inter_preimage`、`image_affineEquiv`、
    `exists_isHPolytope_subset_mem_nhds`。
  - `Topology.PiecewiseLinear.PiecewiseAffine`：`IsPiecewiseAffineOn`；`isPiecewiseAffineOn_of_affine`、`_id`、
    `_of_locally`、`.mono`、`.congr`、`.continuousAt`、`.comp`、`.symm`（PL 同胚之逆）；辅助
    `linear_injective_of_injOn_of_interior_nonempty`、`iUnion_interior_nonempty_mem_nhds`。
  - `Topology.PiecewiseLinear.Groupoid`：`plPregroupoid`、`plGroupoid`、`mem_plGroupoid_iff`、
    `mem_plGroupoid_of_isPiecewiseAffineOn`、`ofSet_mem_plGroupoid`、`ClosedUnderRestriction (plGroupoid n)`。
  - `Topology.Manifold.PartialAtlas`：`AtlasOn G U` 及 `congr`、`empty`、`ofOpenPartialHomeomorph`、`restrict`、
    `transport`、`union`、`chartedSpace`、`hasGroupoid`、`ofChartedSpace`；`ofSet_mem_of_closedUnderRestriction`。
  - `Topology.PiecewiseLinear.Approximation`：接口 `PLApproximation n`（§4.2 的 A）；健全性定理
    `plApproximation_zero : PLApproximation 0`（0 维时接口可满足，说明接口不是矛盾或空洞的；用到
    `IsHPolytope.univ_of_subsingleton`、`isPiecewiseAffineOn_of_subsingleton`）。
  - `Topology.PiecewiseLinear.ChartGluing`：两集合拼接桥 `exists_atlasOn_union_of_plApproximation`
    （度量空间版）与 `_of_metrizable`；有限图卡归纳 `exists_atlasOn_univ_of_plApproximation`；
    `exists_chartedSpace_hasGroupoid_plGroupoid_of_plApproximation`（条件性 Moise 三角剖分：`∃ C, HasGroupoid X (plGroupoid n)`）。
  - `Topology.PiecewiseLinear.Smoothing`：接口 `PLSmoothing n`（B）；端点
    `exists_isManifold_of_plApproximation_of_plSmoothing` 与 `n = 3` 的书中接口形式
    `exists_isManifold_three_of_plApproximation_of_plSmoothing`；健全性 `plSmoothing_zero : PLSmoothing 0`，
    以及由两个 0 维接口实例装配出的**无条件**端点 `exists_isManifold_zero`
    （紧致 T2 的 0 维拓扑流形有同拓扑光滑结构），验证桥 + 归纳 + 装配链在给定接口时确实合成为真定理。
  - `#print axioms`（临时审计文件 import `Smoothing`）：以上端点及 `IsPiecewiseAffineOn.symm/comp`、
    `AtlasOn.hasGroupoid/restrict`、`exists_isHPolytope_subset_mem_nhds` 均只依赖 `propext`、`Classical.choice`、`Quot.sound`。
    条件性完全由签名中的 `PLApproximation`/`PLSmoothing` 假设表达，树中没有新增 `sorry`/`axiom`。

- 2026-09-14（车道 E.0，不变域，工作树 `D:/differential-geometry-moise-e0`，分支 `codex/moise-e0`）：
  四砖已闭合：`Topology/InvarianceOfDomain.lean`（上游解析证明与图卡接口，保留抽象条件签名）；
  `Topology/FixedPoint/NoRetraction.lean`（任意正有限维无收缩，一维连通性，高维球面顶维同调）；
  `Topology/FixedPoint/Brouwer.lean`（任意有限维闭单位球不动点定理及已证实例，含零维）；
  `Topology/InvarianceOfDomainManifold.lean`（七个无未证类参数的最终接口）。
  主端点为 `invariance_of_domain_isOpen_image`、`isOpen_image_of_continuousOn_injOn`、
  `isOpenMap_of_continuous_injective`；另有
  `isOpen_range_of_isOpen_of_continuous_injective_real`、`isOpen_range_of_isOpen_of_isEmbedding_real`、
  `isInteriorPoint_iff_any_chart_real`、`isBoundaryPoint_iff_any_chart_real`。
  模型空间 `E : Type*`、流形宇宙独立，且审计文件显式检查了 `EuclideanSpace ℝ (Fin n)` 的要求形式。
  每砖仅经交接脚本 `check-f.ps1` 串行检查（均 exit=0、零错误零警告），
  `AuditE01`/`AuditE02`/`AuditE03`/`AuditE0`（本车道 `.lake/scratch`）审计只含允许的标准公理；
  七个最终接口、无收缩定理、不动点定理及其实例均只含 `propext`、`Classical.choice`、`Quot.sound`。
  检查点 `8a113f636`、`87d67526b`、`5025cc6f0`、`7723c30c3` 已逐砖推送。
  与交接路线的实现差异：直接复用 `integralSingularHomology_subsingleton_of_contractible`，省去约化同调桥；
  流形证明用一个源图卡与已有模型到流形开像定理；追加四个显式无条件的实模型接口。
  原生移植来源为 mccorvie/classification-of-surfaces@e3c7230，原版权/作者声明、Apache-2.0 全文和修改记录
  保存在 `docs/third_party/`。无新增证明债、注释、诊断命令或资源选项。
  最终同步已抓取并纳入 F 分支 `6b67ac39f`；为同时保留逐砖发布历史与禁止 force-push 的约束，采用
  `5770071c3` 将 F 更新合入 E.0。普通 rebase 会重写已发布的四个检查点，其本地结果未发布，已恢复到
  内容相同且保留双方历史的合并节点。未修改 F 工作树或分支，未合并 E.0 到 F，未运行 `lake build`，
  未登记根聚合；E.0 数学端点完成，S.1、M.3、E.3/E.4 自身义务继续由各自车道承担。

- 2026-09-14（S 车道前半，`D:/differential-geometry-moise-s`，`codex/moise-s`）：
  - S0.1：`a940dc7e4` vendoring `ClassificationOfSurfaces` 的 16 个平面 PL 模块，来源固定为
    `e3c7230fe78d7b056a415d9ecae6f77887046b32`，Apache-2.0；保留注释、版权头、命名空间和原始文档。
    每处 import/API 漂移与 13 条获准保留的原始纯风格警告均记录于 `External/ClassificationOfSurfaces/VENDOR.md`。
    按依赖序逐模块检查 exit=0，AuditS1 仅标准三公理。
  - S0.2/P.1：`81b0310b5` 的 `PlanarSchoenflies.lean` 与 `SimplexFrontier.lean` 证明
    原生 PL 1-球面与 `PolygonalCircle` 的双向转换，以及 `isPLBall_of_isPLSphere_one` 的有界 PL 2-球填充。
    `72fb0bbd3` 补齐完整 3.7：`exists_isPLHomeomorphOn_straighten` / `_of_isPLSphere_one` 给全平面
    双向 PL 的相对整直，固定指定开集外；原 `_on_closedRegion` 签名保留为推论。AuditS10 十项仅标准三公理。
    自由三角形移动及剥离归纳的出处和修改记录已补入 VENDOR。
    P.3 已有三角剖分多边形盘的两个几何自由三角形，P.5 已有多边形 θ-图区域分解；一般相对胞腔删除、
    任意弧 4.4 和 Problem 4.1 未闭合。第二批只提供 6.2–6.3 的嵌入逼近，未覆盖 P.4 的 10.8，故没有导入。
  - S.1：`a04d993c4` 整合 E3 的 frontier/边界点球邻域证明，适配 F 的规范边界不变性，
    `PolyhedralBoundary.lean` 与 `FrontierBoundary.lean` 提供所有正维欧氏形式和流形形式。
    AuditS3 含显式 ℝ³ 签名，六项均仅标准三公理；没有把重用 E3 的代码报告为独立新证明。
  - P.2：`ff7fc67ca` 的 `BallFrontier.lean` 证明实际 frontier 上的 PL 球边界延拓，
    `n = 1` 给平面 2-球形式，并证明 PL 球 frontier 的球面性；AuditS6 四项仅标准三公理。
  - S.2 **partial**：`8a6995d74` 的 `PushProperty.lean` 证明 17.7；`b29c69f17` 的
    `AmbientExtension.lean` / `ConeIsotopy.lean` 给相对多面体邻域中的顶点移动及锥顶连续路径移动；
    `8c4d4fe91` 的 `SimplexBoundaryImage.lean` / `SimplexPush.lean` 闭合 17.4 的任意四面体面推送。
    核对并修正计划原先的邻域写法：使用 `C \ J`，不取闭包，J 是盘的内在边界圈而非环境 frontier D。
    `e3686847e` 增加固定 frontier 的恒等延拓、交集保持的 PL 拼接及两侧锥环境延拓，
    三个新声明连同全平面相对定理通过 AuditS11。17.5 尚缺四面体边界星的锥交集、frontier、
    支撑控制几何条件和保留指定三角形的删除归纳；17.6、17.8 仍依赖它。无占位证明债。
  - 最终 13 个 S 原生模块和 2 个同步的 F 半空间模块逐一复查 exit=0、零警告；
    AuditS12 在同一环境中审计 60 个不同声明，全部仅标准三公理、exit=0。
    日志为 `.lake/scratch/final2-*.log` 和 `audit-final2-s.log`。未运行 lake build，未登记根聚合。
    最终同步 F 至 `b66f6b5b0` 时使用普通合并保留已发布检查点，未重写历史或 force-push，
    未将 S 分支合并到其它分支；精确消费状态和 §17.4–17.12 拟定陈述见 `PHASE3_APPROXIMATION_PLAN.md` §4.1–4.2。

- 2026-09-15（S 车道继续，工作树与分支保持不变）：
  - 平面链：`4fffc8f99` 将保留指定三角形接入删除归纳；`91172ea49` 证明 PL 球/球面非空、
    有限剖分的纯维性及同维欧氏 PL 球的内部稠密性，并由此识别任意原生平面 PL 圆盘为多边形闭区域。
    `exists_isPLHomeomorphOn_remove_geometricallyFree_triangle` 给整盘的精确删除像和剩余盘球性。
    `80fceca30` 的 `exists_isPLHomeomorphOn_straighten_to_face` 接受任意原生剖分及任意指定三角形。
  - 17.5 的几何准备：`21401b31b` / `01974cece` 实际构造顶点星的两侧锥并证明交集、frontier 和支撑；
    `afc350cbe` 产生与 D 兼容且闭星足够细的边界剖分，以及星到对面的单纯坐标。
    `aebd603dd` 的 `SimplexAffine` / `SimplexCornerChart` 给真正二维欧氏坐标、实际边界和开星对应；
    环境延拓保持整个四面体，逐点固定对面与给定邻域外，并给任意边界子集的精确图像公式。
  - `80fceca30` 的 `SimplexDisk`：对整个 D 位于一个原始顶点开星内的情形，
    `exists_isPLHomeomorphOn_straighten_to_face_in_simplex_vertex_star` 将 D 整直到任意指定剖分三角形，
    保持四面体并固定对面及邻域外；任意 PL 圆盘的推论自行产生该三角形。
    `8fa61de34` 的 `StarSubdivision` 证明闭星覆盖控制在任意后续细分下保持。
  - 真实剩余义务：跨星圆盘的局部自由三角形删除须控制接缝并证明整个圆盘的删除像，再作保留三角形归纳。
    星内交集未必是盘，上游的整盘删除不能直接用于它。完整 17.5、17.6、17.8 及 S.2 仍为 partial；
    P.3 的一般 17.2/17.3、P.4 的 10.8、P.5 的任意弧版本仍未闭合，第二批仍不触发。
  - 验证：每层原生检查 exit=0、零警告；AuditS13–S21 的端点仅标准三公理。
    `9c9002426` 纳入 F 至 `8c1ce1d4f` 时复查 39 个修改/相关模块、AuditS18 审计 127 项；
    最后抓取并合入 F 至 `d0902b2cd`，保留 S 已完成的 P.1/P.2，整合 F 的横截弧剖分、边界和降阶输入。
    最后复查 12 个模块均 exit=0、零警告；AuditS22 去重审计 198 个声明，仅标准三公理、exit=0；
    日志为 `final3-*.log` 与 `audit-final3-s.log`。
    所有同步均为 S 上的普通合并，未改其它车道源码或重写已发布历史；未运行 lake build，未登记根聚合。
    逐层出处、调整和验证记录位于 `External/ClassificationOfSurfaces/VENDOR.md`，本轮未修改 vendor Lean 源码。

- 2026-09-15（Phase 3 车道 C：Moise §24 C.1–C.3，工作树 `D:\differential-geometry-moise-e3`，分支 `codex/moise-e3`）：
  `CoveringLift.lean` 闭合 24.1–24.4：PL 球的单连通与局部道路连通、覆盖唯一提升、基本群映射单射、闭路提升判据、
  单值作用的稳定子/像子群识别、连通覆盖的纤维基数等于像子群指标；九个端点检查 exit=0、零 warning，AuditC1
  仅 `propext`、`Classical.choice`、`Quot.sound`，源码提交 `2df0546f5`。`DoubleCoverComplex.lean` 从有限复形上的
  `SimplicialBoolCocycle` 构造 `BoolCocycle` 二重覆盖，证明纤维基数为 2，并以连续截面双向识别上边界，得到
  `connectedSpace_iff : ConnectedSpace TotalSpace ↔ ¬ IsCoboundary`；二十三个端点检查 exit=0、零 warning，AuditC2
  仅标准三公理，源码提交 `364fbe752`。`CoveringTriangulation.lean` 对任意有限纤维覆盖逐基单形作唯一提升，以纤维顶点
  的标准基实现有限复形，粘合出 `coveringSpaceHomeomorph`；投影逐单形等于仿射映射并满射到一个基单形，顶点 link 的
  `coveringVertexLink_isGlueIso` 给出任意维 `IsCombinatorialManifoldWithBoundary` 保持，最终端点为
  `exists_lift_simplicialComplex`。十六个端点检查 exit=0、零 warning，AuditC3 仅标准三公理，源码提交 `f7e70bc61`；
  直接逐单形提升比 Moise 24.6 的均匀覆盖细分路线更强，未弱化结论。
  D4 首次复用审计逐条记录如下，全部只依赖标准三公理：AuditC1Reuse 的
  `IsPLHomeomorphOn.homeomorph`、`Convex.contractibleSpace`、`Convex.locallyPathConnectedSpace`、
  `ContinuousMap.HomotopyEquiv.simplyConnectedSpace`、`IsCoveringMap.existsUnique_continuousMap_lifts`、
  `IsCoveringMap.continuous`、`IsCoveringMap.injective_path_homotopic_map`、`FundamentalGroup.map`、
  `FundamentalGroup.map_apply`、`IsCoveringMap.fundamentalGroupMulAction`、`IsCoveringMap.monodromy`、
  `IsCoveringMap.liftPathQuotient`、`IsCoveringMap.map_liftPathQuotient`、`IsCoveringMap.monodromy_eq_of_map_eq`、
  `IsCoveringMap.liftPath`、`IsCoveringMap.liftPath_zero`、`IsCoveringMap.liftPath_lifts`、
  `MulAction.index_stabilizer_of_transitive`；AuditC2Reuse 的 `BoolCocycle.isCoveringMap_proj`、
  `BoolCocycle.toFiberBundleCore`、`BoolCocycle.sectionCoord`、`BoolCocycle.sectionCoord_change`、
  `BoolCocycle.isLocallyConstant_sectionCoord`、`Covering.exists_section_of_not_connected_double_cover`、
  `Covering.not_connected_of_double_cover_section`、`FiberBundle.isClosedMap_projection_of_finite`、
  `Bundle.Trivialization.preimageSingletonHomeomorph`、`FiberBundle.continuousAt_totalSpace`、
  `FiberBundle.mem_trivializationAt_proj_source`；AuditC3Reuse 的 `IsCoveringMap.exists_unique_lift_of_isPLBall`、
  `PiecewiseLinear.IsCoveringMap.exists_unique_lift_of_face`、`Covering.t2Space_of_isCoveringMap`。整条 C.1–C.3 链未 import、
  未传递经过含 `sorry` 的 `Topology/Homology/HurewiczLowDegrees.lean`。同步时保留上游 `BoundaryInvariance.lean` 的五个
  边界/前沿不变性端点并合入 `polyhedralBoundary`，修正剩余旧实例语法后该模块检查 exit=0、零 warning；未运行根构建，
  未登记根聚合。E3.2/E3.3 仍因非紧局部有限表示层缺口搁置，详见 `PHASE3_APPROXIMATION_PLAN.md` 的 F6.3/E.2/E.3/R9。

- 2026-09-15（F 车道，§12.1 的 E.3 条件版检查点）：`Transition361.lean` 明确定义 `Moise352`
  与 `IsPLHomeomorphInto`。逆映射按像中每点的 `IsPLWithinAt` 表述，避免空源、非空目标时总逆函数不存在；
  `isPLHomeomorphInto_iff_exists_inverse` 证明源非空时与原单个总逆映射形式等价。
  `Moise352.exists_approx_of_isOpen` 用 F6.3 对整个开集一次应用 35.2，单独处理空集；
  `IsPLHomeomorphInto.isOpen_image` 从 E.0 推出开像。聚焦检查 exit=0、零 warning，AuditF115
  十个声明均仅 `propext`、`Classical.choice`、`Quot.sound`。完整 36.1 陈述在同一审计文件中通过类型检查；
  像集等式尚待穷竭论证，E.3/E.4 尚未完成，35.2 仍只是显式命题。未运行 lake build，未登记根聚合。

- 2026-09-15（F 车道，砖 15）：`Transition361.lean` 闭合 `exists_plh_approx_of_isOpen`，条件仅为
  显式 `Moise352 3`；一般正维版本为 `Moise352.exists_approx_image_eq_of_isOpen`。F6.3 塔提供紧致穷竭，
  局部有限的阶段前沿与连通分支分别给连续正误差控制；对整个 U 一次应用 35.2 后，紧致路径被穷竭捕获，
  前沿分离推出像集相等。此论证不需要增加阶段连通假设。`IsPLHomeomorphInto.image_polyhedralBoundary`
  从 M.3 和不变域给精确边界像等式；更一般的紧集前沿等式先在拓扑层证明。
  该模块聚焦检查 exit=0、零 warning；AuditF116 审计十五个声明，全部仅标准三公理。
  36.1 已完成条件版；35.2 仍未证，端点砖 16 随后接入。未运行 lake build，未登记根聚合。

- 2026-09-15（F 车道，砖 16）：`Endgame.lean` 的 `plApproximationManifold_three_of_moise352`
  证明 `Moise352.{u} 3 → PLApproximationManifold.{u} 3`。在 U = univ 使用 36.1，像集相等给满射，
  不变域给开映射，由连续双射组装同胚；保留原端点的任意连续正误差与两侧 PL 流形实例。
  `Endgame` 聚焦检查 exit=0、零 warning；AuditF117 连同砖 15 接口共十六项，全部仅
  `propext`、`Classical.choice`、`Quot.sound`。E.3/E.4 均为条件版 done，35.2 本身没有被证明。
  下一项按 §12.2 处理 F5.2 的整体片与载体约束扰动。未运行 lake build，未登记根聚合。

- 2026-09-15（F 车道，F5.2 的 §12.2 路线审查）：`CarrierPerturbation.lean` 证明最小载体约束的刚性。
  顶点的 `carrierFace` 是单点；当原顶点映到目标顶点，任何仍在原载体仿射包内的顶点像都等于原值，
  `simplicialMap_eqOn_of_mem_affineSpan_carrierFace` 给整个单纯映射相等，双点集也精确不变。
  `not_disjoint_doublePointSet_vertices_of_mem_affineSpan_carrierFace` 证明既有顶点双点不能移离目标顶点集。
  六个声明聚焦检查 exit=0、零 warning；AuditF118 连同砖 15/16 共二十二项全部仅标准三公理。
  此结果是 §12.2 固定最小载体路线的障碍证明，不是 F5.2 正规形式的存在证明。按交接约定在数学缺口处汇报，
  F5.2 保持 partial，等待允许跨出低维载体且保持目标片内兼容性的设计；详见交接 §14 和风险 R10。

- 2026-09-15（C 车道，L.1 定义层）：工作树 `D:\differential-geometry-moise-e3`、分支 `codex/moise-e3` 的
  `DerivedNeighborhoodRetraction.lean` 以导出细分的重心坐标质量、矩与投影显式构造子复形导出邻域到子复形的强形变收缩，
  `derivedNeighborhoodFundamentalGroupInclusionEquiv_apply` 识别所得基本群同构为实际包含映射的 `FundamentalGroup.map`。
  `LoopTheorem/SingularCell.lean` 定义 `SingularTwoCell`、自由环的 `FreeLoop.conjugacyClass`、顶点碰撞复杂度与
  `NormalSystem`；`K₁` 为保留像单形的相对导出邻域且载体等于标准导出邻域，`B₁` 为边界中环复形的导出邻域；
  `NormalSystem.complexity_eq_zero_iff_isNonsingular`、`NormalSystem.loopConjugacyClass_eq_of_connector` 与
  `NormalSystem.loopConjugacyClass_disjoint_normal` 分别闭合复杂度零、连接道路无关性与正规子群不交条件。
  两个模块的聚焦检查均 exit=0、零 warning；AuditL1 对 51 项端点及复用声明审计 exit=0，全部公理闭包均包含于
  `propext`、`Classical.choice`、`Quot.sound`。本砖首次复用并逐条审计的拓扑/相对导出声明为
  `exists_basedCircle_free_homotopic`、`basedCircleHomotopyTrack_commutes`、
  `fundamentalGroupChangeBasepoint_connector`、`fundamentalGroupMulEquivOfHomotopyEquiv`、
  `faces_subset_relativeDerivedNeighborhood`、`relativeDerivedNeighborhood_faces_finite`，均仅标准三公理；未经过
  `Topology/Homology/HurewiczLowDegrees.lean`。源码提交 `d81e1897c`；L.1 无未闭合书中步骤，未运行根构建，未登记根聚合。

- 2026-09-15（S 车道 S.3 / P.3 一般 17.2 / S.5 当前交付，数学提交 `08ee37003`）：
  `ConvexStraightening`、`ConeStraightening`、`PlanarDiskGluing` 无条件证明 17.9–17.11，
  保留每个凸开邻域外恒同及盘的内在内部；线性层形式精确匹配 F 的冻结接口。
  `FreeDiskCell` 对任意有限维实赋范空间的共同有限三角剖分证明一般盘分解的两个不同自由胞腔，
  并给避开一个指定胞腔的推论；17.3 的指定真盘子复形版本仍未证。
  `SchoenfliesFoundations.lean` 的 `schoenflies_input` 填满原样保留的
  `SchoenfliesInput` 四字段，无未证输入。S.4 由 F 车道实现。
  `SchoenfliesManifold`（23.9）与 `PushManifold`（23.10）按授权显式接受完整 17.12 的陈述，
  给顶点开星内填充与保持精确相对邻域的推移；该参数仍待 F 的生产者交付后解除。
  `BallGluing` / `BallGluingManifold`（23.11）已无条件完成，包含两球位于不同顶点星的有限组合流形形式。
  最终 9 个端点模块检查 exit=0、零警告；AuditS61 精确核对 F 接口，AuditS62 的 16 个声明仅标准三公理。
  源码散列与日志见 `.lake/scratch/S3-P3-S5-VERIFICATION.json`；各层来源与差异见
  `External/ClassificationOfSurfaces/VENDOR.md`。没有修改 vendored Lean、没有 lake build 或根聚合登记。
  最后文档提交前已 fetch 并 merge `origin/codex/moise-integration`，保留所有已发布检查点。

- 2026-09-15（H 车道 H.2a，任意线性细分与 PL 定向不变性）：
  已通过整合分支取得 F 的 `PLBallSphere.lean` 连通性 API；本次合并的远端端点为 `b9a2cb2ca`，
  H 的合并提交为 `4be28804d`，没有复制、cherry-pick 或直接合并其它车道。
  `AffineOrientation.lean`、`ManifoldConnectivity.lean`、`Orientation.lean` 串行聚焦检查均 exit=0、零警告
  （分别 12.9、10.9、30.8 秒），使用原始 `check-f.ps1` 写入共享库，每次启动前核对主机进程配额。
  正向细分以仿射坐标矩阵行列式的符号传递顶维定向，反向用每个旧顶维单形内的对偶图连通性证明局部比较符号恒定；
  对偶图连通性经顶点 link 的维数归纳取得。由此闭合
  `isOrientable_iff_of_isSubdivision`、`isOrientable_iff_of_isPLHomeomorphOn`、
  `isOrientable_of_isPLBall`、`isOrientable_of_isPLSphere`、`isOrientable_faceStarComplex`、
  `exists_unique_coherentOrientation_comparison_faceStarComplex`，包含零维。
  细分和 PL 不变性保留源复形的组合流形假设；球面接口维数为 `IsPLSphere n → IsOrientable n`。
  “恰两个定向”指统一顶点序后的所有顶维符号相同或互为负号，不是原始 `CoherentOrientation` 结构仅有两个元素。
  `AuditH2aIntegrated` 对 53 项核心声明逐项审计 exit=0；`AuditH2aIntegratedReuse` 对下列 22 项复用声明逐项审计
  exit=0，所有闭包均为 `propext`、`Classical.choice`、`Quot.sound`：
  本库 `Topology.SimplicialComplex.mem_geometricLink_singleton`、`finite_geometricLink_faces`；
  PL 层的 `exists_face_superset_card_eq_of_isPLBall_or_isPLSphere`、`exists_face_superset_card_eq_of_isPLBall`、
  `IsPLBall.nonempty`、`IsPLSphere.nonempty`、`IsPLBall.isCombinatorialManifoldWithBoundary`、
  `IsPLSphere.isCombinatorialManifold`、`IsCombinatorialManifoldWithBoundary.card_le_one`、
  `IsPLBall.isConnected`、`IsPLSphere.isConnected`、`isConnected_stdSimplexBoundary`、
  `faceStarComplex`、`faceStarComplex_faces_finite`、`IsCombinatorialManifoldWithBoundary.isPLBall_faceStarComplex`、
  `restrict`、`restrict_faces_finite`、`restrict_space_of_eq_biUnion`、`IsSubdivision.convexHull_eq_biUnion`、
  `exists_isGlueIso_of_isPLHomeomorphOn`、`IsCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn`；
  Mathlib 的 `AffineIndependent.card_le_card_of_subset_affineSpan`。
  未经过 `Homology/HurewiczLowDegrees.lean`，未运行根构建，未登记根聚合。
  H.2a 无未闭合端点；H.2b 的定向上循环仍待按交接 §7.3 构造，H.6/H.4a/H.5 不在本次闭合范围。

- 2026-09-15（H 车道 H.2b，闭星局部定向上循环）：
  `DerivedCarrier.lean` 给重心细分顶点与原面载体的对应及旗标公共上面；
  `Orientation.lean` 的 `CoherentOrientation.restrict` / `IsOrientable.of_le` 推广到包含零维的任意 `n`；
  `OrientationCocycle.lean` 先统一局部顶点序，再在公共顶维单形上比较每个非空面闭星的相干定向。
  比较符号的选择无关性由公共闭星的对偶连通性证明，三角形恒等式在同一顶维单形上验证；
  没有使用旧“非顶维边取 0”的构造。构造层提交 `85cd6e095`。
  `orientationCocycle_isCoboundary_iff` 双向证明上边界当且仅当全局可定向：
  正向由上边界的顶点符号翻转局部定向并验证所有余维一面的边界抵消，反向限制全局定向并取局部比较符号。
  `exists_orientationCocycle_of_not_isOrientable` 从 H.2a 的闭星可定向性选局部族，给 C.4 所需的非上边界上循环。
  三个端点对任意 `n`、有限维实赋范环境、有限复形成立，没有连通性、正维或公开 `DecidableEq` 假设。
  三个目标模块均聚焦检查 exit=0、零警告；`AuditH2bReuse` exit=0，逐项核对 12 项核心声明与 12 项复用声明，
  公理闭包全为 `propext`、`Classical.choice`、`Quot.sound`，并检查三个端点的完整签名。
  核心审计为 `CoherentOrientation.restrict`、`IsOrientable.of_le`、`carrierFace_centroid`、
  `carrierFace_mem_of_mem_barycentricSubdivision`、`centroid_carrierFace_of_mem_barycentricSubdivision`、
  `exists_face_superset_carrierFaces_of_mem_barycentricSubdivision`、`pair_centroid_mem_barycentricSubdivision`、
  `faceStarComplex_antitone`、`faceCofaces_faceStarComplex_self`、`orientationCocycle`、
  `orientationCocycle_isCoboundary_iff`、`exists_orientationCocycle_of_not_isOrientable`。
  复用审计为 `SimplicialBoolCocycle`、`SimplicialBoolCocycle.IsCoboundary`、`carrierFace`、`carrierFace_mem`、
  `mem_openSimplex_carrierFace`、`face_eq_of_mem_openSimplex`、`centroid_mem_openSimplex`、
  `centroid_mem_openSimplex_of_mem_faces`、`IsFlag.subset_or_subset`、`IsFlag.exists_top`、
  `mem_faceStarComplex_faces_of_subset`、`faceStarComplex_faces_subset`，均来自整合后已有 PL 源码。
  H.2b 要求的三个端点均闭合；C.4 的二重覆盖流形及其可定向性没有在本次代做。
  未经过 `Homology/HurewiczLowDegrees.lean`，未运行根构建，未登记根聚合；H.6/H.4a/H.5 顺序和目标不变。

- 2026-09-15（H-M2 开邻域几何层中间检查点）：`SubcomplexNeighborhood.lean` 聚焦检查 exit=0、零警告。
  19 项新声明、8 项复用声明在 `AuditNightHM2Neighborhood.lean` 逐项审计，均仅标准三公理。
  `AuditNightHM2Reuse.lean` 另外逐项预审计了 PL 的质量、投影、同伦、质量与矩的过滤和公式、
  投影的凸包归属与权重公式、投影固定子复形、质量与矩连续性、细分过滤面、
  `derivedNeighborhoodStrongDeformationRetract`、细分顶点的重心表示，共 14 项；
  原生 Homology 的 `subspaceSmallShortExact`、`smallChainHomologyIso`、
  `augmentedSubspaceSmallShortExact`、`augmentedSmallChainHomologyIso`、
  `reducedMayerVietorisConnectingMap_coefficient_naturality` 共 5 项，均仅标准三公理。
  两个审计文件保留在 H 工作树 `.lake/scratch`。闭导出邻域的已有形变收缩不能直接充当开覆盖；
  此处实际构造了正重心质量开邻域，并证明交子复形的邻域等于邻域之交。
  H-M2 的同调正合性与自然性搬运仍待完成，没有将几何层记作 28.11 已证明。

- 2026-09-15（H-M2，子复形 Mayer–Vietoris 与 28.11 闭合）：
  几何层提交 `11826f868`；随后 `MayerVietorisSubcomplex.lean` 的
  `exists_mem_inter_of_map_eq_zero` 对有限复形的两子复形覆盖、任意次数、任意环和系数模成立，
  特别包含整系数 28.11。交子复形的开邻域与两个开邻域之交相等，三个包含都诱导同调同构，
  原来的子复形包含与开邻域包含的自然性方块严格交换；未引入闭覆盖 MV 的假设或单纯链复形。
  `bettiNumber_union_le` 证明任意域系数下
  `b_(n+1)(K) ≤ b_(n+1)(L) + b_(n+1)(M) + b_n(L∩M)`；
  `bettiOne_union_le` 为有理一阶特例，保留 `b_0(L∩M)` 项，不假设交集连通。
  通用数学归位于 `Homology/Algebra/PushoutHomology.lean`、`Homology/HomotopyEquivalence.lean`、
  `Homology/BettiNumber.lean`、`Homology/SmallChains/{Exactness,BettiBound}.lean`。
  七个相关模块最终各次聚焦检查均 exit=0、零 warning；同调搬运模块最后检查 10.5 秒。
  `.lake/scratch/AuditNightHM2*.lean` 保留 83 项去重后的逐项审计，包括新增 39 项声明及 44 项复用/预审计声明。
  `AuditNightHM2ExactReuse` 首次逐项审计 `pushoutShortComplex`、`pushoutShortExact`、
  `subspaceInclusion`、`twoSetFamily`、`firstSubspaceToSmall`、`secondSubspaceToSmall`、
  两个 `SubspaceToSmall_ι`、`subspaceSmallChainSquare`、`smallChainMap`、`smallChainHomologyIso_hom`；
  `AuditNightHM2BoundReuse` 逐项审计 `finrank_eq_range_add_range`、`homologyBiprodIso`、
  `finiteHomologyType_biprod`、`finiteHomologyType_twoSetSmall`、
  `finiteHomologyType_iff_of_homotopyEquiv`、`finiteHomologyType_geometricSpace`。
  全部闭包只含标准三公理或更少；无 `sorryAx`，不经过 `HurewiczLowDegrees`，未登记根聚合。
  闭曲面顶维同调与 I5 仍属于后续 H-M3/H-M4，不由本次 MV 工具自动推出。

- 2026-09-15（H-M3 低阶同调层，数学提交 `163a27733`）：
  `GeometricHomology` 复用既有有限 simplicial-set realization 的奇异同调桥，证明任意环/系数模的维数以上消失；
  `GeometricConnectivity` 给有限几何复形的局部路径连通与连通到路径连通；
  `BettiPolyhedra` 给低阶 χ 展开、连通图的 `b_1=1-χ` 与 PL 多边形 `b_1=1`。
  `.lake/scratch/AuditNightHM3*.lean` 逐项审计 26 项去重声明（11 新、2 既有复核、13 复用/预审计），仅标准三公理。
  首次复用单独审计：`orderedSimplicialSet`、`orderedSimplicialSet_hasDimensionLT`、
  `geometricRealizationHomeomorphism`、`geometricInclusion`、`DifferentialGeometry.SSet.realizationHomologyIso`、
  `SSet.isZero_homology_of_hasDimensionLT`、`Homology.eulerChar_eq_sum`；另预审计
  `localEuclideanSphereHomologyIso`、`euclideanLocalGenerator_ne_zero`、`euclideanBallLocalGenerator_ne_zero`。
  三条 PL 复用复核为 `IsPLSphere.isCombinatorialManifold`、`IsCombinatorialManifold.card_le`、`IsPLSphere.isConnected`。
  `subcomplexInclusion` 现直接复用原生 `geometricInclusion`，重查 MV 消费者 exit=0。
  五个改动模块均检查 exit=0、零 warning；`BettiPolyhedra` 11.2 秒，MV 消费者 12.1 秒。
  全局 H₂ 的局部检测与跨边符号比较未证明，未声称 H.4a 完成；具体义务和原路线修正在 HANDOFF §8。

## 7. 决策与风险

- 不采用 Bing 定理 7 的“保留单形”强形式，只用 Moise §8/§35 的紧致图卡归纳（书中 `chap:two-set-gluing` 的方案）。
- 不变域定理不进入 Phase 1（`f(O) = O` 由接口 A 给出，与 Moise 36.1 一致）。
- `PLApproximation`/`PLSmoothing` 以 `Prop` 假设而非 `sorry` 出现：公理审计干净，但**报告时必须说明条件性**。
- 主机内存约 31.5 GB、空闲不足 10 GB：构建限 2 worker；本任务的聚焦检查一次只开一个 `lean.exe`。
- 2026-09-12：Phase 3 按 Moise GTM 47 §30–36（伪胞腔 / 典范构形）而非用户路线图 `main04.tex` 的 Shalen 式章节组织，
  因为本机只有 Moise 的完整书面证明；两者终点陈述相同。Phase 3 的表示层决定 D1–D6（多面体层 + 流形层、不引入带边
  PL 流形图卡范畴、有限复形单纯 ℤ-链、复用 Mathlib/本库覆盖与基本群、只做三种一般位置、外部移植不变域）记录在
  `PHASE3_APPROXIMATION_PLAN.md` §1；最大开放点是同调层（单纯 vs 奇异）。
- Schoenflies 三版本互不蕴含：平面拓扑版（vendored）、PL ℝ³ 版（本链 §17 自证，依赖平面多边形版 3.6、3.3、10.8）、
  光滑 ℝ³ 版（负责人，sorry）。本链不消费光滑版；不重复负责人的工作。
