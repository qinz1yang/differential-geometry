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
