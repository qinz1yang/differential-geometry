# Phase 3 具体计划：A′ `PLApproximationManifold 3` 的经典证明链（Moise GTM 47）

本文件是 `MOISE_PLAN.md` §5 "Phase 3+" 的展开，只描述 Phase 3；目标、基线、Phase 1/2 的状态仍以 `MOISE_PLAN.md` 为准。
日期均为绝对日期（起草 2026-09-12）。路径省略 `DifferentialGeometry/` 前缀。
来源：Moise, *Geometric Topology in Dimensions 2 and 3*（GTM 47，本机 PDF 副本，书页 p ≈ PDF 页 p+10）。
"Moise a.b" 指该书 §a 定理 b；"L a.b" 指 §a 引理 b。

## 0. 目标命题与已证消费者

Phase 3 的唯一终点是一条定理：

```lean
theorem plApproximationManifold_three : PLApproximationManifold.{u} 3
```

其中（`Topology/PiecewiseLinear/Manifold.lean`，已定义、无 sorry）：

```lean
def PLApproximationManifold (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)] (h : M₁ ≃ₜ M₂)
    (φ : M₁ → ℝ), Continuous φ → (∀ x, 0 < φ x) →
    ∃ f : M₁ ≃ₜ M₂, IsPL n n f ∧ ∀ x, dist (f x) (h x) < φ x
```

已证（Phase 1）的下游链，Phase 3 完成后自动变成无条件定理：

- `plApproximation_of_plApproximationManifold : PLApproximationManifold n → PLApproximation n`（A′ → A）。
- `exists_chartedSpace_hasGroupoid_plGroupoid_of_plApproximation`：A → 紧致 T2 拓扑 `n`-流形有 PL 图册（Moise 三角剖分定理的图册形式）。
- `exists_isManifold_three_of_plApproximation_of_plSmoothing`：A + B（Phase 2）→ 书中接口 `∃ s : ChartedSpace ℝ³ M, IsManifold (𝓡 3) ∞ M`。

Phase 3 结束时应新增两条无条件推论并做公理审计：

```lean
theorem plApproximation_three : PLApproximation.{u} 3 :=
  plApproximation_of_plApproximationManifold plApproximationManifold_three

theorem exists_chartedSpace_hasGroupoid_plGroupoid_three {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] :
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X, letI := C; HasGroupoid X (plGroupoid 3)
```

### 0.1 A′ 与 Moise 36.1 的对应，以及必须处理的非紧性

Moise 36.1：`M₁ M₂` PL 3-流形，`U ⊆ M₁` 开，`h : U → M₂` 同胚到开集 `h(U)`，`φ ≫ 0` 于 `U`；
则存在 PLH `f : U → M₂`，`f` 是 `h` 的 φ-逼近且 `f(U) = h(U)`。
A′ 是 `U = M₁`、`h` 满射的情形；两集拼接桥需要的开子集情形已经由
`plApproximation_of_plApproximationManifold` 通过 `Opens` 子类型 PL 流形归约到 A′。
因此 A′ 的证明必须覆盖**非紧致** `M₁`（开子集通常非紧），且 `M₂` 的度量任意。
Moise 的"强正函数"在这里换成连续正函数 `φ`（局部紧可分空间上二者等价，见 `MOISE_PLAN.md` §4.2）。

Moise 的推导顺序是 35.1（线性图正则邻域，非紧、流形层）→ 35.2（多面体 3-流形带边，非紧）→ 36.1（开集，
`f(U) = h(U)` 由穷竭 + 不变域得到，"与 8.4 从 6.4 的过渡完全一样"）。本计划保持这一顺序。

### 0.2 与用户路线图 `main04.tex` 的关系

`Moise_Theorem/main04.tex` 按 Shalen 1984 的路线（覆盖塔、Nielsen、受控对齐、Heegaard 结构）组织章节，
而本计划按 Moise §30–36（伪胞腔 / 典范构形）组织；二者的终点陈述相同（`thm:boundaryless-approx-main04` = 36.1）。
选 Moise 的理由：本机有完整可核对的书面证明；Shalen 原文不在本机。章节名重合处在下表中标注
（`chap:pl-schoenflies`、`chap:pl-coverings`、`chap:regular-neighborhoods`、`chap:dehn-loop`、
`chap:noncompact-approximation`、`chap:two-set-gluing`）。路线图"仅在证明来源固定后才加入平面 Schoenflies 边"的保留
现在可以落地：Moise §17 的证明确实使用平面多边形 Schoenflies（3.6）、自由 2-胞腔引理（3.3）与平面线性图的驯顺嵌入（10.8），
见 §4.2。

## 1. 表示层决定（Phase 3 词汇）

Phase 1 刻意用 H-多面体 + 图册回避了细分理论；Phase 3 无法回避：正则邻域、胞腔分解、分裂运算、Euler 数与
同调计数、一般位置全部以三角剖分表达。以下决定在实现前冻结（修改需回写本文件与 `MOISE_PLAN.md` §7）。

- **D1 两个层次。** (i) *多面体层*：固定 `E := EuclideanSpace ℝ (Fin N)`；紧致多面体 = 有限个 H-多面体之并
  （`IsPolyhedron`）；三角剖分 = 有限 `Geometry.SimplicialComplex ℝ E`（Mathlib 原生，本库 `Topology/SimplicialComplex/*`
  已有 link、star、Euler 数、实现同胚）；PL 映射 = `IsPiecewiseAffineOn` / `IsPLHomeomorphOn`；组合流形（带边）
  由顶点 link 定义。(ii) *流形层*：`[ChartedSpace ℝ³ M] [HasGroupoid M (plGroupoid 3)]`，映射用 `IsPL`。
  Moise §23–§35 的对象（多面体 3-胞腔、多面体 2-球面、正则邻域、CST）都定义在多面体层，通过"`M` 中的紧致多面体"
  （`PolyhedronIn`：有限复形 + 逐图卡 PL 的嵌入，与 `PLTriangulation` 同型）进入流形层。
- **D2 不引入带边 PL 流形的图卡范畴。** 带边对象只作为多面体层的有限复形 `IsCombinatorialManifoldWithBoundary 3 K`
  出现（在 ℝᴺ 中，或作为 PL 流形内的 `PolyhedronIn`）。§25 需要的 2-重覆盖用 24.6 + 7.1 实现成有限复形，
  不需要抽象带边流形。
- **D3 同调层用有限复形的单纯 ℤ-链。** 可定向性（23.14 的 3-链定义）、`p¹`（H₁ 的秩）、`χ`（顶点−边+面）、
  28.11 型引理全部在单纯链上陈述与证明；需要拓扑不变性的地方按 Moise 原路（21.4–21.5 经细分不变性与 2D 结果）处理，
  或在车道 H 决定改用本库奇异同调（`Topology/Homology/*`）加比较定理。这是 Phase 3 最大的开放设计点（§8 R3）。
- **D4 基本群与覆盖用 Mathlib/本库。** `FundamentalGroup`、`Path`、`IsCoveringMap`、`IsCoveringMap.liftPath`、
  `monodromy`（Mathlib `Topology/Homotopy/Lifting.lean`）；本库 `Topology/Covering/*`（`BoolCocycle`、`DoubleCoverComponents`、
  `DeckGroup`、`SimplyConnectedCover`）与 `Topology/VanKampen/*`（`FreeProduct`、`SimplyConnectedUnion`）是复用候选，
  使用前必须做 `#print axioms`（Phase 2 审计指出树中存在 sorry 支撑的链）。多面体中的道路先取 PL 代表
  （1 维单纯逼近，车道 F 提供）。
- **D5 一般位置只做本链用到的三种。** (a) 两张多面体曲面（或曲面与 2-胞腔）经任意小 PLH 后横截相交于有限条
  多边形与折线（§26.4、§30–§34 的"cross one another"）；(b) PL 奇异 2-胞腔的正规形式（§25 L2：奇点为不交多边形与折线，
  仅"crossing"）；(c) 多边形相对水平平面族的一般位置（§17.12）。不做一般的 PL 一般位置定理。
- **D6 不变域定理原生移植与 Brouwer 条件消去（E.0 已完成）。**
  mccorvie/classification-of-surfaces@e3c7230 的
  `ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean`（Apache-2.0）原本显式假设
  `BrouwerFixedPoint E`；其 Stone–Weierstrass 逼近与 Jacobian 测度论证原生移植于
  `Topology/InvarianceOfDomain.lean`。`Topology/FixedPoint/NoRetraction.lean` 用本树球面顶维同调与
  可缩空间正维同调消失证明任意正维数无收缩；`Topology/FixedPoint/Brouwer.lean` 将上游射线构造推广到
  任意有限维实内积空间，并单独处理零维，给出已证的 Brouwer 实例。
  `Topology/InvarianceOfDomainManifold.lean` 导出无未证类参数的
  `invariance_of_domain_isOpen_image`、`isOpen_image_of_continuousOn_injOn`、
  `isOpenMap_of_continuous_injective`，以及实 `ModelWithCorners` 的开像、嵌入、内点与边界图卡接口。
  全部最终端点通过 `AuditE0`，仅含标准三公理；出处、原版权声明、修改记录与完整许可证在
  `docs/third_party/InvarianceOfDomain.md` 及同目录 `classification-of-surfaces-LICENSE`。
  供 S.1、M.3 与 E.3/E.4 消费；这些消费者自身的剩余义务不由 E.0 的完成替代。

## 2. 章节依赖（只列 36.1 实际消费的边）

- §7 / §8.2（PL 复形、开集是多面体）→ 一切；本计划用 §1 的 D1 替代 §7 的"PL 复形"。
- 2D 输入：3.3, 3.6, 5.3, 5.4, 10.8 → §17；2.7–2.8, 4.4 → §26.7, §27.2, §30.1；§21–22（χ, p¹, 可定向性，22.5–22.9, 22.11）
  → §23.18–19, §26.8, §28.6, §30.4, §30.6, §32, §33 L7/L11/L12。
- §17（PL Schoenflies, 推移性质 17.4–17.8）→ §23.9–23.11, §28.1 后半, §30.5, §33 末（3-胞腔延拓）。
- §23（三角剖分 3-流形：23.2–23.4, 23.8, 23.9–23.12, 23.14–23.19）→ §24.7–24.8, §25, §26.2, §28, §30.4, §36.1。
- §24（覆盖：24.1–24.6 通用；24.7, 24.8 二重覆盖；24.9–24.12 CST）→ §25 L3, §28.19, §31。
- §25（Stallings 环定理 25.1, 25.2）→ §26.4。
- §26（26.1–26.4 双领与扩展环定理；26.6–26.8 ℝ³ 中曲面；问题 26.3）→ §27.1, §28.1 后半, §30.4, §30.6, §30.7, §32 Type 2, §33 L5/L9–L11。
- §27.1–27.4（胞腔同胚、环带中多边形；**27.5 Dehn 引理不在关键路径**）→ §28.2–28.3, §31.4, §32 L2, §35 L1。
- §28.2–28.4, 28.6–28.11, 28.19–28.20（**28.5, 28.12–28.18 不在关键路径**）→ §30.3–30.4, §31.4, §32, §33 L7, §34 L4/L11。
- §30.1–30.8 → §31.1–31.2, §32 Step 2, §33 L5, §34 L3。
- §31 → §32.1。§32.1–32.4 → §33。§33.1 → §34 L1。§34.1 → §35.1。§35.1 → §35.2 → §36.1 → A′。

## 3. 车道划分

| 车道 | 内容 | 前置 | 估计 Lean 行数 |
|---|---|---|---|
| F 基础 | §4.0：多面体/三角剖分/细分/公共细分/PL 映射单纯化/link 唯一性/锥延拓/正则邻域/一般位置/局部有限三角剖分与穷竭/T1、T2 | 无 | 35k–60k |
| H 同调与曲面 | §4.1 后半：单纯链、H₁、p¹、χ、可定向性；§21–22 所需；23.14–23.19；28.11 | F1–F3 | 20k–35k |
| S Schoenflies 与 3-胞腔 | §4.1 前半（3.3, 3.6, 5.3, 5.4, 10.8）；§17；23.9–23.12；PL Alexander 技巧；30.5 | F | 20k–35k |
| C 覆盖 / 环定理 / 环带 / 实心环面 | §24、§25、§26、§27.1–27.4、§28（关键子集） | F, H, S | 45k–75k |
| I 插值与逼近 | §30–§34 | C, S, H | 60k–100k |
| E 终局 | D6 不变域移植（可立即开始）；§35–§36；穷竭；端点与推论；公理审计 | I, F6 | 15k–25k |

总计约 **200k–330k** 行（不含 Phase 1 的 1.4k 与 Phase 2）。这比 `MOISE_PLAN.md` 早先给出的 Phase 3 估计
（110k–210k）高：早先估计在通读 §24–§35 之前给出；通读后可见 §25、§32–§34 各自都是 2D 项目
（88.7k 行 `Moise/` 目录）量级的一半以上。时间：4 条并行车道、每车道每日 1k–1.5k 已验证行，约 6–9 个月；
单车道则线性放大。降本杠杆：D6（−1k）、D4 复用（−10k–20k）、H 车道若能避免完整 2D 分类（§8 R3，不确定）。

顺序：F、H、S、E0（D6 移植）立即并行；C 在 F1–F4、H 前半、S 的 §17 完成后开始；I 在 C 的 §26.4、§28 与 S 完成后开始；
E 最后。每车道的对外接口定理在本文件 §4 表中列出，签名冻结后修改必须回写此表。

## 4. 分章定理清单与拟定 Lean 陈述

记 `ℝ³ := EuclideanSpace ℝ (Fin 3)`，`E` 为有限维实赋范空间。所有签名是**拟定**形式（实现时可调整隐式参数与
携带的有限性假设），但陈述的数学内容不得弱化。表中"状态"：`new` 待写；`ext` 外部移植；`nat` 本库已有或可直接推出；
`skip` 不在关键路径。

### 4.0 车道 F：PL 基础（维数无关，除非注明 3D）

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| F1.1 | 紧致多面体 | `def IsPolyhedron (P : Set E) : Prop := ∃ (ι : Type) (_ : Finite ι) (C : ι → Set E), (∀ i, IsHPolytope (C i)) ∧ P = ⋃ i, C i`；对有限并、交、仿射像封闭 | 全部 | done（`Polyhedra.lean`，2026-09-12） | 1k |
| F1.2 | 多面体可三角剖分（实现：全体定义泛函的排列胞腔 + 胞腔导出细分，不用逐维锥分） | `theorem IsPolyhedron.exists_simplicialComplex (hP : IsPolyhedron P) : ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = P` | F2, T2 | done（`Arrangement.lean`、`CellComplex.lean`、`Triangulation.lean`，2026-09-12） | 4k–7k |
| F2.1 | 细分 | `def Geometry.SimplicialComplex.IsSubdivision (K' K) : Prop := K'.space = K.space ∧ ∀ s ∈ K'.faces, ∃ t ∈ K.faces, convexHull ℝ ↑s ⊆ convexHull ℝ ↑t`；传递性；子复形的细分 | 全部 | done（`Subdivision.lean` + `Barycentric.lean`：`IsSubdivision`、`openSimplex`、载体面、`weights`；2026-09-12） | 1k–2k |
| F2.2 | 重心细分与网格 | `def barycentricSubdivision (K)`；`barycentricSubdivision_isSubdivision`；`theorem exists_isSubdivision_diam_lt (K) (hK : Finite K.faces) (ε) (hε : 0 < ε) : ∃ K', IsSubdivision K' K ∧ ∀ s ∈ K'.faces, Metric.diam (convexHull ℝ ↑s) < ε`（本库 `FaceBarycenter.lean`、`Homology/AffineSubdivision.lean` 可部分复用） | §23 正则邻域、§33–35 的"充分细" | done（`Derived.lean`：任意内点的导出细分 `derived`、`barycentricSubdivision`；`Mesh.lean`：`exists_isSubdivision_diam_lt`；2026-09-12） | 3k–5k |
| F2.3 | 子复形化 / 公共细分（RS 2.12） | `theorem exists_isSubdivision_subcomplexes (K) (hK : Finite K.faces) (P : Finset (Set E)) (hP : ∀ p ∈ P, IsPolyhedron p ∧ p ⊆ K.space) : ∃ K', IsSubdivision K' K ∧ ∀ p ∈ P, ∃ L ≤ K', L.space = p`；推论 `exists_common_subdivision (K L) (h : K.space = L.space)` | §25–§35 到处用"取三角剖分使 S, Δ, N, J 为子复形" | done（`Triangulation.lean`：`exists_isSubdivision_subcomplexes`（多面体族以 `Finite` 类型索引）、`exists_common_subdivision`；2026-09-12） | 8k–15k |
| F3.1 | PL 映射经细分单纯（RS 2.14） | `theorem IsPiecewiseAffineOn.exists_isSubdivision_affineOn (hK : Finite K.faces) (hf : IsPiecewiseAffineOn f K.space) : ∃ K', IsSubdivision K' K ∧ ∀ s ∈ K'.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ ↑s)` 及逆命题 | 一般位置、覆盖提升、§25 | done（`PiecewiseAffineSimplicial.lean`：`IsPiecewiseAffineOn.exists_isSubdivision_affineOn_faces`；逆命题 `isPiecewiseAffineOn_space_of_forall_face` 与单纯延拓 `simplicialMap`、`isPLHomeomorphOn_simplicialMap` 在 `Star.lean`/`SimplicialMap.lean`；2026-09-12） | 3k–5k |
| F3.2 | 1 维单纯逼近 | 多面体中任意道路同伦于 PL 道路；闭道路同理（D4） | §24–§25, §30–§35 中"PL 闭道路" | done（2026-09-13）`PLPath.lean`：`IsPLPath γ`（子空间中道路的延拓在 `[0,1]` 上逐段仿射），线段道路 `segmentPath` 与 `Path.trans` 保持 PL 性，闭星是星形集故可缩、单连通（`homotopic_of_forall_mem_closedStar`：闭星内同端点道路同伦），截断的拼接同伦 `homotopic_truncateOfLE_trans`（显式参数同伦），主定理 `exists_isPLPath_homotopic : ∀ γ : Path x y (in K.space), ∃ γ', IsPLPath γ' ∧ γ.Homotopic γ'`（开星覆盖的 Lebesgue 数把 `[0,1]` 等分，每段用经顶点的两段折线替换）；闭道路即 `x = y` 的情形 | 1k–2k |
| F3.3 | link 的 PL 唯一性（RS 2.21–2.24） | 同一多面体的两个三角剖分中同一点的 link PL 同胚；推论：`IsCombinatorialManifold n K` 只依赖 `K.space` 的 PL 结构 | T2、§23 | done（核心，2026-09-13）：`RadialProjection.lean` 伪径向投影 `exists_isPLHomeomorphOn_of_radial`（两个同顶点锥底相互适配且交同一射线族 ⟹ PL 同胚，证明要点：单形上仿射延拓保持每个面上的锥，故单射）；`LinkSubdivision.lean` 细分不变 `exists_isPLHomeomorphOn_geometricLink_of_isSubdivision`、`isPLSphere_geometricLink_iff_of_isSubdivision`；`LinkEuclidean.lean` 欧氏情形 `isPLSphere_geometricLink_of_mem_nhds`（`finrank E = n+1`，`K.space ∈ 𝓝 p` ⟹ 顶点 link 是 PL `n`-球面，T2 所需形式）。2026-09-14 已补组合流形 PL 不变性推论：`ManifoldInvariance.lean` 的 `IsCombinatorialManifold.of_isPLHomeomorphOn` 及带边界版本，AuditF19 仅标准三公理、聚焦检查 exit=0 零 warning，源码 `46963b844` 已推送。未做：非顶点处的 link（单形内点的 link = 边界 ∗ link，需 join 理论），本链暂不需要 | 5k–8k |
| F3.4 | PL 球/球面基本性质与锥延拓（PL Alexander 技巧） | `theorem exists_isPLHomeomorphOn_of_frontier (h₁ : IsPLBall n B₁) (h₂ : IsPLBall n B₂) (hf : IsPLHomeomorphOn f (frontier B₁) (frontier B₂)) : ∃ g, IsPLHomeomorphOn g B₁ B₂ ∧ EqOn g f (frontier B₁)`；PL 球的边界是 PL 球面；`IsPLBall` 在 PL 同胚下不变；标准单形的锥 | §17.5, §23.11, §33 末尾, §34 (5)–(7) | done（组合边界形式，2026-09-14，砖 9）；`frontier` 形式仍待 E.0/S.1。`BoundaryExtension.lean`：`exists_isPLHomeomorphOn_of_boundaryComplex` 对有限复形实现的任意正维 PL 球，将其组合边界之间的任意 PL 同胚延拓为球之间的 PL 同胚，并逐点保持给定边界映射。证明经 `BoundaryOfBall.lean` 的 `boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex` 搬到标准单形边界，使用 `StdSimplexCone.lean` 与 `ConeExtension.lean` 的 `exists_isPLHomeomorphOn_coneComplex`，再由球的参数化搬回。既有 `isPLSphere_boundaryComplex_space_of_isPLBall` 给出球边界的球面性；`IsPLBall.of_isPLHomeomorphOn` / `IsPLSphere.of_isPLHomeomorphOn`、标准单形与闭星的球性均保留。聚焦检查 exit=0 零 warning，AuditF27 端点仅标准三公理，源码 `5eba0ee4a` 已推送；未使用 Schoenflies；补（`0a645e32b`）：通用边界延拓现在显式沿用两侧 DecidableEq 实例，避免具体欧氏空间中实例不一致造成展开超时，数学陈述不变；其二维边界弧延拓消费者已闭合。两模块检查 exit=0、零 warning；F97 审计 30 项均仅标准三公理。 | 3k–5k |
| F4.1 | 带边组合流形与边界复形 | `def IsCombinatorialManifoldWithBoundary (n) (K) : Prop`（顶点 link 是 PL `(n−1)`-球面或 PL `(n−1)`-球）；`def boundaryComplex (K)`（恰在一个 `n`-面中的 `(n−1)`-面及其面）；`theorem isCombinatorialManifold_boundaryComplex (h : IsCombinatorialManifoldWithBoundary (n+1) K) : IsCombinatorialManifold n (boundaryComplex K)`（Moise 23.3/23.7 的 3D 证明经 23.2/23.6） | §23–§35 | **done**（2026-09-13）：`ManifoldWithBoundary.lean`：`IsCombinatorialManifoldWithBoundary n K`（顶点 link 为 PL `(n−1)`-球面或球）、`boundaryComplex n K`（含于某个 link 为 PL `(n−|t|)`-球的面 `t`（`|t| ≤ n`）的面）、`geometricLink_boundaryComplex`（`lk(v, ∂K) = ∂(lk v K)`）；`BoundaryOfBall.lean`：**`isCombinatorialManifold_boundaryComplex (h : IsCombinatorialManifoldWithBoundary (n+1) K) : IsCombinatorialManifold n (boundaryComplex (n+1) K)`**，经 `isPLSphere_boundaryComplex_space_of_isPLBall`（三角剖分的 PL 球的边界复形空间 = 模型单形边界的像 `boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex`，是 PL 球面）；`BoundaryFaces.lean`：`IsCombinatorialManifoldWithBoundary.isPLSphere_or_isPLBall_geometricLink`（面 link 二分）、`mem_boundaryComplex_faces_iff`（边界面 = link 为球的面）、`IsCombinatorialManifold.boundaryComplex_faces_eq_empty`。支撑理论（均新增、聚焦检查零警告、AuditF16 仅标准公理）：`LinkRadial`（径向 link 引理：闭星被锥覆盖的锥底 ≅ link）、`SimplexAvoiding`（避开面的单形子复形；`isPLBall_simplexAvoiding_singleton` 经 far 复形迭代锥）、`StellarSphere`（`unionComplex`、`swapVertex`、避开面及其补的复形 ≅ 小一维单形边界的星形细分 ⟹ PL 球面）、`SimplexLink`（单形/单形边界细分中顶点 link 的球/球面判据 `isPLBall_geometricLink_iff_of_isSubdivision_simplexComplex`）、`FaceLink`（`geometricLink_insert`：面 link = link 中的 link）、`IsomorphicSubdivision`（PL 同胚复形有单纯同构细分 `exists_isGlueIso_of_isPLHomeomorphOn`）、`BallSphereLink`（PL 球面/球的三角剖分中顶点与面 link 的球/球面性；球中顶点 link 是球 ⟺ 顶点在模型边界像内）、`StarAvoiding`（面相对内部点的 link ≅ `starAvoiding K t`，link 型在开单形上常值）、`Join`/`JoinTransport`/`JoinInternal`/`JoinStandard`/`JoinInvariance`（外部 join、同构与细分传递、内部 join 同构、`∂σ ∗ ∂τ`/`∂σ ∗ τ` 的标准模型、join 的 PL 不变性、`isPLSphere_joinComplex_of_isPLSphere`、`isPLBall_joinComplex_of_isPLSphere_of_isPLBall`）、`StarJoin`（`starAvoiding K t ≅ ∂t ∗ lk(t)`，点 link 的球/球面上升引理）、`LinkDimension`（PL 球/球面三角剖分的面至多 `m+1` 个顶点；开单形闭包）。原计划的 F4.1.c/d（顶点图卡）不再需要。`PLBallSphere`、`LinkHalfSpace` 保留 | 3k–5k |
| F4.2 | 正则邻域（`b²K` 中与 `L` 相交的单形） | `def regularNeighborhood (K L) (h : L ≤ K) : Geometry.SimplicialComplex ℝ E`；`regularNeighborhood_space_mem_nhdsSet`；`N(v)`, `N'(σ)` 的定义与"是 3-胞腔、两两交于 2-胞腔"（Moise §23 预备）；**3D**：`theorem isCombinatorialManifoldWithBoundary_regularNeighborhood (hK : IsCombinatorialManifold 3 K) (hL : L ≤ K) : IsCombinatorialManifoldWithBoundary 3 (regularNeighborhood K L h)`（`chap:regular-neighborhoods`） | §23.12, §24.11–12, §25, §26.3, §27.5, §28.19, §32, §33–§35 | **done（主定理，任意维数，2026-09-13 深夜）**：`DerivedNeighborhood.lean`：`derivedNeighborhood K L`（第二重心细分 `secondDerived K` 中所有链元素都与 `L'` 的顶点相交的面；等价于 Moise 的 `N(L)`）、`derivedNeighborhood_mem_nhdsWithin`（含每个 `|L|` 点的闭星，故是 `|L|` 在 `|K|` 中的邻域）；`ManifoldSubdivision.lean`：`IsCombinatorialManifoldWithBoundary.of_isSubdivision`/`.barycentricSubdivision`/`.secondDerived`（细分不变性，经点 link ≅ `∂t ∗ lk t` 上升引理）与面顶点数上界；`UpperLink.lean`：`upperLink K e`（严格含 `e` 的链）经自 `ê` 的伪径向投影 ≅ `lk(e, K)`；`DerivedWeights.lean`（重心细分中点的重心坐标：极大坐标恰在链的最小元）；`FaceNeighborhoodBall.lean`：**单形中一个面的导出邻域是 PL 球**（自 `f̂` 星形，径向前沿 = 最小元与补面相交的链 ∪ 缺 `f` 某顶点的链，为锥底且径向投影 ≅ `f` 对面诸面片）；`FaceNeighborhoodLink.lean`：顶点 `T̂` 在该邻域中的 link 是 PL 球（锥延拓把 `T̂` 送到单形边界）；`DerivedNeighborhoodLink.lean`：`lk(ê, N) = internalJoin (下部：`∂e` 的导出邻域中的链) (upperLink)`；`DerivedNeighborhoodManifold.lean`：**`IsCombinatorialManifoldWithBoundary.derivedNeighborhood (h : IsCombinatorialManifoldWithBoundary (n+1) K) (L) : IsCombinatorialManifoldWithBoundary (n+1) (derivedNeighborhood K L)`**（`e ⊆ V(L')` 时 link 同 `K''`；否则 = 下部球 ∗ `lk(e,K')`，用 `JoinBall.lean` 的球∗球、球∗球面）。AuditF17 仅标准公理。未做（移入 F4.3）：`N(v)`、`N'(σ)` 的 3-胞腔结构与两两交于 2-胞腔。旧的集合版 `regularNeighborhoodIn K A` 保留未用。2026-09-14 砖 7 完成：`LocalManifold.lean` 的 `IsLocallyCombinatorialManifoldWithBoundary`、`.mono`、`.card_le`、`.isPLSphere_or_isPLBall_geometricLink`、`.of_isSubdivision`、`.derivedNeighborhood`；只要求与给定集合相交的单形之顶点具有好 link。细分的最高维分支只用包含载体面的单形的维数界。局部导出邻域定理不需要 `L.faces ⊆ K.faces`（所选面形心自动属于 `L.space`）；邻域性仍单独使用子复形条件。聚焦检查 exit=0 零 warning，AuditF25 全部 14 个声明仅标准三公理，源码 `85cc59a2a` 已推送 | 6k–10k |
| F4.3 | 管的对偶胞腔与分裂盘（§32 开头定义） | 拟定 Lean：对有限 `IsCombinatorialManifold 3 K`、`L.faces ⊆ K.faces`、`∀ s ∈ L.faces, s.card ≤ 2`，保留 `N := derivedNeighborhood K L`；`graphDualCell K L v := restrict N (closedStar (barycentricSubdivision K) v)`；`dualCell K e` 是 `e` 的形心对 `upperLink K e` 的锥；`splittingDisk K e` 是该形心在 `barycentricSubdivision (dualCell K e)` 中的闭星。目标：`isPLBall_graphDualCell`（3-球）、`isPLBall_splittingDisk`（2-球）、`graphDualCell_space_inter`（相邻交集为共享盘，非相邻为空）、`splittingDisk_space_inter`（与 L 的载体恰交于边形心）、胞腔覆盖 N、每胞腔恰含对应顶点、盘两两不交；组合内部与组合边界用于分离陈述，细分后胞腔直径任意小 | §32–§35 | partial（2026-09-14，砖 6，`DualCells.lean`）：保留现有 `derivedNeighborhood` 定义。已证 `IsCombinatorialManifold.isPLSphere_upperLink`、`isPLBall_dualCell`、`isPLBall_splittingDisk`、`splittingDisk_space_inter`（对原图恰交于边形心）、`iUnion_graphDualCell_space`（胞腔覆盖）、`mem_graphDualCell_space_iff_of_singleton_mem`（每胞腔恰含对应图顶点）、`graphDualCell_space_inter`（相邻交集为共享盘）、`graphDualCell_space_inter_eq_empty`（非相邻不交）、`disjoint_splittingDisk_space`、`diam_graphDualCell_le` 及 `exists_isSubdivision_graphDualCell_diam_lt`（兼容图的任意小细分）。49 个定义/定理，聚焦检查 exit=0 零 warning，AuditF24 全部仅标准三公理；源码 `ccf7a2035` 已推送。按交接 §9.0，剩余顶点胞腔球性 `IsPLBall 3 (graphDualCell K L v).space` 依赖 S.5 的带边界盘粘接；组合内部中的分离结论随该依赖闭合。不得将已证对偶锥球性等同于被邻域截取后的胞腔球性。Q 消费者在 S.5 完成前只能显式携带 `hcell` 并标为条件性定理，不用 sorry。逐点径向公式 `v + ρ(z) • (z-v)` 一般不是 PL，不能替代该证明。不修改正则邻域语义，不重复 Schoenflies；继续局部导出邻域、非紧穷竭和组合边界延拓 | 3k–5k |
| F5.1 | 一般位置 (a)：曲面对 | 紧致多面体曲面（带边）`S₁ S₂ ⊆ ℝ³` 与 `ε`：存在 PLH `h` ε-接近恒同、在给定闭集外恒同，使 `h '' S₁ ∩ S₂` 为有限个不交多边形与折线之并且横截（Moise 的"cross one another"）；平面族版本（§17.12 的水平平面） | §17.12, §26.4, §26.6, §28.2, §30.4, §32–§34 | done（2026-09-14，`GeneralPosition.lean`）。`exists_small_homeomorph_generalPosition` 与相对端点 `exists_small_homeomorph_generalPosition_relative` 对三维有限带边组合 2-流形构造任意小、指定开邻域外恒同的环境 PL 同胚；相对版本固定整个既有一般位置子复形。交集为有限一维带边组合流形，处处 `HasPLCrossingAt`。按交接 §9.5，一维组合流形即约定的有限多边形/折线之并的表示。`exists_generalPosition_height_fibers` 给出全水平平面族：顶点高度两两不同，各层为有限至多一维图，原顶点外度数二且 crossing，每层至多一个原顶点，普通层为无边界一维组合流形；临界点允许孤立或分叉。`exists_small_simplicialMap_preimage_manifold_relative` 对任意子复形使用相对细分并保持整个映射，允许全局自交而各单形上单射，给出一维带边原像流形及源边界度数一、源内部度数二。`exists_small_simplicialMap_preimage_manifold_of_isPLBall` 固定原 PL 球的整个组合边界，并按原边界给出度数分类；m=n=1 为 §26.6 圆盘映射消费者。`exists_isPLHomeomorphOn_extension_of_small_vertex_perturbation` 证明统一阈值内的每个顶点扰动均延拓为任意小、指定邻域外恒同的环境 PL 同胚；基础为全局 Lipschitz 顶点基函数及 `IsPiecewiseAffineOn.exists_lipschitz_extension`。分析支撑在 `Analysis/Calculus/Interpolation/LipschitzSelection.lean`。聚焦检查 exit=0 零 warning，AuditF55 共 162 声明（GeneralPosition 158，分析 4）仅 propext、Classical.choice、Quot.sound，源码 `bebaf278c` 已推送，无 Schoenflies 依赖。下一砖 F5.2 奇异 2-胞腔正规形式。 | 6k–10k |
| F5.2 | 一般位置 (b)：奇异 2-胞腔正规形式 | PL 映射 `D : Δ → M` 局部同胚、至多 2 对 1，可微扰使奇点集为不交多边形与折线的并且为"crossing"（§25 L2 前言） | §25 | partial（2026-09-14，`SingularGeneralPosition.lean`）。欧氏环境端点 `exists_small_simplicialMap_doublePointSet_manifold` 已闭合：任意小 PL 扰动、原域细分、闭星上到像的 PL 同胚、局部单射、每个纤维至多两点；`doublePointSet` 精确表示两个不同原像的奇点像，其有限三角剖分是一维带边组合流形，每点满足 `HasPLDoubleCrossingAt`（两个互不相交的源邻域、到像的 PL 同胚、实际环境 crossing、附近全部纤维由两片覆盖）。稳定性生产者 `exists_isSubdivision_stable_fiber_encard_le_two` 使用闭星注入半径和分离三点配置空间的紧致最小值。`faceStarComplex` 保留原单形，`isPLBall_faceStarComplex` 给出闭面星球性；`hasPLDoubleCrossingAt_and_exists_local_intersection` 构造两片及局部一维交集；`isCombinatorialManifoldWithBoundary_one_of_locally_eq` 经径向 link 不变性把局部结论传给精确全局奇点图。边界范围已核对：`injOn_boundaryComplex_of_transverse_faces` 证明欧氏自由横截条件强制源边界单射，因此不能代替 §25 允许边界双点的受约束版本。已完成受约束点生产者 `exists_small_affineIndependent_subsets_relative`、`exists_small_affineIndependent_subsets_in_submodule`、`exists_small_affineIndependent_subsets_in_halfSpace`：固定点族的相对扰动、边界维数与环境维数的独立性条件、核平面及严格正侧保持。`exists_small_vertexMap_transverse_in_halfSpace` 给出任意小边界相容通用顶点映射：相交的不交面若全部顶点在边界，其方向空间之和等于核平面，否则等于整个环境；两个方向生产者为 `vectorSpan_sup_eq_submodule_of_affineIndependent_subsets` 和 `vectorSpan_sup_eq_top_of_affineIndependent_subsets_relative`，原自由版本已改为相对定理的推论。聚焦检查 exit=0 零 warning；AuditF78 的 109 声明（SingularGeneralPosition 105，BoundaryInvariance 4）（GeneralPosition 162 声明此前由 AuditF74 验证）仅 propext、Classical.choice、Quot.sound 或无公理；源码 `83e2905b0` 已推送。`exists_small_simplicialMap_transverse_in_halfSpace` 已把点生产者接到有限组合曲面：对原本映入闭半空间且边界平面原像恰为源组合边界的 PL 映射，给出任意小扰动、闭星 PL 同胚、局部单射、至多两点纤维、全载体半空间保持、原源边界零集保持、各面单射和分层横截。`linearMap_simplicialMap` 与三个非负/零集引理证明正重心权重下零集只由顶点零集决定。`HasPLBoundaryCrossingAt` 新增独立边界模型：同一个环境半空间内的两个半平面，交线存在归一化共同内向向量；旧 `HasPLCrossingAt` 的语义不变。`halfSpace_eq_of_linearMap_pos`、`exists_common_inward_vector_of_sup_eq_ker` 给出正侧锥和公共内向方向；`hasPLBoundaryCrossingAt_of_halfSpace_cones` 构造环境 PL 平移模型；`eventually_mem_space_iff_mem_unique_coface_cone` 与 `hasPLBoundaryCrossingAt_of_unique_cofaces` 把两条各有唯一邻面的边接到该边界模型。`neighbors_singleton_of_eventually_nonneg_ray` 证明有限一维图的局部半射线芽迫使该顶点恰有一个邻点；`exists_nonneg_ray_eq_inter_halfSpace_cones` 与 `eventually_mem_inter_iff_nonneg_ray_of_halfSpace_cones` 已从互补边界方向及共同正侧生产该射线芽，`neighbors_singleton_of_unique_cofaces` 已把实际三角剖分的两条唯一邻面边接到度数一结论。`exists_isCombinatorialManifoldWithBoundary_inter_in_halfSpace` 已从有限带边组合曲面的非负顶点、零面位于组合边界及分层横截，构造精确交集的一维带边组合流形，并证明边界平面上的交点度数一；支撑为 `linearMap_eq_zero_iff_of_mem_openSimplex`、`IsCombinatorialManifoldWithBoundary.exists_unique_coface_in_halfSpace`、`neighbors_of_inter_in_halfSpace`。GeneralPosition 的维数界推广为 `card_add_finrank_sup_le_of_subset_faces`，当前载体面邻点分类提取为 `neighbors_singleton_or_pair_of_transverse_face`，旧端点签名保持。`IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_of_faces_subset` 证明同维子复形继承原边界余维一面；`boundaryComplex_space_of_isPLHomeomorphOn_of_isPLBall`、`IsPLHomeomorphOn.mem_boundaryComplex_image` 和 `boundary_faces_of_simplicialImage_of_faces_subset` 把该性质传给闭星的单射像。半空间交集及邻点定理新增 `_of_boundary_edges` 主版本，只要求零高度的边及更高维面位于边界；旧全零面接口保留为推论。`exists_local_intersection_at_doublePoint_in_halfSpace` 已把两个原像闭星的单射像接到局部一维交集；`exists_triangulation_doublePointSet_finrank_sup_le` 给出实际方向空间之和的维数界，原自由版本保留为推论；`exists_isCombinatorialManifoldWithBoundary_doublePointSet_in_halfSpace` 给出精确全局奇点图的一维带边组合流形性。`exists_small_simplicialMap_doublePointSet_manifold_in_halfSpace` 对原本正常映入半空间的 PL 2-球（边界平面原像恰为源边界）组合任意小扰动、源细分、闭星 PL 同胚、局部单射、至多两点纤维、半空间/原边界零集保持及精确奇点图流形性。`HasPLBoundaryDoubleCrossingAt` 给出两个互不相交的源邻域到像的 PL 同胚、共同半空间 crossing 及附近全部纤维覆盖。`hasPLCrossingAt_or_hasPLBoundaryCrossingAt_of_transverse_faces` 同时保留边界交集的具体内向半射线；`exists_local_intersection_with_crossings_at_doublePoint_in_halfSpace` 将其传给实际奇点集。`exists_isCombinatorialManifoldWithBoundary_doublePointSet_with_crossings_in_halfSpace` 与 `exists_small_simplicialMap_doublePointSet_with_crossings_in_halfSpace` 已把正侧普通 crossing、零高度边界 crossing 和精确全局奇点图在零高度顶点的度数一接到扰动端点。旧较弱端点保留为推论。`IsCombinatorialManifoldWithBoundary.codimension_one_cofaces_of_notMem_boundary` 与 `neighbors_eq_pair_of_transverse_face` 证明两张曲面均处于内部时的度数二；原无边界余维一面定理已改为推论。`geometricLink_faceStarComplex`、`mem_boundaryComplex_faceStarComplex_faces_iff`、`mem_boundaryComplex_faceStarComplex_space_iff` 保持闭星中心载体面及其相对内部点的边界类型；固定三角剖分版本 `isCombinatorialManifoldWithBoundary_inter_in_halfSpace_of_boundary_edges`、`neighbors_eq_pair_of_inter_in_halfSpace_of_notMem_boundary`、`neighbors_eq_pair_of_eventually_eq` 提供把局部内部交点度数二传给精确奇点图的接口。`exists_local_intersection_with_crossings_and_degrees_at_doublePoint_in_halfSpace` 已接回两个实际原像的闭星，证明避开源边界像的双点在局部奇点图中度数二；`exists_isCombinatorialManifoldWithBoundary_doublePointSet_with_degrees_in_halfSpace` 将其传给精确全局奇点图；`exists_small_simplicialMap_doublePointSet_normal_form_in_halfSpace` 闭合正常映入半空间的圆盘版本，零高度奇点度数一，正侧奇点度数二，并保留两类 crossing。旧三个端点保持签名并改为推论。`simplicialMap_indicator_compl_subcomplex_eq_zero_iff` 在重心细分上构造零集恰为任意子复形的非负 PL 函数；`exists_small_simplicialMap_in_halfSpace_of_subcomplex` 对任意有限源复形，在固定整个指定子复形映射的同时，将其余点推入严格正侧，保持任意小误差、闭星 PL 同胚、局部单射与至多两点纤维。`exists_small_simplicialMap_doublePointSet_normal_form_in_halfSpace_of_maps_boundary` 已去掉初始内部严格正侧条件，只要求全圆盘映入闭半空间且源边界映到零平面；原正常映射端点保持签名并改为推论。`singleton_mem_faces_of_eventually_nonneg_ray` 证明局部半射线的端点必为复形顶点；`mem_boundaryComplex_one_space_iff` 将一维组合边界识别为度数一顶点；`boundaryComplex_one_space_eq_inter_of_rays_and_degrees` 排除零平面中的边内部点。`exists_small_simplicialMap_doublePointSet_with_boundary_in_halfSpace` 新增精确等式：奇点图组合边界 = 奇点图与零平面的交集。`exists_small_simplicialMap_doublePointSet_normal_form_in_halfSpace_in_boundary_neighborhood` 只要求 B′ 是原源边界像在零平面内的逐点相对邻域，便保持整个扰动后源边界像及全部边界奇点留在 B′；保留任意小误差、正常化、两类 crossing 和完整度数分类。半空间模型及其边界邻域约束已闭合。新增 `BoundaryInvariance.lean`：`isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision`、`boundaryComplex_space_of_isSubdivision`、`mem_boundaryComplex_space_iff_of_isPLHomeomorphOn`、`boundaryComplex_space_of_isPLHomeomorphOn`，把组合边界不变性推广到任意正维有限带边组合流形。半空间主端点 `exists_small_simplicialMap_doublePointSet_with_boundary_in_halfSpace` 的源已推广为任意有限带边组合 2-流形，两处圆盘消费者已同步；原 PL 球边界搬运端点保持签名并成为一般定理的推论。`doublePointSet_comp_of_injOn` 给出任意单射后复合的精确奇点集等式；`exists_triangulation_doublePointSet_comp_of_isPLHomeomorphOn` 沿目标 PL 同胚搬运精确奇点图、一维组合流形性及组合边界。独立边界模块避免共享检出重编旧模块时覆盖本车道新增导出。`PLHomeomorphOpen.lean` 给出开放 PL 同胚与 `OpenPartialHomeomorph` 的转换，以及任意源 PL 同胚的局部坐标后复合；`HasPLCrossingAt.image_openPartialHomeomorph`、`HasPLBoundaryCrossingAt.image_openPartialHomeomorph` 搬运两种 crossing，两个 `postcomp_openPartialHomeomorph` 双点端点同时保留不交源邻域、到像的 PL 同胚及附近完整纤维覆盖。两模块聚焦检查 exit=0 零 warning；AuditF79 共 116 声明（边界 4、开放 PL 同胚 3、奇点 109）仅标准三公理或无公理，源码 `37c102e29` 已推送。`SingularChart.lean` 的 `exists_small_map_doublePointSet_normal_form_in_halfSpace_chart`、`exists_small_map_doublePointSet_normal_form_in_boundary_chart` 完成整幅像落在一张 PL 边界图卡内的版本：复用统一复合半径控制逆图卡误差及留在定义域，保留源细分、闭星 PL 同胚、局部单射、至多二重纤维、映射留在 M、源边界恰映到 Bd M、边界像留在 B′、精确奇点图及其组合边界等式、两类 crossing；源允许任意有限带边组合 2-流形。`HasPLBoundaryCrossingAt.congr` 与 `HasPLBoundaryDoubleCrossingAt.congr_target` 允许用相同局部集合替换目标。两模块检查 exit=0 零 warning，AuditF80 共 121 声明（边界 4、开放 PL 同胚 3、奇点 111、图卡 2、复用分析端点 1）仅标准三公理或无公理，源码 `2e43f59a0` 已推送。共享 olean 的 PLImage/PLBallSphere 新旧声明碰撞后，在 D 的 `.lake/scratch/f-lib` 保存完整 DifferentialGeometry olean 快照；仍用 check-f.ps1/audit-f.ps1，仅读写此项目快照，外部包仍读 E，编译参数与单进程规则不变；按 D 源聚焦重检 PLImage 已通过，不再覆盖 E 的项目 oleans。`HalfSpacePerturbation.lean` 为多图卡拼接补充保持边界的环境延拓：`exists_piecewiseAffine_lipschitz_vertex_function_vanishing_on_hyperplane` 裁剪内部顶点权函数，在边界平面上为零，保持原复形插值、支撑和 Lipschitz 性；`exists_isPLHomeomorphOn_extension_of_small_vertex_perturbation_preserving_halfSpace` 将任意阈值内、边界顶点留在平面的扰动延拓为任意小、指定邻域外恒同的环境 PL 同胚，且逐点保持高度为零及非负的充要条件。通过法向 Lipschitz 控制证明两侧不互换，未把边界不变性作为结论型假设。聚焦检查 exit=0 零 warning，AuditF81 两端点仅标准三公理，源码 `03fcb6389` 已推送。`HalfSpaceGeneralPosition.lean` 的 `exists_small_vertexMaps_transverse_in_halfSpace` 对两个带标签顶点族同时扰动，保持高度为零的充要条件与非负性，各至多三点子族仿射无关；相交面在边界平面中张成核，其他情形张成全空间。`exists_small_homeomorphs_transverse_in_halfSpace` 将两片的扰动分别延拓为任意小、指定共同邻域外恒同、保持半空间的环境 PL 同胚，并与各自单纯映射在整片上相等。聚焦检查 exit=0 零 warning，AuditF82 连同半空间延拓共四端点仅标准三公理，源码 `6cdf0c738` 已推送。`exists_small_homeomorphs_generalPosition_in_halfSpace` 将横截面条件落实为两片移动后的有限一维带边交集和每点 crossing；`exists_small_homeomorph_generalPosition_in_halfSpace` 再用第二片的逆同胚固定第二片，得到任意小、指定共同邻域外恒同、保持半空间的单个环境 PL 同胚。输入仅要求两片是有限带边组合 2-流形、位于半空间、在高度零处属于各自组合边界；允许人工截取边界位于半空间内部，故该局部交集的所有端点不宣称都在高度零处。聚焦检查 exit=0 零 warning，AuditF83 连同延拓共六端点仅标准三公理，源码 `b201d541a` 已推送。两个 `Pasting.lean` 模块完成局部修改的粘合层：一般拓扑端点证明接缝像邻域内恒同的分片后复合保持局部单射；集合端点对任意重数上界证明单张源片修改后的纤维计数，并给出支撑外精确纤维不变。`exists_piecewiseAffineOn_postcomp_on_polyhedron_of_locallyInjective` 将其接到闭多面体分解，保留 PL 性、局部单射、至多二重纤维及两片上的精确公式；仅要求目标修改是单射 PL 映射，不要求额外的逆映射或满射。接缝像须避开支撑闭包，未把接缝处相等误用为局部单射保证。聚焦检查均 exit=0 零 warning，AuditF84 六端点仅标准三公理，源码 `6c0101276` 已推送。`SingularPasting.lean` 的 `exists_isPLBall_patches_at_doublePoint` 从原始局部单射、至多二重的 PL 映射与实际双点构造两张不交 PL 球源片、闭多面体余片及任意指定邻域内的扰动支撑；支撑闭包避开接缝像，附近全部纤维由两片覆盖，余片上方保持单射。`exists_isPLBall_postcomp_neighborhood_at_doublePoint` 将任何在该支撑外恒同的单射 PL 后复合粘回全源，保持局部单射、至多二重、逐点误差控制、整张源片上的复合公式和支撑外精确纤维。源维数为任意正维。聚焦检查 exit=0 零 warning，AuditF85 四端点仅标准三公理，源码 `3179a4cb4` 已推送。`Topology/Homeomorph/Conjugate.lean` 的 `OpenPartialHomeomorph.conjugateHomeomorph` 将图卡目标中紧支撑的同胚共轭并延拓为原空间全局同胚；显式正逆公式、图卡外恒同、局部集合模型保持和统一误差半径均已证。`ChartConjugate.lean` 的 `isPiecewiseAffineOn_conjugateMap`、`isPLHomeomorphOn_conjugateHomeomorph`、`isPL_conjugateHomeomorph` 证明该延拓分别具有欧氏 PL 性、PL 同胚性和任意维抽象 PL 流形上的 PL 性；连续性与 PL 性在图卡边缘由紧支撑的恒同邻域证明。两模块聚焦检查 exit=0 零 warning，AuditF86 共十三声明仅标准三公理，源码 `95ef721ed` 已推送。`PLMap.lean` 的 `IsPLAt.comp_isPLWithinAt`、`IsPL.comp_isPLOn`、`IsPL.comp` 和 `IsPLOn.piecewise_postcomp_of_isClosed` 补齐抽象目标上的 PL 后复合与接缝邻域恒同粘合。`SingularPasting.lean` 的源片生产者新增 `_of_continuousOn` 主版本，目标只需 Hausdorff 正则空间，旧欧氏签名保留为推论；`exists_isPLBall_postcomp_neighborhood_at_doublePoint_in_manifold` 将实际双点的局部修改接到抽象带 PL 图册的目标，保留全源 PL 性、局部单射、至多二重及支撑外精确纤维。两模块聚焦检查 exit=0 零 warning，AuditF87 十个端点仅标准三公理，源码 `03a9c146f` 已推送。`098a404b5`：抽象目标流形上的双点局部修改现在同时保护任意有限族紧致单射源片，并在每片上给出与原映射或同一个目标后复合的精确相等；`Topology/Pasting.lean` 与 `SingularPasting.lean` 聚焦检查 exit=0、零 warning，F88 审计 11 个声明只有标准三公理。`0c86d10e5`：`GeneralPosition.lean` 新增无固定面横截假设的 `exists_small_vertexMap_transverse_off_fixed`，非横截交集必局限于固定顶点凸包；`exists_small_homeomorph_generalPosition_off_subcomplex` 给出固定指定子复形、其外全部 crossing 的任意小支撑 PL 同胚。原三个相对选择端点保留签名并成为推论。聚焦检查及 SingularGeneralPosition、HalfSpaceGeneralPosition 下游检查均 exit=0、零 warning；F89 审计 GeneralPosition 全部 166 个声明只有标准三公理。固定子复形边缘的 crossing 保持尚需证明，此结果不等于一般 M 正规形式。`e07a2eaf4`：`SingularPasting.lean` 的 `exists_isPLBall_patches_at_doublePoint_within` 将双点两张紧致 PL 球源片的整个像同时收进任意给定目标邻域，保留补片、接缝避让、单射性和附近完整纤维覆盖；原连续映射端点成为推论。聚焦检查 exit=0、零 warning；F90 审计该文件 8 个声明只有标准三公理。`2f9d771cb`：新增 `SingularLocal.lean`，`exists_small_piecewiseAffineOn_doublePointSet_crossing_neighborhood` 已实际构造三维欧氏目标中双点的支撑局部正规形式：任意小 PL 修改、全局局部单射与纤维数 ≤2、给定目标邻域外纤维完全不变，在含原双点的开邻域内真实双点集精确等于有限带边一维组合流形且全部满足 HasPLDoubleCrossingAt；另有内部/边界双片 crossing 到真实双点 crossing 的拼接引理。`SingularPasting.lean` 新增 `exists_isPLBall_patches_at_fiber_pair`，可同时指定两原像点及各自源邻域，供内外嵌套源片使用；`PLImage.lean` 增加 IsPLBall.isPolyhedron 并复用。四模块聚焦检查 exit=0、零 warning；F91 审计 25 个声明只有标准三公理。仍仅为局部正规形式，未宣称一般 M 的有限多图卡闭环。`e029bbec9`：`PLHomeomorph.lean` 将多面体限制证明推广到 IsPiecewiseAffineWithinAt，原 On 端点保留签名为推论；`PLMap.lean` 新增 IsPLWithinAt/IsPLOn.mono_of_isPolyhedron 及 `isPLOn_iff_isPiecewiseAffineOn_comp_chart`，使抽象目标流形上的 PL 映射可在紧致源片上转为指定图卡中的逐片仿射映射。聚焦检查及 SingularPasting、SingularLocal 下游检查均 exit=0、零 warning；F92 审计 21 个声明只有标准三公理。`4e8a4536c`：`PLMap.lean` 的 `IsPLOn.exists_isPLHomeomorphOn_chart_image` 从抽象目标 PL 映射、紧致多面体源域和单射性构造指定图卡中的有限像复形及 PL 同胚；`Pasting.lean` 的 `exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective` 推广局部修改到流形值映射，保留局部单射、纤维数 ≤2、两片精确相等及支撑外完整纤维。SingularPasting 原抽象双点修改已改为调用此通用端点。检查及下游 SingularLocal 均 exit=0、零 warning；F93 审计 24 个声明只有标准三公理。`96648a384`：新增 `SingularManifoldLocal.lean`，`exists_small_isPL_homeomorph_generalPosition_in_chart` 在任意度量 PL 三维流形的指定图卡内构造有紧支撑的任意小环境 PL 同胚，使两张坐标源片达到一般位置；`exists_small_isPLOn_doublePointSet_crossing_neighborhood_in_chart` 从实际双点构造局部正规形式，保持全源 PL 性、任意小误差、局部单射、纤维数 ≤2 及指定邻域外精确纤维。局部奇点集在图卡内精确由有限带边一维组合流形表示；crossing 的源域显式限制在图卡真实定义域的原像，排除域外默认值产生伪双点。聚焦检查 exit=0、零 warning；F105 审计两个端点仅标准三公理，已推送。`553156344`：`isCompact_doublePointSet_of_isLocallyInjective` 在任意拓扑源与 Hausdorff 目标中证明紧致源上的连续局部单射映射具有紧致双点集，不要求 PL 性或二重纤维上界；证明将非对角等纤维点对识别为紧致子类型积中的闭集。`exists_isOpen_forall_exists_small_isPLOn_crossing_in_chart` 将局部正规化邻域放在误差量 ε 的量词之前：同一个预先选定的开邻域可实现任意小扰动，原端点保持签名并成为推论。两模块聚焦检查 exit=0、零 warning；F106 审计全部 115 个声明仅标准三公理或无公理，源码已推送。多图卡归纳的确切数学缺口是同时保持先前保护区域与新区域内所有实际双点的 crossing；`exists_small_homeomorph_generalPosition_off_subcomplex` 只给固定子复形外的 crossing，未控制其边缘。不能由 C0 小扰动推出 crossing 保持：平面折线 y=max(-x,0) 与 y=abs(x)/2 在原点交叉，将后者向右平移任意 δ>0 后，在 x=δ 与前者切触；沿第三坐标取积给三维 PL 双片反例。须补含图卡折点与固定子复形边缘控制的相对一般位置构造，不能增加结论型假设或据此标记 F5.2 done。仍待：完成 §25 对一般带边三维流形 M 的有限多图卡相对扰动与拼接；单张边界图卡内的完整正规形式已闭合。现有欧氏 crossing 定义保持原语义，不把欧氏端点称作整个 F5.2 完成。 | 4k–8k |
| F6.1 | PL 流形中的紧致多面体 | `structure PolyhedronIn (n) (M) [ChartedSpace ℝⁿ M]`（有限复形 `K ⊆ ℝᴺ`、映射 `g`、`BijOn g K.space P`、逐图卡两向 PL）；`IsPolyhedralManifoldWithBoundary 3 (P : Set M)`；`M` 中多面体 3-胞腔 / 2-球面 / CST 的定义；"落在一个 `Int \|St v\|`（即一张图卡）内的多面体对象可搬到 ℝ³" | §23 以后所有流形层陈述 | partial（2026-09-13）：`PolyhedronIn.lean`——`PolyhedronIn n X P := PLPiece n X P`（T2 的 `PLPiece` 即所需结构），`IsPolyhedralBall m P`/`IsPolyhedralSphere m P`（存在一个 PL 片其复形空间是 PL 球/球面），落在一张图卡内的片经 `e ∘ g` 搬到 `ℝⁿ`：`PLPieceIn.isPLHomeomorphOn_chart_image`、`isPolyhedron_chart_image`、`IsPolyhedralBall.isPLBall_chart_image`，反向 `isPolyhedralBall_of_isPLBall_chart`；2026-09-14 砖 1 完成：`PieceTransition.lean`——`PLPieceIn.isPiecewiseAffineOn_transition`、`PLPieceIn.isPLHomeomorphOn_transition`，球/球面的 `isPLBall_of_piece`/`isPLSphere_of_piece` 与 `isPolyhedralBall_of_pieceIn`/`isPolyhedralSphere_of_pieceIn`；路线为共同图卡局部复合及片双射的逆，正向过渡不要求目标环境有限维。聚焦检查 exit=0、零 warning，AuditF18 六端点仅标准三公理；源码提交 `d5fdb2d33` 已推送；2026-09-14 砖 2 完成：`ManifoldInvariance.lean`——细分的反向流形不变性、`IsCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn` / `IsCombinatorialManifold.of_isPLHomeomorphOn`，及 PL 球/球面的组合流形推论。零维用有限载体排除非退化线段，正维用 link 细分不变性；反向细分只要求细分复形有限。聚焦检查 exit=0、零 warning，AuditF19 六端点仅标准三公理；源码提交 `46963b844` 已推送；2026-09-14 砖 3 完成：`PieceRestrict.lean`——`IsPiecewiseAffineWithinAt` / `IsPiecewiseAffineOn` 的 `inter_of_isPolyhedron`、`inter_preimage_of_isPolyhedron`，`PLPieceIn.restrict` 及 `restrict_complex`、`restrict_map`。有限多胞形族作乘积并取交，交集限制无需有限维假设；片限制保持原映射且双向图卡 PL。聚焦检查 exit=0、零 warning，AuditF20 七端点仅标准三公理；源码提交 `96eaa7048` 已推送；2026-09-14 砖 4 完成：`PolyhedralManifold.lean`——`IsPolyhedralManifoldWithBoundary` / `IsPolyhedralManifold`，选片无关、从任意有限维片引入、紧致性、球/球面的流形推论及无边界到带边界转换。聚焦检查 exit=0、零 warning，AuditF21 两定义及九端点仅标准三公理；源码提交 `d76a084f8` 已推送。F6.1 的片、球/球面及多面体流形基础 API 已完成；CST 专用对象随对应消费者落实 | 3k–5k |
| F6.2 | 开子集的局部有限三角剖分与穷竭（Moise 8.2/8.3 的 PL 版） | `theorem exists_exhaustion_of_isOpen ... : ∃ N : ℕ → Set M, (∀ i, IsCompact (N i) ∧ IsPolyhedralManifoldWithBoundary (m + 1) (N i) ∧ N i ⊆ interior (N (i + 1))) ∧ ⋃ i, N i = U`；另需 F6.3 的相容局部有限三角剖分 | §35.1–35.2（局部有限性）、§36.1 | partial（穷竭端点 done，局部有限三角剖分未做；2026-09-15 核对）：`ExhaustionGeneral.lean` 的 `exists_exhaustion_of_isOpen` 适用于任意 Hausdorff、第二可数、非空 PL `(m+1)`-流形，无紧致性假设；每项紧致且为带边多面体 `(m+1)`-流形，`N i ⊆ interior (N (i+1))`，并集恰为给定开集。生产者、聚焦检查与 AuditF26 记录保持有效。该穷竭不提供相邻有限片三角剖分的延拓相容性，故不能单独表示 35.2 所需的非紧多面体。 | 8k–15k |
| F6.3 | 局部有限三角剖分塔（有限片上升、内核不再重分） | 拟定：`structure LocallyFinitePLTriangulation (n) (U : Set M)` 表示可非紧、局部有限的复形实现；`theorem exists_locallyFinitePLTriangulation_of_isOpen` 同时给出穷竭 `N i` 与有限片 `T i`，使 `T (i + 1)` 在 `N i` 上严格延伸 `T i`、以后各层不再重分该内核，且余极限局部有限并实现 `U` | E.1、E.2、E.3 | new（表示层缺口；必须先于 E 终局闭合） | 4k–8k |
| T1 | `CombinatorialManifoldPLStructure n`（`Polyhedron.lean` 已陈述） | 有限组合流形的实现有与线性结构相容的 PL 图册（图卡 = 顶点 star 的 PL 参数化，用 F3.3） | §35–36 把多面体层结论搬回图册 | done（2026-09-13）：`combinatorialManifoldPLStructure : ∀ n, CombinatorialManifoldPLStructure n`（`CombinatorialZero.lean`；`n+1` 情形 `combinatorialManifoldPLStructure_succ` 在 `VertexChart.lean`：顶点开星 `openStar`（`OpenStar.lean`）经星同胚 `starHomeo` 拉回到标准单形的开单形，再经 `stdProj`/`stdLift`（`StdChart.lean`）投到 `EuclideanSpace ℝ (Fin (n+1))` 的开集 `stdTarget`；图卡族 `vertexChartAt`，转移映射由 PL 复合给出 `vertexChart_trans_mem_plGroupoid`；`n = 0` 情形离散） | 4k–6k |
| T2 | `PLManifoldTriangulation n`（已陈述） | 紧致 PL 流形有组合三角剖分（沿有限 PL 图卡归纳，用 F1.2、F2.3、F3.3） | §35.2 应用于 `M₁` 的紧致片 | **done**（2026-09-13）：`plManifoldTriangulation : ∀ n, PLManifoldTriangulation n`（`Combinatorial.lean`）；T2.e **done** `StarComplex.lean`（顶点星复形 `starComplex`，`geometricLink_starComplex`，link 沿单纯同构搬运 `IsGlueIso.geometricLink`/`IsGlueIso.isPLSphere_geometricLink`）+ `Combinatorial.lean`（`exists_isSubdivision_closedStar_subset`：细分至网格小于图卡覆盖的 Lebesgue 数的一半，每个顶点的闭星落入某图卡；`PLPieceIn.isPLSphere_geometricLink`：星复形经 F3.1 后由 `e ∘ g` 单纯嵌入 `ℝ^(m+1)`，像是像顶点的邻域（用 `PLPieceIn.isPiecewiseAffineOn_chart_symm` 的连续性），`isPLSphere_geometricLink_of_mem_nhds` 给出 PL 球面 link，再经 link 的细分不变与单纯同构搬回；`n = 0`：图卡把 `X` 变成离散空间，边的像连通故不存在）。路线记录：T2.a **done** `PLImage.lean`（`IsPolyhedron.image_of_isPiecewiseAffineOn`、`IsPLHomeomorphOn.isPolyhedron_preimage`、`.restrict`、`exists_isPLHomeomorphOn_image`）；T2.b **done** `RelativeDerived.lean`（相对导出细分 `relDerived`：`relDerived_isSubdivision`、`faces_subset_relDerived`——子复形 `L` 的细分 `L'` 延拓为 `K` 的细分且 `L'` 是其子复形；面 = `L'` 的单形 ∪ `K∖L` 中一条旗的内点，唯一性经沿射线剥离顶点）；T2.c **done** `Gluing.lean`（`PLPieceIn.glue`：两片 `PLPieceIn` 沿子复形的单纯同构 `IsGlueIso` 粘接为 `E₁ × E₂ × ℝ` 中的一片；实现：顶点映射 `glueEmbed₁ v = (v, ψ v, 0/1)`、`glueEmbed₂ w = (ψ' w, w, 0/-1)` 给出带仿射左逆的单纯嵌入 `embedComplex`，高度坐标使两复形恰交于被识别的子复形——要求该子复形在第一侧是满的（full），由相对导出细分 `relDerived` 保证；粘接映射逐片定义，PL 条件经 `IsPiecewiseAffineOn.union_of_open`）；T2.d **done** `ChartPiece.lean`（图卡片 `chartPiece`：`e.symm '' C`，`C` 为 `e.target` 内的 H-多胞形）、`Subcomplex.lean`（子复形 `restrict K Q`、F2.3 的推论 `exists_isSubdivision_restrict_isSubdivision`）、`SubdivisionTransport.lean`（细分沿单纯同构搬运 `IsGlueIso.exists_isSubdivision`）、`ChartGlue.lean`（`PLPieceIn.exists_glue_chart`：重叠 `|K| ∩ g⁻¹(e.symm '' C)` 是多面体（紧致 + `isPolyhedron_inter_preimage_of_isCompact`），F2.3 使之成为子复形，F3.1 使 `e ∘ g` 在其上逐单形仿射，像复形 `simplicialImage` 在图卡侧经 F2.3 细分对齐再搬回，两侧用 `relDerived` 延拓后用 T2.c 粘接）、`TriangulationExistence.lean`（`exists_pLTriangulation : Nonempty (PLTriangulation n X)`，紧致 T2 非空 PL 流形，有限图卡归纳 `exists_pLPiece_biUnion`）；注意：`PLManifoldTriangulation n` 增加了 `[Nonempty X]`（空流形没有 `PLTriangulation`，因 `map : ℝ^N → X`）；T2.e 组合性：细分至每个闭星落在某图卡内，F3.1 使图卡在星上逐单形仿射，像复形（`SimplicialImage`）是欧氏邻域的三角剖分，用 `isPLSphere_geometricLink_of_mem_nhds` 与 link 在细分下不变；`n = 0` 单独处理 | 6k–10k |

实现记录（2026-09-12）：F2 的导出细分按"每个面选一个内点、旗张成单形"的一般形式实现（`Derived.lean`），
重心细分是特例；`inter_subset_convexHull` 由"过一点的旗唯一"（顶面系数由该点决定，逐层剥离归纳）证明。
F1.2 与 F2.3 将共用同一套机制：H-多面体的（暴露）面、相对内部（Mathlib `intrinsicInterior`）、面的旗，
以及"从相对内点出发的射线恰交相对边界一次"，据此定义凸胞腔复形（交集复形 `σ ∩ τ`）的导出细分；
这是 F1.2/F2.3 的既定路线，估计合计 5k–10k 行。

实现记录（2026-09-13，F3.3）：link 唯一性按 RS 的伪径向投影实现，但不经"锥上的射线单调"论证：
对锥底 `L'` 的每个单形 `σ`，把顶点径向投影到 `L` 上再仿射延拓（`simplicialMap L' (radialProj p L.space)`），
该映射在以 `p` 为顶点、`σ` 为底的锥上是正对角线性映射，保持每个面上的锥，于是全局单射（`injOn_simplicialMap_radialProj`）；
像复形由通用构造 `SimplicialImage.lean`（单形仿射单射的单纯映射把有限复形映成 PL 同胚的复形）给出。
辅助模块：`Cone.lean`（径向单射性 `IsRadiallyInjective`、径向投影 `radialProj`、锥底 `IsConeBase`，顶点 link 是锥底，
闭星内每条射线交 link）。欧氏情形的证明：闭星是邻域 ⟹ 取小单形 `T`（`p` 在其开单形内且 `conv T` 是邻域），
用 F2.3 把各面锥 `conv (insert p (T.erase v))` 细分成子复形，再对细分后的 link 用伪径向投影到 `∂T`。

### 4.1 2D 输入与同调（车道 S 前半、车道 H）

| 编号 | 内容 | 拟定 Lean / 来源 | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| P.1 | 平面多边形 Schoenflies（Moise 3.6）与组合形式 5.3（多边形界定组合 2-胞腔） | 由 vendored `External/Schoenflies/`（拓扑平面版）导出多边形版，或直接按 Moise §3 组合证明；输出 `theorem isPLBall_of_isPLSphere_one {J : Set ℝ²} (hJ : IsPLSphere 1 J) : ∃ D, IsPLBall 2 D ∧ frontier D = J` | §17, §21.4, §26.7, §27.2 | done（2026-09-15）：`PolygonalSchoenflies.lean` 的 `exists_polyhedral_region_of_isPLSphere_one` 已由 PL 1-球面构造有界连通开区域，前沿等于原曲线，并给出闭包的有限三角剖分且原曲线是子复形；同时证明一般的 `isPolyhedron_closure_of_isPolyhedron_frontier`，`PLBallSphere.lean` 补 `IsPLSphere.isPolyhedron`。只消费 Jordan 分离，不消费拓扑 Schoenflies。两模块聚焦检查 exit=0、零 warning；`AuditF94.lean` 审计 22 项均仅标准三公理（包含所用 Jordan 端点）；源码提交 `99a798b7e` 已推送。补：`exists_isCutPair_isPLBall_of_isPLSphere_one` 给出指定两点的 PL 弧切分，`isPLBall_of_isArc_subset_isPLSphere` 证明圆周内任意弧的 PL 1-球性，`isPLBall_compl_openArc_of_isPLSphere_one` 证明删去开弧后的 PL 1-球性；同时闭合分片仿射闭路、子弧与拼接 API，并将 `PLPath.lean` 的 `isHPolytope_Icc` 的端点推广为任意实数。两模块检查 exit=0、零 warning；F95 审计 43 项均仅标准三公理，源码提交 `6bf5d9791` 已推送。`8985ab274`：`PLImage.lean` 闭合多面体上单射分片仿射满射的 PL 逆映射；`PLPiece.lean` 的 `IsPLHomeomorphOn.union` / `piecewise` 从精确交集像证明跨片单射性并粘接两侧 PL 同胚。`PolygonalSchoenflies.lean` 的 `exists_isPLHomeomorphOn_Icc_of_isArcBetween` 匹配指定弧端点，`exists_isPLHomeomorphOn_of_isCutPair` 同时匹配两条圆的两段边界弧和端点。三模块检查 exit=0、零 warning；F96 审计 54 项均仅标准三公理，源码已推送。`0a645e32b`：`exists_isPLHomeomorphOn_eqOn_arc_of_isPLSphere_one` 延拓给定公共弧映射到整个圆；`exists_isPLHomeomorphOn_eqOn_arc_of_boundaryComplex` 进而延拓到两个 PL 2-球之间，逐点保持给定弧映射。BoundaryExtension 与本模块检查 exit=0、零 warning；F97 审计 30 项均仅标准三公理，已推送。`3a7f41705`：`isPLBall_union_of_boundary_arc` 已证明两个平面 PL 2-球沿公共边界弧的并仍是 PL 2-球；先实际构造沿线段相交、并为一个三角形的两块三角形，再将给定公共弧同胚分别延拓到两盘并粘接。支撑 API `SimplexLink.lean` 的 `geometricLink_simplexComplex`和 `boundaryComplex_simplexComplex` 给出余面 link 与真面边界公式。三模块检查 exit=0、零 warning；F98 审计 45 项均仅标准三公理，源码已推送。`04be6b739`：`isPLSphere_one_of_isCutPair` 从两段 PL 弧构造 PL 圆，`isPLSphere_one_union_of_isCrosscut` 保证横截弧切分后的两条边界仍为 PL 圆；原圆匹配接口保留为更一般弧匹配定理的推论。`PlanarJordan/Regions.lean` 的 `frontier_closure_inside` 确认闭区域的前沿仍是原曲线，`closure_inside_union_of_isCrosscut` / `closure_inside_inter_of_isCrosscut` 给出两侧闭区域的并恰为原闭区域、交恰为横截弧。仅消费 Jordan 分离和多边形弧领圈；两模块检查 exit=0、零 warning；F99 审计 40 项均仅标准三公理，已推送。`b40f5411c`：`restrict_closure_space_of_frontier_subset_subcomplex` 允许屏障子复形包含区域前沿且与内部不交；原前沿等式接口保留。`restrict_closure_inside_space_of_isCrosscut` 使两侧闭区域继承原有限三角剖分，并证明其空间的并、交公式。检查 exit=0、零 warning；F100 审计 41 项均仅标准三公理，源码已推送。`a702d805a`：`BoundaryInvariance.lean` 的 `boundaryComplex_space_subset_frontier_of_finrank` 证明同维组合流形的组合边界不进入环境内部；`PlanarJordan/Regions.lean` 证明 Jordan 圆周子集必相等并抽出弧唯一性。`PolygonalSchoenflies.lean` 因而识别侧区域的组合边界与几何边界，`isPLBall_closure_inside_of_isCrosscut` 将两侧 PL 2-球沿横截弧粘为原闭区域的 PL 2-球。三个模块检查 exit=0、零 warning；F101 审计 54 项均仅标准三公理，源码已推送。`e6b9bd078`：`Combinatorial.lean` 证明有限复形中开区域闭包由满维单形覆盖，并推出每个面的满维上面存在性；`Subcomplex.lean` 补限制空间单调性、单形凸包与并集保持公式。`ncard_faces_card_restrict_closure_inside_lt_of_isCrosscut` 证明横截弧每一侧继承的三角剖分，其三角形数严格小于原剖分，不把降阶作为假设。三个模块检查 exit=0、零 warning；F102 审计 69 项均仅标准三公理，源码已推送。`61054ac73`：`restrict_arc_space_of_isCutPair` 证明原顶点处切出的两段边界弧仍为子复形，`restrict_closure_inside_boundary_space_of_isCrosscut` 保证侧区域的新边界直接沿用原剖分；`isCrosscut_segment_of_mem_faces` 从内部边实际构造横截弧。`exists_triangle_with_boundary_edge` 从 PL 圆周的一条边和满维覆盖产生边界邻接三角形；闭区域剖分接口另以 `exists_triangulation_closure_inside_of_isPLSphere_one` 精确保留 inside 闭包。支撑 API 补 PL 球面非空性和二次限制公式。四模块检查 exit=0、零 warning；F103 审计 87 项均仅标准三公理，源码已推送。`8b87ef710`：`isPLBall_or_exists_isCrosscut_of_triangulation` 从边界邻接三角形实际证明终止情形或沿现有边构造横截弧；`isPLBall_space_of_triangulation_closure_inside` 对三角形数强归纳，侧区域严格降阶并沿公共 PL 边界弧粘回。最终端点 `isPLBall_closure_inside_of_isPLSphere_one` 与 `isPLBall_of_isPLSphere_one` 已闭合：原 PL 圆周的有界内区域闭包是 PL 2-球，frontier 恰等于原曲线。`SimplexBoundary.lean` 同时证明任意满维单形的内部与前沿公式。两模块检查 exit=0、零 warning；F104 审计全部 73 个声明均仅标准三公理。源码已提交推送，P.1 完成。 | 5k–10k |
| P.2 | 5.4：多面体 2-胞腔边界间 PLH 延拓 | F3.4 的 `n = 2` 实例（锥延拓）加 5.3 | §17.10, §33 L13, §34 | new | 1k |
| P.3 | 3.3 / 17.2–17.3：2-胞腔的胞腔分解至少有两个自由 2-胞腔；不在给定真子复形中的自由胞腔 | 组合陈述（用 P.1 的分离性质） | §17.9–17.12 | new | 2k–4k |
| P.4 | 10.8：ℝ² 中有限线性图驯顺（给定开集 `U ⊇ M`、`φ ≫ 0`，存在同胚 `h : ℝ² ≃ₜ ℝ²`，`h(M)` 多面体，`U` 外恒同，`U` 上 φ-逼近恒同） | §10 定理 6–8（框架定理 10.6 + 收缩族） | §17.2（胞腔复形可视为多面体） | new | 6k–10k |
| P.5 | 2.7–2.8 θ-图、4.4 盘中两弧不分离、Problem 4.1 | 平面分离引理（可由本库 `Topology/PlanarJordan/*` 或 `SphereSeparation` 的 2D 情形推出） | §26.7, §27.2, §30.1 | new/nat | 2k–4k |
| H.1 | 有限复形的单纯 ℤ-链、边界、`H₁`、`H₂`、`H₃`，`p¹`（秩），`χ` 与 Euler–Poincaré | D3；本库 `EulerCharacteristic.lean` 的 `faceEulerChar` 复用 | §21–23, §24.8, §28, §31–§34 | new | 8k–12k |
| H.2 | 可定向性（23.14 的 3-链定义；带边 `∂C³` 是 `∂K` 上的 2-循环）、23.15–23.17 | `def IsOrientable (K)`；子复形与二重覆盖的可定向性 | §24.7–24.8, §24.11, §26.8, §33 L11 | new | 3k–5k |
| H.3 | §21：开胞腔复形的 χ 与运算 α–δ 不变；21.6 `χ(J) = 0`；21.7 2-胞腔 `χ = 1`；21.8 加法；21.10–21.11 分裂与张成 | 组合陈述于多面体曲面 | §22, §23.18–19, §28.20, §30.4, §33 L7 | new | 4k–6k |
| H.4 | §22：22.5 `χ = 2 − (2h + m)`、22.6–22.7 `p¹` 与 `χ`、22.8–22.10 分类（可定向 + χ 决定同胚型）、22.11 单连通 ⟹ 2-球面、Problems 22.11–22.12 | 只对**多面体**紧致曲面陈述；22.9 用于 §33 L11–L12；22.11 用于 §30.6、§32；备选：移植 classification-of-surfaces 的 `classification_of_surfaces`（拓扑版，142k 行依赖，**不推荐**整体移植） | §26.8, §28.6, §30.4, §30.6, §32, §33 | new | 10k–18k |
| H.5 | 23.18–23.19：`h(B) = p¹(N)`（`dim L ≤ 1`）、`p¹(K) ≥ h(Bd \|K\|)`（可定向带边） | 用 23.11–23.16、H.3、H.4 | §24.8 | new | 4k–6k |
| H.6 | 28.11：`K = K₁ ∪ K₂`，`Zⁿ` 在 `K₁` 上、在 `K` 上零调 ⟹ `K₁` 上同调于 `K₁ ∩ K₂` 上的循环 | 单纯链的直接计算 | §31.4, §34 L4 | new | 1k |

### 4.2 车道 S：§17 PL Schoenflies（`chap:pl-schoenflies`）与 3-胞腔

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| S.1 | 17.1：ℝ³ 中闭 3-流形带边 `M` 有 `Bd M = Fr M` | D6 + F4.1 | §17.12, §23.8 | new | 1k |
| S.2 | 17.4–17.8 推移性质：3-单形对每个面有推移性质；PLH 保持；单嵌入 2-球面有推移性质 | `def HasPushProperty (C : Set ℝ³) (D₁ : Set ℝ³) : Prop := ∀ N, IsPolyhedron N → closure (C \ frontier D₁) ⊆ interior N → ∃ h : ℝ³ ≃ₜ ℝ³, IsPiecewiseAffineOn h univ ∧ h '' D₁ = closure (frontier C \ D₁) ∧ EqOn h id Nᶜ` | §23.10, §33 末, §34 | new | 4k–7k |
| S.3 | 17.9–17.11：凸多面体 3-胞腔边界单嵌入；2-胞腔与点的 join；两单嵌入球面交于平面 2-胞腔之并单嵌入 | 用 P.3 的自由胞腔删除归纳 | §17.12 | new | 4k–6k |
| S.4 | **17.12 PL Schoenflies** | `theorem exists_isPLBall_of_isPLSphere_two {S : Set ℝ³} (hS : IsPLSphere 2 S) : ∃ B, IsPLBall 3 B ∧ frontier B = S ∧ Bornology.IsBounded B`；证明：水平平面族一般位置（F5.1 变体）、指标 `Ind S` 归纳（L1–L6）、S.3 收尾 | §23.9, §28.1 后半, §30.5, §33 末 | new | 8k–12k |
| S.5 | 23.9–23.11 流形版：`Int \|St v\|` 内多面体 2-球面界定组合 3-胞腔；推移；两 3-胞腔交于 2-胞腔之并是 3-胞腔 | `theorem isPLBall_union_of_inter_isPLBall_two (h₁ : IsPLBall 3 C₁) (h₂ : IsPLBall 3 C₂) (hD : IsPLBall 2 (C₁ ∩ C₂)) (hD₁ : C₁ ∩ C₂ ⊆ frontier C₁) (hD₂ : C₁ ∩ C₂ ⊆ frontier C₂) : IsPLBall 3 (C₁ ∪ C₂)`（在图卡内） | F4.2 的 3D 部分、§23.12, §23.18, §26.2, §32 | new | 2k–3k |
| S.6 | 30.5：嵌套拓扑 3-胞腔 `C₁ ⊆ Int C₂`、`Cl(C₂ − C₁)` 球壳 ⟹ 中间有多面体 3-胞腔 | 用 30.4（车道 I）+ S.4；放在 I 完成 30.4 后收尾 | §34 L3 | new | 1k |
| S.7 | §33 末尾引用的 3-胞腔延拓（书中编号疑为笔误，§18 是 Antoine 集）：`Bd C_v ↔ Bd C''_v` 的 PLH 延拓到 3-胞腔 | S.4 + F3.4 | §33, §34 (5)–(7), §35 | new | 0.5k |

### 4.3 车道 C（1）：§23 三角剖分 3-流形

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| M.0 | 23.1（三角剖分 3-流形是组合流形） | **不需要**：本链所有三角剖分由构造是组合的（T2 经 F3.3；正则邻域经 F4.2；覆盖提升经 C.3）。记录以防有人误加 | — | skip | 0 |
| M.1 | 23.2 / 23.4：边界点的 3-胞腔邻域 `C³ ∩ Bd M = 2-胞腔` | 由 F4.1 的 link 是 PL 2-球直接给出（star 结构） | §26.2, Problem 26.1–26.3 | new | 1k–2k |
| M.2 | 23.5–23.7 倍化、`\|∂K\| = Bd \|K\|` | D2 下只需 `boundaryComplex_space_eq_frontier`（F4.1）；倍化仅 23.13/23.16 用，见 H.5 | H.5 | new | 1k–2k |
| M.3 | 23.8：`Bd M' = Fr M'`（闭带边 3-流形在 3-流形内） | D6 | §28.1 后半, §30.4, §36.1 | new | 0.5k |
| M.4 | 23.12–23.13, 23.16：`\|L\|` 与 `N(L)` 组合等价；带边流形是某 3-流形中子复形的正则邻域 | 用 S.5 反复；23.16 需 H.2 | §23.19（H.5） | new | 3k–5k |

### 4.4 车道 C（2）：§24 覆盖空间（`chap:pl-coverings`）

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| C.1 | 24.1–24.4：提升、诱导同态单射、`k`-重覆盖与指标 | `IsPLBall.simplyConnectedSpace`、`.locallyPathConnectedSpace`；`IsCoveringMap.exists_unique_lift_of_isPLBall`、`.injective_fundamentalGroup_map`、`.fundamentalGroup_stabilizer_eq_range`、`.monodromy_eq_iff_mem_range`、`.liftPath_one_eq_iff_mem_range`、`.fundamentalGroupMulAction_isPretransitive`、`.card_fiber_eq_index` | §25 | done（2026-09-15，`CoveringLift.lean`）：24.1–24.4 的九个桥接端点全部闭合；检查 exit=0、零 warning，AuditC1 九端点及 AuditC1Reuse 十八条 D4 复用声明均仅标准三公理，未经过 `HurewiczLowDegrees.lean`；源码提交 `2df0546f5`。 | 1k（桥接） |
| C.2 | 24.5（`k = 2`）：有限复形上的 ℤ₂ 1-上循环构造二重覆盖 | `SimplicialBoolCocycle K`、`IsCoboundary`、`toBoolCocycle`、`isCoveringMap`、`card_fiber = 2`、`connectedSpace_iff : ConnectedSpace TotalSpace ↔ ¬ IsCoboundary` | C.4, C.5 | done（2026-09-15，`DoubleCoverComplex.lean`）：开星上循环产生本库 `BoolCocycle` 二重覆盖；构造无不动点换层映射及两方向截面判据，连通当且仅当非上边界。检查 exit=0、零 warning，AuditC2 二十三端点及 AuditC2Reuse 十一条 D4 复用声明均仅标准三公理，未经过 `HurewiczLowDegrees.lean`；源码提交 `364fbe752`。 | 3k–5k |
| C.3 | 24.6：三角剖分提升到有限覆盖，且组合流形性保持 | `theorem exists_lift_simplicialComplex [FiniteDimensional ℝ E] (K) [Finite K.faces] {p : X' → K.space} (hp : IsCoveringMap p) (hfin : ∀ x, (p ⁻¹' {x}).Finite) : ∃ N (K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))) (e : K'.space ≃ₜ X'), K'.faces.Finite ∧ (∀ q (hq : q ∈ K'.faces), ∃ t ∈ K.faces, ∃ A, (∀ x (hx : x ∈ convexHull ℝ (q : Set _)), ((p (e ⟨x, K'.convexHull_subset_space hq hx⟩) : K.space) : E) = A x) ∧ A '' convexHull ℝ (q : Set _) = convexHull ℝ (t : Set E)) ∧ ∀ n, IsCombinatorialManifoldWithBoundary n K → IsCombinatorialManifoldWithBoundary n K'` | §25 L3 | done（2026-09-15，`CoveringTriangulation.lean`）：以基复形顶点的纤维为有限顶点集，每个基单形从指定纤维点唯一提升；重叠由提升唯一性粘合。标准基实现给出有限 `coveringComplex`，逐面映射粘为 `coveringSpaceHomeomorph`；顶点 link 的 `coveringVertexLink_isGlueIso` 搬运任意维带边组合流形性。此直接逐单形路线不需要先细分至均匀覆盖闭星。检查 exit=0、零 warning，AuditC3 十六端点及 AuditC3Reuse 三条 D4 复用声明均仅标准三公理，未经过 `HurewiczLowDegrees.lean`；源码提交 `f7e70bc61`。 | 4k–6k |
| C.4 | 24.7：不可定向连通带边多面体 3-流形有二重覆盖（且覆盖可定向，Problem 24.11） | 定向上循环 + C.2 | §25 L3 | new | 2k–3k |
| C.5 | 24.8：紧致连通可定向带边、某边界分支非 2-球面 ⟹ 二重覆盖 | H.5 的 `p¹ > 0` ⟹ `H₁ → ℤ₂` 满 ⟹ C.2 | §25 L3 | new | 2k–3k |
| C.6 | 24.9–24.10 CST 与柱形图、CST 两两组合等价 | `def IsCST (S : Set M)`（有限个 3-胞腔循环相邻交于 2-胞腔）；`exists_cylindricalDiagram` | §28, §30.7, §31 | new | 3k–5k |
| C.7 | 24.11–24.12：可定向 3-流形中多边形的正则邻域是 CST；可缩多边形的正则邻域是 CST（任意 `M`） | 用 F4.2、H.2、C.4 的定向传递（24.12 只需 28.19 的特例：`J = Bd Δ`，Problem 28.4 指出可直接证） | §28.19, §31, §34 L1 | new | 3k–5k |

### 4.5 车道 C（3）：§25 Stallings 环定理（`chap:dehn-loop`）

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| L.1 | 奇异 2-胞腔、`L(X)` 共轭类、正规系统 `[M₁, K₁, D, K(Δ), B₁, N₁]` 与复杂度 | 定义层 | L.2–L.4 | new | 2k–3k |
| L.2 | 25 L1：`B` 2-球面时（`B'` 为 `\|L\|` 的正则邻域是 `k`-环带，π 自由）直接得非奇异 `D₁` | 用 P.1 变体（球面上多边形界定 2-胞腔）、F4.2 | L.4 | new | 2k–3k |
| L.3 | 25 L2：局部同胚、至多 2 对 1 的 `D` 的四种情形（Case 1–4，切开与复杂度归纳） | F5.2 正规形式 + 柱形图（Figure 25.2）+ 基本群字计算（Figures 25.3–25.6） | L.4 | new | 8k–14k |
| L.4 | 25 L3 / **25.1**：对每个正规系统存在非奇异 `D'`（二重覆盖降复杂度：C.3–C.5，`g*` 指标 2 不满） | `theorem loop_theorem_stallings (hK : IsCombinatorialManifoldWithBoundary 3 K) (B : boundary component) (N : Subgroup (FundamentalGroup B.space P₀)) [N.Normal] (D : PL singular 2-cell with Bd D ⊆ B.space) (hD : loopClass (Bd D) ∉ N) : ∃ Δ ⊆ K.space, IsPLBall 2 Δ ∧ Δ ∩ (boundaryComplex K).space = frontier Δ ∧ frontier Δ ⊆ B.space ∧ loopClass (frontier Δ) ∉ N` | L.5 | new | 8k–12k |
| L.5 | **25.2 环定理第一形式**（可定向、`N = ⊥`） | `theorem loop_theorem (hK) (hor : IsOrientable K) (B) (L : loop in B) (hL : contractible in K.space) (hB : ¬ contractible in B.space) : ∃ Δ, IsPLBall 2 Δ ∧ Δ ⊆ K.space ∧ frontier Δ = Δ ∩ (boundaryComplex K).space ∧ ¬ contractible (frontier Δ) in B.space` | §26.4 | new | 1k |

### 4.6 车道 C（4）：§26 双领邻域与扩展环定理；ℝ³ 中的曲面

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| B.1 | 26.1：3-流形带边 `N` 的边界分支之并两侧（two sided）定义与命题 | `def IsTwoSided (M² : Set M³)` | §26.3, §30.4 | new | 1k |
| B.2 | Problems 26.1–26.3（27.1 用）：`Bd M³` 中多面体 2-胞腔 `d` 的任意邻域含多面体 3-胞腔 `C` 使 `d = C ∩ Bd M³`；`N ⊆ Int M³` 两侧各一 | 用 M.1、F4.2 | §26.2, §27.1 | new | 2k–3k |
| B.3 | 26.2 领邻域（紧致 `B = Bd M³` 有 PLH `ρ : B × [0,1] ↔ W`） | 对 `B` 的 2-胞腔分解归纳（用 B.2、S.5） | §26.3 | new | 3k–5k |
| B.4 | 26.3 双领邻域（紧致两侧多面体 2-流形 `M² ⊆ Int M³`） | `theorem exists_bicollar (hM : IsPolyhedralSurface M²) (h2 : IsTwoSided M²) : ∃ ρ : M² × Icc (-1) 1 → M³, PL embedding, ρ (P, 0) = P, range ρ ∈ 𝓝ˢ M²` | §26.4, §28.1 后半, §30.7 | new | 2k–3k |
| B.5 | **26.4 扩展环定理**（Papakyriakopoulos）：`M²` 紧致两侧、`ker i* ≠ 1` ⟹ 多面体 2-胞腔 `Δ`，`Δ ∩ M² = Bd Δ` 在 `M²` 中不可缩 | `theorem loop_theorem_two_sided (hK : IsCombinatorialManifoldWithBoundary 3 K) (hM : compact polyhedral 2-manifold M² ⊆ interior K.space) (h2 : IsTwoSided M²) (hker : ¬ Function.Injective (π₁-map)) : ∃ Δ, IsPLBall 2 Δ ∧ Δ ⊆ K.space ∧ Δ ∩ M² = frontier Δ ∧ ¬ contractible (frontier Δ) in M²`；证明：F5.1（相对 `Bd W`）、最内多边形三情形、L.5 | §30.4, §30.6, §30.7, §33 L9–L10 | new | 5k–8k |
| B.6 | 26.6：ℝ³ 中紧致连通多面体 2-流形两侧，且 `ℝ³ − M²` 恰两分支、`M²` 为公共边界 | 用 F5.1（`ρ(Δ)` 相对 `M²` 一般位置）+ 图的奇偶论证 + B.4 | §26.7, §30.6, §32 Type 2, §33 L5 | new | 4k–6k |
| B.7 | 26.7：三张带边曲面公共边界，其中一张在另两张之并的内部 | 2.7 的三维类比（P.5） | §32 Type 2 | new | 2k–3k |
| B.8 | 26.8：ℝ³ 中紧致连通多面体 2-流形可定向 | 用 S.4/S.5（放入 3-球面三角剖分）+ H.1 `H₃ ≅ ℤ` + 无 Möbius 带 | §33 L11 | new | 2k–4k |

### 4.7 车道 C（5）：§27.1–27.4 胞腔同胚（27.5 Dehn 引理 **skip**）

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| D.1 | 27.1：`Bd N` 上的胞腔 PLH `h : M² ↔ M²` 延拓为 `M³ ↔ M³`，`N ↔ N`，给定邻域外恒同 | B.2 + F3.4（两 3-胞腔的锥延拓） | §27.4, §28.2 | new | 2k–3k |
| D.2 | 27.2：PL 环带中两个不界定 2-胞腔的多边形经有限个胞腔 PLH 互变（边界固定） | 矩形图中的一般位置与 P.5 | §27.3, §27.4, §28.1 后半, §28.2 | new | 4k–6k |
| D.3 | 27.3：PL 环带内部多边形要么界定 2-胞腔要么携带 `H₁(A)` 与 `π(A)` 的生成元 | `theorem polygon_in_annulus (hA : IsPLAnnulus A) (hJ : IsPLSphere 1 J) (hJA : J ⊆ interior A) : (∃ D, IsPLBall 2 D ∧ D ⊆ A ∧ frontier D = J) ∨ carriesGenerator J A` | §31.4, §32 L2, §35 L1 | new | 1k |
| D.4 | 27.4：环带 `A ⊆ Bd N` 中 `J ↦ J'` 的 PLH `M³ ↔ M³`，`W` 外恒同 | D.1 + D.2 | §28.2, §28.13（skip） | new | 1k |

### 4.8 车道 C（6）：§28 CST 边界上的多边形（关键子集）

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| T.1 | 28.1 **后半**：ℝ³ 中 PL 实心环面 `S`，`Δ₁ Δ₂` 为两不交多面体 2-胞腔、`Δ_i ∩ Bd S = Bd Δ_i` 把 `Bd S` 分成两环带 ⟹ `S` 是 CST（两块 `D_i` 由 S.4 给出，`S ⊆ D₁ ∪ D₂` 由 M.3 + B.4 + 连通性） | `theorem isCST_of_two_meridian_disks ...` | §30.7 Case 2 | new | 3k–4k |
| T.2 | 纬向多边形 `J_x`、标准位置定义；28.2、28.3（经胞腔 PLH 把多边形放入标准位置，`W` 外恒同） | D.1, D.2, D.4 | T.3–T.7, §34 L11 | new | 3k–5k |
| T.3 | 28.4：标准位置下 `Z¹(J) ∼ n·Y¹` 于 `S` | H.1 | T.6 | new | 1k |
| T.4 | 28.6：`T` 上不交非平凡多边形 `J_i` 的补分支闭包是环带 | T.2 + H.4（可定向排除 Möbius） | §32 Type 2/3、"no fourth type" | new | 2k–3k |
| T.5 | 28.7, 28.8：非平凡多边形正则邻域的补是环带；不交多边形之并携带 `H₁(S)` 生成元 ⟹ 每个都携带 | T.2, T.4 | §28.19, §34 L11 | new | 2k |
| T.6 | 28.9：`J ∼ 0` 于 `T` ⟹ `J` 在 `T` 中界定 2-胞腔 | T.2, T.3 | §31.4, §32 L2 | new | 1k–2k |
| T.7 | 28.10：`K ⊆ T` 携带生成元、`J ⊆ T − K` 不界定 ⟹ `J` 携带 `H₁(S)` 生成元 | T.5, T.6 | §34 L4/L11（核对） | new | 1k |
| T.8 | 28.19：`Δ ∩ M² = Bd Δ = J` ⟹ `J` 在 `M²` 中有环带邻域（`N(J)` 是 CST 的特例 C.7；`M² ∩ N` 环带或 Möbius，后者由 T.5 排除） | `theorem exists_annular_nhd_of_spanning_disk` | §30.3–30.4, §33 L7 | new | 2k–3k |
| T.9 | 分裂运算（split `M² ∪ Δ` apart at `Δ`）定义与 28.20：`χ(M₁²) = χ(M²) + 2` | 定义 + H.3 | §30.3–30.4, §30.6, §32, §33 L3–L7, §34 Op.1 | new | 2k–3k |

### 4.9 车道 I（1）：§30 多面体插值定理

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| I.1 | 30.1：单连通、局部连通、连通开集道路连通的 `X` 中，`C ∪ D` 分离 `H` 与 `K` ⟹ `C` 或 `D` 分离（Δ 上的 4.4 型分离） | `theorem separates_of_union_separates [SimplyConnectedSpace X] [LocallyConnectedSpace X] (hpath : ∀ U, IsOpen U → IsConnected U → IsPathConnected U) (hC : IsClosed C) (hD : IsClosed D) ... : Separates C H K ∨ Separates D H K`；需要"单连通 ⟹ 圆周上映射延拓到圆盘"（Mathlib `SimplyConnectedSpace` + P.5） | I.2, §32 Step 2 | new | 3k–5k |
| I.2 | 30.2：有限分支的闭集分离 ⟹ 某分支分离 | 归纳 | §30.4, §30.6, §33 L5/L6, §33 L10 | new | 0.5k |
| I.3 | 30.3：分裂运算保持分离性（`N(Δ)`、`Bd A_i`、`C'`） | T.8, T.9 | §30.4, §30.6, §30.7, §32 | new | 2k–3k |
| I.4 | **30.4 球壳定理**：ℝ³ 中球壳 `X` 内有多面体 2-球面分离 `B₀` 与 `B₁` | `theorem exists_isPLSphere_separating_of_sphericalShell (X : Set ℝ³) (hX : IsSphericalShell X B₀ B₁) : ∃ S, IsPLSphere 2 S ∧ S ⊆ interior X ∧ Separates S B₀ B₁`；证明：F4.2 的多面体邻域 `N`、M.3、B.1、B.5、T.8、I.3、`p¹` 下降（H.4） | S.6, §34 L3 | new | 4k–6k |
| I.5 | 30.6 环壳定理：ℝ³ 中环壳 `Y` 内有多面体环面分离 `T₀` 与 `T₁` | I.2, I.3, B.5, B.6, van Kampen 最简情形（本库 `VanKampen/FreeProduct.lean`，待审计）、H.4（`π(T)` 交换 ⟹ 环面，避免 26.8） | §30.7 | new | 5k–8k |
| I.6 | 30.7：拓扑实心环面 `S₁ ⊆ Int S₂`、`Cl(S₂ − S₁)` 环壳 ⟹ 存在 CST `S`，`S₁ ⊆ Int S`，`S ⊆ S₂` | I.5, B.5, I.3, T.1 | §31.1 | new | 3k–4k |
| I.7 | 30.8：脊 `J` 生成 `π(S)` | `π(S₂) ≅ ℤ` 与收缩核 | §31.2, §34 L1–L2 | new | 1k–2k |

### 4.10 车道 I（2）：§31 典范构形

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| K.1 | 定义：绕 `y` 轴旋转的 2-胞腔链 `D_j` → 实心环面 `S_j`、环带 `A_j`、圆 `J_j`；同胚 `h`；多面体 `S''_j`，`T''_j` 两两一般位置 | `structure CanonicalConfiguration` | K.2–K.4, §32 | new | 2k–3k |
| K.2 | 31.1（存在，I.6 反复）、31.2（`J'_j, J'_{j+1}` 携带 `π(S''_j)` 生成元，I.7）、31.3（`S''_i ∩ S''_{i+2} = ∅`） | | §32 | new | 2k |
| K.3 | 31.4：`T''_j ∩ T''_{j+1}` 中多边形要么携带两侧生成元要么在两侧各界定 2-胞腔 | H.6, T.6, D.3, F3.2 | §32 L2 | new | 2k–3k |

### 4.11 车道 I（3）：§32 管的柄分解与伪胞腔

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| Q.1 | 管、对偶胞腔、分裂盘（F4.3）、开 2-胞腔、伪胞腔 `E = U ∪ J`（`U − P` 多面体） | `structure PseudoCell` | Q.2–Q.4, §33 | new | 1k–2k |
| Q.2 | **32.1**：分裂盘 `D` 的像 `D'` 附近存在伪胞腔 `E`，`Bd E = Bd D'`，`E ⊆ W`，`Int E` 在 `Int(C'₁ ∪ C'₂)` 中分离 `v'₁` 与 `v'₂`；证明：无穷同心环带 `A_i` 与典范构形（K.1–K.3）、L1 闭性、L2（K.3）、L3 分离、Step 1（I.3 内分裂）、Type 1–3（I.1, B.6, B.7, T.4）、"无第四类"（T.4） | `theorem exists_pseudoCell (tube data) (W : closed nbhd of Int D' \ {P'}) ... : ∃ E : PseudoCell, ...` | §32.2–32.4 | new | 10k–16k |
| Q.3 | 32.2：`(C'₁ ∪ C'₂) − E` 恰两分支，`Bd C'_i ∩ Bd N' ⊆ Fr U_i` | Q.2 + 多面体 2-流形局部结构 | §33 L6 | new | 2k |
| Q.4 | 32.3：所有边同时处理，得 `C''_i` 与 (7)–(10) | Q.2, Q.3 | §33 L1 | new | 3k–4k |
| Q.5 | 32.4：伪胞腔中心附近有多面体 2-胞腔 `Δ₁ ⊆ N(P', δ)`，`Bd Δ₁ = Δ₁ ∩ E` 在 `E` 中界定含 `P'` 的 2-胞腔 | 最内分裂归纳（I.3, T.9） | §33 L8, §33 末 | new | 2k–3k |

### 4.12 车道 I（4）：§33 线性图正则邻域的 PLH 逼近

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| G.1 | L1–L2：`C''_v` 直径小；多面体带边 3-流形 `X`，`K' ⊆ Int X ⊆ Int N'`，`Bd X` 与伪胞腔一般位置 | Q.4, F5.1（伪胞腔的多面体部分） | G.2–G.5 | new | 2k–3k |
| G.2 | L3–L4：每个 `E ∩ Bd X` 是单个多边形（分裂减少分支数） | I.3, T.9 | G.3 | new | 2k–3k |
| G.3 | L5–L6：`X`、`Bd X` 连通（I.2, B.6）；`A'_v = C''_v ∩ Bd X` 连通带边 2-流形，`Bd A'_v` 在伪胞腔中 | | G.4 | new | 2k–3k |
| G.4 | L7–L9：无 LTD（环定理盘）；L8 用 Q.5 + S.4 的 2-球面分离；L9 用最内分裂 | B.5, Q.5, S.4, I.2 | G.5 | new | 4k–6k |
| G.5 | L10–L12：`i* : π(Bd X) ↔ π(N' − K')` 同构（`Bd N × (0,1) ≅ Int N' − K'`，Figure 33.1 的 PL 格论证，I.2）；`Bd X ≅ Bd N`（B.8 + H.4 22.9）；`A'_v` 是盘或带孔盘（H.4 计数） | | G.6 | new | 4k–6k |
| G.6 | L13 + 定理收尾：PLH `f : Bd N ↔ Bd X`，`f(A_v) = A'_v`（P.2 反复、Figure 33.2–33.3 的盘拼接），Q.5 替换 `E ∩ X` 为多面体盘，延拓到分裂盘与 3-胞腔（S.7） | **33.1** `theorem exists_regularNeighborhood_plh_approx (K : finite connected linear graph ⊆ ℝ³ without end-points) (U : Opens ℝ³) (hKU : K ⊆ U) (h : U → ℝ³) (hh : IsOpenEmbedding-like homeomorphism onto image) (ε) : ∃ N (regular nbhd of K in U) (f : ℝ³ → ℝ³), IsPLHomeomorphOn f N (f '' N) ∧ f '' N ∈ 𝓝ˢ (h '' K) ∧ ∀ P ∈ N, dist (h P) (f P) < ε` | §34 L1 | new | 4k–6k |

### 4.13 车道 I（5）：§34 多面体 3-胞腔的 PLH 逼近

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| A.1 | 归约：`K` 推入 `Int K`（PLH 接近恒同），`h` 延拓到邻域 `U`；细分使 link 中"边内部不分离两顶点" | F2.2, F3.4 | A.2 | new | 2k |
| A.2 | L1–L2：1-骨架正则邻域 `N` 与 PLH `f₁ : N ↔ N''`（G.6），条件 (1)–(5)；`J' = Bd σ'` 携带 `π(N''_σ)` 生成元（I.7） | G.6, I.7 | A.3–A.6 | new | 2k–3k |
| A.3 | L3–L5：`σ'` 的任意小多面体 3-胞腔邻域 `C_σ`（S.6/I.4）；L4 `Bd C ∩ Bd N''_σ ∩ Bd N''` 携带 `H₁(N''_σ)` 生成元（H.6）；L5 的 (1)–(8) | | A.4 | new | 3k–5k |
| A.4 | Operations 1–2 与 L6–L8（保持条件；终止性） | I.3, T.9 | A.5 | new | 3k–5k |
| A.5 | L9–L11：`Bd C_σ ∩ Bd C''_v ∩ Bd N''` 无多边形；无两端在同一 `D''_e` 的折线；每个分支恰穿过每个 `Bd D''_e` 一次（T.5 28.8） | | A.6 | new | 4k–6k |
| A.6 | 收尾：`D_σ, C(σ³), X(σ³, v)` 的复制（`W_i` 三孔球面、`X_i/Y_i` 选择、无界分支论证），分 (1)–(7) 步延拓 PLH | **34.1** `theorem exists_plh_approx_of_isPLBall (hK : IsPLBall 3 K) (h : K → ℝ³) (hh : homeomorphism into) (ε) (hε : 0 < ε) : ∃ f : ℝ³ → ℝ³, IsPLHomeomorphOn f K (f '' K) ∧ ∀ P ∈ K, dist (h P) (f P) < ε` | §35.1 | new | 6k–10k |

### 4.14 车道 E：§35–§36 与端点

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| E.0 | D6 不变域原生移植；同调无收缩与任意维 Brouwer 消去外部条件 | `invariance_of_domain_isOpen_image`、`isOpen_image_of_continuousOn_injOn`、`isOpenMap_of_continuous_injective`；实 `ModelWithCorners` 的四个 `_real` 接口 | S.1, M.3, E.3/E.4 | done（2026-09-14；`Topology/InvarianceOfDomain.lean`、`FixedPoint/NoRetraction.lean`、`FixedPoint/Brouwer.lean`、`InvarianceOfDomainManifold.lean`；聚焦检查均 exit=0、零警告；AuditE01/E02/E03/E0 仅允许的标准公理，七个最终接口无未证类参数；出处见 `docs/third_party/InvarianceOfDomain.md`） | 1019 行 Lean |
| E.1 | **35.1**：PL 3-流形 `M₁` 中 1 维多面体 `K`（可非紧、闭于 `U`）、`U ⊇ K` 开、`h : U → M₂` 同胚（到像）、`φ` 连续正 ⟹ 正则邻域 `N` 与 PLH `f : N ↔ X ⊆ M₂`，`X ∈ 𝓝ˢ (h '' K)`，φ-逼近。证明：`ε(A) = inf φ\|A`、对偶胞腔改造（Figure 35.1）、逐胞腔用 A.6（在图卡内）、条件 (2)–(8)、L1–L3（D.3、极小性条件）、拼接 | `theorem exists_regularNeighborhood_plh_approx_manifold ...`（流形层，F6.1/F6.2 的局部有限性） | E.2 | new | 6k–10k |
| E.2 | **35.2**：`K` 为 `M₁` 中局部有限、可非紧的多面体 3-流形带边，`h : K → M₂` 是到其像的同胚，`φ ≫ 0`；结论只有 φ-逼近的 PLH `f : K → M₂`，无关于 `f(K)` 的附加条款。证明 = A.1–A.6 在流形层的重复，以 E.1 代替 G.6，逐单形处理 | 拟定显式假设：`def Moise352 (n : ℕ) : Prop := ∀ {M₁ M₂} [PL n-manifold data] {K : Set M₁} (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n K) (h : K → M₂) (hh : Topology.IsEmbedding h) (φ : K → ℝ) (hφ : Continuous φ) (hpos : ∀ x, 0 < φ x), ∃ f : K → M₂, IsPLHomeomorphInto n f ∧ ∀ x, dist (f x) (h x) < φ x`；其中两个拟定谓词由 F6.3 提供非紧局部有限表示，并将 `IsPLHomeomorphInto` 明确定义为到像的双向 PL 同胚。 | E.3 | new / blocked on F6.3（条件性命题已定形，表示谓词尚不存在；不得用当前有限片、因而紧致的 `IsPolyhedralManifoldWithBoundary` 替代） | 4k–6k |
| E.3 | 36.1 的过渡（Moise 8.4 的三维版）：连通分支归约、穷竭 `N_i ⊆ Int N_{i+1}`（F6.2）、`φ'` 的 (a)–(d)、E.0 得 `h(U)` 与 `Int N'_i` 开、M.3 得 `f(Bd N_{i+1}) = Fr f(N_{i+1})`、连通性得 `N'_i ⊆ f(N_{i+1})` | `theorem exists_plh_approx_of_isOpen (h352 : Moise352 3) (U : Opens M₁) (h : U → M₂) ... : ∃ f, IsPLOn 3 3 f U ∧ f '' U = h '' U ∧ ∀ x ∈ U, dist (f x) (h x) < φ x` | E.4 | blocked on F6.3（`exists_exhaustion_of_isOpen` 已闭合且 AuditF26 仅标准三公理；但对各紧致 `N i` 分别逼近只产生不相容的 `f_i`，不能替代在整个局部有限 `U` 上一次应用 35.2） | 3k–5k |
| E.4 | **端点**与推论、公理审计 | `plApproximationManifold_three`（E.3 取 `U = M₁`，`f` 双射 ⟹ `M₁ ≃ₜ M₂`，`IsPL 3 3 f` 由 `IsPLOn` 于 `univ` 得到）；推论 `plApproximation_three`、`exists_chartedSpace_hasGroupoid_plGroupoid_three`；`#print axioms` | 书中 `FND-SMOOTHABILITY` 链（与 Phase 2 合成） | new | 1k |

## 5. 验收标准

- 每个模块用 Phase 1 相同的配方逐模块检查（`lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true -Dlinter.style.header=false -Dlinter.style.longLine=false -Dpp.unicode.fun=true`，或共享检出中的 `scripts/lake-locked.ps1 check`），零错误零警告；
  非 vendored Lean 零注释、零 docstring；新叶子登记到 `DifferentialGeometry.lean`。
- 车道对外接口定理（§4 表中带粗体或标明"消费者"跨车道者）签名冻结；变更需同时更新本表。
- 每车道结束时对其接口定理做 `#print axioms`，只允许 `propext`、`Classical.choice`、`Quot.sound`；
  D4/D6 复用的外部或本库声明在首次使用时单独审计并把结果记入 `MOISE_PLAN.md` §6。
- 陈述与 Moise 编号的对照只维护在本文件（Lean 源不得含注释）；证明与书中不同处在本文件 §8 记录。
- 报告规则：在 `plApproximationManifold_three` 完成前，所有 Phase 1 端点保持"条件性"报告；每车道报告分"已证生产者 / 条件性消费者"。
- 不在共享检出启动完整 `lake build`；聚焦检查按 `WORKING_STATUS.md` 与 `lake-locked.ps1 status` 协调。

## 6. 文件布局提案（`Topology/PiecewiseLinear/` 下）

`Polyhedra.lean`、`Subdivision.lean`、`CommonSubdivision.lean`、`SimplicialMaps.lean`、`LinkUniqueness.lean`、
`ConeExtension.lean`、`CombinatorialManifoldWithBoundary.lean`、`RegularNeighborhood.lean`、`Tube.lean`、
`GeneralPosition/{Surfaces,SingularDisk,Planes}.lean`、`PolyhedronIn.lean`、`Exhaustion.lean`、`Triangulation/{Realization,Existence}.lean`（T1/T2）；
`Homology/{Chains,FirstHomology,Orientation,EulerCharacteristic}.lean`；`Plane/{PolygonalSchoenflies,DiskExtension,FreeCells,TameGraphs,Separation}.lean`；
`Surface/{OpenCellComplex,Classification,Handles}.lean`；`Schoenflies/{PushProperty,SimplyImbedded,Main}.lean`；
`ThreeManifold/{Boundary,CellUnion,RegularNeighborhoodEquivalence,Orientation,BettiHandles}.lean`；
`Covering/{Cocycle,LiftTriangulation,TwoFold,SolidTorus}.lean`；`LoopTheorem/{NormalSystem,SphereCase,TwoToOne,Stallings,FirstForm}.lean`；
`Bicollar/{Collar,Bicollar,Extended,SurfacesInSpace}.lean`；`Cellular/{Extension,Annulus,Polygon}.lean`；
`SolidTorus/{Meridian,StandardPosition,Polygons,Splitting}.lean`；`Interpolation/{Separation,Splitting,SphericalShell,ToroidalShell,SolidTori,Spine}.lean`；
`Canonical/{Configuration,Polygons}.lean`；`PseudoCell/{Defs,Existence,Components,Disk}.lean`；
`GraphApprox/{Setup,Boundary,LoopDisks,Isomorphism,Assembly}.lean`；`CellApprox/{Setup,Operations,Crossings,Assembly}.lean`；
`Approximation/{GraphManifold,ManifoldWithBoundary,OpenSubset}.lean`；`Endpoint.lean`。
约 60–80 个新叶子；每个文件控制在 3k 行以内。

## 7. 与 Schoenflies 负责人的接口

三个互不蕴含的 Schoenflies：

1. 平面拓扑版（`External/Schoenflies/`，vendored，已证）：本链在 P.1 中把它降到多边形版使用（或独立组合证明）。
2. PL ℝ³ 版（Alexander；Moise 17.12）：本链在车道 S 自证 `exists_isPLBall_of_isPLSphere_two`，输入 PL 2-球面，
   输出 PL 3-球。它**依赖**平面多边形 Schoenflies（3.6）、3.3 与 10.8——这条早先只是"可能"的边现已由证明来源确定。
3. 光滑 ℝ³ 版（负责人，`Topology/ThreeManifold/SmoothSchoenflies.lean` 的 `smooth_schoenflies_three`，目前 sorry）：
   本链不消费它。若负责人希望经 PL 版导出光滑版，需要"光滑 2-球面 ⇒ 同痕于 PL 2-球面"与"PL 3-球的光滑化"两座桥，
   均为 Phase 2 级别的 PL/光滑比较，不在 Phase 3 范围；Phase 3 车道 S 完成后可作为其上游被消费。

## 8. 风险与开放决定

- **R1 规模。** 200k–330k 行是当前最诚实的估计（§3）；若资源只允许单车道，应先做 F、S、E.0，它们对 Phase 2（T1/T2）也有用。
- **R2 一般位置。** D5 的三种一般位置是全链最容易被低估的部分；Moise 到处以"slight perturbation"带过。建议车道 F 先用
  §26.6 的证明（最简单的曲面对情形）做样板，确定表示后再推广。
- **R3 同调层。** D3 若用单纯链，需要 `p¹` 与 `χ` 在细分与 PL 同胚下不变（组合证明可行但长）；若用本库奇异同调，需要
  有限复形的单纯–奇异比较定理（本库 `Homology/Subdivision*` 有部分素材）。车道 H 开工前必须二选一并记录。
- **R4 2D 分类。** §22 只对多面体曲面陈述可减少一半工作量；22.9（可定向 + χ ⟹ 同胚型）在 §33 L11–L12 的使用可能可以改成
  `p¹` 计数直接给出"盘或带孔盘"，若成立可跳过 22.8–22.10；实现时验证。
- **R5 非紧性。** E.1/E.2 需要 §33/§34 的构造在局部有限复形上进行（每步只影响有限个单形）；这是 Moise 一句"virtually a repetition"
  掩盖的真实成本，估计已计入 E.1/E.2。
- **R6 书中引用。** §33 末尾的"Theorem 18.2"与 §18（Antoine 集）不符，本计划按其内容用 S.7；其它引用已逐条核对到本文件 §2。
- **R7 外部复用。** D4 的本库覆盖/van Kampen 声明与 D6 的移植都必须先 `#print axioms`；Phase 2 审计已发现树中有 sorry 支撑链。
- **R8 对偶胞腔球性。** F4.3 的顶点胞腔球性依赖 S.5 的带边界盘粘接；早先行数估计未含此项。现有球性端点证明的是对偶锥与分裂盘，不是 `graphDualCell`；在依赖闭合前 F4.3 保持 partial，Q 消费者须显式携带 `hcell`。
- **R9 局部有限表示层。** Moise 35.2 的 `K` 可非紧，36.1 更要求把它一次用于整个开集 `U`；当前 `IsPolyhedralManifoldWithBoundary` 由有限 `PLPiece` 表示，故其底空间必紧致。F6.2 的紧致穷竭只给集合层的 `N i`，逐项调用紧致版本会得到彼此不相容的 PLH，不能拼成 36.1 的全局映射。必须先完成 F6.3：构造相容的有限片三角剖分上升塔，扩展时固定既有内核，并从其余极限取得局部有限三角剖分；E.2/E.3 在此之前保持 blocked，不以弱化陈述绕过。
