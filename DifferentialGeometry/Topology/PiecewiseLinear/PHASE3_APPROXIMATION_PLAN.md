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
- **D3′ 同调层用本库奇异同调，不引入单纯链复形（已定）。** `χ` 用已有的 `faceEulerChar = eulerChar` 桥，
  不另做 §21 的开胞腔复形及运算 α–δ；`p¹ := finrank ℚ H₁(·; ℚ)`，C.5 所需的 ℤ₂ 信息直接用 ℤ₂ 系数陈述。
  可定向性采用 23.14 的顶维相干定向，纯组合地证明线性细分及 PL 不变性，不依赖单纯–奇异比较定理。
  柄数取 `h(B) := p¹(B) / 2`，由 22.6–22.7 保证；闭曲面的顶维同调从局部同调基本类取得，28.11 走子复形开邻域与小链 Mayer–Vietoris。
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
| F3.4 | PL 球/球面基本性质与锥延拓（PL Alexander 技巧） | `exists_isPLHomeomorphOn_of_frontier`：对 `B₁ B₂ : Set (EuclideanSpace ℝ (Fin (n+1)))`、`IsPLBall (n+1) B₁`、`IsPLBall (n+1) B₂`，任意 `IsPLHomeomorphOn f (frontier B₁) (frontier B₂)` 延拓为球间 PL 同胚并保持边界值；PL 球的边界是 PL 球面；`IsPLBall` 在 PL 同胚下不变；标准单形的锥 | §17.5, §23.11, §33 末尾, §34 (5)–(7) | done（组合边界形式，2026-09-14，砖 9）；`frontier` 形式已由 S 车道的 `BallFrontier.lean` 闭合（2026-09-14，`ff7fc67ca`，见 P.2）。`BoundaryExtension.lean`：`exists_isPLHomeomorphOn_of_boundaryComplex` 对有限复形实现的任意正维 PL 球，将其组合边界之间的任意 PL 同胚延拓为球之间的 PL 同胚，并逐点保持给定边界映射。证明经 `BoundaryOfBall.lean` 的 `boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex` 搬到标准单形边界，使用 `StdSimplexCone.lean` 与 `ConeExtension.lean` 的 `exists_isPLHomeomorphOn_coneComplex`，再由球的参数化搬回。既有 `isPLSphere_boundaryComplex_space_of_isPLBall` 给出球边界的球面性；`IsPLBall.of_isPLHomeomorphOn` / `IsPLSphere.of_isPLHomeomorphOn`、标准单形与闭星的球性均保留。聚焦检查 exit=0 零 warning，AuditF27 端点仅标准三公理，源码 `5eba0ee4a` 已推送；未使用 Schoenflies；补（`0a645e32b`）：通用边界延拓现在显式沿用两侧 DecidableEq 实例，避免具体欧氏空间中实例不一致造成展开超时，数学陈述不变；其二维边界弧延拓消费者已闭合。两模块检查 exit=0、零 warning；F97 审计 30 项均仅标准三公理。 | 3k–5k |
| F4.1 | 带边组合流形与边界复形 | `def IsCombinatorialManifoldWithBoundary (n) (K) : Prop`（顶点 link 是 PL `(n−1)`-球面或 PL `(n−1)`-球）；`def boundaryComplex (K)`（恰在一个 `n`-面中的 `(n−1)`-面及其面）；`theorem isCombinatorialManifold_boundaryComplex (h : IsCombinatorialManifoldWithBoundary (n+1) K) : IsCombinatorialManifold n (boundaryComplex K)`（Moise 23.3/23.7 的 3D 证明经 23.2/23.6） | §23–§35 | **done**（2026-09-13）：`ManifoldWithBoundary.lean`：`IsCombinatorialManifoldWithBoundary n K`（顶点 link 为 PL `(n−1)`-球面或球）、`boundaryComplex n K`（含于某个 link 为 PL `(n−|t|)`-球的面 `t`（`|t| ≤ n`）的面）、`geometricLink_boundaryComplex`（`lk(v, ∂K) = ∂(lk v K)`）；`BoundaryOfBall.lean`：**`isCombinatorialManifold_boundaryComplex (h : IsCombinatorialManifoldWithBoundary (n+1) K) : IsCombinatorialManifold n (boundaryComplex (n+1) K)`**，经 `isPLSphere_boundaryComplex_space_of_isPLBall`（三角剖分的 PL 球的边界复形空间 = 模型单形边界的像 `boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex`，是 PL 球面）；`BoundaryFaces.lean`：`IsCombinatorialManifoldWithBoundary.isPLSphere_or_isPLBall_geometricLink`（面 link 二分）、`mem_boundaryComplex_faces_iff`（边界面 = link 为球的面）、`IsCombinatorialManifold.boundaryComplex_faces_eq_empty`。支撑理论（均新增、聚焦检查零警告、AuditF16 仅标准公理）：`LinkRadial`（径向 link 引理：闭星被锥覆盖的锥底 ≅ link）、`SimplexAvoiding`（避开面的单形子复形；`isPLBall_simplexAvoiding_singleton` 经 far 复形迭代锥）、`StellarSphere`（`unionComplex`、`swapVertex`、避开面及其补的复形 ≅ 小一维单形边界的星形细分 ⟹ PL 球面）、`SimplexLink`（单形/单形边界细分中顶点 link 的球/球面判据 `isPLBall_geometricLink_iff_of_isSubdivision_simplexComplex`）、`FaceLink`（`geometricLink_insert`：面 link = link 中的 link）、`IsomorphicSubdivision`（PL 同胚复形有单纯同构细分 `exists_isGlueIso_of_isPLHomeomorphOn`）、`BallSphereLink`（PL 球面/球的三角剖分中顶点与面 link 的球/球面性；球中顶点 link 是球 ⟺ 顶点在模型边界像内）、`StarAvoiding`（面相对内部点的 link ≅ `starAvoiding K t`，link 型在开单形上常值）、`Join`/`JoinTransport`/`JoinInternal`/`JoinStandard`/`JoinInvariance`（外部 join、同构与细分传递、内部 join 同构、`∂σ ∗ ∂τ`/`∂σ ∗ τ` 的标准模型、join 的 PL 不变性、`isPLSphere_joinComplex_of_isPLSphere`、`isPLBall_joinComplex_of_isPLSphere_of_isPLBall`）、`StarJoin`（`starAvoiding K t ≅ ∂t ∗ lk(t)`，点 link 的球/球面上升引理）、`LinkDimension`（PL 球/球面三角剖分的面至多 `m+1` 个顶点；开单形闭包）。原计划的 F4.1.c/d（顶点图卡）不再需要。`PLBallSphere`、`LinkHalfSpace` 保留 | 3k–5k |
| F4.2 | 正则邻域（`b²K` 中与 `L` 相交的单形） | `def regularNeighborhood (K L) (h : L ≤ K) : Geometry.SimplicialComplex ℝ E`；`regularNeighborhood_space_mem_nhdsSet`；`N(v)`, `N'(σ)` 的定义与"是 3-胞腔、两两交于 2-胞腔"（Moise §23 预备）；**3D**：`theorem isCombinatorialManifoldWithBoundary_regularNeighborhood (hK : IsCombinatorialManifold 3 K) (hL : L ≤ K) : IsCombinatorialManifoldWithBoundary 3 (regularNeighborhood K L h)`（`chap:regular-neighborhoods`） | §23.12, §24.11–12, §25, §26.3, §27.5, §28.19, §32, §33–§35 | **done（主定理，任意维数，2026-09-13 深夜）**：`DerivedNeighborhood.lean`：`derivedNeighborhood K L`（第二重心细分 `secondDerived K` 中所有链元素都与 `L'` 的顶点相交的面；等价于 Moise 的 `N(L)`）、`derivedNeighborhood_mem_nhdsWithin`（含每个 `|L|` 点的闭星，故是 `|L|` 在 `|K|` 中的邻域）；`ManifoldSubdivision.lean`：`IsCombinatorialManifoldWithBoundary.of_isSubdivision`/`.barycentricSubdivision`/`.secondDerived`（细分不变性，经点 link ≅ `∂t ∗ lk t` 上升引理）与面顶点数上界；`UpperLink.lean`：`upperLink K e`（严格含 `e` 的链）经自 `ê` 的伪径向投影 ≅ `lk(e, K)`；`DerivedWeights.lean`（重心细分中点的重心坐标：极大坐标恰在链的最小元）；`FaceNeighborhoodBall.lean`：**单形中一个面的导出邻域是 PL 球**（自 `f̂` 星形，径向前沿 = 最小元与补面相交的链 ∪ 缺 `f` 某顶点的链，为锥底且径向投影 ≅ `f` 对面诸面片）；`FaceNeighborhoodLink.lean`：顶点 `T̂` 在该邻域中的 link 是 PL 球（锥延拓把 `T̂` 送到单形边界）；`DerivedNeighborhoodLink.lean`：`lk(ê, N) = internalJoin (下部：`∂e` 的导出邻域中的链) (upperLink)`；`DerivedNeighborhoodManifold.lean`：**`IsCombinatorialManifoldWithBoundary.derivedNeighborhood (h : IsCombinatorialManifoldWithBoundary (n+1) K) (L) : IsCombinatorialManifoldWithBoundary (n+1) (derivedNeighborhood K L)`**（`e ⊆ V(L')` 时 link 同 `K''`；否则 = 下部球 ∗ `lk(e,K')`，用 `JoinBall.lean` 的球∗球、球∗球面）。AuditF17 仅标准公理。未做（移入 F4.3）：`N(v)`、`N'(σ)` 的 3-胞腔结构与两两交于 2-胞腔。旧的集合版 `regularNeighborhoodIn K A` 保留未用。2026-09-14 砖 7 完成：`LocalManifold.lean` 的 `IsLocallyCombinatorialManifoldWithBoundary`、`.mono`、`.card_le`、`.isPLSphere_or_isPLBall_geometricLink`、`.of_isSubdivision`、`.derivedNeighborhood`；只要求与给定集合相交的单形之顶点具有好 link。细分的最高维分支只用包含载体面的单形的维数界。局部导出邻域定理不需要 `L.faces ⊆ K.faces`（所选面形心自动属于 `L.space`）；邻域性仍单独使用子复形条件。聚焦检查 exit=0 零 warning，AuditF25 全部 14 个声明仅标准三公理，源码 `85cc59a2a` 已推送 | 6k–10k |
| F4.3 | 管的对偶胞腔与分裂盘（§32 开头定义） | 拟定 Lean：对有限 `IsCombinatorialManifold 3 K`、`L.faces ⊆ K.faces`、`∀ s ∈ L.faces, s.card ≤ 2`，保留 `N := derivedNeighborhood K L`；`graphDualCell K L v := restrict N (closedStar (barycentricSubdivision K) v)`；`dualCell K e` 是 `e` 的形心对 `upperLink K e` 的锥；`splittingDisk K e` 是该形心在 `barycentricSubdivision (dualCell K e)` 中的闭星。目标：`isPLBall_graphDualCell`（3-球）、`isPLBall_splittingDisk`（2-球）、`graphDualCell_space_inter`（相邻交集为共享盘，非相邻为空）、`splittingDisk_space_inter`（与 L 的载体恰交于边形心）、胞腔覆盖 N、每胞腔恰含对应顶点、盘两两不交；组合内部与组合边界用于分离陈述，细分后胞腔直径任意小 | §32–§35 | partial（2026-09-14，砖 6，`DualCells.lean`）：保留现有 `derivedNeighborhood` 定义。已证 `IsCombinatorialManifold.isPLSphere_upperLink`、`isPLBall_dualCell`、`isPLBall_splittingDisk`、`splittingDisk_space_inter`（对原图恰交于边形心）、`iUnion_graphDualCell_space`（胞腔覆盖）、`mem_graphDualCell_space_iff_of_singleton_mem`（每胞腔恰含对应图顶点）、`graphDualCell_space_inter`（相邻交集为共享盘）、`graphDualCell_space_inter_eq_empty`（非相邻不交）、`disjoint_splittingDisk_space`、`diam_graphDualCell_le` 及 `exists_isSubdivision_graphDualCell_diam_lt`（兼容图的任意小细分）。49 个定义/定理，聚焦检查 exit=0 零 warning，AuditF24 全部仅标准三公理；源码 `ccf7a2035` 已推送。按交接 §9.0，剩余顶点胞腔球性 `IsPLBall 3 (graphDualCell K L v).space` 依赖 S.5 的带边界盘粘接；组合内部中的分离结论随该依赖闭合。不得将已证对偶锥球性等同于被邻域截取后的胞腔球性。Q 消费者在 S.5 完成前只能显式携带 `hcell` 并标为条件性定理，不用 sorry。逐点径向公式 `v + ρ(z) • (z-v)` 一般不是 PL，不能替代该证明。不修改正则邻域语义，不重复 Schoenflies；继续局部导出邻域、非紧穷竭和组合边界延拓 | 3k–5k |
| F5.1 | 一般位置 (a)：曲面对 | 紧致多面体曲面（带边）`S₁ S₂ ⊆ ℝ³` 与 `ε`：存在 PLH `h` ε-接近恒同、在给定闭集外恒同，使 `h '' S₁ ∩ S₂` 为有限个不交多边形与折线之并且横截（Moise 的"cross one another"）；平面族版本（§17.12 的水平平面） | §17.12, §26.4, §26.6, §28.2, §30.4, §32–§34 | done（2026-09-14，`GeneralPosition.lean`）。`exists_small_homeomorph_generalPosition` 与相对端点 `exists_small_homeomorph_generalPosition_relative` 对三维有限带边组合 2-流形构造任意小、指定开邻域外恒同的环境 PL 同胚；相对版本固定整个既有一般位置子复形。交集为有限一维带边组合流形，处处 `HasPLCrossingAt`。按交接 §9.5，一维组合流形即约定的有限多边形/折线之并的表示。`exists_generalPosition_height_fibers` 给出全水平平面族：顶点高度两两不同，各层为有限至多一维图，原顶点外度数二且 crossing，每层至多一个原顶点，普通层为无边界一维组合流形；临界点允许孤立或分叉。`exists_small_simplicialMap_preimage_manifold_relative` 对任意子复形使用相对细分并保持整个映射，允许全局自交而各单形上单射，给出一维带边原像流形及源边界度数一、源内部度数二。`exists_small_simplicialMap_preimage_manifold_of_isPLBall` 固定原 PL 球的整个组合边界，并按原边界给出度数分类；m=n=1 为 §26.6 圆盘映射消费者。`exists_isPLHomeomorphOn_extension_of_small_vertex_perturbation` 证明统一阈值内的每个顶点扰动均延拓为任意小、指定邻域外恒同的环境 PL 同胚；基础为全局 Lipschitz 顶点基函数及 `IsPiecewiseAffineOn.exists_lipschitz_extension`。分析支撑在 `Analysis/Calculus/Interpolation/LipschitzSelection.lean`。聚焦检查 exit=0 零 warning，AuditF55 共 162 声明（GeneralPosition 158，分析 4）仅 propext、Classical.choice、Quot.sound，源码 `bebaf278c` 已推送，无 Schoenflies 依赖。下一砖 F5.2 奇异 2-胞腔正规形式。 | 6k–10k |
| F5.2 | 一般位置 (b)：奇异 2-胞腔正规形式 | PL 映射 `D : Δ → M` 局部同胚、至多 2 对 1，可微扰使奇点集为不交多边形与折线的并且为"crossing"（§25 L2 前言） | §25 | partial（2026-09-15，`SingularGeneralPosition.lean`）。欧氏环境端点 `exists_small_simplicialMap_doublePointSet_manifold` 已闭合：任意小 PL 扰动、原域细分、闭星上到像的 PL 同胚、局部单射、每个纤维至多两点；`doublePointSet` 精确表示两个不同原像的奇点像，其有限三角剖分是一维带边组合流形，每点满足 `HasPLDoubleCrossingAt`（两个互不相交的源邻域、到像的 PL 同胚、实际环境 crossing、附近全部纤维由两片覆盖）。稳定性生产者 `exists_isSubdivision_stable_fiber_encard_le_two` 使用闭星注入半径和分离三点配置空间的紧致最小值。`faceStarComplex` 保留原单形，`isPLBall_faceStarComplex` 给出闭面星球性；`hasPLDoubleCrossingAt_and_exists_local_intersection` 构造两片及局部一维交集；`isCombinatorialManifoldWithBoundary_one_of_locally_eq` 经径向 link 不变性把局部结论传给精确全局奇点图。边界范围已核对：`injOn_boundaryComplex_of_transverse_faces` 证明欧氏自由横截条件强制源边界单射，因此不能代替 §25 允许边界双点的受约束版本。已完成受约束点生产者 `exists_small_affineIndependent_subsets_relative`、`exists_small_affineIndependent_subsets_in_submodule`、`exists_small_affineIndependent_subsets_in_halfSpace`：固定点族的相对扰动、边界维数与环境维数的独立性条件、核平面及严格正侧保持。`exists_small_vertexMap_transverse_in_halfSpace` 给出任意小边界相容通用顶点映射：相交的不交面若全部顶点在边界，其方向空间之和等于核平面，否则等于整个环境；两个方向生产者为 `vectorSpan_sup_eq_submodule_of_affineIndependent_subsets` 和 `vectorSpan_sup_eq_top_of_affineIndependent_subsets_relative`，原自由版本已改为相对定理的推论。聚焦检查 exit=0 零 warning；AuditF78 的 109 声明（SingularGeneralPosition 105，BoundaryInvariance 4）（GeneralPosition 162 声明此前由 AuditF74 验证）仅 propext、Classical.choice、Quot.sound 或无公理；源码 `83e2905b0` 已推送。`exists_small_simplicialMap_transverse_in_halfSpace` 已把点生产者接到有限组合曲面：对原本映入闭半空间且边界平面原像恰为源组合边界的 PL 映射，给出任意小扰动、闭星 PL 同胚、局部单射、至多两点纤维、全载体半空间保持、原源边界零集保持、各面单射和分层横截。`linearMap_simplicialMap` 与三个非负/零集引理证明正重心权重下零集只由顶点零集决定。`HasPLBoundaryCrossingAt` 新增独立边界模型：同一个环境半空间内的两个半平面，交线存在归一化共同内向向量；旧 `HasPLCrossingAt` 的语义不变。`halfSpace_eq_of_linearMap_pos`、`exists_common_inward_vector_of_sup_eq_ker` 给出正侧锥和公共内向方向；`hasPLBoundaryCrossingAt_of_halfSpace_cones` 构造环境 PL 平移模型；`eventually_mem_space_iff_mem_unique_coface_cone` 与 `hasPLBoundaryCrossingAt_of_unique_cofaces` 把两条各有唯一邻面的边接到该边界模型。`neighbors_singleton_of_eventually_nonneg_ray` 证明有限一维图的局部半射线芽迫使该顶点恰有一个邻点；`exists_nonneg_ray_eq_inter_halfSpace_cones` 与 `eventually_mem_inter_iff_nonneg_ray_of_halfSpace_cones` 已从互补边界方向及共同正侧生产该射线芽，`neighbors_singleton_of_unique_cofaces` 已把实际三角剖分的两条唯一邻面边接到度数一结论。`exists_isCombinatorialManifoldWithBoundary_inter_in_halfSpace` 已从有限带边组合曲面的非负顶点、零面位于组合边界及分层横截，构造精确交集的一维带边组合流形，并证明边界平面上的交点度数一；支撑为 `linearMap_eq_zero_iff_of_mem_openSimplex`、`IsCombinatorialManifoldWithBoundary.exists_unique_coface_in_halfSpace`、`neighbors_of_inter_in_halfSpace`。GeneralPosition 的维数界推广为 `card_add_finrank_sup_le_of_subset_faces`，当前载体面邻点分类提取为 `neighbors_singleton_or_pair_of_transverse_face`，旧端点签名保持。`IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_of_faces_subset` 证明同维子复形继承原边界余维一面；`boundaryComplex_space_of_isPLHomeomorphOn_of_isPLBall`、`IsPLHomeomorphOn.mem_boundaryComplex_image` 和 `boundary_faces_of_simplicialImage_of_faces_subset` 把该性质传给闭星的单射像。半空间交集及邻点定理新增 `_of_boundary_edges` 主版本，只要求零高度的边及更高维面位于边界；旧全零面接口保留为推论。`exists_local_intersection_at_doublePoint_in_halfSpace` 已把两个原像闭星的单射像接到局部一维交集；`exists_triangulation_doublePointSet_finrank_sup_le` 给出实际方向空间之和的维数界，原自由版本保留为推论；`exists_isCombinatorialManifoldWithBoundary_doublePointSet_in_halfSpace` 给出精确全局奇点图的一维带边组合流形性。`exists_small_simplicialMap_doublePointSet_manifold_in_halfSpace` 对原本正常映入半空间的 PL 2-球（边界平面原像恰为源边界）组合任意小扰动、源细分、闭星 PL 同胚、局部单射、至多两点纤维、半空间/原边界零集保持及精确奇点图流形性。`HasPLBoundaryDoubleCrossingAt` 给出两个互不相交的源邻域到像的 PL 同胚、共同半空间 crossing 及附近全部纤维覆盖。`hasPLCrossingAt_or_hasPLBoundaryCrossingAt_of_transverse_faces` 同时保留边界交集的具体内向半射线；`exists_local_intersection_with_crossings_at_doublePoint_in_halfSpace` 将其传给实际奇点集。`exists_isCombinatorialManifoldWithBoundary_doublePointSet_with_crossings_in_halfSpace` 与 `exists_small_simplicialMap_doublePointSet_with_crossings_in_halfSpace` 已把正侧普通 crossing、零高度边界 crossing 和精确全局奇点图在零高度顶点的度数一接到扰动端点。旧较弱端点保留为推论。`IsCombinatorialManifoldWithBoundary.codimension_one_cofaces_of_notMem_boundary` 与 `neighbors_eq_pair_of_transverse_face` 证明两张曲面均处于内部时的度数二；原无边界余维一面定理已改为推论。`geometricLink_faceStarComplex`、`mem_boundaryComplex_faceStarComplex_faces_iff`、`mem_boundaryComplex_faceStarComplex_space_iff` 保持闭星中心载体面及其相对内部点的边界类型；固定三角剖分版本 `isCombinatorialManifoldWithBoundary_inter_in_halfSpace_of_boundary_edges`、`neighbors_eq_pair_of_inter_in_halfSpace_of_notMem_boundary`、`neighbors_eq_pair_of_eventually_eq` 提供把局部内部交点度数二传给精确奇点图的接口。`exists_local_intersection_with_crossings_and_degrees_at_doublePoint_in_halfSpace` 已接回两个实际原像的闭星，证明避开源边界像的双点在局部奇点图中度数二；`exists_isCombinatorialManifoldWithBoundary_doublePointSet_with_degrees_in_halfSpace` 将其传给精确全局奇点图；`exists_small_simplicialMap_doublePointSet_normal_form_in_halfSpace` 闭合正常映入半空间的圆盘版本，零高度奇点度数一，正侧奇点度数二，并保留两类 crossing。旧三个端点保持签名并改为推论。`simplicialMap_indicator_compl_subcomplex_eq_zero_iff` 在重心细分上构造零集恰为任意子复形的非负 PL 函数；`exists_small_simplicialMap_in_halfSpace_of_subcomplex` 对任意有限源复形，在固定整个指定子复形映射的同时，将其余点推入严格正侧，保持任意小误差、闭星 PL 同胚、局部单射与至多两点纤维。`exists_small_simplicialMap_doublePointSet_normal_form_in_halfSpace_of_maps_boundary` 已去掉初始内部严格正侧条件，只要求全圆盘映入闭半空间且源边界映到零平面；原正常映射端点保持签名并改为推论。`singleton_mem_faces_of_eventually_nonneg_ray` 证明局部半射线的端点必为复形顶点；`mem_boundaryComplex_one_space_iff` 将一维组合边界识别为度数一顶点；`boundaryComplex_one_space_eq_inter_of_rays_and_degrees` 排除零平面中的边内部点。`exists_small_simplicialMap_doublePointSet_with_boundary_in_halfSpace` 新增精确等式：奇点图组合边界 = 奇点图与零平面的交集。`exists_small_simplicialMap_doublePointSet_normal_form_in_halfSpace_in_boundary_neighborhood` 只要求 B′ 是原源边界像在零平面内的逐点相对邻域，便保持整个扰动后源边界像及全部边界奇点留在 B′；保留任意小误差、正常化、两类 crossing 和完整度数分类。半空间模型及其边界邻域约束已闭合。新增 `BoundaryInvariance.lean`：`isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision`、`boundaryComplex_space_of_isSubdivision`、`mem_boundaryComplex_space_iff_of_isPLHomeomorphOn`、`boundaryComplex_space_of_isPLHomeomorphOn`，把组合边界不变性推广到任意正维有限带边组合流形。半空间主端点 `exists_small_simplicialMap_doublePointSet_with_boundary_in_halfSpace` 的源已推广为任意有限带边组合 2-流形，两处圆盘消费者已同步；原 PL 球边界搬运端点保持签名并成为一般定理的推论。`doublePointSet_comp_of_injOn` 给出任意单射后复合的精确奇点集等式；`exists_triangulation_doublePointSet_comp_of_isPLHomeomorphOn` 沿目标 PL 同胚搬运精确奇点图、一维组合流形性及组合边界。独立边界模块避免共享检出重编旧模块时覆盖本车道新增导出。`PLHomeomorphOpen.lean` 给出开放 PL 同胚与 `OpenPartialHomeomorph` 的转换，以及任意源 PL 同胚的局部坐标后复合；`HasPLCrossingAt.image_openPartialHomeomorph`、`HasPLBoundaryCrossingAt.image_openPartialHomeomorph` 搬运两种 crossing，两个 `postcomp_openPartialHomeomorph` 双点端点同时保留不交源邻域、到像的 PL 同胚及附近完整纤维覆盖。两模块聚焦检查 exit=0 零 warning；AuditF79 共 116 声明（边界 4、开放 PL 同胚 3、奇点 109）仅标准三公理或无公理，源码 `37c102e29` 已推送。`SingularChart.lean` 的 `exists_small_map_doublePointSet_normal_form_in_halfSpace_chart`、`exists_small_map_doublePointSet_normal_form_in_boundary_chart` 完成整幅像落在一张 PL 边界图卡内的版本：复用统一复合半径控制逆图卡误差及留在定义域，保留源细分、闭星 PL 同胚、局部单射、至多二重纤维、映射留在 M、源边界恰映到 Bd M、边界像留在 B′、精确奇点图及其组合边界等式、两类 crossing；源允许任意有限带边组合 2-流形。`HasPLBoundaryCrossingAt.congr` 与 `HasPLBoundaryDoubleCrossingAt.congr_target` 允许用相同局部集合替换目标。两模块检查 exit=0 零 warning，AuditF80 共 121 声明（边界 4、开放 PL 同胚 3、奇点 111、图卡 2、复用分析端点 1）仅标准三公理或无公理，源码 `2e43f59a0` 已推送。共享 olean 的 PLImage/PLBallSphere 新旧声明碰撞后，在 D 的 `.lake/scratch/f-lib` 保存完整 DifferentialGeometry olean 快照；仍用 check-f.ps1/audit-f.ps1，仅读写此项目快照，外部包仍读 E，编译参数与单进程规则不变；按 D 源聚焦重检 PLImage 已通过，不再覆盖 E 的项目 oleans。`HalfSpacePerturbation.lean` 为多图卡拼接补充保持边界的环境延拓：`exists_piecewiseAffine_lipschitz_vertex_function_vanishing_on_hyperplane` 裁剪内部顶点权函数，在边界平面上为零，保持原复形插值、支撑和 Lipschitz 性；`exists_isPLHomeomorphOn_extension_of_small_vertex_perturbation_preserving_halfSpace` 将任意阈值内、边界顶点留在平面的扰动延拓为任意小、指定邻域外恒同的环境 PL 同胚，且逐点保持高度为零及非负的充要条件。通过法向 Lipschitz 控制证明两侧不互换，未把边界不变性作为结论型假设。聚焦检查 exit=0 零 warning，AuditF81 两端点仅标准三公理，源码 `03fcb6389` 已推送。`HalfSpaceGeneralPosition.lean` 的 `exists_small_vertexMaps_transverse_in_halfSpace` 对两个带标签顶点族同时扰动，保持高度为零的充要条件与非负性，各至多三点子族仿射无关；相交面在边界平面中张成核，其他情形张成全空间。`exists_small_homeomorphs_transverse_in_halfSpace` 将两片的扰动分别延拓为任意小、指定共同邻域外恒同、保持半空间的环境 PL 同胚，并与各自单纯映射在整片上相等。聚焦检查 exit=0 零 warning，AuditF82 连同半空间延拓共四端点仅标准三公理，源码 `6cdf0c738` 已推送。`exists_small_homeomorphs_generalPosition_in_halfSpace` 将横截面条件落实为两片移动后的有限一维带边交集和每点 crossing；`exists_small_homeomorph_generalPosition_in_halfSpace` 再用第二片的逆同胚固定第二片，得到任意小、指定共同邻域外恒同、保持半空间的单个环境 PL 同胚。输入仅要求两片是有限带边组合 2-流形、位于半空间、在高度零处属于各自组合边界；允许人工截取边界位于半空间内部，故该局部交集的所有端点不宣称都在高度零处。聚焦检查 exit=0 零 warning，AuditF83 连同延拓共六端点仅标准三公理，源码 `b201d541a` 已推送。两个 `Pasting.lean` 模块完成局部修改的粘合层：一般拓扑端点证明接缝像邻域内恒同的分片后复合保持局部单射；集合端点对任意重数上界证明单张源片修改后的纤维计数，并给出支撑外精确纤维不变。`exists_piecewiseAffineOn_postcomp_on_polyhedron_of_locallyInjective` 将其接到闭多面体分解，保留 PL 性、局部单射、至多二重纤维及两片上的精确公式；仅要求目标修改是单射 PL 映射，不要求额外的逆映射或满射。接缝像须避开支撑闭包，未把接缝处相等误用为局部单射保证。聚焦检查均 exit=0 零 warning，AuditF84 六端点仅标准三公理，源码 `6c0101276` 已推送。`SingularPasting.lean` 的 `exists_isPLBall_patches_at_doublePoint` 从原始局部单射、至多二重的 PL 映射与实际双点构造两张不交 PL 球源片、闭多面体余片及任意指定邻域内的扰动支撑；支撑闭包避开接缝像，附近全部纤维由两片覆盖，余片上方保持单射。`exists_isPLBall_postcomp_neighborhood_at_doublePoint` 将任何在该支撑外恒同的单射 PL 后复合粘回全源，保持局部单射、至多二重、逐点误差控制、整张源片上的复合公式和支撑外精确纤维。源维数为任意正维。聚焦检查 exit=0 零 warning，AuditF85 四端点仅标准三公理，源码 `3179a4cb4` 已推送。`Topology/Homeomorph/Conjugate.lean` 的 `OpenPartialHomeomorph.conjugateHomeomorph` 将图卡目标中紧支撑的同胚共轭并延拓为原空间全局同胚；显式正逆公式、图卡外恒同、局部集合模型保持和统一误差半径均已证。`ChartConjugate.lean` 的 `isPiecewiseAffineOn_conjugateMap`、`isPLHomeomorphOn_conjugateHomeomorph`、`isPL_conjugateHomeomorph` 证明该延拓分别具有欧氏 PL 性、PL 同胚性和任意维抽象 PL 流形上的 PL 性；连续性与 PL 性在图卡边缘由紧支撑的恒同邻域证明。两模块聚焦检查 exit=0 零 warning，AuditF86 共十三声明仅标准三公理，源码 `95ef721ed` 已推送。`PLMap.lean` 的 `IsPLAt.comp_isPLWithinAt`、`IsPL.comp_isPLOn`、`IsPL.comp` 和 `IsPLOn.piecewise_postcomp_of_isClosed` 补齐抽象目标上的 PL 后复合与接缝邻域恒同粘合。`SingularPasting.lean` 的源片生产者新增 `_of_continuousOn` 主版本，目标只需 Hausdorff 正则空间，旧欧氏签名保留为推论；`exists_isPLBall_postcomp_neighborhood_at_doublePoint_in_manifold` 将实际双点的局部修改接到抽象带 PL 图册的目标，保留全源 PL 性、局部单射、至多二重及支撑外精确纤维。两模块聚焦检查 exit=0 零 warning，AuditF87 十个端点仅标准三公理，源码 `03a9c146f` 已推送。`098a404b5`：抽象目标流形上的双点局部修改现在同时保护任意有限族紧致单射源片，并在每片上给出与原映射或同一个目标后复合的精确相等；`Topology/Pasting.lean` 与 `SingularPasting.lean` 聚焦检查 exit=0、零 warning，F88 审计 11 个声明只有标准三公理。`0c86d10e5`：`GeneralPosition.lean` 新增无固定面横截假设的 `exists_small_vertexMap_transverse_off_fixed`，非横截交集必局限于固定顶点凸包；`exists_small_homeomorph_generalPosition_off_subcomplex` 给出固定指定子复形、其外全部 crossing 的任意小支撑 PL 同胚。原三个相对选择端点保留签名并成为推论。聚焦检查及 SingularGeneralPosition、HalfSpaceGeneralPosition 下游检查均 exit=0、零 warning；F89 审计 GeneralPosition 全部 166 个声明只有标准三公理。固定子复形边缘的 crossing 保持尚需证明，此结果不等于一般 M 正规形式。`e07a2eaf4`：`SingularPasting.lean` 的 `exists_isPLBall_patches_at_doublePoint_within` 将双点两张紧致 PL 球源片的整个像同时收进任意给定目标邻域，保留补片、接缝避让、单射性和附近完整纤维覆盖；原连续映射端点成为推论。聚焦检查 exit=0、零 warning；F90 审计该文件 8 个声明只有标准三公理。`2f9d771cb`：新增 `SingularLocal.lean`，`exists_small_piecewiseAffineOn_doublePointSet_crossing_neighborhood` 已实际构造三维欧氏目标中双点的支撑局部正规形式：任意小 PL 修改、全局局部单射与纤维数 ≤2、给定目标邻域外纤维完全不变，在含原双点的开邻域内真实双点集精确等于有限带边一维组合流形且全部满足 HasPLDoubleCrossingAt；另有内部/边界双片 crossing 到真实双点 crossing 的拼接引理。`SingularPasting.lean` 新增 `exists_isPLBall_patches_at_fiber_pair`，可同时指定两原像点及各自源邻域，供内外嵌套源片使用；`PLImage.lean` 增加 IsPLBall.isPolyhedron 并复用。四模块聚焦检查 exit=0、零 warning；F91 审计 25 个声明只有标准三公理。仍仅为局部正规形式，未宣称一般 M 的有限多图卡闭环。`e029bbec9`：`PLHomeomorph.lean` 将多面体限制证明推广到 IsPiecewiseAffineWithinAt，原 On 端点保留签名为推论；`PLMap.lean` 新增 IsPLWithinAt/IsPLOn.mono_of_isPolyhedron 及 `isPLOn_iff_isPiecewiseAffineOn_comp_chart`，使抽象目标流形上的 PL 映射可在紧致源片上转为指定图卡中的逐片仿射映射。聚焦检查及 SingularPasting、SingularLocal 下游检查均 exit=0、零 warning；F92 审计 21 个声明只有标准三公理。`4e8a4536c`：`PLMap.lean` 的 `IsPLOn.exists_isPLHomeomorphOn_chart_image` 从抽象目标 PL 映射、紧致多面体源域和单射性构造指定图卡中的有限像复形及 PL 同胚；`Pasting.lean` 的 `exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective` 推广局部修改到流形值映射，保留局部单射、纤维数 ≤2、两片精确相等及支撑外完整纤维。SingularPasting 原抽象双点修改已改为调用此通用端点。检查及下游 SingularLocal 均 exit=0、零 warning；F93 审计 24 个声明只有标准三公理。`96648a384`：新增 `SingularManifoldLocal.lean`，`exists_small_isPL_homeomorph_generalPosition_in_chart` 在任意度量 PL 三维流形的指定图卡内构造有紧支撑的任意小环境 PL 同胚，使两张坐标源片达到一般位置；`exists_small_isPLOn_doublePointSet_crossing_neighborhood_in_chart` 从实际双点构造局部正规形式，保持全源 PL 性、任意小误差、局部单射、纤维数 ≤2 及指定邻域外精确纤维。局部奇点集在图卡内精确由有限带边一维组合流形表示；crossing 的源域显式限制在图卡真实定义域的原像，排除域外默认值产生伪双点。聚焦检查 exit=0、零 warning；F105 审计两个端点仅标准三公理，已推送。`553156344`：`isCompact_doublePointSet_of_isLocallyInjective` 在任意拓扑源与 Hausdorff 目标中证明紧致源上的连续局部单射映射具有紧致双点集，不要求 PL 性或二重纤维上界；证明将非对角等纤维点对识别为紧致子类型积中的闭集。`exists_isOpen_forall_exists_small_isPLOn_crossing_in_chart` 将局部正规化邻域放在误差量 ε 的量词之前：同一个预先选定的开邻域可实现任意小扰动，原端点保持签名并成为推论。两模块聚焦检查 exit=0、零 warning；F106 审计全部 115 个声明仅标准三公理或无公理，源码已推送。多图卡归纳的确切数学缺口是同时保持先前保护区域与新区域内所有实际双点的 crossing；`exists_small_homeomorph_generalPosition_off_subcomplex` 只给固定子复形外的 crossing，未控制其边缘。不能由 C0 小扰动推出 crossing 保持：平面折线 y=max(-x,0) 与 y=abs(x)/2 在原点交叉，将后者向右平移任意 δ>0 后，在 x=δ 与前者切触；沿第三坐标取积给三维 PL 双片反例。须补含图卡折点与固定子复形边缘控制的相对一般位置构造，不能增加结论型假设或据此标记 F5.2 done。仍待：完成 §25 对一般带边三维流形 M 的有限多图卡相对扰动与拼接；单张边界图卡内的完整正规形式已闭合。现有欧氏 crossing 定义保持原语义，不把欧氏端点称作整个 F5.2 完成。 §10.3 范围确认：保持 partial，暂停继续攻多图卡 crossing 保持缺口，消费者为 §25 L.3，届时再定路线。备选设计：奇异 2-胞腔的像紧致，用 F6.2 的 `exists_isPolyhedralManifoldWithBoundary_neighborhood` 取含像的紧致多面体流形片 N 及其 PLPiece T，将问题整体搬到 T 的复形空间；须把欧氏端点的三维欧氏目标推广为高维欧氏空间中的三维多面体流形。 §12.2 最新停点（2026-09-15）：按原映射值的唯一相对内部最小载体 `carrierFace` 实现时，单纯化后的顶点像都是目标顶点，其载体为单点，仿射包约束固定全部顶点像。`CarrierPerturbation.lean` 的 `simplicialMap_eqOn_of_mem_affineSpan_carrierFace` 证明整个映射不变，`doublePointSet_simplicialMap_eq_of_mem_affineSpan_carrierFace` 证明双点集精确不变，`not_disjoint_doublePointSet_vertices_of_mem_affineSpan_carrierFace` 证明任何既有顶点双点都不能移离目标顶点集。六个新声明聚焦检查 exit=0、零 warning；AuditF118 连同砖 15/16 共二十二项仅标准三公理。因而固定最小载体的路线不能产生第 2(iii) 步所需的一般位置；须先设计允许离开低维载体、同时保持落在目标片及公共面兼容的扰动。具体反例与待修订义务见 HANDOFF_CODEX_F.md §14。按 §12.2 报告后停在此设计缺口，第 1 步检查点未完成，F5.2 不标 done、不冻结未证端点，也不回到旧多图卡 crossing 保持路线。 §15 已由用户改派为有限 PL 球图卡归纳，原整体载体路线取消。砖 18 `FoldCrossing.lean` 已完成：`exists_isPLHomeomorphOn_straighten_fold` 对任意有限维实赋范空间中互补子空间及两个不重合的商方向构造保持横截子空间的全局 PL 拉直同胚；`hasPLCrossingAt_of_fold` 将一条折线上的两个半平面芽与横截平面芽接到原 `HasPLCrossingAt`。聚焦检查 exit=0、零 warning；AuditF119 两项仅标准三公理。砖 19 停在 §15.1(3) 的固定折边缺口：混合三角形的对顶点可动、公共折边两端却固定时，两张折叠片的共同像边无法移开；相对通用位置仍允许两组四点分别仿射独立，因此不能推出双点处至多一张折叠。`RelativeNormalForm.lean` 的四个支撑声明证明固定面的实际单纯延拓与双点保留，并从现有相对生产者构造保留共同边及全部相对通用位置条件的任意小双折点族。若把最小载体固定边归为固定/固定，边上逐点相等仍不等于邻接混合三角形的曲面芽不变，§15.1(4) 的 crossing 搬运也不能据此应用。聚焦检查 exit=0、零 warning；AuditF120 连同砖 18 共六项仅标准三公理。完整目标缺口、坐标说明与后续所需设计见 HANDOFF_CODEX_F.md §16.2、风险 R11；按 §15.2 报告后暂停，未完成砖 19 零平面分支，未进入砖 20，F5.2 仍为 partial。 | 4k–8k |
| F6.1 | PL 流形中的紧致多面体 | `structure PolyhedronIn (n) (M) [ChartedSpace ℝⁿ M]`（有限复形 `K ⊆ ℝᴺ`、映射 `g`、`BijOn g K.space P`、逐图卡两向 PL）；`IsPolyhedralManifoldWithBoundary 3 (P : Set M)`；`M` 中多面体 3-胞腔 / 2-球面 / CST 的定义；"落在一个 `Int \|St v\|`（即一张图卡）内的多面体对象可搬到 ℝ³" | §23 以后所有流形层陈述 | partial（2026-09-13）：`PolyhedronIn.lean`——`PolyhedronIn n X P := PLPiece n X P`（T2 的 `PLPiece` 即所需结构），`IsPolyhedralBall m P`/`IsPolyhedralSphere m P`（存在一个 PL 片其复形空间是 PL 球/球面），落在一张图卡内的片经 `e ∘ g` 搬到 `ℝⁿ`：`PLPieceIn.isPLHomeomorphOn_chart_image`、`isPolyhedron_chart_image`、`IsPolyhedralBall.isPLBall_chart_image`，反向 `isPolyhedralBall_of_isPLBall_chart`；2026-09-14 砖 1 完成：`PieceTransition.lean`——`PLPieceIn.isPiecewiseAffineOn_transition`、`PLPieceIn.isPLHomeomorphOn_transition`，球/球面的 `isPLBall_of_piece`/`isPLSphere_of_piece` 与 `isPolyhedralBall_of_pieceIn`/`isPolyhedralSphere_of_pieceIn`；路线为共同图卡局部复合及片双射的逆，正向过渡不要求目标环境有限维。聚焦检查 exit=0、零 warning，AuditF18 六端点仅标准三公理；源码提交 `d5fdb2d33` 已推送；2026-09-14 砖 2 完成：`ManifoldInvariance.lean`——细分的反向流形不变性、`IsCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn` / `IsCombinatorialManifold.of_isPLHomeomorphOn`，及 PL 球/球面的组合流形推论。零维用有限载体排除非退化线段，正维用 link 细分不变性；反向细分只要求细分复形有限。聚焦检查 exit=0、零 warning，AuditF19 六端点仅标准三公理；源码提交 `46963b844` 已推送；2026-09-14 砖 3 完成：`PieceRestrict.lean`——`IsPiecewiseAffineWithinAt` / `IsPiecewiseAffineOn` 的 `inter_of_isPolyhedron`、`inter_preimage_of_isPolyhedron`，`PLPieceIn.restrict` 及 `restrict_complex`、`restrict_map`。有限多胞形族作乘积并取交，交集限制无需有限维假设；片限制保持原映射且双向图卡 PL。聚焦检查 exit=0、零 warning，AuditF20 七端点仅标准三公理；源码提交 `96eaa7048` 已推送；2026-09-14 砖 4 完成：`PolyhedralManifold.lean`——`IsPolyhedralManifoldWithBoundary` / `IsPolyhedralManifold`，选片无关、从任意有限维片引入、紧致性、球/球面的流形推论及无边界到带边界转换。聚焦检查 exit=0、零 warning，AuditF21 两定义及九端点仅标准三公理；源码提交 `d76a084f8` 已推送。F6.1 的片、球/球面及多面体流形基础 API 已完成；CST 专用对象随对应消费者落实 | 3k–5k |
| F6.2 | 开子集的局部有限三角剖分与穷竭（Moise 8.2/8.3 的 PL 版） | `theorem exists_exhaustion_of_isOpen ... : ∃ N : ℕ → Set M, (∀ i, IsCompact (N i) ∧ IsPolyhedralManifoldWithBoundary (m + 1) (N i) ∧ N i ⊆ interior (N (i + 1))) ∧ ⋃ i, N i = U`；相容局部有限三角剖分由 F6.3 的塔表示提供 | §35.1–35.2（局部有限性）、§36.1 | done（2026-09-15；紧致穷竭与 F6.3 的相容塔表示均已闭合）。`ExhaustionGeneral.lean` 的 `exists_exhaustion_of_isOpen` 适用于任意 Hausdorff、第二可数、非空 PL `(m+1)`-流形，无紧致性假设；每项紧致且为带边多面体 `(m+1)`-流形，`N i ⊆ interior (N (i+1))`，并集恰为给定开集。原生产者、聚焦检查与 AuditF26 记录保持有效。单独的集合穷竭不携带三角剖分相容性；该部分由 F6.3 的 `exists_locallyFinitePieceTower_of_isOpen` 提供（`bfd458cdc`，AuditF114 仅标准三公理）。 | 8k–15k |
| F6.3 | 局部有限三角剖分塔（有限片上升、内核不再重分） | 已实现：`LocallyFinitePieceTower n X U` 含相对 U 的 `subset_nhdsWithin`、有限片覆盖 U、下一层内核覆盖上一层、显式内核像子复形、`IsGlueIso` 嵌入及 `map_embed` 一致性；`IsLocallyFinitePolyhedralManifoldWithBoundary` 要求各阶段为组合带边流形；存在端点 `exists_locallyFinitePieceTower_of_isOpen`。 | E.1、E.2、E.3 | done（2026-09-15，表示、局部性与一般存在均闭合）。`LocallyFinitePieceTower.lean`（`677fcbce4`）定义塔与局部有限谓词，`ofPiece` / `IsPolyhedralManifoldWithBoundary.isLocallyFinite` 给紧致常值塔，`exists_core_of_isCompact` / `core_space_eventually` 给紧致捕获及内核单调性，`exists_glue` 沿实际单纯映射拼接内核上一致的映射族；紧致局部有限对象反向得到有限多面体流形。`RelativeDerivedNeighborhood.lean`（`891d666a4`）闭合 F4.2-rel：相对 K₀ 的二次重心细分固定 K₀ 原单形，在该细分上限制普通导出邻域；`relativeDerivedNeighborhood_space` 从 K₀ 处 L 的相对邻域条件证明两者支撑相同，`faces_subset_relativeDerivedNeighborhood` 保留 K₀，`IsLocallyCombinatorialManifoldWithBoundary.relativeDerivedNeighborhood` 及全局版本给带边流形性，邻域 API 保留 L。两文件聚焦检查 exit=0、零 warning；AuditF108 共 45 声明仅 propext、Classical.choice、Quot.sound。图卡拼接局部性也已完成（`97eeade38`）：`RelativeSubdivision.lean` 的 `exists_isSubdivision_extension_of_disjoint` 与 `exists_isSubdivision_restrict_space_preserving_subcomplex` 固定不交子复形；`RelativeGluing.lean` 的 `PLPieceIn.exists_glue_preserving_subcomplex` 保留内核像和映射；`ChartGlue.lean` 的 `exists_glue_chart_preserving_subcomplex` 从闭星邻域避开图卡多胞形原像得到精确 `IsGlueIso` 嵌入与 `map_embed`。`Gluing.lean` 新增带复形、映射等式的 `exists_glue_of_full`；两个旧拼接端点签名保持，成为新端点推论。四个修改模块检查 exit=0、零 warning；AuditF109 共 56 声明仅标准三公理。`d71a6fee3` 进一步给出闭星控制：`regularNeighborhoodIn_space_subset_of_isSubdivision`、`regularNeighborhoodIn_gluedComplex_subset`、`exists_glue_with_regularNeighborhood`、`exists_glue_chart_with_regularNeighborhood` 证明新片的内核闭星像包含在旧闭星像中，可持续加入避开该固定紧集的图卡；三个模块检查 exit=0、零 warning，AuditF110 共 61 声明仅标准三公理。欧氏坐标搬运已完成（`0c500ae65`）：`PieceTransport.lean` 在归一化环境维数时保留原单形、内核映射及闭星像；`SubdivisionTransport.lean` 给 `IsGlueIso.trans`、实际单纯映射复合及闭星搬运，三个修改模块检查 exit=0、零 warning，AuditF111 共 72 声明仅标准三公理。有限图卡递推已完成（`58d76ba3c`）：`RelativeExhaustion.lean` 的 `PLPiece.exists_union_charts_with_regularNeighborhood` 和 `exists_neighborhood_preserving_subcomplex` 在保留内核单纯同构、映射及闭星像控制的同时，为任意紧集扩大片的邻域；`ChartGlue.lean` 的强端点显式沿用源端 DecidableEq 实例。两个修改模块检查 exit=0、零 warning，AuditF112 共 75 声明仅标准三公理。相对流形邻域抽取已完成（`d14f605dd`）：`RelativeMesh.lean` 的 `exists_isSubdivision_diam_lt_preserving_subcomplex` 将未变小的新单形限制在旧内核闭星中；`RelativePieceNeighborhood.lean` 的 `PLPieceIn.exists_manifold_neighborhood_preserving_subcomplex` 保留原内核单形，构造覆盖指定紧集的新内核，并证明其闭星像位于新流形片内部。三层闭星的距离控制和 F4.2-rel 给出该结论；`isPLSphere_geometricLink_of_mem_interior` 给任意片内部顶点的球面 link。三个修改模块检查 exit=0、零 warning，AuditF113 共 80 声明仅标准三公理。最终存在定理已闭合（`bfd458cdc`）：`RelativeExhaustion.lean` 的 `PLPiece.exists_manifold_neighborhood_with_core` 组装保留内核的图卡扩张和流形邻域抽取；`LocallyFinitePieceTowerExistence.lean` 的 `exists_locallyFinitePieceTower_of_isOpen` 从开集的紧致覆盖递推有限流形片，保留真实内核单纯同构及映射，上一阶段落在下一阶段内核中，并证明并集恰为 U；`isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen` 给表示谓词的开集实例。适用范围与 §10.1 一致：T2、第二可数、非空 PL 正维流形；无全空间紧致假设。两个修改模块聚焦检查 exit=0、零 warning；AuditF114 共 83 声明仅 propext、Classical.choice、Quot.sound。E.2/E.3 的 F6.3 前置已解除，交由 E 车道继续。§10.3 改派有效，砖 11 取消，不进入 S.* / P.*；整合 `f211579f1` 已合入 C、S、H、E.0，验证脚本已恢复共享 olean 路径，仅重检本次修改的模块。 | 4k–8k |
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
| P.1 | 平面多边形 Schoenflies（Moise 3.6）与组合形式 5.3 | F 原生规范链 `PolygonalSchoenflies.lean` 的 `isPLBall_of_isPLSphere_one`、`exists_polyhedral_region_of_isPLSphere_one`；S vendored 链 `External/ClassificationOfSurfaces/Moise/PolygonalSchoenflies.lean` 与原生桥接 `PlanarSchoenflies.lean` 保留 3.7 相对整直 | §17, §21.4, §26.7, §27.2 | done（两条证明：F 原生为规范陈述，S vendored 提供 3.7）；F 的 `8b87ef710` / `a036bf104` 由 Jordan 分离和横截弧三角剖分归纳证明有界内区域闭包为 PL 2-球，AuditF104 仅标准三公理。S0.1/S0.2 的 16 个 vendored 模块与桥接给 `exists_isPLHomeomorphOn_straighten` / `_of_isPLSphere_one`：全平面双向 PL 环境同胚固定指定开集之外；修改记录见 `External/ClassificationOfSurfaces/VENDOR.md`，AuditS1/S2/S10 仅标准三公理。后续不再重复证明 P.1，只按需桥接两条链 | 16 个外部模块 + 原生规范链与 1084 行相对桥接 |
| P.2 | 5.4：多面体 2-胞腔边界间 PLH 延拓 | `BallFrontier.lean` 的 `exists_isPLHomeomorphOn_of_frontier`，取 `n = 1` 得平面 PL 2-球；一般形式作用于 ℝ^(n+1) 中的 PL (n+1)-球。消费 S.1 与 F 的 `exists_isPLHomeomorphOn_of_boundaryComplex` | §17.10, §33 L13, §34 | done（2026-09-14，`ff7fc67ca`）；任意给定实际 frontier 上的 PL 同胚延拓到球，并逐点保持边界映射；`IsPLBall.isPLSphere_frontier` 同时给边界球面性。检查 exit=0 零警告，AuditS6 四项仅标准三公理；`91172ea49` 的 `IsPLBall.interior_nonempty` / `closure_interior` 证明所有正维同维欧氏 PL 球内部非空、内部闭包等于原球，供平面盘识别使用 | BallFrontier 及 PLImage 公共 API |
| P.3 | 3.3 / 17.2–17.3：2-胞腔分解的两个自由胞腔及相对形式 | vendored `TriangleMesh.exists_two_geometricallyFreeTriangles_of_polygonalDisk` 给两个不同几何自由三角形；原生桥接给全空间 PL 删除及保留指定三角形的归纳；F 的精确字段为 `SchoenfliesInput.exists_two_free_disk_cells`：对共同有限三角剖分上的 `IsPLDiskDecomposition K cells`、`1 < cells.card`，给两个不同的 `C,D ∈ cells`，均满足 `IsFreeDiskCell K`，允许任意 PL 圆盘胞腔 | §17.5, §17.9–17.12 | **done**（2026-09-15）。原有自由三角形删除、保留指定三角形的相对归纳与球面网格删除保持。一般 17.2 由 `08ee37003` 的 `FreeDiskCell.lean` 给出，`IsPLDiskDecomposition.exists_two_free_disk_cells` 对任意有限维实赋范空间及任意有限 PL 盘胞腔分解成立；AuditS61/S62 仅标准三公理。一般相对 17.3 由 `f0383a381` 的 `RelativeFreeDiskCell.lean` 闭合：`exists_free_disk_cell_not_subset` 对由胞腔子族组成的指定真盘 D，给不包含于 D 的自由胞腔。证明先找有非平凡外边界迹的外部胞腔，再在必要时分盘并于 D 的另一侧应用 17.2，最后平面化搬运。未将指定真盘缩弱为一个指定胞腔。两模块聚焦检查 exit=0、零警告；AuditS77RelativeDisk 四项仅标准三公理 早期相对删除与网格桥接见 `4fffc8f99`、`91172ea49`、`80fceca30`（AuditS13/S17/S20）；球面网格局部删除与保留指定三角形归纳见 `9701b821a`、`2fe7240ef`（AuditS37–S39），星内交集仅要求纯二维。整合分支原记录的 17.3 缺口由上述一般相对端点补齐 | 17.2–17.3 已闭合 |
| P.4 | 10.8：ℝ² 中有限线性图驯顺，支持在给定开集内并按正控制函数逼近恒等 | §10 定理 6–8（框架定理 10.6 + 收缩族） | §17.2（胞腔复形可视为多面体） | **done（本行有限图范围，S，2026-09-16；无 hSchoenflies）**。`138e73e21` 的 `PiecewiseLinear/PlanarGraphTameness.lean` / `Graph.IsDrawing.exists_homeomorph_isPolyhedron_image_dist_lt`：任意有限平面图的实际绘图、包含全图的开集 U，以及在 U 的每个紧子集上有正下界的函数 ε，产生平面同胚 e，使全图像满足原生 `IsPolyhedron`、每条边像满足 `IsPLBall 1`，固定全部原顶点及 U 外所有点，且对每个 x ∈ U 有 dist (e x) x < ε x。强正假设按书页 46 原定义，不要求连续；连续正函数版本为推论。`27677c894` 的 `EndpointAccess.lean` 通过删端点后局部有限整直、收缩开链、简单多边形弧链和极限参数化生产辅助端点弧；`3f0d19da7` 的 `EndpointStraightening.lean` 由此消掉度至少为 2 的限制，覆盖度 1 和孤立顶点。小盘层由已构造的任意小 PL 盘邻域、有限 frontier 扰动及同时横截弧整直组成；无需把书中的恰二交点框架作为额外输入。`866b2535e` 给短边的统一位移界；`93d1aa39d` 的 `ArcFamilyDrawing.lean`、`GraphSubdivision.lean`、`GraphApproximation.lean` 构造真实有限细分，保留原点集及顶点，以短边整直消掉直径限制，再在 U 内取紧邻域得到完整强正逐点控制。最后五个改动/新模块聚焦检查 exit=0、零警告；AuditS144–S146 共 16 项仅标准三公理。整合分支 bbd488861 已合入；逐层证据与源差异见 HANDOFF_CODEX_S.md，既有方框链出处见 docs/third_party/PlanarArcNeighborhood.md；本轮没有 vendored 源码修改。书中非有限局部有限图的扩展不在本行范围，未声称交付 | 6k–10k |
| P.5 | 2.7–2.8 θ-图、4.4 盘中两弧不分离、Problem 4.1 | 第一批 `PolygonalTheta.disjoint_interior13_interior23`、`closedRegion13_inter_closedRegion23`、`closedRegion_eq_union` 给多边形 θ-图的区域分解、交集与内部不交 | §26.7, §27.2, §30.1 | partial（2026-09-14）；以上三项 AuditS5 仅标准三公理。任意弧版本 4.4 与 Problem 4.1 未闭合；第二批 `PolygonalFamilyPolyhedron` 的有限多边形族兼容细分也未提供这两个结论，故 S0.3 未触发 | 2k–4k（剩余估计） |
| H.1 | 有限复形的单纯 ℤ-链、边界、`H₁`、`H₂`、`H₃`，`p¹`（秩），`χ` 与 Euler–Poincaré | D3；本库 `EulerCharacteristic.lean` 的 `faceEulerChar` 复用 | §21–23, §24.8, §28, §31–§34 | **done（2026-09-16，行状态此前未同步）**：χ 工具箱在 `EulerPolyhedra.lean`；Betti 数与 Euler–Poincaré 在 `Homology/BettiNumber.lean` 与 `BettiPolyhedra.lean` （`eulerChar_eq_sum_bettiNumber`、`eulerChar_eq_one_sub_bettiOne_add_bettiTwo`）；几何实现与面 Euler 数的桥 `eulerChar_geometricSpace_eq_faceEulerChar`；维数以上奇异同调消失 `isZero_singularHomology_geometricSpace_of_card_le`。全部经 H 车道审计，仅标准三公理 | 8k–12k |
| H.2 | 顶维相干定向、边界定向、子流形与倍化；H.2a 线性细分及 PL 不变性；H.2b 定向上循环 | `CoherentOrientation n K`、`IsOrientable n K`；`isOrientable_iff_of_isSubdivision`、`isOrientable_iff_of_isPLHomeomorphOn` 保留源复形的 `IsCombinatorialManifoldWithBoundary n K`，有限复形；PL 版本的环境有限维。`isOrientable_of_isPLBall` / `isOrientable_of_isPLSphere` 的定向维数均为 `n`；闭星接口为 `isOrientable_faceStarComplex` / `exists_unique_coherentOrientation_comparison_faceStarComplex`。`OrientationCocycle.lean` 提供 `orientationCocycle hK o`、`orientationCocycle_isCoboundary_iff`、`exists_orientationCocycle_of_not_isOrientable`，任意 `n`、有限维环境、有限复形，无公开 `[DecidableEq E]` | §24.7–24.8, §24.11, §26.8, §33 L11 | H.2a/H.2b done（2026-09-15）；已有定向基础、边界、子流形、倍化；H.2a `87b44df51` 闭合任意线性细分双向不变性、PL 不变性、PL 球/球面可定向及闭星恰两个相容顶维定向（先统一顶点序，不声称原始结构恰两元素），53 项核心及 22 项复用声明仅标准三公理。H.2b 按交接 §7.3 比较每个非空面闭星的局部定向，证明上边界当且仅当可定向，给 C.4 非上边界上循环；构造层提交 `85cd6e095`。所有目标模块检查 exit=0、零警告；H.2b 的 12 项核心及 12 项复用声明仅标准三公理，登记见 `MOISE_PLAN.md` §6。旧“非顶维边取 0”构造未使用 | H.2a/H.2b 无未闭合端点；C.4 的覆盖可定向性仍属 C 车道 |
| H.3 | §21：开胞腔复形的 χ 与运算 α–δ 不变；21.6 `χ(J) = 0`；21.7 2-胞腔 `χ = 1`；21.8 加法；21.10–21.11 分裂与张成 | 组合陈述于多面体曲面 | §22, §23.18–19, §28.20, §30.4, §33 L7 | done（2026-09-16，`9bcc38d82`）：`EulerCellOperations.lean` 证明 α–δ 单步及有限迭代保持开胞腔计数 χ，将三维数桥回 `faceEulerChar`，并给按面并集的包含排除与 PL 多边形交的 21.8 加法；21.6、21.7 复用已证 PL 1-球面/PL 球 Euler 端点。`SurfaceSplitEuler.lean` 以公共核心、乘积环带、双多边形边界及两 PL 2-胞腔定义分裂和封口，证明 21.10 χ 不变与 21.11 χ 增 2。两模块 exit=0、零 warning；AuditHM7 的 39 项均至多标准三公理 | 306 行 |
| H.4 | §22：22.5 `χ = 2 − (2h + m)`、22.6–22.7 `p¹` 与 `χ`、22.8–22.10 分类（可定向 + χ 决定同胚型）、22.11 单连通 ⟹ 2-球面、Problems 22.11–22.12 | 只对**多面体**紧致曲面陈述；22.11 用于 §30.6、§32。2026-09-17 的 H-M2 已确认 §33 L11–L12 不需要 22.8–22.10：L10 已给基本群同构，L13 会另造保持分块的强 PLH；L12 改走逐边界封盘、H.4a 数值公式与 H.4b 球面识别 | §26.8, §28.6, §30.4, §30.6, §32, §33 | partial（2026-09-17 更新）：22.5–22.7、22.11 与 H.4a 已闭合。`SurfaceHomology.lean` 直接计算闭连通组合曲面的有理顶维同调，得到可定向时 `b₂=1`、不可定向时 `b₂=0`，从而无条件证明 22.7 的 `χ=2-b₁` / `χ=1-b₁`；`bettiOne_pos_of_isOrientable_of_eulerChar_ne_two` 给出 H-M1 消费端点。`SurfaceInvariants.lean` 对实际给出的标准柄/交叉帽剖分及其 refinement 证明 22.5，并导出 22.6 的三种数值公式与可定向柄数；这不包含 22.4 正规形存在性。`FieldPathCones.lean` 与 `SurfaceSimplyConnected.lean` 则证明 22.11。22.8–22.10 对主链改标 skip；若以后作为独立库结果实现，仍属本行可选余项 | 主链无需完整分类 |
| H.5 | 23.18–23.19：`h(B) = p¹(N)`（`dim L ≤ 1`）、`p¹(K) ≥ h(Bd \|K\|)`（可定向带边） | 用 23.11–23.16、H.3、H.4 | §24.8 | new | 4k–6k |
| H.6 | 28.11：`K = K₁ ∪ K₂`，`Zⁿ` 在 `K₁` 上、在 `K` 上零调 ⟹ `K₁` 上同调于 `K₁ ∩ K₂` 上的循环 | 本库奇异同调的小链 Mayer–Vietoris，经相容开邻域强形变收缩搬回有限子复形 | §31.4, §34 L4 | done（2026-09-15，`11826f868`、`c9fff0308`；2026-09-17 状态同步）：`MayerVietorisSubcomplex.lean` 的 `exists_mem_inter_of_map_eq_zero` 对任意次数、任意环与系数模给出 28.11，并同时给 `bettiNumber_union_le` / `bettiOne_union_le`。七个模块聚焦检查 exit=0、零 warning；AuditNightHM2 的 83 项仅标准三公理 | 已闭合 |

F 车道同步补充的原生平面输入（至 `d0902b2cd`）：`PolygonalSchoenflies.lean`（与 S 的 vendored 桥接文件
`PlanarSchoenflies.lean` 不同）已提供 Jordan 区域的有限三角剖分与边界子复形、指定端点的 PL 弧匹配、
公共弧映射的圆周及圆盘延拓、沿公共边界弧的 PL 圆盘粘合。新增横截弧两侧闭区域的限制剖分、
精确并交公式与几何边界识别，侧区域三角形数严格下降，指定原顶点处切分的边界弧继续为子复形，
并从内部边构造横截弧、从边界边产生邻接三角形。`Combinatorial` 给开区域闭包的满维面覆盖；
`Subcomplex` 给二次限制、凸包和并集公式；`BoundaryInvariance` 给任意同维有限维环境的边界不进入内部。
这些原生输入补充已完成的 S 车道 P.1/P.2；F 的独立原生 P.1 归纳仍未闭合，不能据此回退 S 的端点状态。

### 4.2 车道 S：§17 PL Schoenflies（`chap:pl-schoenflies`）与 3-胞腔

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| S.1 | 17.1：ℝ³ 中闭 3-流形带边 M 的组合边界等于实际 frontier | `FrontierBoundary.lean` 的 `frontier_space_eq_boundaryComplex_space` 对所有正维 ℝ^(n+1) 中的有限组合带边流形成立，ℝ³ 取 `n = 2`；另有流形形式 `frontier_eq_polyhedralBoundary` 与边界点球邻域 | §17.12, §23.8 | done（2026-09-14，`a04d993c4`）；整合 E3 的 `702c1fa19`/`f40a9b3f7` 证明并适配 F 的规范 `BoundaryInvariance`，将流形边界定义独立置于 `PolyhedralBoundary.lean`。检查 exit=0 零警告，AuditS3 六项（含显式 ℝ³ 签名）仅标准三公理；不重复实现 E3 的证明 | 84 + 513 行整合源码 |
| S.2 | 17.4–17.8 推移性质 | `HasPushPropertyAt C D`、`HasPushProperty C` 保留精确邻域条件 `C \ J ⊆ interior N`；17.5 `exists_isPLHomeomorphOn_straighten_disk_in_tetrahedron`，17.6 `hasPushProperty_convexHull_simplex`，17.8 `exists_hasPushProperty_of_isSimplyEmbedded` | §23.10, §33 末, §34 | done（2026-09-15）；17.4 面推送与 17.7 环境 PL 不变性保留。`9701b821a` 从局部受保护边族的平面删除构造保持整个四面体的环境删除；`2fe7240ef` 在固定兼容剖分上按三角形数归纳，先保留指定小三角形，再比较原盘与原始面，闭合任意边界盘的完整 17.5。`16ade009b` 闭合 17.6、17.8，单嵌入定义保留每个凸开邻域的量词。21 个受影响或指定复核模块的最终聚焦检查均 exit=0、零警告；AuditS38 四端点、AuditS39 的 17.4–17.8 十项均仅标准三公理。无占位证明债、Brouwer 类或等价结论假设 | 分模块端点与验证记录列于下方 |
| S.3 | 17.9–17.11：凸多面体 3-胞腔、盘与点之 join、沿平面盘拼合的球面单嵌入 | F 的冻结接口 `SchoenfliesInput.lean`：`.isSimplyEmbedded_frontier_of_convex`、`.isSimplyEmbedded_frontier_coneComplex`、`.isSimplyEmbedded_union_sdiff_diskInterior`；17.11 的盘位于非零线性形式的同一层，删除 `D \ (f '' stdSimplexBoundary 2)`；精确参数与量词以源码字段为准 | §17.12 | **done**（2026-09-15）；`ConvexStraightening.lean`（`97995c328`）、`ConeStraightening.lean`（`26d321906`）、`PlanarDiskGluing.lean`（`f1d104761`，线性层形式 `caa641003`）给三个无条件生产者，均保留每个凸开邻域外恒同。结合一般 17.2，`SchoenfliesFoundations.lean` 的 `schoenflies_input : SchoenfliesInput` 已由 `08ee37003` 证明；四字段签名未修改，无未证输入。聚焦检查 exit=0、零警告；AuditS55/S61/S62 仅标准三公理 | 模块与验证见下方 |
| S.4 | **17.12 PL Schoenflies** | 冻结目标 `isSimplyEmbedded_of_isPLSphere_two (I : SchoenfliesInput) (hS : IsPLSphere 2 S) : IsSimplyEmbedded S`；`exists_isPLBall_of_isPLSphere_two (I : SchoenfliesInput) (hS : IsPLSphere 2 S) : ∃ B, IsPLBall 3 B ∧ frontier B = S ∧ Bornology.IsBounded B`，`S : Set (EuclideanSpace ℝ (Fin 3))`。F 车道负责 `Ind S` 与 L1–L6，S 车道生产显式接口。 | §23.9, §28.1 后半, §30.5, §33 末 | **done 且无条件（2026-09-16）**：`Schoenflies.lean` 的 `isSimplyEmbedded_of_isPLSphere_two` 与 `exists_isPLBall_of_isPLSphere_two` 条件于 `SchoenfliesInput`；S 车道的 `schoenflies_input` 实例把它消掉，`PLSchoenflies.lean` 给无条件形式 `IsPLSphere.isSimplyEmbedded`、`IsPLSphere.exists_isPLBall_frontier_eq`。92 个模块重编 exit 0、零警告，250 项审计仅标准三公理 | 8k–12k |
| S.5 | 23.9–23.11 流形版：顶点开星内球面填充、相对推移、沿边界盘拼合 3-胞腔 | `SchoenfliesManifold.lean`：`exists_isPolyhedralBall_of_isPolyhedralSphere_in_openStar`；`PushManifold.lean`：`exists_isPL_homeomorph_push_between_disks_in_openStar`；`BallGluingManifold.lean`：`isPolyhedralBall_union_of_inter_isPolyhedralBall_two`，并保留图卡、PL piece 与欧氏形式 | E3 的 §26.2、§25 Lemma 1；F4.3；F4.2 的 3D 部分；§23.12、§23.18、§32 | **done 且无条件（2026-09-16）**：23.9/23.10 的显式 `hSchoenflies` 参数已随 17.12 的无条件化删除（`SchoenfliesManifold.lean`、`PushManifold.lean`）；23.11 本来就无条件。树中已无 PL 侧的 `hSchoenflies` | 实现与审计见下方 |
| S.6 | 30.5：嵌套拓扑 3-胞腔 `C₁ ⊆ Int C₂`、`Cl(C₂ − C₁)` 球壳 ⟹ 中间有多面体 3-胞腔 | 用 30.4（车道 I）+ S.4，并需 `TopologicalCellComplementConnected` 排除 `C₂ᶜ` 的额外有界分支 | §34 L3 | blocked（2026-09-17 H-M3 评估）：除 I.4 外，任意拓扑 3-胞腔补集连通仍缺一般拓扑球面的 Jordan–Brouwer。现有 `JordanBrouwer` 的紧致像证书消费者可直接复用，但证书生产需真正的专门 Alexander 对偶；`SpecializedAlexanderDuality` 当前只是条件，且从分支数生产它的反向定理对本目标循环。wild sphere 无 smooth/open-bicollar，树中无 Čech/紧支撑理论。最窄无 `sorryAx` 路线估 10k–18k 行；未获批准前不启动 | 30.4 后仍有独立大前置 |
| S.7 | §33 末尾引用的 3-胞腔延拓（书中编号疑为笔误，§18 是 Antoine 集）：`Bd C_v ↔ Bd C''_v` 的 PLH 延拓到 3-胞腔 | S.4 + F3.4 | §33, §34 (5)–(7), §35 | **done（2026-09-16）**：`ThreeCellExtension.lean` 的 `exists_isPLHomeomorphOn_extension_of_threeCell` 是 P.2 的一般定理 `exists_isPLHomeomorphOn_of_stdSimplexBoundary` 在 `n = 2` 的实例；该定理对任意维数成立，本行原先被误记为未开始。§33 收尾与 §34 的六步延拓都消费它 | 0.5k |

#### §17 逐条接口与当前缺口（S 车道，2026-09-15）

以下用 `E3 := EuclideanSpace ℝ (Fin 3)`，`C(T) := convexHull ℝ (T : Set E3)`。
原书核对范围为书页 117–122（本地 PDF 页 127–132）。推移性质定义在书页 118：
`N` 是 `C \ J` 的闭多面体邻域，**不是** `closure (C \ J)` 的邻域。
二维盘在 ℝ³ 中的环境 `frontier D` 等于 D，不能充当其内在边界圈。
原生定义对每个 `f : (Fin 3 → ℝ) → E3`、`IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3)) D`
使用 `J := f '' stdSimplexBoundary 2`，要求 `C \ J ⊆ interior N`；所得 h 是全空间双向 PL 同胚，
把 D 送到 `closure (frontier C \ D)`，且在 N 外恒同。`HasPushPropertyAt` 明确包含 C 为 PL 3-球、
D 为 PL 2-球及 D 位于 frontier C，`HasPushProperty` 对所有这样的 D 量化。
`SimplexBoundaryImage.lean` 证明任意单形参数化给出同一个几何边界，避免依赖参数化的圈定义。

- **17.4，已证。** T 是三个仿射无关顶点，a 不在 T 中，`insert a T` 仿射无关，则
  `hasPushPropertyAt_convexHull_simplex_face` 给 `HasPushPropertyAt (C (insert a T)) (C T)`。
  更一般的 `exists_isPLHomeomorphOn_push_simplex` 在任意有限维实赋范空间中，把至少一维单形
  `C T` 送到 `⋃ v ∈ T, C (insert a (T.erase v))`，固定边界及指定多面体邻域之外。
  证明由相对 PL 函数延拓、支持于开星邻域的顶点小移动、连通参数空间上的锥顶移动组成；没有径向
  投影为 PL 的假定。`closure_frontier_convexHull_sdiff_face` 将目标并集识别为所需的补盘闭包。
- **17.5，已证（`2fe7240ef`）。** `SimplexDiskStraightening.lean` 的
  `exists_isPLHomeomorphOn_straighten_disk_in_tetrahedron`：对四面体 C(T)、`IsPLBall 2 D`、`D ⊆ frontier (C T)`、
  `IsOpen W`、`C T ⊆ W`，存在 h 和 `v ∈ T`，满足
  `IsPLHomeomorphOn h univ univ`、`h '' C T = C T`、`h '' D = C (T.erase v)`、`EqOn h id Wᶜ`。
  书中路线是在边界三角剖分中保留一个三角形，依次删除另一个自由三角形，并把每次盘内 PL 移动经
  内外两侧的锥延拓为保持整个四面体的环境移动。P.1 的完整全平面相对形式现已闭合。
  当前已闭合的实际生产者如下：

  - `ConeHalfSpace`、`ConeIntersection`、`SimplexCorner`、`SimplexCornerFrontier` 从四面体、指定顶点和 W
    构造两侧锥并证明精确交集、frontier 和支撑控制，已消掉原先的几何占位条件。
  - `exists_isSubdivision_subcomplexes_closedStars_subset_openStar` 保留 D 为子复形，同时使每个面各顶点
    闭星的并落在某个原始顶点开星内；`IsSubdivision.closedStars_subset_cover` 保证任意后续公共细分继续满足它。
  - `exists_isPLHomeomorphOn_simplex_vertex_star_euclidean` 给真正的平面坐标，在每个原始面上仿射，
    把星的边界送到实际 frontier、开星送到实际 interior。`SimplexAffine` 提供跨环境的仿射单形坐标。
  - `exists_isPLHomeomorphOn_extension_simplex_vertex_star_of_chart` 把坐标内的 PL 自同胚延拓成环境同胚，
    保持 C(T)，固定整个对面和 W 外；对任意边界子集给出星内共轭像与星外原集的精确并集公式。
  - `exists_isPLHomeomorphOn_straighten_to_face_in_simplex_vertex_star` 对**整个 D 位于一个原始开星内**的情形，
    将 D 整直到任意指定剖分三角形；`exists_isPLHomeomorphOn_straighten_disk_in_simplex_vertex_star` 从原生
    `IsPLBall 2 D` 自行产生该三角形。面包含引理保证坐标在任意 D 的剖分面上仿射，不额外假定剖分兼容性。

  - `PlanarRelativeDeletion`、`PlanarRelativeSubcomplex` 用受保护边族固定局部盘之外每个三角形的边界，
    由平面紧盘识别推出这些三角形集合保持，并给整个纯二维网格的精确删除后像。
    `PlanarChartDeletion` 把该结果搬到逐面仿射的平面坐标；不要求整个坐标交集为圆盘。
  - `SimplexDiskDeletion` 把图内三角形与对面中的固定部分分开，通过内外锥扩张给整个球面圆盘的精确像。
    `SimplexDiskStraightening` 保留一个小三角形不作删除，在固定剖分和固定平面模型上按三角形数递降归纳。
    分别将原盘和含该小三角形的原始面送到这个小三角形，再复合一方的逆映射得到最终整直。

  完整端点只要求四个仿射无关顶点、`IsPLBall 2 D`、D 位于实际 frontier、指定开邻域包含四面体。
  它自行产生剖分、平面模型、自由三角形、环境扩张和最终原始面；保留所有支撑控制。
  聚焦检查 exit=0、零警告，AuditS38/S39 的端点仅含标准三公理。
- **17.6，已证（`16ade009b`）。** `TetrahedronPush.lean` 的 `hasPushProperty_convexHull_simplex`：
  T 有四个仿射无关顶点，则 `HasPushProperty (C T)`。由 17.5 整直任意边界盘，应用 17.4 后以 17.7 搬回。
  原有邻域条件与盘参数化量词保持不变；检查 exit=0、零警告，AuditS39 仅标准三公理。
- **单嵌入，已落源码（`16ade009b`）。** `SimplyEmbedded.lean` 的 `IsSimplyEmbedded S` 表示 `IsPLSphere 2 S`，且对每个
  `Convex ℝ W`、`IsOpen W`、`S ⊆ W`，存在全空间 PL 同胚 h 与四个仿射无关顶点 T，
  使 `h '' S = frontier (C T)`、`EqOn h id Wᶜ`。这保留书中对每个凸开邻域的量词。
- **17.7，已证。** `HasPushPropertyAt.image`、`HasPushProperty.image`、`hasPushProperty_image_iff`。
  证明通过共轭，同时搬运盘的参数化、内在边界圈、多面体邻域、补盘闭包和支撑条件。
- **17.8，已证（`16ade009b`）。** `SimplyEmbedded.lean` 的 `exists_hasPushProperty_of_isSimplyEmbedded`：
  由 `IsSimplyEmbedded S` 得
  `∃ C, IsPLBall 3 C ∧ frontier C = S ∧ Bornology.IsBounded C ∧ HasPushProperty C`。
  证明将 17.6 的四面体沿单嵌入环境同胚的逆搬回，边界由同胚保持，球的紧性给有界性。
  检查 exit=0、零警告，AuditS39 仅标准三公理；没有把推移性质作为额外输入。

S.2 验证记录：`.lake/scratch/S2-VERIFICATION.json` 保存源码提交 `16ade009b`、21 个模块的最终
检查结果与源码 SHA-256；`.lake/scratch/audit-simplex-disk-straightening.log`、
`.lake/scratch/audit-s2-push-property.log` 保存完整端点签名与公理输出。
接收 C 线程交错编辑后的 FaceStarBoundary/FaceStarDeletion/PlanarFreeFace 复核见 AuditS29；
本轮未改 vendored Lean 源码，原生适配与各层差异见 `External/ClassificationOfSurfaces/VENDOR.md`。

- **17.9，已证（`97995c328`）。** `ConvexStraightening.lean` 的
  `isSimplyEmbedded_frontier_of_convex`：`Convex ℝ C`、`IsPLBall 3 C` 推出
  `IsSimplyEmbedded (frontier C)`，多面体性由球性导出。证明经凸边界锥表示、受支持的自由四面体删除及 17.10。
- **17.10，已证（`26d321906`）。** `ConeStraightening.lean` 的
  `isSimplyEmbedded_frontier_coneComplex` 对有限 `L`、`IsPLBall 2 L.space`、`IsConeBase p L`
  给锥边界的单嵌入；不要求原底盘已经位于平面。
- **17.11，已证（`f1d104761`、`caa641003`）。** `PlanarDiskGluing.lean` 的
  `isSimplyEmbedded_union_sdiff_diskInterior` 给仿射平面形式，
  `isSimplyEmbedded_union_sdiff_diskInterior_of_subset_fiber` 匹配 F 的非零线性层字段。
  给参数化 `f`、`J := f '' stdSimplexBoundary 2`，结论是
  `IsSimplyEmbedded ((S₁ ∪ S₂) \ (D \ J))`。删除盘的内在内部；完整凸开邻域支持量词保留。
- **17.2，一般胞腔分解已证（`08ee37003`）。** `FreeDiskCell.lean` 的
  `IsPLDiskDecomposition.exists_two_free_disk_cells` 允许任意有限维实赋范空间、共同有限三角剖分及任意 PL
  圆盘胞腔。`DiskDecomposition` 平面化与子族限制、`DiskCrosscut`、`PlanarDiskSplit`、
  `PlanarDiskDecomposition` 的自由性传递组成严格子族归纳。避开一个指定胞腔的推论也已证；17.3 的真盘子复形版本仍未证。
- **给 F 的完整输入（`08ee37003`）。** `SchoenfliesFoundations.lean` 的
  `schoenflies_input : SchoenfliesInput` 包含上述四个已证字段。接口与 F 的 `44806ee61` 原文件相同。
  AuditS61 检查完整结构及精确三维第四字段，公理只有标准三项。
- **17.12，由 F 车道负责。** 本分支未实现或声明该定理已证；F 可将已证 `schoenflies_input` 代入其条件接口。
- **23.9/23.10，条件形式已证。** `SchoenfliesManifold.lean` 与 `PushManifold.lean` 显式接受
  `∀ S : Set (EuclideanSpace ℝ (Fin 3)), IsPLSphere 2 S → IsSimplyEmbedded S`。
  前者在原顶点开星内填充；后者在给定多面体邻域内推移两张互补边界盘，保持邻域外恒同，且不要求整个邻域包含于图卡。
- **23.11，无条件已证。** `BallGluing.lean` 给共同有限维环境及欧氏三维形式；
  `BallGluingManifold.lean` 给任意有限组合三维流形形式，球不必处于同一顶点星。
  交集必须是位于两球 frontier 内的 PL 二维球，结论为并集的 PL 三维球性。

S.3/P.3/S.5 最终核验（2026-09-15，数学提交 `08ee37003`）：9 个端点模块检查均 exit=0、零警告；
AuditS62 的 16 项传递公理闭包均仅 `propext`、`Classical.choice`、`Quot.sound`。
`.lake/scratch/S3-P3-S5-VERIFICATION.json` 记录源码散列与日志路径；
`.lake/scratch/audit-s3-p3-s5-final.log` 保存最终审计。此前逐层验证与数学差异详见
`External/ClassificationOfSurfaces/VENDOR.md`。本轮没有修改 vendored Lean 文件。
最终文档检查点已 fetch 并 merge `origin/codex/moise-integration`；未改写已发布历史。

2026-09-15 同步已抓取并纳入 F 至 `d0902b2cd`；`9c9002426` 先纳入 `8c1ce1d4f`。
逐砖提交已经发布，因此按禁止重写已发布历史、禁止 force-push 的规则使用普通合并；未将 S 合入任何其它分支。
同步复用 `Polyhedron` 中的 `IsPLSphere.nonempty`，删除 F 在 `PLBallSphere` 的重复声明；保持既有公开名称与签名。
本轮每个修改的原生模块均逐层检查 exit=0、零警告；第一次同步另复查 39 个修改/相关模块，AuditS18 审计 127 项。
最后同步复查 12 个修改/相关模块；`AuditS22.lean` 合并去重后的 198 个声明涵盖 S0、S.1、17.4/17.7、
平面删除、锥几何、星坐标、局部整直及 F 的横截弧输入，检查结果见 `.lake/scratch/final3-*.log`
与 `.lake/scratch/audit-final3-s.log`，均 exit=0、原生零警告，198 个传递公理闭包均仅标准三公理。
验证只使用 S 的 `check-f.ps1` / `audit-f.ps1`，一次一个 Lean；
共享边界 olean 冲突时从 S 源码按规定脚本恢复产物，未改其它车道源码，未运行 lake build，未登记根聚合。

### 4.3 车道 C（1）：§23 三角剖分 3-流形

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| M.0 | 23.1（三角剖分 3-流形是组合流形） | **不需要**：本链所有三角剖分由构造是组合的（T2 经 F3.3；正则邻域经 F4.2；覆盖提升经 C.3）。记录以防有人误加 | — | skip | 0 |
| M.1 | 23.2 / 23.4：边界点的 3-胞腔邻域与边界交成 2-胞腔 | `exists_isPLBall_closedStar_inter_boundary`：有限组合带边流形每个边界点有相对邻域 C，C 是 PL (n+1)-球，C 与边界交成 PL n-球 | §26.2, Problem 26.1–26.3 | partial（2026-09-14）；已整合并审计 E3 的任意有限维欧氏实现形式，ℝ³ 取 n=2；一般流形图卡中的邻域包装未在本车道新增 | 1k–2k |
| M.2 | 23.5–23.7 倍化、组合边界与拓扑边界一致 | D2 下的边界一致性由 `frontier_space_eq_boundaryComplex_space` 和 `polyhedralBoundary_eq_of_piece` 提供；倍化仅 23.13/23.16 使用 | H.5 | partial（2026-09-14）；S.1 整合 E3/F 后，有限欧氏实现（含 ℝ³）及流形边界兼容接口已检查、审计；倍化本身仍未实现 | 1k–2k |
| M.3 | 23.8：闭带边 3-流形在 3-流形内，Bd 等于 Fr | `frontier_eq_polyhedralBoundary`：T2 的 PL (n+1)-流形中，`IsPolyhedralManifoldWithBoundary (n := n+1) (n+1) P` 的 frontier 等于其内在边界 | §28.1 后半, §30.4, §36.1 | partial（2026-09-14）；E3 的有限多面体（因此紧致）版本已整合至 S.1 并经 AuditS3 验证；未声称覆盖任意非紧闭带边流形 | 0.5k |
| M.4 | 23.12–23.13, 23.16：`\|L\|` 与 `N(L)` 组合等价；带边流形是某 3-流形中子复形的正则邻域 | 用 S.5 反复；23.16 需 H.2 | §23.19（H.5） | new | 3k–5k |

### 4.4 车道 C（2）：§24 覆盖空间（`chap:pl-coverings`）

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| C.1 | 24.1–24.4：提升、诱导同态单射、`k`-重覆盖与指标 | `IsPLBall.simplyConnectedSpace`、`.locallyPathConnectedSpace`；`IsCoveringMap.exists_unique_lift_of_isPLBall`、`.injective_fundamentalGroup_map`、`.fundamentalGroup_stabilizer_eq_range`、`.monodromy_eq_iff_mem_range`、`.liftPath_one_eq_iff_mem_range`、`.fundamentalGroupMulAction_isPretransitive`、`.card_fiber_eq_index` | §25 | done（2026-09-15，`CoveringLift.lean`）：24.1–24.4 的九个桥接端点全部闭合；检查 exit=0、零 warning，AuditC1 九端点及 AuditC1Reuse 十八条 D4 复用声明均仅标准三公理，未经过 `HurewiczLowDegrees.lean`；源码提交 `2df0546f5`。 | 1k（桥接） |
| C.2 | 24.5（`k = 2`）：有限复形上的 ℤ₂ 1-上循环构造二重覆盖 | `SimplicialBoolCocycle K`、`IsCoboundary`、`toBoolCocycle`、`isCoveringMap`、`card_fiber = 2`、`connectedSpace_iff : ConnectedSpace TotalSpace ↔ ¬ IsCoboundary` | C.4, C.5 | done（2026-09-15，`DoubleCoverComplex.lean`）：开星上循环产生本库 `BoolCocycle` 二重覆盖；构造无不动点换层映射及两方向截面判据，连通当且仅当非上边界。检查 exit=0、零 warning，AuditC2 二十三端点及 AuditC2Reuse 十一条 D4 复用声明均仅标准三公理，未经过 `HurewiczLowDegrees.lean`；源码提交 `364fbe752`。 | 3k–5k |
| C.3 | 24.6：三角剖分提升到有限覆盖，且组合流形性保持 | `theorem exists_lift_simplicialComplex [FiniteDimensional ℝ E] (K) [Finite K.faces] {p : X' → K.space} (hp : IsCoveringMap p) (hfin : ∀ x, (p ⁻¹' {x}).Finite) : ∃ N (K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))) (e : K'.space ≃ₜ X'), K'.faces.Finite ∧ (∀ q (hq : q ∈ K'.faces), ∃ t ∈ K.faces, ∃ A, (∀ x (hx : x ∈ convexHull ℝ (q : Set _)), ((p (e ⟨x, K'.convexHull_subset_space hq hx⟩) : K.space) : E) = A x) ∧ A '' convexHull ℝ (q : Set _) = convexHull ℝ (t : Set E)) ∧ ∀ n, IsCombinatorialManifoldWithBoundary n K → IsCombinatorialManifoldWithBoundary n K'` | §25 L3 | done（2026-09-15，`CoveringTriangulation.lean`）：以基复形顶点的纤维为有限顶点集，每个基单形从指定纤维点唯一提升；重叠由提升唯一性粘合。标准基实现给出有限 `coveringComplex`，逐面映射粘为 `coveringSpaceHomeomorph`；顶点 link 的 `coveringVertexLink_isGlueIso` 搬运任意维带边组合流形性。此直接逐单形路线不需要先细分至均匀覆盖闭星。检查 exit=0、零 warning，AuditC3 十六端点及 AuditC3Reuse 三条 D4 复用声明均仅标准三公理，未经过 `HurewiczLowDegrees.lean`；源码提交 `f7e70bc61`。 | 4k–6k |
| C.4 | 24.7：不可定向连通带边多面体 3-流形有二重覆盖（且覆盖可定向，Problem 24.11） | H.2b 的 `OrientationCocycle.lean`：`exists_orientationCocycle_of_not_isOrientable hK h` 给 `barycentricSubdivision K` 上的 `SimplicialBoolCocycle` 且非上边界；接 C.2 | §25 L3 | new；H.2b 输入已闭合并审计，二重覆盖流形的构造与可定向性仍待 C.4 消费者证明，不能由输入完成推断 C.4 已完成 | 2k–3k |
| C.5 | 24.8：紧致连通可定向带边、某边界分支非 2-球面 ⟹ 二重覆盖 | H.5 的 `p¹ > 0` ⟹ `H₁(-;ℤ₂) ≠ 0` ⟹ 非上边界 `SimplicialBoolCocycle` ⟹ C.2/C.3 | §25 L3 | done（2026-09-16，`65bd07eb6`、`cb2153a6c`）。`BoundaryHomology.lean`/`HandleCount.lean` 将 I5 的 Betti 系数推广到任意域，原 `bettiOne_pos_of_boundary_component_not_sphere` 的 ℚ 端点保持不变。`HomologyCocycle.lean` 通过有限几何复形的 normalized chain complex 与 realization 同调同构，从非零 `H₁(-;ℤ₂)` 选取非零对偶函子，在边上构造实际 `SimplicialBoolCocycle`，并用对某一循环非零而对所有 2-边界为零证明它不是上边界。`DoubleCoverExistence.lean` 的 `exists_connected_double_cover_complex_of_isOrientable_of_boundary_component_not_sphere` 直接消费 I5，给出连通二重覆盖、有限提升复形及带边组合 3-流形性。两模块检查 exit=0、零 warning；AuditC5 的 17 项新端点/首次复用声明均仅 `propext`、`Classical.choice`、`Quot.sound`；未 import 或传递经过 `Topology/Homology/HurewiczLowDegrees.lean` | 2k–3k |
| C.6 | 24.9–24.10 CST 与柱形图、CST 两两组合等价 | 原书页 178 的 CST 先要求底空间是拓扑实心环面，再要求循环 PL 3-胞腔分解。`IsCylindricalDiagram` 精确限制纤维：只有两个端面之间允许识别；`exists_cylindricalDiagram_iff_ball_pair` 等价于两个 PL 3-球相交于各自边界上的两个不交 PL 2-盘 | §28, §30.7, §31 | **partial（2026-09-16 更新）**。`77345bbef` 完成两个不交边界盘的同时定位，允许指定第一个盘的映射；`3a22c9bc4` 构造柱形图；`1c7986c99` 从柱形图实际切出两个球及边界盘，证明双向判据，并在端面识别相同的条件下构造 PL 同胚（`CylinderComparison.lean`）。首尾识别条件仅属于该比较引理，没有被当作 24.10 的新假设。仍需一般原书循环分解与此切开判据的完整接线，以及盘自同胚的无扭转分类；24.9/24.10 尚未标 done。全部聚焦检查 exit=0、零警告；AuditS150–S152 共 25 项（含复用的 `IsOrientable.of_le`）仅标准三公理 | 3k–5k |
| C.7 | 24.11–24.12：可定向 3-流形中多边形的正则邻域是 CST；可缩多边形的正则邻域是 CST（任意 `M`） | `NeighborhoodCycle.lean` 的实际循环片与 `NeighborhoodCylinder.lean` 的柱形图；定向传递直接使用 `Orientation.lean` 的 `IsOrientable.of_le`，不含 23.17 参数 | §28.19, §31, §34 L1 | **partial（2026-09-16 更新）**。`3a22c9bc4` 的 `exists_ball_pair_with_boundary_cover_derivedNeighborhood_circle` 给出两个实际有限 3-球复形及同时属于两者边界的两个不交 2-盘；`exists_cylindricalDiagram_derivedNeighborhood_circle` 无需可定向性；`exists_cylindricalDiagram_isOrientable_derivedNeighborhood_circle` 从 `IsOrientable 3 K` 得邻域可定向及柱形图，直接消费已证 23.17。该层已闭合、无未证参数。仍需可定向柱形图的无扭转识别才能给出 24.11 的 CST 端点；24.12 的可缩回路定向传递尚未接线。已读到整合分支 `CoveringOrientation.lean` 的 `isOrientable_coveringComplex_orientationCocycle`，不得再把覆盖的可定向性当作尚无生产者。检查 exit=0、零警告，AuditS151 十项仅标准三公理（计入 C.6 所列总数） | 3k–5k |

### 4.5 车道 C（3）：§25 Stallings 环定理（`chap:dehn-loop`）

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| L.1 | 奇异 2-胞腔、`L(X)` 共轭类、正规系统 `[M₁, K₁, D, K(Δ), B₁, N₁]` 与复杂度 | `SingularTwoCell`、`FreeLoop.conjugacyClass`、`NormalSystem`、`NormalSystem.complexity_eq_zero_iff_isNonsingular`；`DerivedNeighborhoodRetraction.lean` 给 `derivedNeighborhoodStrongDeformationRetract` 与实际包含映射诱导的 `derivedNeighborhoodFundamentalGroupInclusionEquiv` | L.2–L.4 | done（2026-09-15，`d81e1897c`；边界参数化补强 2026-09-16，`b3d9e8150`）：`K₁` 取保留像单形的相对导出邻域，其载体与标准导出邻域相等；`B₁` 为边界中环复形的导出邻域；环共轭类不依赖连接道路，正规子群给共轭类包含/不交二择一，复杂度为顶点碰撞对数且零当且仅当全单纯映射单射。`NormalSystem.boundaryParam : loopCircle ≃ₜ frontier sourceComplex.space` 与 `boundaryLoop_eq` 把边界环逐点钉死到 `simplicialMap sourceComplex vertexMap`，原 `boundaryLoop_range` 改为同名推论，消费者签名不变。`SingularCell` 与 16 个传递下游全部重检 exit=0、零 warning；AuditE3M2 含新增两字段和推论共 50 项，均仅标准三公理；L.1 无未闭合书中步骤 | 1137 行 |
| L.2 | 25 L1：`B` 2-球面时（`B'` 为 `\|L\|` 的正则邻域是 `k`-环带，π 自由）直接得非奇异 `D₁` | 用 P.1 变体（球面上多边形界定 2-胞腔）、F4.2 | L.4 | partial（2026-09-15）。`SphereSchoenflies.lean` 的 `exists_isPLBall_pair_of_isPLSphere_two` 证明球面多边形界定两个互补 PL 2-胞腔（`fa1bf738e`）；`CellAttachmentKernel.lean` 与 `BoundaryGeneration.lean` 完成逐盘 van Kampen、有限迭代、任意基点的正规生成及边界环像识别（`ad9bf6542`、`350c126a0`、`4ace4b80c`）。`SphereCase.lean` 的条件端点 `exists_nonsingular_two_cell_of_sphere_boundary` 以 `B' = sphereWithDiskInteriorsRemoved B D` 为输入；`724267986` 将其补成显式环境 `{M B : Set ℝ³}`，假设 `hM : IsPolyhedralManifoldWithBoundary (n := 3) 3 M`、`hBBdM : B ⊆ polyhedralBoundary 3 M hM`，并在 `hpush` 和结论中都要求 `D₁ '' D₁.domain ⊆ M`。精确 `hpush` 为 `∀ Δ r, IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ → Δ ⊆ polyhedralBoundary 3 M hM → ∃ D₁, D₁.IsNonsingular ∧ D₁ '' D₁.domain ⊆ M ∧ range D₁.boundary = r '' stdSimplexBoundary 2 ∧ D₁ '' D₁.domain ∩ polyhedralBoundary 3 M hM = r '' stdSimplexBoundary 2`；相对边界必须写 `r '' stdSimplexBoundary 2`，不能写三维环境 frontier。`SurfaceNeighborhood.lean`（`cc4e2a06e`）证明 `B'` 是有限带边组合 2-流形、其边界为有限个两两不交 PL 多边形，并逐分支给出互补 Schoenflies 盘；检查 exit=0、零 warning，相关审计均仅标准三公理。尚缺两项：有限 Jordan 边界域定理，以证明该连通紧曲面精确等于删去所选互补盘相对内部；以及任意补盘的全局 `hpush`（整合后的 `BoundaryPush.lean` 目前只给局部小边界盘），后者由 S.5/B.3 接线 | 2k–3k |
| L.3 | 25 L2：局部同胚、至多 2 对 1 的 `D` 的四种情形（Case 1–4，切开与复杂度归纳） | F5.2 正规形式 + 柱形图（Figure 25.2）+ 基本群字计算（Figures 25.3–25.6） | L.4 | new | 8k–14k |
| L.4 | 25 L3 / **25.1**：对每个正规系统存在非奇异 `D'`（二重覆盖降复杂度：C.3–C.5，`g*` 指标 2 不满） | `theorem loop_theorem_stallings (hK : IsCombinatorialManifoldWithBoundary 3 K) (B : boundary component) (N : Subgroup (FundamentalGroup B.space P₀)) [N.Normal] (D : PL singular 2-cell with Bd D ⊆ B.space) (hD : loopClass (Bd D) ∉ N) : ∃ Δ ⊆ K.space, IsPLBall 2 Δ ∧ Δ ∩ (boundaryComplex K).space = frontier Δ ∧ frontier Δ ⊆ B.space ∧ loopClass (frontier Δ) ∉ N` | L.5 | partial（2026-09-15，`130e6f402`，条件性骨架）。`LoopTheorem/StallingsInduction.lean` 定义精确的 `NormalSystem.NonsingularCell`、边界分支 `boundaryComponent`、`IsOrientableManifold` 与实际二重覆盖降阶数据 `DoubleCoverReduction`；`simplicialComplexity_lt_of_factorization_of_separated` 证明提升映射因子分解且分开至少一个顶点碰撞对时复杂度严格下降；`exists_nonsingular_cell_of_stallings_induction` 对复杂度作强归纳，球面分支消费 Lemma 1，两个非球面分支按可定向性分别消费 24.8/24.7，再以 Lemma 2 回推。检查 exit=0、零 warning，AuditStallingsInduction 的 6 个新声明与 7 个关键复用声明均仅标准三公理。尚缺把 C.4/C.5 的实际覆盖经 C.1/C.3 组装成 `DoubleCoverReduction`，尤其“复杂度相等则限制同胚并迫使 `g*` 满，与指标 2 矛盾”；Lemma 1、Lemma 2 与两个覆盖生产者均保留为显式条件 | 8k–12k |
| L.5 | **25.2 环定理第一形式**（可定向、`N = ⊥`） | `theorem loop_theorem (hK) (hor : IsOrientable K) (B) (L : loop in B) (hL : contractible in K.space) (hB : ¬ contractible in B.space) : ∃ Δ, IsPLBall 2 Δ ∧ Δ ⊆ K.space ∧ frontier Δ = Δ ∩ (boundaryComplex K).space ∧ ¬ contractible (frontier Δ) in B.space` | §26.4 | new | 1k |

### 4.6 车道 C（4）：§26 双领邻域与扩展环定理；ℝ³ 中的曲面

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| B.1 | 26.1：3-流形带边 `N` 的边界分支之并两侧（two sided）定义与命题 | `def IsTwoSided (M² : Set M³)` | §26.3, §30.4 | **done（S 车道）**。`Connected/TwoSided.lean` 按每个连通分支定义 `IsTwoSided`；`ddf717a4b` 的 `PolyhedralManifoldTopology.lean` 在 Hausdorff PL 图卡环境中证明边界及其分支之并两侧。`7746cff68` 的 `ManifoldRelativeTopology.lean` 进一步在任意有限组合带边流形 K 的子类型拓扑中证明：同维有限带边流形 A 包含于 K 且避开 Bd K 时，其相对边界恰为 Bd A，Bd A 及其任意连通分支之并两侧。适用于所有正维数和任意有限维实赋范环境；无额外正则闭、局部连通、图卡或分离假设，亦无需把整个 K.space 设为无边流形。聚焦检查 exit=0、零警告，AuditS104 五项仅标准三公理；此前一般图卡结果见 AuditS76 | 1k |
| B.2 | Problems 26.1–26.3（27.1 用）：`Bd M³` 中多面体 2-胞腔 `d` 的任意邻域含多面体 3-胞腔 `C` 使 `d = C ∩ Bd M³`；`N ⊆ Int M³` 两侧各一 | `BoundaryBall.lean`、`BoundarySubdivision.lean`；用 M.1、S.5 和有限圆盘归纳 | §25 Lemma 1 的 hpush、§26.2、§27.1 | **done（含内部两侧的 Problem 26.3）**。`249311c83`、`57a3f6a4e`、`ee2a8a29d` 的片、交盘与单形基例经 `2375fc812` 推广到任意有限维环境；`32a3b37e8`、`d12dd514a` 完成自由三角形删除的面分类、各贴合盘与整盘归纳，证明 Problem 26.1：`exists_isPLBall_containing_boundary_disk`。`a5b945228`、`bd74dd7ca` 给一般环境的精确贴边球与参数化推离盘，以及 ℝ³ 的非奇异胞腔端点。`41b78491e` 的 `BoundaryDiskNeighborhood.lean` 再将球、盘领和推离盘放入任意指定相对邻域，闭合本条的邻域控制。均无 Schoenflies 假设；聚焦检查 exit=0、零警告，AuditS70–S74 与 AuditS78BoundaryNeighborhood 仅标准三公理。I2 已按 NIGHT_PLAN §6.1 交付 double 环境：`b926417f6` 的 `LoopTheorem/DoubleBoundaryPush.lean` 在 `(double 3 K).space` 的已构造无边图卡环境中给出非奇异胞腔、像在 K 的第二份拷贝内、边界像及与该份边界交集的精确等式，并给 E3 hpush 可直接消费的版本。三个新模块 exit=0、零警告，AuditS114 七项仅标准三公理，E3 签名适配检查通过；无额外 Schoenflies 假设。2026-09-16 的 `7d74a1d84` 完成 `InteriorManifoldComplement.lean`、`ManifoldPieceInclusion.lean`、`TwoSidedDiskNeighborhood.lean`、`TwoSidedDiskNeighborhoodManifold.lean`：对任意 Hausdorff PL 三流形中的多面体带边三流形 N、N ⊆ interior M、D 为 frontier N 中的多面体二球及任意 D 的邻域 U，`IsPolyhedralManifoldWithBoundary.exists_isPolyhedralBall_pair_inter_frontier_eq` 构造两个三球 C₁ ⊆ N、C₂ ⊆ closure (M − N)，二者均在 U 内，且 C₁ ∩ frontier N = C₂ ∩ frontier N = C₁ ∩ C₂ = D。M 本身无需额外紧致或流形假设，无 hSchoenflies。四模块检查 exit=0、零警告，AuditS118 六项及 AuditS120 复审均仅标准三公理 | 2k–3k |
| B.3 | 26.2 领邻域（紧致 `B = Bd M³` 有 PLH `ρ : B × [0,1] ↔ W`，W 是 M 中 B 的邻域，`ρ(P,0)=P`） | 对 B 的 2-胞腔分解归纳（用 B.2、S.5、P.2 和锥延拓） | §26.3 | **done（S 车道，有限组合流形接口）**。`CollarNeighborhood.lean` 的 `IsCombinatorialManifoldWithBoundary.exists_collar`（`f778f73ff`）对任意有限维实赋范环境中的有限带边组合 3-流形给出整个内蕴边界乘 `[0,1]` 到 `W ⊆ K.space` 的 PL 同胚，证明 `W ∈ 𝓝ˢ[K.space] (boundaryComplex 3 K).space`、底面恒同、精确边界交集及正高度避边界，无 Schoenflies 或未证接口假设。`691c7329d` 的有限弧分解消掉领扩张的弧两两不交假设；`e9feba0c2` 的 `SurfaceCollar.lean` 对实际顶点双胞腔族作有限归纳，构造产品嵌入并返回实际闭补集的有限组合流形。邻域性由边界点的盘邻域、棱柱边界公式及实际补边界公式证明。九个改动 Lean 模块聚焦检查 exit=0、零警告；AuditS88/S89/S90 共十二项仅标准三公理。此处完成 NIGHT_PLAN 的有限 `K` 端点；任意抽象 PL 图卡环境的搬运不在本端点中。更早的局部盘领、补空间与边界保持检查记录见 HANDOFF_CODEX_S.md | 3k–5k |
| B.4 | 26.3 双领邻域（紧致两侧多面体 2-流形 `M² ⊆ Int M³`） | `theorem exists_bicollar (hM : IsPolyhedralSurface M²) (h2 : IsTwoSided M²) : ∃ ρ : M² × Icc (-1) 1 → M³, PL embedding, ρ (P, 0) = P, range ρ ∈ 𝓝ˢ M²` | §26.4, §28.1 后半, §30.7 | **done（S 车道；有限组合流形与一般 Hausdorff PL 图卡环境）**。`3a55ac834` 的 `Bicollar.lean` / `IsCombinatorialManifoldWithBoundary.exists_bicollar` 对任意有限维实赋范环境中、有限带边组合 3-流形 K 内部的有限闭曲面 L，在其每个指定相对邻域 U 中构造 PLH `L.space × [-1,1] ↔ W`，W 为整张曲面的相对邻域且避开 Bd K，底面恒同；不要求 L 连通。`52d70d778` 的 `BicollarManifold.lean` / `IsPolyhedralManifold.exists_bicollar` 将端点搬运到一般 Hausdorff PL 3-流形，交付实际 `S × [-1,1] ≃ₜ W` 及双向图卡 PL 的 `PLPieceIn` 证书，W 位于任意指定邻域；不要求环境紧致或第二可数。有限分支隔离、两侧闭包流形、领的限制与拼合均已证明，无 Schoenflies 或未证接口参数。聚焦检查 exit=0、零警告，AuditS100–S103 共 25 项仅标准三公理 | 2k–3k |
| B.5 | **26.4 扩展环定理**（Papakyriakopoulos）：`M²` 紧致两侧、`ker i* ≠ 1` ⟹ 多面体 2-胞腔 `Δ`，`Δ ∩ M² = Bd Δ` 在 `M²` 中不可缩 | `theorem loop_theorem_two_sided (hK : IsCombinatorialManifoldWithBoundary 3 K) (hM : compact polyhedral 2-manifold M² ⊆ interior K.space) (h2 : IsTwoSided M²) (hker : ¬ Function.Injective (π₁-map)) : ∃ Δ, IsPLBall 2 Δ ∧ Δ ⊆ K.space ∧ Δ ∩ M² = frontier Δ ∧ ¬ contractible (frontier Δ) in M²`；证明：F5.1（相对 `Bd W`）、最内多边形三情形、L.5 | §30.4, §30.6, §30.7, §33 L9–L10 | new | 5k–8k |
| B.6 | 26.6：ℝ³ 中紧致连通多面体 2-流形两侧，且 `ℝ³ − M²` 恰两分支、`M²` 为公共边界 | 用 F5.1（`ρ(Δ)` 相对 `M²` 一般位置）+ 图的奇偶论证 + B.4 | §26.7, §30.6, §32 Type 2, §33 L5 | **done（S，2026-09-16，无 hSchoenflies）**。`OneManifoldBoundary.lean` 以握手引理证明有限带边组合一流形的边界点数为偶；`PreimageBoundary.lean` / `PreimageBoundaryRelative.lean` 把相对一般位置原像边界与源边界的交点集精确识别。`OpenPLPath.lean`、`TransverseSegment.lean`、`CircleMap.lean`、`SingleIntersectionCircle.lean` 生产实际单穿越 PL 圆与可避开有限源点的平移；`BoundaryCrossingObstruction.lean` / `SurfaceSeparation.lean` 在细分盘上应用奇偶矛盾，证明任意非空有限闭组合二流形在三维环境中的补集不连通（`d387cf718`）。`c4645eeb0` 的 `SurfaceComplement.lean`、`EuclideanPolyhedralManifold.lean`、`PolyhedralSurfaceComplement.lean` 给最终 `IsPolyhedralManifold.exists_connectedComponentIn_pair_compl` 与 `.isTwoSided`：连通曲面的补集恰为两个不交连通分支，两闭包覆盖 ℝ³、交集等于曲面，两个 frontier 都等于曲面。所改模块聚焦检查 exit=0、零警告；AuditS116/S117/S119–S122 均仅标准三公理，最终 AuditS122 七项；HANDOFF 记录逐层出处与检查 | 4k–6k |
| B.7 | 26.7：三张带边曲面公共边界，其中一张在另两张之并的内部 | 2.7 的三维类比（P.5） | §32 Type 2 | new | 2k–3k |
| B.8 | 26.8：ℝ³ 中紧致连通多面体 2-流形可定向 | 用 B.6 的两侧性：将曲面放入大 3-单形，取一侧闭包的有限带边组合 3-流形；环境仿射定向诱导其边界定向，再经共同细分限制到原曲面 | §33 L11 | done（H，2026-09-16，`6a02d3559`）。`EuclideanSurfaceOrientation.lean` 的 `IsCombinatorialManifold.isOrientable_of_finrank_eq_three` 对任意三维有限维实赋范空间中的有限连通闭组合 2-流形证明 `IsOrientable 2 L`，`isOrientable_euclidean_three` 给 ℝ³ 专门版本。证明消费 B.6 的 `IsCombinatorialManifold.isTwoSided` 与两侧闭包流形生产者，选一侧在大 3-单形内用仿射定向构造 3-维相干定向，取组合边界后以共同细分截出原曲面并搬回；未使用 `H₃ ≅ ℤ`。聚焦检查 exit=0、零 warning，AuditHM9 十六项仅标准三公理 | 83 行 |

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
| T.9 | 分裂运算（split `M² ∪ Δ` apart at `Δ`）定义与 28.20：`χ(M₁²) = χ(M²) + 2` | 定义 + H.3 | §30.3–30.4, §30.6, §32, §33 L3–L7, §34 Op.1 | done（2026-09-16，`9bcc38d82`）：`SurfaceSplitAlongPolygon` 精确记录切开所需的核心、乘积环带和双边界 PL 数据，`SurfaceSplitAndCap` 记录两张互不相交的封口 PL 2-胞腔；`SurfaceSplitAndCap.eulerChar_eq_add_two` 证明 `χ(result)=χ(source)+2`，不把 Euler 等式包装成输入 | H.3 已同时交付 |

### 4.9 车道 I（1）：§30 多面体插值定理

| 编号 | 内容 | 拟定 Lean | 消费者 | 状态 | 行数 |
|---|---|---|---|---|---|
| I.1 | 30.1（书页 214）：X 单连通、局部连通且连通开集道路连通；H、K、C、D 是两两不交的闭集，H、K 连通；C ∪ D 分离 H、K 则 C 或 D 分离 H、K | 书上完整特化签名：`[SimplyConnectedSpace X] [LocallyConnectedSpace X] (hpath : ∀ U : Set X, IsOpen U → IsConnected U → IsPathConnected U) {H K C D : Set X} (hH : IsConnected H) (hK : IsConnected K) (hHclosed : IsClosed H) (hKclosed : IsClosed K) (hC : IsClosed C) (hD : IsClosed D) (hHK : Disjoint H K) (hHC : Disjoint H C) (hHD : Disjoint H D) (hKC : Disjoint K C) (hKD : Disjoint K D) (hCD : Disjoint C D) (hsep : Separates (C ∪ D) H K) : Separates C H K ∨ Separates D H K`；由 `separates_or_separates_of_union hpath hC hD hCD hH.isPreconnected hK.isPreconnected hsep` 直接得到 | I.2, §32 Step 2 | **done**。`6cf85c2d3`；`Connected/PhragmenBrouwer.lean` 的通用端点及局部道路连通版本 `phragmen_brouwer` 保留 H/K 的 `IsPreconnected` 假设，比书上允许更弱条件：无需闭、允许为空。书上 `IsConnected H/K` 蕴含这些假设；`Disjoint C D` 明确保留，其余不交条件由分离前提蕴含。两个模块 exit=0、零警告，AuditS147 九项仅标准三公理 | 3k–5k |
| I.2 | 30.2：有限分支的闭集分离两个非空连通集 ⟹ 某分支分离 | `Connected/SeparatingComponent.lean`：`exists_separates_of_finite_iUnion`、`exists_separating_connectedComponentIn`、`exists_separating_component` | §30.4, §30.6, §33 L5/L6, §33 L10 | **done**。`bc20b0b45`；从 `[Finite (ConnectedComponents C)]`、`IsClosed C` 和 `Separates C H K` 实际产生 `x ∈ C`，使 `connectedComponentIn C x` 分离 H/K。先对有限个两两不交闭集归纳，再由真实连通分支构造该族。两种空间假设版本同 I.1，无未证参数。模块 exit=0、零警告，AuditS148 三项仅标准三公理 | 0.5k |
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
| G.5 | L10–L12：`i* : π(Bd X) ↔ π(N' − K')` 同构（`Bd N × (0,1) ≅ Int N' − K'`，Figure 33.1 的 PL 格论证，I.2）。不做原书 L11 的无结构 `Bd X ≅ Bd N`：由 L10 经一维 Hurewicz/阿贝尔化桥得 `b₁(Bd X)=b₁(Bd N)`；对每个 `A'_v` 的全部多边形边界封 PL 盘得闭曲面 `Â'_v`，Euler 加法与 H.4a 给 `b₁(Bd X)=b₁(Bd N)+∑v b₁(Â'_v)`，故各项为零；H.4b 将每个 `Â'_v` 识别为 PL 2-球面，删去封盘内部即得 `A'_v` 是盘或带孔盘。最后所需保持分块的 PLH 仍由 G.6/L13 构造 | H.4a、H.4b、P.2；需新增无 `sorryAx` 的一维 Hurewicz桥及有限封盘复形 | G.6 | new；22.8–22.10 非前置 | 3k–5k |
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
| E.2 | **35.2**：局部有限、可非紧的多面体 3-流形带边上的到像同胚可任意小地逼近为到像 PL 同胚；不增加像集结论。证明待 E.1 与流形层 A.1–A.6。 | `Transition361.lean`：`def Moise352 (n : ℕ) : Prop := ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁] [MetricSpace M₂] [SecondCountableTopology M₂] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂] [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)] {K : Set M₁}, IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n K → ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) → ∀ φ : M₁ → ℝ, ContinuousOn φ K → (∀ x ∈ K, 0 < φ x) → ∃ f : M₁ → M₂, IsPLHomeomorphInto n f K ∧ ∀ x ∈ K, dist (f x) (h x) < φ x`。`IsPLHomeomorphInto n f K := IsPLOn n n f K ∧ Set.InjOn f K ∧ ∀ y ∈ f '' K, ∃ g : M₂ → M₁, IsPLWithinAt n n g (f '' K) y ∧ Set.LeftInvOn g f K`。 | E.3 | 命题与接口已定义，35.2 本身未证（2026-09-15，§12.1 检查点）：逐点逆映射形式兼容空源；`isPLHomeomorphInto_iff_exists_inverse` 证明源非空时等价于单个总逆映射的双向 `IsPLOn` 形式。`Set.domRestrict` 是旧 `Set.restrict` 的无弃用警告名称。两定义、连续性、逆映射 PL 性、开像和 `Moise352.exists_approx_of_isOpen` 已检查 exit=0、零 warning；AuditF115 十项仅标准三公理。源域不要求闭或紧，不把 35.2 当成已证定理。 | 4k–6k |
| E.3 | 36.1 的过渡（Moise 8.4 的三维版）：整个 U 一次应用 35.2，穷竭及边界距离控制证明像集相等 | `exists_plh_approx_of_isOpen (h352 : Moise352.{u} 3)`：`{U : Set M₁} → IsOpen U → Topology.IsEmbedding (U.domRestrict h) → ContinuousOn φ U → (∀ x ∈ U, 0 < φ x) → ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f U ∧ f '' U = h '' U ∧ ∀ x ∈ U, dist (f x) (h x) < φ x`；流形实例与 E.2 相同。 | E.4 | done（条件于 `Moise352 3`，2026-09-15）：`Transition361.lean` 的 `exists_plh_approx_of_isOpen` 具有本行完整结论；一般正维版本为 `Moise352.exists_approx_image_eq_of_isOpen`。对整个 U 一次应用 35.2，用 F6.3 塔的紧致阶段构造穷竭；连续正误差控制使像留在原连通分支，并使阶段前沿避开上一阶段。每条紧致路径被某阶段捕获，连通性与前沿分离给满射，故无需假设阶段本身连通。`IsPLHomeomorphInto.image_polyhedralBoundary` 由 M.3 与不变域给 `f(Bd P) = Fr(f(P))`；拓扑层前沿搬运不要求先三角剖分像集。包含空 U、空源情形，不增加开像或像集假设。聚焦检查 exit=0、零 warning；AuditF116 十五项仅标准三公理。 | 3k–5k |
| E.4 | **端点**与推论、公理审计 | `theorem plApproximationManifold_three_of_moise352 (h352 : Moise352.{u} 3) : PLApproximationManifold.{u} 3`（`Endgame.lean`）。E.3 取 U = univ，由像集等式得满射，连续单射经 E.0 得开映射，组装同胚；`IsPLOn` 于 univ 给 `IsPL`。 | 书中 `FND-SMOOTHABILITY` 链（与 Phase 2 合成） | done（条件于 `Moise352 3`，2026-09-15）：`plApproximationManifold_three_of_moise352` 已证明，两个新模块分别聚焦检查 exit=0、零 warning；AuditF117 包含最终端点的十六个声明均仅 `propext`、`Classical.choice`、`Quot.sound`。35.2 本身仍未证，未把该条件端点记成无条件光滑化。 | 1k |

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
- **R3 同调层（已定并闭合所列缺口）。** 采用 D3′ 的本库奇异同调、现成 χ 桥及纯组合定向，不引入新的单纯链复形，也不以缺失的
  单纯–奇异比较定理为前置。H.2a 已证明相干定向的细分及 PL 不变性；H.6 由相容开邻域与本库小链 Mayer–Vietoris 给出子复形
  28.11，H.4a 由现有 ordered normalized chain complex 的 realization 同调桥给出闭曲面顶维基本类与所需 `χ ≠ 2 ⟹ b₁ > 0`。
- **R4 2D 分类（主链决定：跳过 22.8–22.10）。** 已核对 Moise 书页 236：L10 已先给 `π₁(Bd X) ≅ π₁(Bd N)`；
  L11 用 22.9 得到的只是无分块控制的同胚，而 L13 随后独立构造满足 `A_v ↦ A'_v` 的强 PLH。L12 改用封盘计数：
  对每个 `A'_v` 的边界封 PL 盘，H.4a 与全局 Euler 加法把 `b₁(Bd X)=b₁(Bd N)` 改写为非负项之和为零，
  H.4b 再把各封闭曲面识别为 PL 2-球面。所需新增仅是一维 Hurewicz/阿贝尔化桥和有限封盘复形；不得经过含 `sorry` 的
  `Topology/Homology/HurewiczLowDegrees.lean`。完整曲面分类保留为可选库结果，不再是 §33 主链前置。
- **R5 非紧性。** E.1/E.2 需要 §33/§34 的构造在局部有限复形上进行（每步只影响有限个单形）；这是 Moise 一句"virtually a repetition"
  掩盖的真实成本，估计已计入 E.1/E.2。
- **R6 书中引用。** §33 末尾的"Theorem 18.2"与 §18（Antoine 集）不符，本计划按其内容用 S.7；其它引用已逐条核对到本文件 §2。
- **R7 外部复用。** D4 的本库覆盖/van Kampen 声明与 D6 的移植都必须先 `#print axioms`；Phase 2 审计已发现树中有 sorry 支撑链。
- **R8 对偶胞腔球性。** F4.3 的顶点胞腔球性依赖 S.5 的带边界盘粘接；早先行数估计未含此项。现有球性端点证明的是对偶锥与分裂盘，不是 `graphDualCell`；在依赖闭合前 F4.3 保持 partial，Q 消费者须显式携带 `hcell`。
- **R9 局部有限表示层（已解除，2026-09-15）。** 有限 `PLPiece` 必紧致，单独的集合穷竭不能提供 35.2/36.1 所需的相容非紧源域。F6.3 现已用 `LocallyFinitePieceTower` 与 `IsLocallyFinitePolyhedralManifoldWithBoundary` 提供该表示；`exists_locallyFinitePieceTower_of_isOpen` 从开集构造塔，保留内核原单形与映射，`exists_core_of_isCompact` 给紧致捕获，`exists_glue` 拼接内核上一致的映射。存在定理源码 `bfd458cdc`，聚焦检查 exit=0、零 warning，AuditF114 仅标准三公理。E.2/E.3 的表示层前置已解除；§12.1 改派后 F 车道已证明 36.1 与 PLApproximationManifold 3 的条件版（Moise352 3 → 端点，AuditF117 仅标准三公理），35.2 本身仍待 E 车道。
- **R10 最小载体约束的刚性（2026-09-15）。** §12.2 的源单纯化把顶点映到目标顶点；carrierFace 的单点仿射包不能提供任何移动自由度。CarrierPerturbation.lean 已证明整映射与双点集不变，并证明既有顶点双点阻止奇点集避开目标顶点。F5.2 保持 partial，必须先修订载体选择及跨单形兼容设计，不能补上一般位置结论型假设。AuditF118 二十二项仅标准三公理。
- **R11 固定折边的相对正规形式（2026-09-15）。** §15 球图卡路线的混合三角形可有固定折边与可动对顶点；两张片的固定折边原来重合时，完整相对通用位置条件仍允许两张在该边处同时折叠。固定边逐点不变不保证曲面芽不变，不能直接用于 crossing 的图卡搬运。FoldCrossing.lean 已闭合单折/平片引理；RelativeNormalForm.lean 仅有四个已验证支撑声明，不是相对正规形式。须生产固定折边处双折构型的处理，或使过渡部分的整片曲面芽恒同并证明缓冲层覆盖。AuditF120 六项仅标准三公理；F5.2 保持 partial，按 HANDOFF_CODEX_F.md §16.2 报告后暂停。
