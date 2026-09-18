# L 车道交接：§25 环定理（Stallings 证明）前半、26.2 领邻域与 §24 后半（C.4/C.5）

日期：2026-09-15。承接线程：原 E3/C 线程（工作树 `D:\differential-geometry-moise-e3`，分支 `codex/moise-e3`）。
环境、硬规则、验证配方与汇报格式沿用 `HANDOFF_CODEX_C.md` §1–§2、§5；本文件只写新增内容。

## 0. 先做的事

1. 离开 S 工作树：`D:\differential-geometry-moise-s` 归 S 线程独占。你在那里未提交的 `RelativeThinKite.lean`
   若已通过 check 就提交并推送，否则连同缺口写入 `HANDOFF_CODEX_S.md` 末尾新的一节后提交推送；之后不再碰 S 工作树。
   汇报你在 `codex/moise-s` 上做过的全部 commit 哈希。
2. 回到 `D:\differential-geometry-moise-e3`，执行 `git fetch origin && git merge --no-ff origin/codex/moise-integration`
   （计划文件冲突两边都保留）。整合分支现在是 `4593e7746`：含 F6.3（`LocallyFinitePieceTower.lean`、
   `LocallyFinitePieceTowerExistence.lean`、`RelativeDerivedNeighborhood.lean`、`RelativeExhaustion.lean` 等）、
   S 车道到 `181fbce8b`、H.1（`EulerPolyhedra.lean`）与你自己的 C.1–C.3。
3. E.3/E.4 已改派 F 车道（塔表示是它的），本线程不再做 `Transition361`/`Endgame`。你在计划里对 E.2 的
   `Moise352` 草稿由 F 车道定稿。

## 1. 可用产出（已审计，只含标准三公理）

- 自己的 C.1–C.3：`CoveringLift.lean`（24.1–24.4）、`DoubleCoverComplex.lean`（24.5，k = 2）、
  `CoveringTriangulation.lean`（24.6，含组合流形性保持）。
- F：导出邻域 `derivedNeighborhood`、`secondDerived`（F4.2，`DerivedNeighborhoodManifold.lean`），相对导出邻域
  `relDerived`（`RelativeDerivedNeighborhood.lean`，固定子复形原样保留），`exists_isPolyhedralManifoldWithBoundary_neighborhood`
  （F6.2），一般位置 F5.1（`GeneralPosition.lean`），P.1 原生 `isPLBall_of_isPLSphere_one`（`PolygonalSchoenflies.lean:1240`：
  ℝ² 中 PL 1-球面界定有界 PL 2-球）、P.2 `Bd` 间 PLH 延拓。
- S：vendored 平面链（`External/ClassificationOfSurfaces/Moise/*`）与桥接 `PlanarSchoenflies.lean`（3.7 相对形式）；
  `PolyhedralBoundary.lean`、`FrontierBoundary.lean`（M.1–M.3）。
- 同伦/基本群：`Topology/Homotopy/DeformationRetract.lean`、`Topology/FundamentalGroup/*`
  （`Sphere.lean` 的 `sphereTwoSimplyConnectedSpace`、`BasepointChange.lean`、`HomotopyEquiv.lean`、`Retraction.lean`）、
  `Topology/Covering/*`（`UniversalDeckGroup.lean`、`SemilocallySimplyConnected.lean`、`FiniteFundamentalGroup.lean`）、
  Mathlib `FundamentalGroup`、`Path.Homotopic.Quotient`、`IsCoveringMap.liftPath`。用前先 `grep`，核对实际假设。
- H 车道正在做 H.2（`Orientation.lean`：组合定向、`IsOrientable`、PL 球的 double；分支 `origin/codex/moise-h`，尚未合并）。
  C.4/C.5 要等它；H 汇报后合并 `origin/codex/moise-h` 或等整合分支。

## 2. 砖块（顺序：L.1 → B.3 → L.2；C.4/C.5 在 H.2 可用时插入）

先读 Moise §25 全部（书页 182–190 = PDF 192–200）与 §26 的 26.1–26.2（书页 191–194 = PDF 201–204），
再读 §24 的 24.7–24.8（书页 178 = PDF 188）。

### 砖 L.1 `DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/SingularCell.lean` —— 定义层（计划行 L.1）

1. 环与奇异 2-胞腔（书页 182）：环 = 无基点的闭道路；奇异 2-胞腔 = `D : EuclideanSpace ℝ (Fin 2) → M` 在 PL 2-球
   `Δ`（`IsPLBall 2 Δ`）上 `IsPLOn 2 3 D Δ`；`Bd D` = `D` 限制在 `frontier Δ`（`IsPLBall.isPLSphere_frontier`）；
   `D` 非奇异 ⇔ 在 `Δ` 上单射。
2. `L(X)`：环 `L` 决定 `π(X, P₀)` 的一个共轭类（Figure 25.1 的论证：`r = q p q⁻¹`，换 `Q₀'`、`q` 只差共轭）。
   用 Mathlib `FundamentalGroup` 与 `Path.Homotopic.Quotient`，基点变换用 `BasepointChange.lean`。
   定义 `loopClassMeets L N`，证明 `N` 正规时 `L(X)` 与 `N` 要么全交要么不交。
3. 正规系统（书页 187–188）`[M₁, K₁, D, K(Δ), B₁, N₁]` 与条件 (1)–(4)，复杂度 `k` = `K(Δ)` 顶点对 `v ≠ v'`、
   `D v = D v'` 的个数；`k = 0 ⇔ D` 非奇异。`M₁ = |K₁|` 用"受限重心细分"两次取 `|D|` 的正则邻域：本树对应
   `relDerived`/`secondDerived` 的导出邻域，`K(Δ)` 的像单形在 `K₁` 中原样保留。
4. 条件 (2) 需要包含 `|D| → M₁` 诱导 `π` 的满同构：证明导出邻域强形变收缩到子复形
   （`derivedNeighborhood K L` 收缩到 `L.space`，在导出细分的每个单形内沿到 `L'` 面的直线段收缩）。
   先查 `Topology/Homotopy/DeformationRetract.lean` 与 `origin/codex/moise-h` 的 H.6（28.11 也要它）是否已有；
   若无，放在 `DerivedNeighborhoodRetraction.lean` 并在计划行 H.6 注明可复用。

### 砖 B.3 `DifferentialGeometry/Topology/PiecewiseLinear/Collar.lean` —— 26.2 领邻域（计划行 B.3，提前）

紧致 `B = Bd M³` 有 PLH `ρ : B × [0,1] ↔ W ⊆ M³`，`W` 是 `B` 的邻域，`ρ(P, 0) = P`。L.2 的"把 `Int Δ` 稍微推离 `B` 进入 `Int M`"、
§26 的双领、§27.1 与后面的 §28 都消费它，所以提前做。按 Moise §26 定理 2 的证明写；若书的证明用到本树没有的工具
（例如正则邻域唯一性），报告确切缺口并给出替代（导出邻域的 join 结构：`Bd M` 的每个顶点在第二导出细分中有内部锥点，
`(v, t) ↦ (1 - t) v + t v̂` 在 join 上拼成）。至少先做子复形版本：`Bd M` 中紧致子复形 `Δ` 的领 `Δ × [0,1] → M`，
`Δ × (0,1]` 落在 `Int M`——L.2 只需要这个。

### 砖 L.2 `DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/SphereCase.lean` —— 25 Lemma 1（计划行 L.2）

`B` 是 2-球面，`B'` 是 `|L|` 在 `B` 中的正则邻域（导出邻域），`P₀ ∈ Int B'`，`N'` 是 `π(B', P₀)` 的正规子群，
`L(B') ∩ N' = ∅` ⟹ 存在非奇异 PL 2-胞腔 `D₁ : Δ → M`，`L₁ = Bd D₁` 是 `B'` 中的环，`|D₁| ∩ Bd M = |L₁|`，
`L₁(B') ∩ N' = ∅`。路线：
1. 球面 Schoenflies 变体：PL 2-球面 `B` 中的多边形 `J` 在 `B` 中界定 PL 2-胞腔（两侧各一）。
   路线：`B` PL 同胚于 3-单形的边界；细分后取与 `J` 不交的开 2-单形去掉，剩下 PL 2-球，PL 同胚到平面多边形区域，
   用 P.1 `isPLBall_of_isPLSphere_one` 后搬回。放在 `SphereSchoenflies.lean`，签名写进计划行 L.2。
2. `B'` 的边界分支 `p_1 … p_k` 是多边形，各界定 `B` 中 2-胞腔 `Δ_i`，`B = B' ∪ ⋃ Δ_i`。需要：`p̄_i` 正规生成 `π(B')`
   （书用"`B'` 是 `k`-环带、`π` 自由"；等价且更易形式化的说法：`π(B) = 1`（`sphereTwoSimplyConnectedSpace` 沿 PL 同胚搬运）
   且贴 2-胞腔的 van Kampen 给 `π(B') / ⟨⟨p̄_i⟩⟩ ≅ π(B)`）。先看 `DifferentialGeometry/Topology/VanKampen/` 与 `Topology/FundamentalGroup/Sphere.lean` 的用法；若没有贴胞腔的 van Kampen，
   报告后再定（备选：覆盖空间论证——若所有 `p̄_i ∈ N'`，对应 `N'` 的覆盖在每个边界分支上平凡，贴回胞腔得 `B` 的覆盖，
   `B` 单连通迫使覆盖平凡）。于是某个 `p̄_i ∉ N'`。
3. 用 B.3 的领把 `Int Δ_i` 推入 `Int M`：`D₁(x) := ρ(x, ε · dist(x, Bd Δ_i))` 一类的 PL 构造，或在导出细分上把内部顶点
   移到锥点；证明 `D₁` 单射、PL、`|D₁| ∩ Bd M = p_i`、`L₁(B') ∩ N' = ∅`（`L₁ = p_i` 同一条环）。

### 砖 C.4 / C.5（24.7、24.8；等 H.2）

- C.4：`M` 连通带边多面体 3-流形不可定向 ⟹ 有二重覆盖且覆盖可定向（Problem 24.11）。用 H.2 的定向上循环
  （`Orientation.lean` 的 `SimplicialBoolCocycle` 形式）接 C.2 的 `DoubleCoverComplex`；不可定向 ⇔ 上循环非上边缘 ⇔ 覆盖连通。
- C.5：紧致连通可定向、某边界分支不是 2-球面 ⟹ 二重覆盖。书：23.19 给 `p¹(M) > 0`，`H₁ ↠ ℤ₂`，`π ↠ H₁`，指标 2 子群。
  本树：H.5 的 23.19′（`b₁ > 0`）+ 由 `H₁(K;ℤ)` 到 `ℤ₂` 的满射得到 ℤ₂ 1-上循环（`SimplicialBoolCocycle`）非上边缘，再用 C.2。
  H.5 未到就先把"上循环 ↔ `Hom(H₁, ℤ₂)`"的桥接做好。

### 之后（不要自行开始，先汇报）

L.3（Cases 1–4，需 F 车道 F5.2 的正规形式，F 正在做）、L.4（Lemma 3：二重覆盖降复杂度，需 C.3–C.5 与 L.1–L.3）、
L.5（25.2 第一形式，需 H.2 的可定向）。

## 3. 记录

- 每砖：聚焦检查 exit=0 零 warning，命名空间感知的 `#print axioms` 审计，提交并推送；计划行状态列写明定理名与提交哈希。
- 新定义（环的共轭类、正规系统、领）的签名一旦被下游引用即冻结，改动必须回写计划 §4 表。
- 检查点：L.1 做完（含形变收缩的取舍）先汇报再做 B.3。

## 4. 2026-09-15 追加：L.1 已复核；B.3 与 L.2 的推离步骤依赖 S.5，改序

### 4.0 复核

`DerivedNeighborhoodRetraction`、`LoopTheorem.SingularCell` 由本方独立重编：exit=0、零 warning；本方按命名空间生成的
105 项 `#print axioms` 审计全部只含标准三公理。`SingularTwoCell`、`NormalSystem`（条件 (1)–(4)：`K₁` 为相对导出邻域、
`|D| ∩ Bd M₁ = |L|`、`B₁` 为边界中碰 `|L|` 的单形之并、`N₁` 正规且 `L(B₁) ∩ N₁ = ∅`）与复杂度定义与书页 187–188 一致。
你报告的 `AuditL1.lean` 不在 `D:\differential-geometry-moise-e3\.lake\scratch`；以后审计文件留在本工作树的 `.lake\scratch`。

### 4.1 依赖更正（本文件 §2 对 B.3、L.2 的估计有误）

- Moise 26.2 的证明（书页 192）第一步"多面体 3-胞腔 `C₁ ⊆ M³` 与 PLH `ρ₁ : d₁ × [0,1] ↔ C₁`，`C₁ ∩ B = d₁`"以及每个
  归纳步的 `C_{i+1}` 都来自 §23 的 23.9–23.11（书页 169：`N(v)`、`N'(σ)` 由 17.12 经 23.9 是组合 3-胞腔）。
  这是计划行 S.5，属 S 车道，S 车道现在还在 S.2。**B.3 阻塞于 S.5**；S.5 到位后按书的归纳做。
- L.2 第 3 步"把 `Int Δ_i` 稍微推离 `B`"同样需要 `Δ_i` 在 `M` 中的 3-胞腔邻域（23.10 型），也阻塞于 S.5。
- 不要用正则邻域唯一性（Rourke–Sanderson 第 3 章）或曲面分类另起炉灶绕过：那是与 S 车道重复的第二条基础路线。
- 把计划行 B.3 改为 "blocked on S.5（23.9–23.11）"，L.2 改为 "partial：推离步骤等 S.5"。

### 4.2 现在做（顺序）

1. `SphereSchoenflies.lean`（L.2 第 1 步，独立可做）：PL 2-球面 `B` 中的多边形 `J` 在 `B` 中界定两个 PL 2-胞腔。
   路线：`B` PL 同胚于 3-单形的边界；细分后去掉一个与 `J` 不交的开 2-单形，剩下的 PL 2-球 PL 同胚到平面多边形区域，
   用 P.1 `isPLBall_of_isPLSphere_one`（`PolygonalSchoenflies.lean:1240`）后搬回；另一侧用 `B` 减去第一侧。
2. `LoopTheorem/BoundaryGeneration.lean`（L.2 第 2 步）：`B'` 为 `B` 减去有限个不交 PL 2-胞腔的内部（边界多边形 `p_i`），
   则 `p̄_i` 正规生成 `π(B', P₀)`。路线：`B` 单连通（`sphereTwoSimplyConnectedSpace` 沿 PL 同胚搬运）与贴 2-胞腔的
   van Kampen（`DifferentialGeometry/Topology/VanKampen/`）。若树里的 van Kampen 形式不合，先汇报确切缺口。
3. `LoopTheorem/SphereCase.lean`：Lemma 1 的条件版。显式假设（不是 sorry）
   `hpush : ∀ Δ, IsPLBall 2 Δ → Δ ⊆ Bd M → ∃ D₁ : SingularTwoCell M, D₁.IsNonsingular ∧ range (Bd D₁) = frontier Δ ∧ range D₁ ∩ Bd M = frontier Δ`
   （精确形式由你定，写进计划行 L.2），结论为 Lemma 1 全部条款。S.5 之后由 B.3 的子复形版本给出 `hpush`。
4. C.4/C.5 桥接（H.2/H.5 到达前可做）：ℤ₂ 单纯 1-上循环 ↔ `Hom(H₁(K;ℤ), ℤ₂)`，指标 2 子群 ↔ `π₁ ↠ ℤ₂`
   （`Topology/Homology/*`、C.1 的 `card_fiber_eq_index`、C.2 的 `SimplicialBoolCocycle`/`IsCoboundary`），
   使 C.4/C.5 在 H 汇报后只剩接线。
5. L.4 的骨架：Lemma 3 的复杂度归纳，条件于 Lemma 1、Lemma 2 与两个二重覆盖存在定理（24.7、24.8）的显式陈述。
   其中"提升的正规系统复杂度更小"：24.1 提升（C.1 `exists_unique_lift_of_isPLBall`）、C.3 `exists_lift_simplicialComplex`
   给 `K̃₁`，`relDerived` 给 `M₂`；复杂度不增，若相等则 `g||D̃|` 为同胚、`(g||D̃|)*` 满、与 `g*` 指标 2 矛盾
   （C.1 `injective_fundamentalGroup_map`、`card_fiber_eq_index`）。这是 L.4 里不依赖 F5.2 的全部内容。
6. 有余力再做 B.1（26.1 两侧性，书页 191）。

L.3（Cases 1–4）等 F 车道的 F5.2；B.3 与 L.2 的推离等 S.5。每砖检查点同 §3；第 1–3 项做完先汇报。

## 5. 2026-09-15 追加：第 1 砖已复核；第 2 砖的接口与架构（2-胞腔贴合基础设施纳入本车道）

### 5.0 复核

`SphereSchoenflies` 由本方独立重编 exit=0、零 warning；`AuditSphereSchoenflies` 三项只含标准三公理。
端点 `exists_isPLBall_pair_of_isPLSphere_two` 的形式（两个盘各带标准单形参数化、并为 `B`、交为 `J`）正是第 2、3 砖要用的。

### 5.1 第 2 砖的接口

```lean
theorem eq_top_of_boundaryLoops_mem_normal
    {B : Set E} (hB : IsPLSphere 2 B) {k : ℕ} (D : Fin k → Set E) (q : Fin k → (Fin 3 → ℝ) → E)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i)) (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Disjoint on D))
    -- B' := B \ ⋃ i, q i '' (相对内部)，作为子类型；P₀ : B'
    (N : Subgroup (FundamentalGroup B' P₀)) [N.Normal]
    (hN : ∀ i, loopClassMeets (第 i 个边界多边形作为 B' 中的 freeLoop) N) : N = ⊤
```
写法自定，以 L.1 的 `freeLoop`、`loopClassMeets`、`loopRepresentativeAlong` 为准；必须允许 `k` 个胞腔与任意基点。
它就是 Lemma 1 里"若所有 `p̄_i ∈ N'` 则 `N' = π(B')`"的那一步。

### 5.2 架构

- 不用库里的抽象贴合空间（`CellAdjunctionSpace` 的 `outerInclusion` 只做了 3-胞腔）。直接在 `B` 里逐个贴胞腔：
  第 `j` 步的环境空间 `X_j := B' ∪ D_1 ∪ … ∪ D_j`（`B` 的闭子集，当作拓扑空间），开集 `U := X_j \ {c_j}`
  （`c_j := q_j(重心)`）、`V := Int D_j`，`U ∩ V` = 去心开盘。`π₁(V) = 1`；`π₁(U ∩ V) ≅ ℤ`
  （`Topology/FundamentalGroup/Circle.lean` 的 `fundamentalGroupCircleEquivInt` 沿 `q_j` 搬运），其生成元在 `U` 中
  同伦于边界环 `p_j`（沿 `q_j` 的径向同伦）；`π₁(U) ≅ π₁(X_{j-1})`（`U` 沿 `q_j` 径向强形变收缩到 `X_{j-1}`，
  `Topology/Homotopy/DeformationRetract.lean`）。
- van Kampen 用 `Topology/VanKampen/Based.lean`（`GrpCat` 中的 pushout）与 `AmalgamatedProduct.lean`；核公式用你在
  scratch 已验证的 `ker_eq_normalClosure_range_of_isPushout_of_subsingleton`（移入正式文件）。
  每步结论：`π₁(X_{j-1}) → π₁(X_j)` 满，核 = `⟨⟨p̄_j⟩⟩`。
- 有限迭代：各步满射 + 核的合成 ⇒ `ker (π₁(B') → π₁(B)) = ⟨⟨p̄_1, …, p̄_k⟩⟩`；`B` 单连通
  （`sphereTwoSimplyConnectedSpace` 沿 `IsPLSphere 2` 的 PL 同胚搬运）⇒ 端点。基点全程取 `P₀ ∈ B'`，
  各环用连接道路；正规闭包与连接道路的选择无关（L.1 已证共轭类不依赖连接道路）。
- 文件：`LoopTheorem/CellAttachmentKernel.lean`（单个胞腔的核定理，纯拓扑）、`LoopTheorem/BoundaryGeneration.lean`
  （迭代与球面）。这组 2-胞腔贴合基础设施明确纳入本车道。
- 第 3 砖的准备：Lemma 1 的 `B'` 是 `|L|` 在 `B` 中的导出邻域，是带边组合 2-流形（F4.2），边界为有限个不交多边形；
  每个边界多边形用第 1 砖分 `B` 为两盘，`B'` 连通且不碰多边形内部，故落在一侧，另一侧就是补分支 `Δ_i`，
  `B = B' ∪ ⋃ Δ_i`。这是接口 5.1 的输入。

里程碑：M1 单胞腔核定理（含径向收缩与生成元自然性）→ 汇报；M2 端点 5.1 → 直接进第 3 砖（Lemma 1 条件版，`hpush` 显式）。

## 6. 2026-09-15 夜间 E3-M1：SphereCase 一般目标版

状态：partial。数学提交 `e3c1b1c96`。

- `exists_nonsingular_two_cell_of_sphere_boundary_map` 把 Lemma 1 的纯逻辑层推广到任意有限维实赋范环境 `E`、任意带
  `ChartedSpace (EuclideanSpace ℝ (Fin 3))` 的目标 `X` 与实现映射 `ι : X → E`；`hpush` 和结论都保留胞腔像落在指定
  `M`、参数化边界像以及与指定 `BdM` 的精确交集。
- `exists_nonsingular_two_cell_of_sphere_boundary` 取 `X = K.space`、`ι = Subtype.val`、
  `BdM = (boundaryComplex 3 K).space`，因此条件端点与 `hpush` 已不再限制于 ℝ³，且结论中的胞腔确实取值于 `K.space`。
- `SphereCase` 聚焦检查 exit=0、零 warning；`.lake/scratch/AuditSphereCase.lean` 的 13 项命名空间感知审计全部只含
  `propext`、`Classical.choice`、`Quot.sound`。
- 确切未闭合项：I2 要从 `hK : IsCombinatorialManifoldWithBoundary 3 K` 自动取得上述 `ChartedSpace`，但本树
  `combinatorialChartedSpace K hK` 的参数实际是 `IsCombinatorialManifold 3 K`；边界顶点的 link 是 PL 2-球而非 PL 2-球面，
  因而不存在到 ℝ³ 开集的局部同胚。当前 `SingularTwoCell` 把目标模型硬编码为 ℝ³，不能用于一般带边 `K.space`。
  要无附加表示假设闭合 I2，必须先提供带边模型（例如半空间图卡）对应的奇异胞腔/PL 映射类型，或把胞腔定义改为内在单纯数据；
  不能用现有 `VertexChart.lean` 的无边界图册冒充该生产者。

## 7. 2026-09-15 夜间 E3-M2：正规奇异分支与割贴字计算

状态：partial。数学提交 `6c8b8e812`。

- `LoopTheorem/NormalCell.lean` 在 I3 尚未进入整合分支时按 §1 I3 的同形字段给出
  `NormalSingularCellData` 与 `NormalSingularSetTriangulation`。它证明奇点复形每个顶点的边数为 1 或 2、边界复形顶点当且
  仅当边数为 1、闭分支每个顶点边数为 2、触边分支含边数为 1 的端点，并以闭分支数加触边分支数定义复杂度。
  `NormalSingularSetTriangulation.complexity_eq_zero_iff` 与
  `NormalSingularCellData.complexity_eq_zero_iff` 证明该复杂度为零当且仅当原奇异 2-胞腔非奇异；
  `NormalSingularCellData.exists_fiber_eq_pair` 和 `fiber_encard_eq_two` 证明每个奇点恰有两个原像。
- `LoopTheorem/CutAndPaste.lean` 证明正规子群中“母环不属于正规子群则至少一个子环不属于正规子群”的两个共轭乘积引理；
  `four_path_mul_conj_inv_mul_factorization` 是书页 187 Case 4 的完整群字恒等式，
  `not_mem_or_not_mem_of_four_path_factorization` 给出其保持 `L(B') ∩ N' = ∅` 的代数结论。
- `NormalCell` 与 `CutAndPaste` 聚焦检查均 exit=0、零 warning；`.lake/scratch/AuditE3M2.lean` 的 15 项
  命名空间感知审计全部只含 `propext`、`Classical.choice`、`Quot.sound`。
- 尚未闭合的第一处义务是从 I3 的 `crossing` 证明
  `D : D.domain ∩ D ⁻¹' doublePointSet D D.domain → doublePointSet D D.domain` 为二重覆盖：
  `HasPLDoubleCrossingAt` 给两张局部片与邻近纤维覆盖，但本树没有把该数据组装成限制映射 `IsCoveringMap` 的桥接定理。
  没有它就不能用 C.1 将闭分支原像分类为一条二重圆周或两条圆周，也不能得到触边分支的两条折线原像。
- 下一处义务是 Case 1/2 的盘内环带正则邻域、在环带上替换 `D` 后仍为正规奇异胞腔，以及 Case 2 的内盘替换与 I2 推离；
  Case 3/4 还需要沿两条原像折线实际切开 PL 2-球并构造两个较低复杂度的 `SingularTwoCell`。现有树只有上面的正规子群字计算，
  没有这些几何构造，因此未建立 `LoopTheorem/LemmaTwo.lean` 的 Lemma 2 端点，也未把几何降复杂度伪装成显式假设。

## 8. 2026-09-15 夜间 E3-M3：Lemma 3 条件性骨架

状态：done（条件性骨架）。数学提交 `93b3ac9cd`。

- 计划指定的 `LoopTheorem/LemmaThree.lean` 现在承载 Lemma 3 开发；旧模块
  `LoopTheorem/StallingsInduction.lean` 只导入它，因而既保留已有消费者的模块路径，又不复制声明。
- `vertexCollisionPairs_subset_of_factorization` 与 `simplicialComplexity_le_of_factorization` 证明提升后的顶点碰撞对包含于原碰撞对，
  所以复杂度不增；`eq_vertexMap_of_eq_simplicialComplexity_of_factorization` 与
  `injOn_vertexMap_iff_of_eq_simplicialComplexity_of_factorization` 精确刻画相等情形：原图中相撞的任意两个源顶点在提升中仍相撞，
  且原、提升顶点映射的单射性等价。严格分开一个原碰撞对时，已有
  `simplicialComplexity_lt_of_factorization_of_separated` 给出严格降阶。
- `exists_nonsingular_cell_of_stallings_induction` 保持四个显式接口：球面边界的 Lemma 1、从提升回推的 Lemma 2、不可定向情形
  24.7 的二重覆盖、可定向且边界分支非球面情形 24.8 的二重覆盖；随后对复杂度作强归纳。没有引入结论型假设或新增公理。
- `LemmaThree` 与兼容模块聚焦检查均 exit=0、零 warning；`.lake/scratch/AuditE3M3.lean` 的 10 项审计全部只含
  `propext`、`Classical.choice`、`Quot.sound`。
- 条件骨架之外尚缺实际 `DoubleCoverReduction` 生产者：要把 C.1/C.3 的提升复形、`relDerived` 正规邻域与提升后的正规系统接好；
  在复杂度相等分支，还须把上述顶点碰撞等价提升为覆盖投影在 `|D̃|` 上的 PL 同胚，再证明其基本群映射满，与
  C.1 的 `card_fiber_eq_index = 2` 矛盾。24.7/24.8 的覆盖本身则等 E3-M4 的 C.4/C.5 接线。

## 9. 2026-09-15 夜间 E3-M4：C.4/C.5 二重覆盖接线

状态：partial。数学提交 `56456ff35`。

- `DoubleCoverExistence.lean` 的 `SimplicialBoolCocycle.finite_fiber` 从 C.2 的纤维基数二得到 C.3 所需的有限纤维；
  `SimplicialBoolCocycle.exists_lift_simplicialComplex` 将该覆盖直接接到 C.3 的有限提升复形，并保留每个提升单形上投影为仿射映射的完整条款。
- `SimplicialBoolCocycle.exists_connected_double_cover_complex` 对任意非上边界上循环同时给出连通二重覆盖、每纤维恰两点、
  有限提升复形及组合流形性保持。`exists_connected_double_cover_complex_of_not_isOrientable` 按 NIGHT_PLAN §1 I4 的精确形式
  把“不可定向产生非上边界定向上循环”保留为显式假设，并在重心细分上交付 C.4 的上述全部覆盖数据。
- 聚焦检查 exit=0、零 warning；`.lake/scratch/AuditE3M4.lean` 的 14 项审计全部只含
  `propext`、`Classical.choice`、`Quot.sound`。其中逐条审计了首次在本模块复用的
  `SimplicialBoolCocycle.isCoveringMap`、`card_fiber`、`connectedSpace_iff`、
  `exists_lift_simplicialComplex` 以及组合流形细分接口；另审计了 Bennett `Coefficients` 的四条换系数端点。
- C.4 尚缺 Problem 24.11 的“所得覆盖可定向”：当前 C.3 已证明提升复形保持带边组合流形性，但整合分支尚无 H.2a 所需的
  定向覆盖上定向构造或相应 PL 不变性端点；I4 的三条定向上循环端点本身也尚未进入整合分支，故当前端点按夜间规则条件于 I4。
- C.5 的群论半边仍由 `Topology/Algebra/Group/IndexTwo.lean` 闭合。Bennett `Coefficients.lean` 实际只构造增广奇异链的换系数映射、
  约化奇异同调换系数映射及其复合与自然性；它不含有限几何复形的单纯链比较、泛系数定理、
  `H¹(K; ℤ₂) ≃ Hom(H₁(K; ℤ), ℤ₂)`，也不把同调同态变成 `SimplicialBoolCocycle`。
  本树同时没有无 `sorry` 的一维 Hurewicz `π₁ᵃᵇ ≃ H₁`，且规则禁止经过 `HurewiczLowDegrees.lean`。
  因而即使 I5 给出 `bettiOne K > 0`，仍不能在不增加结论型假设的前提下产生非上边界 ℤ₂ 上循环；C.5 保持 partial，未弱化端点。

## 10. 2026-09-15 E3-M2 追加：奇点原像的二重覆盖

状态：done（E3-M2 的第一个独立阻塞已闭合，整体 L.3 仍为 partial）。数学提交 `3f077e13f`。

- 新模块 `LoopTheorem/DoublePointCover.lean` 定义 `doublePointPreimage` 与
  `doublePointProjection`。`isLocalHomeomorph_doublePointProjection` 把两张互不相交的局部嵌入片、相对邻域与邻近纤维覆盖
  组装为奇点原像到奇点集的局部同胚；该拓扑定理不额外假设纤维基数。
- `doublePointSheetsAt_of_hasPLDoubleCrossingAt_chart` 把图内
  `HasPLDoubleCrossingAt (e ∘ D)` 的两张 PL 片拉回到目标空间，证明相对邻域、嵌入性和邻近纤维覆盖在拉回后保持。
  因此 `NormalSingularCellData.doublePointProjection_isCoveringMap` 在 `[T2Space M]` 下给出完整
  `IsCoveringMap`；紧致性由奇异盘的紧致定义域和局部单射推出。
- `NormalSingularCellData.doublePointProjection_fiber_encard_eq_two` 把覆盖纤维与
  `D.domain ∩ D ⁻¹' {y}` 通过子类型值映射精确识别，证明每个奇点上的纤维 `encard = 2`。
- 聚焦检查 exit=0、零 warning；`.lake/scratch/AuditDoublePointCover.lean` 对 10 个新声明与
  D4 首次在本桥接复用的 `isLocalHomeomorph_iff_isOpenEmbedding_restrict`、
  `isLocalHomeomorph_iff_isCoveringMap` 逐条审计，共12 项，全部只含
  `propext`、`Classical.choice`、`Quot.sound`。
- 确切未闭合项：下一步要用 C.1 将闭分支上的二重覆盖分类为一条二重多边形或两条不交多边形，
  并将触边分支的原像分解为两条不交折线。当 F 的最终 I3 加入边界半空间析取时，还需从
  `HasPLBoundaryDoubleCrossingAt` 到 `HasDoublePointSheetsAt` 的同类桥接。之后 Case 1–4 仍缺环带正则邻域、盘内替换、
  沿两条原像折线切开 PL 2-球并重建较低复杂度奇异胞腔的几何生产者；它们没有被弱化为假设。

## 11. 2026-09-15 E3-M2 追加：二重覆盖的连通分支分类

状态：done（E3-M2 的拓扑分支分类层已闭合，整体 L.3 仍为 partial）。数学提交 `8a4d706ed`。

- 新模块 `Topology/Covering/TwoSheetComponents.lean` 从每个纤维 `encard = 2` 构造规范的另一纤维点
  `fiberSwap`，并将已有 `exists_exactly_two_components_of_not_connected` 应用于二重覆盖。端点
  `connectedSpace_or_exists_exactly_two_components` 证明连通基空间上的二重覆盖要么连通，要么恰由两个连通分支组成，
  且每个分支到基空间都是同胚。
- `connectedSpace_or_exists_exactly_two_components_restrictPreimage` 将同一结论推广到任意连通子集 `J` 上的限制覆盖；
  `NormalSingularCellData.doublePointProjection_connected_or_two_components` 因而直接分类任意连通奇异分支上的原像。
  `doublePointPreimage_isCompact` 与 `doublePointProjection_isClosedMap` 同时把上一里程碑中隐含在覆盖证明里的紧致、闭映射层独立暴露。
- `TwoSheetComponents` 聚焦检查 exit=0、零 warning；`.lake/scratch/AuditTwoSheetComponents.lean` 的 10 项审计全部只含
  `propext`、`Classical.choice`、`Quot.sound`。`DoublePointCover` 聚焦检查 exit=0、零 warning；更新后的
  `.lake/scratch/AuditDoublePointCover.lean` 共 15 项，全部只含这三个标准公理。
- D4 首次复用并逐条审计了
  `DifferentialGeometry.Topology.Covering.exists_exactly_two_components_of_not_connected`、
  `IsCoveringMap.restrictPreimage`、`IsClosedMap.restrictPreimage`；其余上一里程碑的 D4 声明继续保留在同一审计文件中。
- 确切未闭合项：`NormalSingularSetTriangulation.Branch` 目前只是有限边图的连通分支，尚未有把其顶点支集实现为
  `doublePointSet D D.domain` 中连通多面体 `J` 的接口；还须证明闭分支的载体为 PL 1-球面、触边分支的载体为 PL 1-球，
  并证明上述限制覆盖的连通分支在 `D.domain` 中是多边形或折线，而不只是拓扑同胚副本。本树尚缺有限一维分支的 PL 载体与
  覆盖原像三角剖分桥接。此后 Case 1/2 的环带正则邻域与盘替换、Case 3/4 的切开重建，以及最终 I3 边界半空间析取到
  `HasDoublePointSheetsAt` 的桥接仍未闭合，也没有被弱化为假设。

## 12. 2026-09-15 E3-M2 追加：图分支的连通子复形载体

状态：done（E3-M2 的分支载体层已闭合，整体 L.3 仍为 partial）。数学提交 `7dd606e0e`。

- 新模块 `Topology/SimplicialComplex/ConnectedSpace.lean` 证明
  `isConnected_space_of_edgeGraph_connected`：单纯复形的边图连通时，其几何实现连通。证明把实现写成所有顶点闭星的并，
  用边图道路把闭星的非空相交关系连接起来。
- 新模块 `LoopTheorem/BranchCarrier.lean` 对每个
  `NormalSingularSetTriangulation.Branch` 构造 `branchComplex`。其顶点与该图分支的支集等价，边图同构于
  `ConnectedComponent.toSimpleGraph`；因此 `branchComplex_space_isConnected`，且其空间是有限多面体。
  `branchComplex_isManifoldWithBoundary` 证明每个分支子复形是带边组合 1-流形；
  `branchComplex_isManifold` 进一步证明闭分支是无边界组合 1-流形。
- `branchCarrier` 是该子复形经 PL 片参数化映入目标后的像；`branchCarrier_subset_doublePointSet` 与
  `branchCarrier_isConnected` 证明它确实是奇点集中的连通分支载体。`branchSet` 将其内在地写成
  `doublePointSet D D.domain` 的子集并证明连通。
- `NormalSingularCellData.doublePointProjection_branch_connected_or_two_components` 现直接接受实际图分支 `c`，并把其原像分类为
  一个连通二重覆盖，或两个各自同胚到 `branchSet c` 的连通分支；不再要求消费者自行提供抽象连通子集 `J`。
- `ConnectedSpace`、`BranchCarrier`、`DoublePointCover` 三模块聚焦检查均 exit=0、零 warning；
  `.lake/scratch/AuditBranchCarrier.lean` 的 30 项与更新后 `.lake/scratch/AuditDoublePointCover.lean` 的 16 项审计
  全部只含 `propext`、`Classical.choice`、`Quot.sound`。本层没有首次复用新的 covering/Van Kampen 声明；覆盖分类继续走
  §11 已逐条审计的 D4 链。
- 确切未闭合项：尚需有限一维组合流形分类桥接，证明闭分支的 `branchComplex.space` 是 PL 1-球面、触边分支的是 PL 1-球；
  还需证明二重覆盖原像的连通分支带有与 `D.domain` 相容的有限 PL 三角剖分，从拓扑同胚升级为多边形圆或折线。
  若 Case 1–4 需要全局分解，还须显式证明各 `branchCarrier` 两两不交并覆盖整个 `doublePointSet`。
  环带正则邻域、盘替换、切开重建与 I3 边界半空间桥接仍未闭合，也没有被弱化为假设。

## 13. 2026-09-15 E3-M2 追加：奇点集的分支分割

状态：done（E3-M2 的全局分支分解层已闭合，整体 L.3 仍为 partial）。数学提交 `defee201d`。

- `space_eq_iUnion_branchComplex` 与 `pairwise_disjoint_branchComplex_space` 证明所有图分支子复形的空间两两不交，且并集恰为
  `singularSet.complex.space`。证明直接使用每个面至多两个顶点和边图连通分支，不加入分类假设。
- `iUnion_branchCarrier` 与 `pairwise_disjoint_branchCarrier` 将该分割经 PL 片的全局单射搬到目标，得到
  `doublePointSet D D.domain` 恰为所有 `branchCarrier` 的两两不交并。
  `iUnion_branchSet` 与 `pairwise_disjoint_branchSet` 给出同一结论的内在子类型形式。
- `BranchCarrier` 聚焦检查 exit=0、零 warning；更新后的 `.lake/scratch/AuditBranchCarrier.lean` 共 36 项，
  全部只含 `propext`、`Classical.choice`、`Quot.sound`。本层未首次复用新的 covering/Van Kampen 声明。
- 确切未闭合项因此缩减为两条表示桥：有限连通一维组合流形的 PL 球/球面分类，以及二重覆盖原像连通分支的有限 PL 三角剖分。
  前者把闭分支升级为多边形圆、触边分支升级为折线；后者把 §11 的拓扑覆盖分类升级为盘内的多边形原像。
  Case 1–4 的环带、替换与切开重建，以及 I3 边界半空间桥接仍未闭合，也没有被弱化为假设。

## 14. 2026-09-15 E3-M2 追加：有限平面复形的几何单纯复形桥接

状态：done（闭分支 PL 圆分类的表示层前置已闭合，整体 L.3 仍为 partial）。数学提交 `8c03e7d5c`。

- `PlanarSchoenflies.lean` 新增 `simplicialComplexOfPlaneComplex`，把 vendored `PlaneComplex` 的有限抽象顶点、面与平面位置
  原样实现为项目的 `Geometry.SimplicialComplex ℝ Plane`；面集是 `simplexes` 经 `position` 的像，不引入额外顶点或面。
- `mem_simplicialComplexOfPlaneComplex_faces_iff` 暴露精确面对应；
  `simplicialComplexOfPlaneComplex_faces_finite` 保留有限性；
  `simplicialComplexOfPlaneComplex_space` 证明新复形空间恰为原 `PlaneComplex.support`。因此
  `PolygonalCircle.edgeComplex_support` 与 `isPLSphere_one_carrier` 现在可直接接入项目的单纯映射 PL 同胚接口。
- `PlanarSchoenflies` 聚焦检查 exit=0、零 warning；`.lake/scratch/AuditPlaneComplexBridge.lean` 的 4 项审计全部只含
  `propext`、`Classical.choice`、`Quot.sound`。本层未首次复用新的 covering/Van Kampen 声明。
- 下一步仍须从有限连通 2-正则边图取得覆盖全部顶点的循环，把其顶点编号与某个同边数的 `PolygonalCircle.edgeComplex`
  做双向面对应，再由 `isPLHomeomorphOn_simplicialMap` 得到闭分支空间是 PL 1-球面。触边分支还需相应的有限路径分类；
  二重覆盖原像的有限 PL 三角剖分、Case 1–4 几何构造与 I3 边界半空间桥接仍未闭合。

## 15. 2026-09-15 E3-M2 追加：一维复形的边图同构搬运

状态：done（闭分支与触边分支分类的共同 PL 搬运层已闭合，整体 L.3 仍为 partial）。数学提交 `3e40133ec`。

- 新模块 `Topology/PiecewiseLinear/OneComplex.lean` 定义 `vertexMapOfEdgeGraphIso`，把两个几何单纯复形边图之间的同构
  延拓为环境向量空间之间的顶点映射；逆映射由反向图同构同样构造。
- `image_mem_faces_of_edgeGraphIso` 证明在所有面至多两个顶点时，边图同构自动保持全部面：单点面由顶点条件保持，双点面恰由边邻接保持。
  `isGlueIso_vertexMapOfEdgeGraphIso` 将双向保持与顶点互逆组装成 `IsGlueIso`；
  `isPLHomeomorphOn_of_edgeGraphIso` 因而直接给出两个有限一维复形空间之间的 PL 同胚。
- `OneComplex` 聚焦检查 exit=0、零 warning；`.lake/scratch/AuditOneComplex.lean` 的 5 项审计全部只含
  `propext`、`Classical.choice`、`Quot.sound`。本层未复用 covering/Van Kampen 声明。
- 现在闭分支只剩纯有限图步骤：从连通 2-正则边图建立到同边数多边形边复形的图同构；触边分支相应只剩连通度数 1/2 图的路径分类。
  二重覆盖原像的有限 PL 三角剖分、Case 1–4 几何构造与 I3 边界半空间桥接仍未闭合。

## 16. 2026-09-16 E3-M2 追加：闭分支的 PL 圆分类

状态：done（闭分支的有限一维组合流形分类已闭合，整体 L.3 仍为 partial）。数学提交 `a0c440917`。

- 新模块 `Topology/PiecewiseLinear/OneManifoldClassification.lean` 证明有限连通 2-正则简单图同构于同顶点数的循环图。
  `exists_spanning_cycle_of_connected_degree_two` 取得覆盖全部顶点的单圈；`cycleVertexEquiv` 精确编号其顶点；
  `exists_cycleGraphIsoOfConnectedDegreeTwo` 将覆盖全部顶点的循环 copy 用两侧度数均为 2 升级为图同构。
- `exists_polygonalCircle_n` 从标准三角形反复在边的中点插点，构造任意指定 `n ≥ 3` 个顶点的 `PolygonalCircle`。
  `polygonComplex` 用 §14 的桥接实现其边复形；`polygonVertexEquiv`、`polygonEdgeGraph_connected` 与
  `exists_polygonEdgeGraphIso` 证明该边复形的边图正是同顶点数循环图。
- `isPLSphere_one_of_edgeGraph_connected` 通过 §15 的边图同构搬运证明：有限、边图连通的组合 1-流形空间是 PL 1-球面。
  `NormalSingularSetTriangulation.branchComplex_isPLSphere` 将此应用于每个非触边分支，正式交付闭分支的 PL 圆端点。
- `OneManifoldClassification` 与 `BranchCarrier` 聚焦检查均 exit=0、零 warning；
  `.lake/scratch/AuditOneManifoldClassification.lean` 的 20 项与更新后 `.lake/scratch/AuditBranchCarrier.lean` 的 37 项审计
  全部只含 `propext`、`Classical.choice`、`Quot.sound`。本层未复用 covering/Van Kampen 声明。
- 尚未闭合的相邻表示步骤是触边分支分类：需证明有限连通、每点度数 1 或 2 且含度数 1 顶点的图是有限路径，继而用同一
  `OneComplex` 搬运层证明 `branchComplex.space` 是 PL 1-球。二重覆盖原像仍需与 `D.domain` 相容的有限 PL 三角剖分；
  Case 1–4 的环带、替换、切开重建及 I3 边界半空间桥接仍未闭合，也没有被弱化为假设。

## 17. 2026-09-16 E3-M2 追加：触边分支的 PL 区间分类

状态：done（有限一维分支的 PL 球/球面分类已闭合，整体 L.3 仍为 partial）。数学提交 `af04ef1c5`。

- `SimpleGraph.exists_spanning_path_of_connected_degree_one_or_two` 从最长简单道路出发，证明有限连通、各点度数为 1 或 2、
  且含度数 1 顶点的简单图恰由一条道路覆盖；`exists_pathGraphIsoOfConnectedDegreeOneOrTwo` 将其升级为与标准有限路径图的同构。
- `polygonPathComplex` 删除 `PolygonalCircle` 的最后一条开边，得到同顶点数的有限路径复形；
  `polygonPathComplex_isPLBall` 由 PL 圆删除开弧的端点证明其空间是 PL 1-球，
  `exists_polygonPathEdgeGraphIso` 证明其边图是标准路径图。
- `isPLBall_one_of_edgeGraph_connected_of_exists_degree_one` 证明有限、边图连通且含度数 1 顶点的带边组合 1-流形空间是 PL 1-球。
  二顶点情形直接识别为一个非退化线段；至少三顶点时通过路径图同构与 `OneComplex` 的 PL 搬运接口归约到
  `polygonPathComplex`。`NormalSingularSetTriangulation.branchComplex_isPLBall` 将其应用到每个触边分支。
- `OneManifoldClassification` 与 `BranchCarrier` 聚焦检查均 exit=0、零 warning；
  `.lake/scratch/AuditOneManifoldClassification.lean` 的 44 项与更新后的 `.lake/scratch/AuditBranchCarrier.lean` 的 38 项审计
  全部只含 `propext`、`Classical.choice`、`Quot.sound`。本层未首次复用新的 covering/Van Kampen 声明。
- 尚未闭合的表示步骤只剩二重覆盖原像连通分支与 `D.domain` 相容的有限 PL 三角剖分；它负责把 §11 的拓扑同胚分支升级为
  盘内多边形圆或折线。其后 Case 1–4 的环带正则邻域、盘替换与切开重建，以及 I3 边界半空间析取到双片覆盖的桥接仍未闭合，
  也没有被弱化为显式假设。

## 18. 2026-09-16 E3-M2 追加：实际分支载体的多面体类型与边界定位

状态：done（目标中的分支载体类型及其环境边界定位已闭合，整体 L.3 仍为 partial）。数学提交 `c9dd16be0`。

- `NormalSingularSetTriangulation.branchPieceIn` 将目标中的实际 `branchCarrier` 表示为原 PL 片在 `branchComplex` 上的限制；
  `branchCarrier_isPolyhedralSphere` 与 `branchCarrier_isPolyhedralBall` 因而把 §16–§17 的源复形分类搬到目标，分别证明闭分支载体是
  一维多面体球面、触边分支载体是一维多面体球。
- `isBoundaryBranch_of_mem_branchComplex_space_of_map_mem_boundary` 证明分支中任一点若映入 `BdM`，该分支必为触边分支；
  `branchCarrier_disjoint_boundary_of_not_isBoundaryBranch` 因而证明闭分支完全位于 `BdM` 外。
  `branchCarrier_inter_boundary_nonempty_of_isBoundaryBranch` 反向证明每个触边分支确实接触 `BdM`；
  `NormalSingularCellData.branchCarrier_inter_boundary_subset` 再证明所有实际边界接触点都落在指定边界邻域 `B`。
- `BranchCarrier` 聚焦检查 exit=0、零 warning；更新后的 `.lake/scratch/AuditBranchCarrier.lean` 共 47 项，
  全部只含 `propext`、`Classical.choice`、`Quot.sound`。本层未首次复用新的 covering/Van Kampen 声明。
- 尚未闭合的精确表示缺口是：给 `doublePointProjection` 在每个 `branchSet` 上的连通原像分支构造与 `D.domain` 相容的有限 PL 三角剖分，
  从而把 §11 的拓扑二重覆盖分类升级为盘内的一条或两条多边形圆/折线；现有 `SingularTwoCell.isPLOn` 没有携带源三角剖分，
  本树也没有任意抽象 PL 映射下多面体原像仍为多面体的生产者。之后仍须完成 Case 1–4 的环带正则邻域、盘替换、切开重建，
  以及 I3 的边界半空间析取到 `HasDoublePointSheetsAt` 的桥接；这些步骤没有被弱化为假设。

## 19. 2026-09-16 E3-M2 追加：触边分支的源 crosscut 与共轭类字分解

状态：partial（书页 186–187 的 Case 3/4 已闭合到源 crosscut 与环类代数结论，整体 L.3 仍未闭合）。数学提交
`1ee830f87`、`57431d277`、`53d256d7e`、`9b039490d`、`7bbeaf51b`。

- `BoundaryCrossing.lean` 用流形版 invariance of domain 证明半空间双交叉的双点纤维只能落在源盘边界；
  `NormalSingularCellData.fiber_subset_frontier_of_boundary_crossing` 给出供最终 I3 边界析取直接调用的形式。
- `BranchBoundary.lean` 的 `branchComplex_boundary_iff_map_mem_boundary` 精确识别触边分支的两个组合端点与目标 `BdM` 中的点。
  `BranchPreimage.lean` 的
  `exists_two_isPLBalls_branchPreimage_of_boundaryBranch_with_coordinate` 同时给出两条不交源 PL 1-球、覆盖全部分支原像，
  并证明各自的 `branchCoordinate` 都是到目标分支复形空间的 PL 同胚。
- `BoundaryBranchCrosscut.lean` 先把任意 PL 1-球参数化为 `Icc 0 1` 并识别组合边界，再由内部点不落盘边界及边界半空间双交叉证明
  `exists_two_isCrosscuts_branchPreimage_of_boundaryBranch`：触边分支的两条源折线都是真正的盘 crosscut。
  当前边界半空间交叉按 NIGHT_PLAN §1 I3 的最终字段写成显式输入；它不是 Lemma 2 的结论，也不假设任何复杂度下降。
- `CutAndPaste.lean` 的 `loopRepresentativeAlong_mem_iff_loopClassMeets` 把选定基点连接道路所得代表元与无基点环的共轭类相交条件对应起来；
  `not_loopClassMeets_or_not_loopClassMeets_of_eq_mul_conj_mul_conj` 与
  `not_loopClassMeets_or_not_loopClassMeets_of_four_path_factorization` 分别把 Case 3 和 Case 4 的书中群字提升为环类结论：母环避开正规子群时，
  两个候选新边界环至少一个仍避开该子群。
- 五个模块的聚焦检查均 exit=0、零 warning。`.lake/scratch/AuditBoundaryCrossing.lean` 的 5 项、
  `.lake/scratch/AuditBranchBoundary.lean` 的 1 项、`.lake/scratch/AuditBranchPreimage.lean` 的 27 项、
  `.lake/scratch/AuditBoundaryBranchCrosscut.lean` 的 3 项及更新后 `.lake/scratch/AuditE3M2.lean` 的 26 项审计全部只含
  `propext`、`Classical.choice`、`Quot.sound`。本层首次复用的
  `DifferentialGeometry.Topology.invariance_of_domain_isOpen_image` 已单独审计；没有新增 covering/Van Kampen 复用声明。
- 确切未闭合项：`SingularTwoCell.exists_two_cells_of_isCrosscut` 只把源盘沿一条 crosscut 限制成两盘，其新边界仍含该奇异弧的像，
  因而不是 Moise Case 3/4 把两条同像原像弧交叉重接所得的 `D₁,D₂`，也不能据此声称新胞腔正规或复杂度下降。
  仍需构造三块源盘沿两条 PL 同胚 crosscut 的两种重接，证明重接映射 PL、边界字分别为书页 186–187 的公式、目标边界相交条件保持，
  并为所选新胞腔重建 `NormalSingularCellData` 且严格减少触边分支数。Case 1/2 还缺环带正则邻域、环带重定义、内盘替换与 I2 推离。

## 20. 2026-09-16 E3-M2 追加：两条 crosscut 的三盘链分解

状态：done（三盘源域分块已闭合，Case 3/4 的交叉重接仍为 partial）。数学提交 `d6f49f179`。

- `DiskCrosscut.lean` 的 `isCrosscut_of_subset_side` 证明：一条 crosscut 若包含在另一条 crosscut 切出的闭盘一侧并避开公共切弧，
  则它仍是该侧盘的 crosscut；证明同时核对端点落在新盘边界、开弧落在新盘内部。
- `SingularTwoCell.exists_two_cells_with_second_crosscut` 先沿第一条源折线切盘，并用第二条折线的连通性、两侧闭性与交集恰为第一条折线，
  证明第二条折线完整落在且仍 crosscut 其中一侧。
  `SingularTwoCell.exists_three_cells_of_two_disjoint_crosscuts` 再切该侧并规范重排，得到三张 PL 奇异 2-胞腔：三域覆盖原盘，
  相邻交依次恰为两条指定 crosscut，首尾两域不交，且三张映射都是原 `D` 的限制。
- `NormalSingularCellData.exists_three_cells_of_boundaryBranch` 将 §19 的触边分支双原像端点与上述通用分解组合，直接为任意触边奇异分支交付
  `A`、`C` 及三盘链；边界半空间交叉仍使用最终 I3 同形的显式输入。
- `DiskCrosscut` 与 `CutAndPaste` 聚焦检查均 exit=0、零 warning；更新后的 `.lake/scratch/AuditE3M2.lean` 共 30 项，
  全部只含 `propext`、`Classical.choice`、`Quot.sound`。本层未首次复用新的 covering/Van Kampen 声明。
- 确切未闭合项：三张输出仍是原映射在三块源盘上的限制，而书中 `D₁,D₂` 是沿 `A`、`C` 的共同目标像作两种交叉重接后的新盘。
  下一步需要一个二维边界弧贴合定理：把两张 PL 2-球沿由 `branchCoordinate|A`、`branchCoordinate|C` 诱导的 PL 同胚贴合，证明贴合空间仍为 PL 2-球，
  并把两侧相容的 PL 映射下降为 `SingularTwoCell`。本树 `Gluing.lean` 提供复形贴合与相容映射，但尚无该二维 PL 球结论的直接端点；
  完成后还须识别新边界环字、重建正规数据并证明复杂度严格下降。

## 21. 2026-09-16 E3-M2 追加：奇异 2-胞腔的边界弧贴合

状态：done（二维贴合层已闭合，Case 3/4 的分支专用交叉重贴仍为 partial）。数学提交 `7a87e8fe0`。

- 新模块 `LoopTheorem/CellGluing.lean` 的
  `SingularTwoCell.exists_glue_of_isPLHomeomorphOn_boundary_arc` 接受两张奇异 2-胞腔、各自边界中的 PL 1-球弧、弧间 PL 同胚，
  以及两张奇异映射在该识别下逐点相容的条件，实际构造贴合后的 `SingularTwoCell`。
- 构造先取 F 车道的标准双盘模型，使两盘交于一条线段；用
  `exists_isPLHomeomorphOn_eqOn_arc_of_isPLSphere_one` 把指定弧同胚延拓到两侧边界，再用
  `exists_isPLHomeomorphOn_of_frontier` 延拓到整盘。两侧参数化后的映射在公共线段上相等，故可逐片贴合。
- 模块内部证明了抽象 PL 目标中的两个必要封闭性步骤：PL 映射沿欧氏逐片仿射参数化预合成仍为 PL，且两个定义在闭多面体上的
  PL 映射若在交集相等，则其逐片函数在并集上仍为 PL。输出保留两侧盘的 PL 参数化、公共弧的精确识别以及贴合映射在每侧的逐点公式。
- 聚焦检查 exit=0、零 warning；更新后的 `.lake/scratch/AuditE3M2.lean` 共 36 项，全部只含
  `propext`、`Classical.choice`、`Quot.sound`。首次直接消费的弧参数化、边界弧延拓、整盘延拓和标准双盘模型均已单独审计；
  本层没有新增 covering/Van Kampen 复用声明。
- 下一精确义务是用 `branchCoordinate|A` 与 `branchCoordinate|C` 组成弧间 PL 同胚，把 §20 的首尾盘分别与中盘按书页 186–187
  的两种交叉配对调用该端点，并识别所得两张新盘的外边界环为 Case 3/4 的 `L₁,L₂`。此后仍须为至少一张新胞腔重建
  `NormalSingularCellData` 并证明触边分支数严格下降；Case 1/2 的环带重定义与内盘替换也尚未闭合。

## 22. 2026-09-16 E3-M2 追加：分支双层识别与三盘缝边界

状态：done（交叉重贴所需的弧间识别与缝边界数据已闭合，Case 3/4 的外边界环识别仍为 partial）。

- `BranchPreimage.lean` 的 `NormalSingularCellData.exists_isPLHomeomorphOn_branch_sheets` 取触边分支的两条源 PL 1-球 `A,C`，
  用 `branchCoordinate|A` 与 `branchCoordinate|C` 的逆合成规范 PL 同胚 `g : A → C`，并由两侧经同一 `branchPieceIn.map`
  证明 `EqOn D (D ∘ g) A`。这是 `SingularTwoCell.exists_glue_of_isPLHomeomorphOn_boundary_arc` 的精确相容性输入。
- `CutAndPaste.lean` 加强三盘链分解：除 `D₁∩D₂=A` 与 `D₂∩D₃=C` 外，现在显式交付
  `A ⊆ frontier D₁.domain ∩ frontier D₂.domain` 及
  `C ⊆ frontier D₂.domain ∩ frontier D₃.domain`。其中中盘的 `A` 边界性由内部单调性与分割前盘的边界性推出。
- `BranchPreimage` 与 `CutAndPaste` 聚焦检查均 exit=0、零 warning；更新后的 `.lake/scratch/AuditE3M2.lean` 共 37 项，
  全部只含 `propext`、`Classical.choice`、`Quot.sound`。本层没有新增 covering/Van Kampen 复用声明。
- 下一精确义务是将首、尾盘沿 `g` 调用边界弧贴合端点，再证贴合盘的剩余边界正是书页 186/187 的
  `συ⁻¹` 或 `συ`。当前贴合端点保留两侧参数化与公共缝，但还没有“两盘沿边界 1-球贴合后，新盘 frontier 等于两侧补弧之并”的精确集合恒等式；
  这一表示引理是识别 `L₁` 的当前精确缺口，未用假设绕过。

## 23. 2026-09-16 E3-M1 追加：I2 的 double 3 环境对接

状态：done（消费者已固定到 NIGHT_PLAN §6.1 的 double 环境；I2 生产者未到，仍为同形显式输入）。

- `SphereCase.lean` 新增 `exists_nonsingular_two_cell_of_sphere_boundary_double`：输入有限带边组合 3-流形 `K`，
  把奇异 2-胞腔的环境精确取为 `X := (double 3 K).space`，并在声明内安装
  `combinatorialChartedSpace (double 3 K) (isCombinatorialManifold_double_succ_succ K hK)`。
- 结论与一般化端点通过 `glueSnd E E : E × E × ℝ → E` 对接：胞腔本身在无边 double 中，而像、边界环与
  `boundaryComplex 3 K` 的交仍在原 `K` 的环境中表述，因此不需将基本群数据运输到嵌入副本。
- I2 当前显式输入的输出已是 `SingularTwoCell (double 3 K).space`，并要求经 `glueSnd` 的胞腔像在 `K.space` 内、
  边界像及与 `boundaryComplex 3 K` 的交都精确为给定盘参数的边界像。S 交付 I2 后只需用其
  `glueEmbed₂` 像版本经 `glueSnd_glueEmbed₂` 消去这一显式输入。
- `SphereCase` 聚焦检查 exit=0、零 warning；更新后的 `.lake/scratch/AuditSphereCase.lean` 共 14 项，
  全部只含 `propext`、`Classical.choice`、`Quot.sound`。

## 24. 2026-09-16 E3-M2 追加：边界弧贴合的 frontier 表示

状态：done（NIGHT_PLAN §6.2 的“frontier = 两侧补弧之并”已闭合）。

- `CellGluing.lean` 新增 `exists_complementary_frontier_arcs_of_isPLBall_union`：对平面中两张 PL 2-球 `C,D`，若
  `C ∩ D` 是同时位于两侧 frontier 的 PL 1-球，则给出共同端点 `p,q` 及两条 PL 补弧 `A,B`，两侧都构成
  `Schoenflies.IsCutPair`，并有精确恒等式 `frontier (C ∪ D) = A ∪ B`。
- 证明先用闭盘的 `interior_union_left` 排除补弧非端点落入并盘内部，再用 PL 1-球删去有限端点后稠密及
  frontier 闭性补回两端。两补弧之并与并盘 frontier 都是 Jordan 圆，
  `PlanarJordan.eq_of_isJordanCurve_of_subset` 将包含关系升级为集合相等。
- `SingularTwoCell.exists_glue_of_isPLHomeomorphOn_boundary_arc` 的输出已加强：除原有两侧盘、参数化、公共缝及映射公式外，
  直接返回两条补弧的 `IsCutPair`、PL 1-球性和新胞腔的 frontier 等式。
- 因整合后共享目录缺少新导入链的中间产物，按规则仅用 `check-f.ps1` 顺次刷新
  `FrontierBoundary`、`BallFrontier`、`PlanarDiskUnion`，未运行 `lake build`。`CellGluing` 最终聚焦检查 exit=0、零 warning；
  `.lake/scratch/AuditE3M2.lean` 共 39 项，全部只含 `propext`、`Classical.choice`、`Quot.sound`。
- 下一步是把三盘链的首尾盘沿分支双层同胚实际贴合，并用本端点返回的补弧识别书页 186/187 的
  `L₁ = συ⁻¹` 或 `L₁ = συ`。

## 25. 2026-09-16 E3-M2 追加：触边分支的外侧盘手术

状态：partial（Case 3/4 的几何贴合及端点定向二分已闭合；正规性重建、严格复杂度下降与边界环字仍未闭合）。数学提交
`c05d49b83`。

- `BoundaryBranchCrosscut.lean` 的
  `exists_two_isCrosscuts_branchPreimage_of_boundaryBranch_with_coordinate` 同时保留两条源 crosscut 的端点、双层 PL 同胚
  `g : A → C` 与 `EqOn D (D ∘ g) A`，使三盘分解与贴合使用同一组规范见证。
- `CellGluing.lean` 的 `IsPLHomeomorphOn.maps_arc_endpoints` 证明 PL 弧同胚的端点只有保向或反向两种配对；
  `exists_complementary_frontier_arcs_of_isPLBall_union_between` 固定公共缝的给定端点，并把这组端点传入两侧 `IsCutPair`；
  `SingularTwoCell.exists_glue_of_isPLHomeomorphOn_boundary_arc` 进一步精确记录公共缝在两侧参数化下的像和四个端点值。
- `CutAndPaste.lean` 加强三盘链端点，使首尾盘的原边界迹都是 PL 1-球，并各自与奇异 crosscut 构成完整 `IsCutPair`。
  新端点 `NormalSingularCellData.exists_boundary_surgery_cell_of_boundaryBranch` 实际沿双层同胚贴合首尾盘，构造
  `G : SingularTwoCell M`，证明 `G '' G.domain ⊆ D '' D.domain`、
  `range G.boundary = D '' (U ∪ V)`、`range G.boundary ⊆ B` 及 `G '' G.domain ∩ BdM ⊆ B`，同时交付
  `(g p = r ∧ g q = s) ∨ (g p = s ∧ g q = r)`，正好区分书中的 Case 4 与 Case 3。
- `BoundaryBranchCrosscut`、`CellGluing`、`CutAndPaste` 依次聚焦检查 exit=0、零 warning；
  `.lake/scratch/AuditE3M2.lean` 共 43 项审计，全部只含 `propext`、`Classical.choice`、`Quot.sound`。
  本层没有首次复用新的 covering/Van Kampen 声明。
- 确切未闭合项有两层。第一，现有无基点环 API 尚未把任意 `SingularTwoCell.boundary` 参数化与上述补弧集合恒等式自动转换为
  `L₁ = συ⁻¹`、`L₂ = σφυτ` 或 `L₁ = συ`、`L₂ = στ⁻¹υφ⁻¹` 的道路等式；群字引理因此尚未接到新盘。
  第二，当前 I3 数据没有“沿一个完整触边分支重贴后仍有相容的正规三角剖分”生产者，故还不能为 `G` 重建
  `IsNormalSingularCell`，也不能证明所有新双点来自除 `c` 外的旧分支，从而严格降低复杂度。这两项均未被改成结论型假设；
  Case 1/2 的环带重定义、内盘替换与 I2 推离亦仍待完成。

## 26. 2026-09-16 E3-M2 追加：F 的 I3 原生接口对接

状态：done（触边分支构造已直接消费 `IsNormalSingularCell` 的正规交叉数据，不再带同形的显式 boundary-crossing 假设）。
数学提交 `67068fb77`。

- `NormalCell.lean` 将 `NormalSingularCellData.crossing` 校正为 I3 的
  `HasPLNormalDoubleCrossingAt`，并新增 `IsNormalSingularCell.exists_normalSingularCellData`，直接从 F 的
  `doublePointSet_triangulated` 见证构造本车道带显式奇点集三角剖分的数据。
- `DoublePointCover.lean` 新增 `doublePointSheetsAt_of_hasPLBoundaryDoubleCrossingAt_chart`；边界半空间双交叉与内部双交叉现在都给出
  `doublePointProjection` 的局部双层，从而原有覆盖空间链保持有效。
- `BoundaryCrossing.lean` 的 `NormalSingularCellData.exists_boundary_crossing_chart` 从 I3 的析取和
  `y ∈ BdM` 自动排除内部分支。`BoundaryBranchCrosscut.lean` 与 `CutAndPaste.lean` 因而删除了贯穿多个端点的显式
  `hboundaryCrossing` 参数；Case 3/4 的 crosscut、三盘链与外侧盘手术现在只条件于 I3 本身。
- 按依赖顺序重检 `NormalCell`、`BranchCarrier`、`DoublePointCover`、`BranchPreimage`、`BranchBoundary`、
  `BoundaryCrossing`、`BoundaryBranchCrosscut`、`CutAndPaste`，全部 exit=0、零 warning；
  `.lake/scratch/AuditE3M2.lean` 共 47 项，全部只含 `propext`、`Classical.choice`、`Quot.sound`。
- 本次对接没有消除 §25 末尾记录的两个剩余义务：需要从手术盘重建 I3 并严格降低复杂度，以及把边界补弧表示接到书中道路字。
  它只消除了此前 I3 已交付却仍重复显式要求边界交叉的接口偏差。

## 27. 2026-09-16 E3-M2 端到端复核：Lemma 2 的精确表示缺口

状态：blocked（不是 Lean 搜索缺口；现有公开数据不足以陈述并证明只条件于 I3 的 Lemma 2，未增加结论型假设，也未弱化端点）。

- 已闭合部分保持 §24–§26 的状态：两盘沿边界弧贴合后的 frontier 精确表示、触边分支的三盘链、Case 3/4 的外侧盘手术、
  端点保向/反向二分，以及 F 的原生 `IsNormalSingularCell` 接线均已通过检查。当前
  `NormalSingularCellData.exists_boundary_surgery_cell_of_boundaryBranch` 给出实际新胞腔 `G`、其像包含关系和边界载体等式，
  不是把书中手术结论作为假设。
- 第一处不可跳过的缺口在 L.1 的 `NormalSystem` 表示。它仅有
  `boundaryLoop_range : range boundaryLoop = loopComplex.space` 和
  `loop_space : loopComplex.space = singularMap '' frontier sourceComplex.space`，没有记录 `boundaryLoop` 与
  `singularMap` 在源盘 frontier 上的参数化相等或自由同伦等价。像集相同不决定环的共轭类：即使载体是一个圆，绕行一次与绕行两次
  也有相同像集；对 Case 3/4 的自交边界图，不同遍历更直接给出不同群字。因此不能从现有字段合法推出书页 186–187 的
  `L₁ = συ⁻¹`、`L₂ = σφυτ` 或 `L₁ = συ`、`L₂ = στ⁻¹υφ⁻¹`，也不能把 §25 已证的群论引理接到几何手术。
  所需的最小生产者是一个不改变结论的边界相容性接口，例如给出从 `loopCircle` 到源 frontier 的参数化并证明复合
  `singularMap` 后与 `boundaryLoop` 相等，或直接证明两者自由同伦；它必须由正规系统的构造产生，不能从载体相等推出。
- 第二处缺口是 I3 对割贴的稳定性。I3 给原胞腔的局部单射、二重纤维、奇点图三角剖分和每个双点的正规交叉，
  但没有生产者证明沿一个完整触边分支把两张外侧盘重贴后，`G` 仍满足 `IsNormalSingularCell`。具体还缺：
  新双点集等于旧双点集中删去所选分支后的相应部分、该集合的有限一维带边组合三角剖分、其余交叉图卡的搬运，
  以及由此得到 `boundaryBranchCount` 严格下降。只凭 `G '' G.domain ⊆ D '' D.domain` 不能推出这些结论。
- Case 1/2 另缺书页 184–185 使用的两个全局生产者：盘内多边形圆的 PL 环带/柱形图及沿该环带重定义后 I3 保持；
  最内圆所界内盘的替换、推离及替换后 I3 保持。当前树没有“PL 圆在 PL 盘内有环带正则邻域”的端点。
  I2 的 double 环境生产者也尚未进入整合分支，所以 Case 2 的推离仍只能等 S 的
  `exists_nonsingular_two_cell_of_boundary_disk`；本车道没有复制或直接合并 S 的文件。
- L.4 当前 `DoubleCoverReduction` 只记录覆盖投影、二重纤维和复杂度严格下降，没有记录提升正规系统的奇异盘经投影分解为原盘、
  边界环/正规子群的映射相容性，或把 `NonsingularCell T` 投影成满足 Lemma 2 假设的奇异胞腔。因此
  `exists_nonsingular_cell_of_stallings_induction` 中名为 `lemmaTwo` 的显式参数仍是“从提升系统回推”的完整接口，不能由尚未存在的
  `LoopTheorem/LemmaTwo.lean` 端点自动消去。要真正接线，`DoubleCoverReduction` 的生产者必须同时交付上述因子分解与边界相容数据。
- I5 仍未交付，故 C.5 按 NIGHT_PLAN §6.1 保持等待；没有用 Bennett `Coefficients.lean` 的链绕过缺失的 `χ_face`/球面识别生产者。
- 复核 `LoopTheorem/CutAndPaste.lean` 使用 `check-f.ps1 -Threads 1`，exit=0、零 warning；
  `.lake/scratch/AuditE3M2.lean` 共 47 项，`audit-f.ps1` exit=0，全部只含 `propext`、`Classical.choice`、`Quot.sound`。

## 28. 2026-09-16 L.1 补强：正规系统的边界参数化

状态：done。数学提交 `b3d9e8150`。

- `NormalSystem` 新增
  `boundaryParam : loopCircle ≃ₜ frontier sourceComplex.space` 与
  `boundaryLoop_eq : ∀ θ, (boundaryLoop θ : E) = simplicialMap sourceComplex vertexMap (boundaryParam θ)`；
  原结构字段 `boundaryLoop_range` 删除，并以完全同名的 `NormalSystem.boundaryLoop_range` 定理从上述两字段和 `loop_space` 推出，
  所有既有消费者的点记法与结论签名保持不变。
- 当前整合树没有 `NormalSystem` 的具体构造器，故本树没有需要补字段的生产者。后续生产者应以 §16 的 PL 圆分类构造
  `boundaryParam`，并以 `BoundaryGeneration.lean` 已有的自由边界环构造证明逐点 `boundaryLoop_eq`；不得再用像集相等替代参数化相容性。
- `SingularCell.lean` 及其 16 个传递下游按导入顺序逐个使用 `check-f.ps1 -Threads 1` 重编，全部 exit=0、零 warning。
  `.lake/scratch/AuditE3M2.lean` 增加两个结构投影与推论后共 50 项，最终 `audit-f.ps1` exit=0，
  全部只含 `propext`、`Classical.choice`、`Quot.sound`。
- 两次早期审计恰逢共享构建目录中的其它 Lean 进程依次重建 `BoundaryCrossing.olean` 与
  `BoundaryBranchCrosscut.olean`，分别报告瞬时缺失；等待共享进程退出后原样重跑即通过，未终止其它进程，也未运行 `lake build`。

## 29. 2026-09-16 E3-M2 追加：割贴后整条边界分支消去

状态：partial（纤维上界、新旧双点集包含及所选分支消去已闭合；局部单射、剩余分支三角剖分与 crossing 搬运待闭合）。数学提交 `9556ea4b2`。

- 已按 NIGHT_PLAN 规则合并并推送整合分支 `11b74c480`，本分支合并提交为 `c42577124`。整合后 S 的
  `exists_nonsingular_two_cell_of_boundary_disk` 及 `exists_nonsingular_two_cell_of_disk_in_double_boundary` 已以 §6.1 的 double 环境进入本树，
  Case 1/2 到内盘推离层时可直接消去旧的显式 I2 参数。
- `exists_three_cells_of_boundaryBranch` 保留两张分支原像片上 `branchCoordinate` 的 PL 同胚；
  `exists_boundary_surgery_cell_of_boundaryBranch` 据此增强为同时交付
  `∀ y, (G.domain ∩ G ⁻¹' {y}).encard ≤ 2`、
  `doublePointSet G G.domain ⊆ doublePointSet D D.domain` 与
  `Disjoint (doublePointSet G G.domain) (hD.singularSet.branchCarrier c)`。
- 证明将新源盘两片分别送回原盘首、尾片，得到新源点到旧源点的单射；于是新纤维注入旧纤维。
  对所选分支，两张坐标片把同像原像精确钉在贴缝上，而贴缝在新源盘中只有一份，因此新双点集与整条 `branchCarrier c` 不交。
- `SingularCell` 与 `CutAndPaste` 均用 `check-f.ps1 -Threads 1` 重编，exit=0、零 warning；
  `.lake/scratch/AuditE3M2.lean` 的 50 项用 `audit-f.ps1` 审计 exit=0，全部只含
  `propext`、`Classical.choice`、`Quot.sound`。首次审计发现整合检查留下的旧 `SingularCell.olean`，
  按规则窄重建 `SingularCell` 及当前模块后原样审计通过。
- 下一精确义务是从原胞腔的局部单射得到贴合胞腔的局部单射：贴缝处需用有限个其它分支的闭性取避开它们的目标邻域，
  再用两片的局部单射与贴缝唯一性排除交叉重合。随后需证明新双点集是旧一维带边组合流形的若干完整连通分支之并，
  以限制子复形重建 `doublePointSet_triangulated`，并在剩余分支上搬运 crossing。

## 30. 2026-09-16 E3-M2 追加：割贴胞腔的局部单射

状态：partial（局部单射已闭合；剩余完整分支、奇点图三角剖分与 crossing 搬运待闭合）。

- `NormalSingularCellData.exists_boundary_surgery_cell_of_boundaryBranch` 现在额外交付
  `∀ x ∈ G.domain, ∃ W ∈ 𝓝[G.domain] x, InjOn G W`。缝外在 `P \ Q` 或 `Q \ P` 内沿 PL 同胚搬运旧胞腔的局部单射；
  缝上先取所有非所选分支载体的有限并，利用每条分支紧致而得到闭集，并在目标中避开该闭集。
- 缝上若出现跨侧同像，首尾盘在旧源盘中不交，故给出旧胞腔的真实双点。避开所有其它分支迫使该双点落在所选分支；
  两个原像随即都落在被贴合的缝上，再由分支坐标片上的单射与首侧 PL 同胚推出源点相等。因此没有把局部单射作为新假设。
- `CutAndPaste` 用 `check-f.ps1 -Threads 1` 检查 exit=0、零 warning；刷新共享缓存中的 `SingularCell` 后再次检查仍 exit=0。
  `.lake/scratch/AuditE3M2.lean` 的 50 项用 `audit-f.ps1` 审计 exit=0，全部只含
  `propext`、`Classical.choice`、`Quot.sound`。
- 下一精确义务是证明 `doublePointSet G G.domain` 在每条旧 `branchCarrier` 中为开闭子集，从而是若干完整分支之并；
  再以这些分支的子复形重建 `doublePointSet_triangulated`，并把旧正规 crossing 图限制到未删除分支。

## 31. 2026-09-16 E3-M2 追加：割贴胞腔的正规性重建

状态：done（`NormalSingularCellData` 已为手术胞腔实际重建；Case 3/4 的边界环字与复杂度严格下降仍为 partial）。

- `CutAndPaste.lean` 的 `NormalSingularCellData.exists_boundary_surgery_cell_of_boundaryBranch` 现在额外交付
  `Nonempty (NormalSingularCellData G BdM B)`。局部单射、二重纤维、边界像约束及奇点图三角剖分均来自已证字段，
  没有把割贴稳定性改写为新假设。
- 对每个保留下来的双点，两张新源片都避开公共贴缝。首侧和尾侧分别限制到 `P ∩ Qᶜ` 与 `Q ∩ Pᶜ`，
  沿 `f₁`、`f₃` 得到到旧源盘的相对开 PL 同胚；旧图卡域与这两张目标片在原像点处互为相对邻域。
  原 `HasPLDoubleCrossingAt` 或 `HasPLBoundaryDoubleCrossingAt` 的两张片由此拉回，新片的像芽与旧片像芽一致。
- 新坐标映射只在图卡原像上使用。附近全部纤维由两片覆盖这一条先从紧致新源盘上 `G` 的精确两点纤维得到，
  再经图卡逆映射搬到欧氏坐标，未错误要求 `e ∘ G` 在整个新源盘上连续。
- `CutAndPaste` 聚焦检查 exit=0、零 warning；`.lake/scratch/audit-cut-and-paste-restriction.lean` 的 12 项及
  `.lake/scratch/AuditE3M2.lean` 的 50 项审计均 exit=0，全部只含 `propext`、`Classical.choice`、`Quot.sound`。
  本层没有首次复用新的 covering/Van Kampen 声明。
- 尚未闭合的是书页 186–187 的 Case 3/4 边界环道路等式及由
  `vertexCollisionPairs` 或实际分支计数推出的复杂度严格下降；Case 1/2 的环带模型与内盘替换也仍待实现。

## 32. 2026-09-16 E3-M2 追加：割贴拉回与单纯复杂度严格下降

状态：partial（跨复形的碰撞对基数比较及手术拉回条件下的严格下降已闭合；适配三角剖分、边界环道路等式与第二张割贴胞腔待闭合）。

- `SingularCell.lean` 新增跨两个有限源复形的比较层：若顶点映射 `r` 单射、把新顶点送到旧顶点且满足
  `f (r v) = g v`，则新 `vertexCollisionPairs` 经 `Finset.image r` 注入旧碰撞对；若至少一个旧碰撞对不在该像中，
  `simplicialComplexity L g < simplicialComplexity K f`。具体的
  `simplicialComplexity_lt_of_vertex_injection_of_missing_collision` 只需给出一对旧碰撞顶点，其中一个不在新顶点像中。
- `NormalSingularCellData.exists_boundary_surgery_cell_of_boundaryBranch` 现在显式交付手术胞腔到原胞腔的
  `pullback`，以及 `MapsTo pullback G.domain D.domain`、`InjOn pullback G.domain`、
  `EqOn (D ∘ pullback) G G.domain` 和 `Disjoint (pullback '' G.domain) C`。最后一项说明第二张分支原像片
  `C` 被整个新源盘的拉回像遗漏，不只是新双点集与分支载体不交。
- `simplicialComplexity_lt_of_surgery_pullback` 已把上述拉回数据接到跨复形比较层：一旦给出适配的原/新有限源三角剖分、
  拉回对顶点的相容性，以及位于 `C` 上的一对旧碰撞顶点，就得到严格复杂度下降。
- 本层没有宣称 Case 3/4 或 Lemma 2 已完成。当前仍缺从 `NormalSystem`/I3 构造上述适配源三角剖分，
  以及把 `C` 上的同像原像选成旧复形顶点；还缺 `L₁` 的边界参数道路等式和由三片交叉贴合产生第二张胞腔 `L₂`。
  现有群论引理已经匹配书页 186–187 的 Case 3/4 字，但在这些几何生产者完成前不能接成 Lemma 2。
- `SingularCell` 与 `CutAndPaste` 的聚焦检查均 exit=0、零 warning；`fresh.py` 报告相对整合提交
  `4401dd9d1` 的 2 个改动 Lean 模块均为 fresh，forbidden=0、stale=0、missing=0。
  `.lake/scratch/AuditE3M2.lean` 的 54 项与 `.lake/scratch/audit-cut-and-paste-restriction.lean` 的 12 项审计均 exit=0，
  全部只含 `propext`、`Classical.choice`、`Quot.sound`。首次 fresh 尝试检测到其它工作树的 Lean 进程后按规则以 17 退出；
  等该进程自然结束后才继续，没有终止其它进程。

## 33. 2026-09-16 E3-M2 追加：Case 3/4 边界道路字与缝端碰撞

状态：partial（书页 186–187 的两种道路重接已按 Mathlib 基本群乘法约定闭合；外侧手术胞腔的缝端碰撞自动给出严格复杂度下降，几何道路生产者与第二张手术胞腔仍待闭合）。

- `SingularCell.lean` 的 `loopRepresentativeAlong_pathToCircle` 把道路闭环 `pathToCircle p` 沿任意基点连接道路搬到 `fundamentalGroupChangeBasepoint q ⟦p⟧`。`CutAndPaste.lean` 的 `loopRepresentativeAlong_mem_iff_loopClassMeets_basedCircle` 及否定版把该指定代表元与自由环共轭类是否遇到正规子群精确对应。
- Mathlib 的基本群乘法满足 `p * q = q.trans p`，所以书中的从左到右道路字在基本群中必须反序。`not_loopClassMeets_or_not_loopClassMeets_of_endpoint_reversing_reconnection` 对
  `L = στυφ` 给出 `L₁ = συ⁻¹` 或 `L₂ = σφυτ` 至少一个仍避开正规子群；`not_loopClassMeets_or_not_loopClassMeets_of_endpoint_preserving_reconnection` 对同一母道路给出 `L₁ = συ` 或 `L₂ = στ⁻¹υφ⁻¹` 至少一个仍避开正规子群。证明插入任意连接道路 `c`，在基本群胚中消去 `c⁻¹c`，再用 `not_mem_or_not_mem_of_four_path_reverse_order` 与 `not_mem_or_not_mem_of_four_path_preserving_order` 的正规共轭闭性；没有把道路字等式改写为假设。
- `NormalSingularCellData.exists_boundary_surgery_cell_of_boundaryBranch` 现在还交付四个缝端分别落在 `A,C` 及 `EqOn D (D ∘ g) A`。`simplicialComplexity_lt_of_surgery_pullback_of_seam` 由端点定向二分自动选择被新拉回遗漏的旧碰撞对 `(p,r)` 或 `(p,s)`；调用者仍需提供适配的原/新有限源三角剖分、顶点搬运和三个缝端是旧顶点。
- `SingularCell` 与 `CutAndPaste` 聚焦检查均 exit=0、零 warning。`fresh.py` 对相对整合提交 `4401dd9d1` 的两个改动 Lean 模块报告 fresh=2、forbidden=0、stale=0、missing=0。更新后的 `.lake/scratch/AuditE3M2.lean` 共 62 项，审计 exit=0，全部只含 `propext`、`Classical.choice`、`Quot.sound`。检查和审计前均先确认全局没有 `lean.exe`；检测到其它工作树进程时以 17 退出并等待，没有终止进程。
- 本层没有宣称 Case 3/4 或 Lemma 2 已完成。仍缺从 `NormalSystem.boundaryParam`、I3 的两条实际分支原像和贴合后的 frontier 表示构造上述 `σ,τ,υ,φ`，并证明手术胞腔的边界参数恰为相应 `pathToCircle`；还缺构造第二张交叉贴合胞腔 `L₂`，以及从适配源三角剖分把缝端选为顶点。Case 1/2 的环带模型、内盘替换与 I2 推离也仍未闭合。

## 34. 2026-09-16 E3-M2 追加：Case 2 的全局最内奇异圆盘

状态：partial（全体奇异分支中的最内圆与内盘隔离已闭合；内盘上的单射坐标、I2 替换及替换后正规性仍待闭合）。数学提交
`faa031702`。

- `BranchPreimage.lean` 证明所有分支原像两两不交，其并集恰为
  `doublePointPreimage D D.domain`；非触边分支的原像位于源盘内部，并可有限分解为一或两个两两不交的 PL 圆。
- 对所有非触边分支的全部圆分量同时应用 `exists_innermost_isPLBall`，得到 `J = frontier Q`，其中
  `Q ⊆ interior D.domain`，且所有非触边分支原像与 `Q` 的交恰为 `J`。被选分支的原像同时保留书中 Case 1/2 的精确二分：
  它等于单个 `J`，或等于 `J ∪ T`，其中 `T` 是与 `J` 不交的另一个 PL 圆。
- `BoundaryBranchCrosscut.lean` 证明若源盘横切弧避开 `frontier Q`，则整条横切弧避开 `Q`：横切弧连通，端点在外盘边界上，而
  `Q` 完全位于外盘内部。每个触边分支的原像是两条这样的横切弧，且不同分支原像两两不交；故最终端点
  `exists_innermost_isPLBall_doublePointPreimage_decomposition_of_exists_not_boundaryBranch`
  将上述交式加强为
  `doublePointPreimage D D.domain ∩ Q = J`，没有把“最内”作为假设。
- `BranchPreimage` 与 `BoundaryBranchCrosscut` 聚焦检查均 exit=0、零 warning；更新后的
  `.lake/scratch/AuditE3M2.lean` 共 72 项，`audit-f.ps1` exit=0，全部只含
  `propext`、`Classical.choice`、`Quot.sound`。本层没有首次复用新的 covering/Van Kampen 声明。
- 下一精确义务是为非触边分支的一圆/两圆分解保留 `branchCoordinate` 在每个圆分量上的 PL 同胚，从而由
  `doublePointPreimage D D.domain ∩ Q = J` 推出 `D` 在 `Q` 内除边界配对外单射，并构造 Case 2 的内盘替换后调用已交付的 I2。
  Case 1 仍缺盘内圆的 PL 环带及 Figure 25.2 柱形图显式模型；Lemma 2 端点尚未宣称完成。

## 35. 2026-09-16 E3-M2 追加：Case 2 的非奇异内盘

状态：partial（两圆情形的内盘限制已构造成实际非奇异 2-胞腔；I2 替换、替换后正规性与复杂度下降仍待闭合）。数学提交
`174006132`。

- `BranchPreimage.lean` 将非触边分支的两圆分解加强为带坐标版本：两圆上的
  `branchCoordinate` 都是到同一 `branchComplex.space` 的 PL 同胚。该结论直接来自二重覆盖的两个连通分支及已有的分支原像
  PL 三角剖分，不把双层参数化另作假设。
- 若 `doublePointPreimage D D.domain ∩ Q = J` 且 `branchCoordinate|J` 为 PL 同胚，则 `D|Q` 单射：两点若在 `Q`
  中同像且不等，二者都属于全局双点原像，故都在 `J`；再由 `branchPieceIn` 与 `branchCoordinate|J` 的单射性得到二者相等。
  `restrict_isNonsingular_of_doublePointPreimage_inter_eq_of_branchCoordinate` 因而构造实际限制胞腔并证明其边界像是 `D '' J`。
- 端点 `exists_innermost_isPLBall_doublePointPreimage_with_nonsingular_case_two` 保留 Case 1/2 二分；在 Case 2 中交付
  `A : SingularTwoCell M`，满足 `A.IsNonsingular`、`A '' A.domain = D '' Q` 与
  `Set.range A.boundary = D '' J`，并同时保留另一圆 `T` 及两张坐标 PL 同胚。
- `BranchPreimage` 与 `BoundaryBranchCrosscut` 聚焦检查均 exit=0、零 warning；
  `.lake/scratch/AuditE3M2.lean` 共 78 项，`audit-f.ps1` exit=0，全部只含
  `propext`、`Classical.choice`、`Quot.sound`。本层没有首次复用新的 covering/Van Kampen 声明。
- 下一精确义务是把上述 `A` 在 `X := (double 3 K).space` 的专门环境中转成 I2 所需的边界盘参数化，调用
  `exists_nonsingular_two_cell_of_disk_in_double_boundary` 构造推离替换盘，并证明替换后的奇点图删去所选闭分支、正规 crossing 保持且
  `vertexCollisionPairs` 严格减少。当前一般 `NormalSingularCellData` 不携带 `K`、double 的嵌入 `ι` 或盘像位于相应
  `boundaryComplex` 的等式，所以该接线必须在 Lemma 2 的 double 专门端点中完成，不能在本一般引理中伪造。

## 36. 2026-09-16 E3-M2 追加：Case 2 的源盘替换参数化

状态：partial（两张源盘之间的边界相容 PL 同胚已闭合；double 环境中的 I2 推离、分片贴回、正规性重建与复杂度下降仍待闭合）。数学提交
`b25555a31`。

- `BranchPreimage.lean` 在两圆情形中为另一圆 `T` 构造 PL 盘 `R ⊆ D.domain`，并由两张
  `branchCoordinate` 坐标先得到 `T → J` 的边界 PL 同胚，再用盘边界延拓得到
  `G : R → Q` 的 PL 同胚。其边界满足逐点等式 `EqOn D (D ∘ G) (frontier R)`，不是仅有边界像集相等。
- `BoundaryBranchCrosscut.lean` 的端点
  `exists_innermost_isPLBall_doublePointPreimage_with_case_two_replacement` 同时交付全局最内关系
  `doublePointPreimage D D.domain ∩ Q = J`、上述 `R,G`，以及非奇异内盘胞腔 `A = D.restrict Q`，其中
  `A '' A.domain = D '' Q` 且 `Set.range A.boundary = D '' J`。这给出了 Moise Case 2 在调用 I2 前所需的两张源盘和精确边界配对。
- `BranchPreimage` 与 `BoundaryBranchCrosscut` 聚焦检查均 exit=0、零 warning；更新后的
  `.lake/scratch/AuditE3M2.lean` 共 81 项，`audit-f.ps1` exit=0，全部只含
  `propext`、`Classical.choice`、`Quot.sound`。本层没有首次复用新的 covering/Van Kampen 声明。
- 下一精确义务仍必须在 `X := (double 3 K).space` 的 Lemma 2 专门环境中完成：先把 `D '' Q` 识别为 I2 所需的
  `boundaryComplex 3 K` 内参数化盘并取得被推离的非奇异盘，再沿 `G` 在 `R` 上分片替换 `D`；随后证明分片映射 PL、所选闭分支整条消失、
  其余 crossing 保持且 `vertexCollisionPairs` 严格减少。一般 `NormalSingularCellData` 没有这些 double/边界定位数据，故本层没有弱化或伪造该接线。
- Case 1 仍缺 `J` 的 PL 环带邻域、书页 185 Figure 25.2 的显式柱形图模型及替换后复杂度证明；Lemma 2 端点尚未宣称完成。

## 37. 2026-09-16 E3-M2 追加：I2 的逐点边界参数桥接

状态：partial（double 环境中的 I2 已补成可逐点贴回指定源盘的形式；Case 2 的分片替换、正规性重建与复杂度下降仍待闭合）。数学提交
`095dabd4d`。

- 新文件 `LoopTheorem/LemmaTwo.lean` 的
  `exists_nonsingular_two_cell_of_disk_in_double_boundary_eqOn` 接受任意 PL 2-盘 `R` 及到
  `ι '' (boundaryComplex 3 K).space` 内边界盘的 PL 同胚 `r : R → D`。它构造
  `A : SingularTwoCell (double 3 K).space`，满足 `A.domain = R`、`A.IsNonsingular`、像落在 `ι '' K.space`，并有逐点接缝等式
  `EqOn (fun x => (A x : E × E × ℝ)) r (frontier R)`；同时保留边界像和与嵌入组合边界的交集都等于 `r '' frontier R`。
- 证明先沿第二份拷贝的 PL 嵌入 `ι` 把输入盘拉回 `K`，调用原生
  `exists_isPLHomeomorphOn_push_boundary_disk`，再把两条同像边界圆之间的 PL 同胚用
  `exists_isPLHomeomorphOn_of_stdSimplexBoundary` 延拓到整盘。最后用 `combinatorialPLPieceIn` 在指定源盘 `R` 上直接实现胞腔，
  因而没有从“边界像集相等”非法推出参数化相等，也没有修改 S 车道的 I2 文件。
- `LemmaTwo` 聚焦检查 exit=0、零 warning；`.lake/scratch/AuditE3M2.lean` 共 82 项，`audit-f.ps1` exit=0，
  全部只含 `propext`、`Classical.choice`、`Quot.sound`。本层没有首次复用新的 covering/Van Kampen 声明。
- 下一精确义务是在 `NormalSystem` 的专门化中把 `simplicialMap sourceComplex vertexMap` 嵌入第二份拷贝，证明 Case 2 内盘限制的环境坐标映射满足本桥接的
  `IsPLHomeomorphOn` 与组合边界包含条件；随后在另一源盘 `R` 上以新胞腔替换原映射，并实际证明 PL 性、所选闭分支消失、其余 crossing 保持及
  `vertexCollisionPairs` 严格减少。一般 `NormalSingularCellData` 仍不携带这组 double/嵌入数据，故没有在一般层伪造该结论。
- Case 1 的环带与 Figure 25.2 柱形图模型仍未闭合；Lemma 2 端点尚未宣称完成。

## 38. 2026-09-16 E3-M2 追加：正规系统的 double 环境实现

状态：partial（正规系统已实现为 `double 3 K` 中的实际奇异 2-胞腔；Case 2 仍缺内盘的单侧局部 3-流形邻域）。数学提交
`dec8e5da0`。

- `LemmaTwo.lean` 的 `NormalSystem.exists_singular_two_cell_in_double` 令
  `K := S.manifoldComplex`，通过第二份拷贝嵌入
  `ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)` 构造实际
  `D : SingularTwoCell (double 3 K).space`。它保留源盘、整个像、边界环像、与 double 组合边界的交，
  并给出逐点边界参数等式与 `D.IsNonsingular ↔ S.IsNonsingular`。因此后续 Case 1/2 可以在 H 车道规定的
  `double 3 K` 环境中直接使用，不再依赖同形的假定结构。
- `LemmaTwo` 聚焦检查 exit=0、零 warning；`.lake/scratch/AuditE3M2.lean` 共 83 项，
  `audit-f.ps1` exit=0，全部只含 `propext`、`Classical.choice`、`Quot.sound`。
  全局无 `lean.exe` 后运行 `fresh.py`，相对整合提交 `4401dd9d1` 的 5 个改动 Lean 模块均为 fresh，
  forbidden=0、stale=0、missing=0。检测到其它工作树的 Lean 进程时已立即暂停，未终止或并发编译。
- 现有 I2 的前提是待推盘已位于一个有边界 3-流形复形的 `boundaryComplex`。但
  `S.imageComplex.space ∩ S.boundaryComplex.space = S.loopComplex.space`，所以 Moise Case 2 的最内盘像位于正则邻域内部，
  只有它的边界圆落在外边界上；它不是 I2 可直接接受的边界盘。
  下一精确生产者是：为这个内嵌 PL 2-盘构造单侧局部 PL 3-流形（或 PL 3-球）邻域，使该盘成为其组合边界子盘，
  再运输到相应 double 中调用 I2。现有 `DiskDerivedNeighborhood`、`DiskCollar`、
  `BoundaryDiskNeighborhood`只处理已在边界的盘；`BicollarManifold`与 `TwoSidedNeighborhood` 只处理无边界闭曲面，
  均不能填补这一步。该局部乘积/半邻域定理尚未在本树中找到，故本层没有将其改写为假设，也没有弱化 Lemma 2。

## 39. 2026-09-16 C.5：非球面边界分支的连通二重覆盖

状态：done。数学提交 `65bd07eb6`、`cb2153a6c`。

- 已合并整合分支 `bbd488861`的 I5。`BoundaryHomology.lean` 与 `HandleCount.lean` 的 I5 支撑层推广到任意域
  `k`，得到 `bettiNumber_one_pos_of_boundary_component_not_sphere`；原有 ℚ 系数端点
  `bettiOne_pos_of_boundary_component_not_sphere` 保持原签名并成为其推论。
- 新模块 `HomologyCocycle.lean` 直接在 `ZMod 2` normalized chain complex 上工作：由正的一阶 Betti 数取非零同调类，
  选取在该类上非零的对偶函子，延拓到一链，并以边基向量上的值构造
  `SimplicialBoolCocycle.exists_not_isCoboundary_of_bettiNumber_one_pos`。三角形边界公式证明 cocycle 条件；若是 coboundary，
  顶点函子将使该对偶函子在所有一循环上为零，与选定的非零类矛盾。
- `DoubleCoverExistence.lean` 的
  `exists_connected_double_cover_complex_of_isOrientable_of_boundary_component_not_sphere`
  无任何 I5/上循环存在的显式假设：对连通、可定向的带边组合 3-流形复形及一个非 PL 2-球面的边界分支，
  产生实际非上边界上循环、连通二重覆盖、有限提升复形及带边组合 3-流形性。该新端点的环境类型为
  `E₀ : Type`，精确对齐当前 I5 支撑链的宇宙层级；原有 `Type*` 覆盖 API 未被改窄。
- `HomologyCocycle` 与 `DoubleCoverExistence` 聚焦检查均 exit=0、零 warning。
  `.lake/scratch/AuditC5.lean` 审计 17 项，包括新端点及首次复用的
  `moduleHomologyClass_surjective`、`moduleHomologyClass_eq_zero_iff`、
  `Module.Projective.exists_dual_ne_zero`、`Subspace.dualLift`、`realizationHomologyIso`、
  `isoOfQuasiIsoAt`、`geometricRealizationHomeomorphism`、`orderedNormalizedChainEquiv` 与边界坐标公式，
  全部只含 `propext`、`Classical.choice`、`Quot.sound`。未 import、未传递经过
  `Topology/Homology/HurewiczLowDegrees.lean`。`fresh.py` 在全局无 `lean.exe` 时报 8 个改动 Lean 模块全部 fresh，
  forbidden=0、stale=0、missing=0。
- C.5 本身已不再条件于 I5。L.4 中的 `orientableNonsphericalBoundaryDoubleCover` 仍是更强的
  `NormalSystem.DoubleCoverReduction` 生产者：它还要求提升整个正规系统、保持边界环/正规子群数据并证明复杂度严格下降，
  不能仅由覆盖复形的存在性消去；该 L.4 生产者缺口保持精确记录。

## 40. 2026-09-16 E3-M2 追加：Case 3/4 的适配三角剖分与碰撞顶点

状态：partial（适配三角剖分、C 片缝端碰撞及外侧手术胞腔的严格复杂度下降已闭合；L₁ 边界参数道路等式与第二张胞腔 L₂ 待闭合）。数学提交 `b1f2dc7c2`。

- `exists_isSubdivision_mapsTo_vertices` 同时细分旧源盘复形，使新源盘有限顶点经手术拉回全部成为旧顶点；随后三次单点细分把缝端 `p,r,s` 变成旧顶点。此构造只用有限点集与源盘的多面体性，不额外假设拉回连续或本身为 PL 映射。
- `exists_simplicialComplexity_lt_of_surgery_pullback_of_seam` 由实际手术拉回、端点定向二分及 `C` 片被拉回像遗漏，自动选择 `(p,r)` 或 `(p,s)` 作为不在新碰撞对像中的旧碰撞对，并产生有限复形 `K,L`，满足 `K.space = D.domain`、`L.space = G.domain` 及 `simplicialComplexity L G < simplicialComplexity K D`。
- `NormalSingularCellData.exists_boundary_surgery_cell_with_simplicialComplexity_lt` 把上述比较接回实际正规手术胞腔；同一个 `G` 同时具有正规性、精确边界载体 `Set.range G.boundary = D '' (U ∪ V)`、像包含关系及严格复杂度下降，没有把所需适配数据改写为调用者假设。
- `CutAndPaste` 聚焦检查 exit=0、零 warning；`.lake/scratch/AuditE3M2.lean` 共 86 项，`audit-f.ps1` exit=0，三个新端点均只含 `propext`、`Classical.choice`、`Quot.sound`。本层没有首次复用新的 covering/Van Kampen 声明。
- 下一精确义务是从 `NormalSystem.boundaryParam` 与三片割贴的 frontier 表示构造 `σ,τ,υ,φ`，证明外侧手术胞腔边界参数对应书页 186–187 的 `L₁` 道路字；随后构造另一种重接得到第二张正规胞腔 `L₂`。Case 1/2 只在这两项完成后继续。

## 41. 2026-09-16 E3-M2 追加：Case 3/4 的 L₁ 边界参数

状态：partial（外侧手术胞腔 L₁ 已有逐点边界道路等式；第二张交叉贴合胞腔 L₂ 待构造）。数学提交
`6b372c448`。

- `CellGluing.lean` 的 `exists_boundaryParam_paths_of_isCutPair_union` 对两条端点相同、仅交于端点且并为盘边界的弧，构造边界同胚
  `e : loopCircle ≃ₜ frontier P` 及道路 `ρ,κ`；结论不仅给出两段的像集，还给出逐点等式
  `e θ = pathToCircle (ρ.trans κ) θ`。证明用两弧参数的拼接为单环，再由紧致域到 Hausdorff 值域的连续双射构造同胚。
- `exists_boundary_surgery_cell_of_boundaryBranch` 现在为实际手术胞腔 `G` 附带 `σ,ω` 与 `e`，其中
  `Set.range σ = D '' U`、`Set.range ω = D '' V`，并且
  `G (e θ) = pathToCircle (σ.trans ω) θ`。这是沿贴合后 frontier 的逐点参数相容，不是从边界像集相等倒推道路等式。
- `CellGluing` 与 `CutAndPaste` 聚焦检查均 exit=0、零 warning；
  `.lake/scratch/AuditE3M2.lean` 共 87 项，`audit-f.ps1` exit=0，全部仅含
  `propext`、`Classical.choice`、`Quot.sound`（部分纯群等式只含 `propext`）。本层没有首次复用新的 covering/Van Kampen 声明。
- 下一精确义务是把三个源片按交叉方式贴合为第二张胞腔 `L₂`，保留边界参数、正规性和对应的严格复杂度下降；随后才进入 Case 1/2。

## 42. 2026-09-16 E3-M2 追加：Case 3/4 的第二张交叉贴合胞腔 L₂

状态：partial（L₂ 的三片交叉重贴、像因子分解与逐点边界参数已闭合；正规性、严格复杂度下降及原四段边界字识别待闭合）。数学提交
`20482bfd3`。

- `CellGluing.lean` 的
  `SingularTwoCell.exists_cross_glue_of_isPLHomeomorphOn_disjoint_boundary_arcs` 先把首片的 `A` 边与中片的 `C` 边沿双层同胚贴合，
  再把中片剩余的 `A` 边与尾片的 `C` 边贴合，实际构造第二张 `SingularTwoCell`。端点保留两级盘参数化、两条公共缝、
  最终补边弧及端点值，并构造 `e : loopCircle ≃ₜ frontier G.domain` 与道路 `σ,ω`，逐点证明
  `G (e θ) = pathToCircle (σ.trans ω) θ`。
- `CutAndPaste.lean` 的
  `NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch` 将该构造接到实际触边分支的三盘链。
  结论显式记录原三片覆盖与相邻交、两次交叉贴合的全部 PL 同胚及逐片映射公式、端点保向/反向二分，并证明
  `G '' G.domain ⊆ D '' D.domain`；因此该端点不是只给出一张与分支数据无关的存在盘。
- `CellGluing` 与 `CutAndPaste` 聚焦检查均 exit=0、零 warning；`.lake/scratch/AuditE3M2.lean` 共 89 项，
  `audit-f.ps1` exit=0，两个新端点均只含 `propext`、`Classical.choice`、`Quot.sound`。
  全局无 `lean.exe` 后运行 `fresh.py`，相对基线的两个改动 Lean 模块均为 fresh，forbidden=0、stale=0、missing=0。
- 尚不能把该 L₂ 称为复杂度下降的正规胞腔：外侧 L₁ 的证明使用一张单射拉回并遗漏整条 `C` 片；L₂ 有两条不同新缝都映到所选目标分支，
  不能直接复用该单射拉回。下一步必须从两级逐片参数化重建局部单射、二重纤维、奇点图与 crossing，继而在适配三角剖分上证明碰撞顶点数严格下降；
  还须把当前两段边界道路进一步识别成书页 186–187 的原四段字 `σφυτ` 或 `στ⁻¹υφ⁻¹`。这些步骤未被改写为假设，Lemma 2 仍未宣称完成；
  在此之前不进入 Case 1/2。

## 43. 2026-09-16 E3-M2 追加：顺序交叉贴合的分支保留障碍

状态：partial（已严格排除现有顺序交叉贴合作为 Moise 的降复杂度 L₂；真正的整支切开并分离构造仍缺）。数学提交
`caddcb29c`。

- `CellGluing.lean` 将第二次贴合前的拉回弧 `A'` 与第一次贴合缝 `P ∩ Q` 的不交性加入公开结论；这是区分最终源盘中两条新缝的必要数据。
- 专门端点改名为 `NormalSingularCellData.exists_cross_reglued_cell_of_boundaryBranch`，并实际证明
  `hD.singularSet.branchCarrier c ⊆ doublePointSet G G.domain`。证明逐点从第一次缝与第二次缝各取一个不同原像，利用上述不交性证明两原像不同，再由两级逐片映射公式证明它们在 `G` 下同像。
- 因而该顺序重贴虽然产生合法 PL 奇异胞腔、保留像因子分解和逐点边界参数，却仍完整保留被选奇异分支；它不能满足 Case 3/4 所需的严格复杂度下降，也不能作为书中 L₂。缺少的精确生产者是沿整条紧致触边双点分支把两张折叠片真正切开并分离的全局 PL 构造，同时保留书页 186–187 的四段边界字、局部单射、纤维至多二、其余 crossing 与适配三角剖分，并使被选分支从新双点集中消失。
- `CellGluing`、`CutAndPaste` 聚焦检查均 exit=0、零 warning；`.lake/scratch/AuditE3M2.lean` 仍审计 89 项，全部只含 `propext`、`Classical.choice`、`Quot.sound`。全局无 `lean.exe` 后 `fresh.py` 报两个改动 Lean 模块均 fresh，forbidden=0、stale=0、missing=0。
- 现有 `locallyInjective_restrict`、`fiber_le_two_restrict` 与 crossing 搬运只能验证给定限制或拉回，不能产生上述整支分离。按既定顺序，L₂ 未闭合前没有进入 Case 1/2。

## 44. 2026-09-16 E3-M2：紧致分支图卡有限化与相容推开的精确缺口

状态：blocked（`NIGHT_PLAN.md` §11.2 的有限覆盖层已闭合；相邻 crossing 图卡上的同向推移无法由现有接口串接，转交 F）。

- `BranchPreimage.lean` 新增
  `NormalSingularCellData.exists_finite_crossing_chart_cover`。对任意正规奇异胞腔和任意奇异分支，它选择每个分支点的
  `OpenPartialHomeomorph`，保留该点的 `HasPLNormalDoubleCrossingAt`，并由
  `branchCarrier_isCompact` 产生一个有限点集，其图卡源覆盖整条 `branchCarrier`。这一步同时覆盖普通内部 crossing 与
  `HasPLBoundaryDoubleCrossingAt` 的端点半空间分支，不把有限覆盖作为假设。
- 聚焦检查 `BranchPreimage` exit=0、零 warning；`.lake/scratch/AuditBranchSeparation.lean` 的新端点审计 exit=0，
  只依赖 `propext`、`Classical.choice`、`Quot.sound`。
- 精确缺口不是有限子覆盖，也不是源盘的两条原像弧或三盘分解。现有
  `HasPLCrossingAt`/`HasPLBoundaryCrossingAt` 在每一点分别存在性地给出图卡、两张平面片和横截模型；在两个图卡的重叠上，
  数据没有指定哪张平面对应固定的源片 `A`，也没有指定横向商线的正向。§16/§17 的 PL 圆/区间分类只给分支本身的次序，
  不给这条横向商线沿分支的相容平凡化。因此无法证明相邻局部推移在重叠上同向，亦无法用线性插值得到单射的全局 PL 自映射。
- F 的三个指定接口都位于这项义务之后：
  `exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective` 只把一个已经给定的全局 `IsPL` 单射 `h` 粘到一张源片；
  `exists_isPLBall_patches_at_doublePoint_within` 只在单个双点选局部源片；
  `exists_isPLBall_postcomp_neighborhood_at_doublePoint_in_manifold` 同样消费已经构造好的、支撑外恒等的 `h`。
  逐点迭代这些定理既不给重叠相等，也不给同向选择；`exists_small_homeomorph_generalPosition` 保持横截交线而不删除它。
  `BicollarManifold.lean` 只接受无边界组合 2-流形，不能用于两条源 crosscut 周围的带边条带；
  `PlanarArcNeighborhood.lean` 只在源平面给弧的盘邻域，不产生目标三流形中的横向坐标。
- 转交 F 的精确生产义务可写成 `exists_supported_separation_along_compact_crossing_arc`：输入紧致 PL 1-球
  `S = branchCarrier c`、两张与 `S` 相交且沿 `S` 满足普通/边界 crossing 的嵌入 PL 条带、`W ∈ 𝓝ˢ S`；输出
  `U`、两张缩小条带 `P,Q` 及全局 `h : M → M`，满足 `IsOpen U`、`S ⊆ U`、`closure U ⊆ W`、
  `IsPL 3 3 h`、`Function.Injective h`、`EqOn h id Uᶜ`、边界端点处 `h (U ∩ BdM) ⊆ BdM`，并使
  `Disjoint (h '' (D '' P)) (D '' Q)`。同时必须给 `P` 与源余片的接缝像避开 `closure U`、余片在 `D ⁻¹' U` 上单射，
  以及分片映射 `g := P.piecewise (h ∘ D) D` 的精确等式
  `doublePointSet g D.domain = doublePointSet D D.domain \ S`。最后一条需包含“不产生邻近的新交线”，不能只给旧分支点离开新奇点集。
  有了这些数据，现有 Pasting/SingularPasting 可直接给 PL 性、局部单射、纤维至多二和支撑外纤维不变；E3 再用已有
  `g`、三盘分解与 `IsGlueIso` 完成 Figure 25.3/25.5 的源盘重连及 Figure 25.4/25.6 的两张胞腔。
- 在该生产者交付前，不能诚实声明 `exists_separated_along_branch`，也不能继续 Case 3/4 的实际 `L₂` 或复杂度下降接线；
  Case 1/2 按用户指定顺序保持未开始。本次没有把缺口改写成显式结论型假设。

## 45. 2026-09-17 E3-M2：横向侧选择的形式核心（弧可行、圆的障碍确切）

- §44 列出的两项缺失里，第一项（哪张平面对应固定源片 `A`）经 F 车道 §19.105 的分析取消：两张片只沿 `S` 相交，
  所以"含 `D(A)` 的那张平面"在每个 crossing 图卡里唯一确定，可直接作为定义，不需要沿分支作相容选择。
- 第二项（横向商线的正向）的形式核心现在在 `BranchSignChain.lean` 里：
  - `exists_sideChoice_of_chain (τ : Fin n → ZMod 2) : ∃ ε : Fin (n+1) → ZMod 2,
    ∀ i, ε i.succ = ε i.castSucc + τ i`。把 `τ i` 读作第 `i` 与第 `i+1` 张图卡在重叠上是否交换两侧，
    `ε` 就是沿链的相容正向选择。链（弧）情形因此**无条件可解**，构造是逐段部分和 `sidePartialSum`。
  - `sum_sideJump_eq_zero_of_cycle`：若在循环指标上存在这样的 `ε`，则 `∑ i, τ i = 0`；
    `not_exists_sideChoice_of_cycle` 是其逆否。这就是圆分支的确切障碍：总单值性非零时不存在相容正向，
    与 F §19.105 的"`Q` 沿 `S` 必须双侧"是同一件事的组合形式。
- 对 §25.1 实际需要的 Case 3/4，`A_j` 是触边分支即弧，故上面的链版本适用。
- `BranchSignChain` 聚焦检查 exit=0（5.7 秒）、零 warning；`.lake/scratch/AuditE3SignChain.lean` 三项仅
  `propext`、`Classical.choice`、`Quot.sound`（第一条甚至不用选择公理）。
- 仍未闭合、按 §44 归 F：把 `exists_finite_crossing_chart_cover` 的有限图卡集**按分支排成链**
  （需要 §16/§17 的 PL 区间分类给出沿弧的次序，以及重叠连通），再把每张图卡里的线性推移用 `ε` 定向、
  在重叠上线性插值成全局单射 PL 自映射。`exists_separated_along_branch` 仍未声明；Case 1/2 未开始。

## 46. 2026-09-18 E3-M2：单张乘积图卡上的长滑移分离（chart 层）

状态：done。新模块 `BranchSlideConjugation.lean`（原名 `BranchSlideSeparation.lean`，与 F 车道同日推送的同名模块在整合分支上 add/add 冲突，本车道让路改名；F 的同名文件保持原名）。

- F 车道的 `ModelSlideLong`/`ChartSlideLong` 把滑移长度 `d` 放成无界参数，于是 §44/§45 里"沿分支把有限图卡排成链、
  用 `ε` 定向、在重叠上线性插值"的整条路线**不再需要**：一张含整条分支的乘积图卡就够。本节把它落到三维流形上。
- 通用引理（`OpenPartialHomeomorph` 命名空间，任意拓扑空间，不要求赋范结构，故可直接用于流形）：
  - `injective_conjugateMap`：`k` 单射且 `MapsTo k e.target e.target` ⟹ `e.conjugateMap k` 单射。
  - `disjoint_conjugateMap_image`：`A, B ⊆ e.target` 且 `Disjoint (k '' A) B` ⟹
    `Disjoint (e.conjugateMap k '' (e.symm '' A)) (e.symm '' B)`。
  两条是 `ChartSlide`/`ChartSlideLong` 中对 `slideMap`/`slideMapLong` 逐点重复的证明的一般化。F 的两条同名结果
  因变量块里的 `[NormedAddCommGroup M]` 不能直接用在流形 `M` 上，这是必须一般化的原因。
- `isPL_conjugateMap`：把 `ChartConjugate.isPL_conjugateHomeomorph` 从 `Homeomorph` 推广到**任意映射** `k`，
  只要 `IsPiecewiseAffineOn k univ`、`MapsTo k e.target e.target`、紧 `C ⊆ e.target` 与 `EqOn k id Cᶜ`。
  这条是必需的：`slideMapLong d R` 只证到双射（`bijective_slideMapLong`），逆的连续性没有，构造不出 `≃ₜ`。
- `exists_separated_slide`：**两层共轭**。外层是流形的 PL 图卡
  `E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))`（`E ∈ (plGroupoid 3).maximalAtlas M`），
  内层是模型上的 PL 拉直 `e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ)`，
  `h := E.conjugateMap (e.conjugateMap (slideMapLong d R))`。这样既不需要 `E ≫ₕ e`，也不需要
  `EuclideanSpace ℝ (Fin 3) ≃L[ℝ] ℝ × ℝ × ℝ` 的线性桥（本仓库没有，造它是无谓开销）。
  - `U` 由 `IsCompact.exists_isOpen_closure_subset` 给出；`RegularSpace M` 不是自动的，要显式
    `have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (H := EuclideanSpace ℝ (Fin 3)) M`
    （Mathlib 里它是定理不是实例），再由 `T2Space` 走 `WeaklyLocallyCompactSpace + R1Space ⟹ RegularSpace`。
  - 边界条款用 `Homeomorph/Conjugate.lean` 的 `conjugateMap_mem_iff` 连做两层，得到比 §44 要求的
    `h (U ∩ BdM) ⊆ BdM` 更强的 `∀ x, h x ∈ BdM ↔ x ∈ BdM`；内层的侧条件就是 `slideMapLong_snd`
    （滑移只动第一坐标），数据是 `Bd₁ ⊆ EuclideanSpace ℝ (Fin 3)` 与 `T ⊆ ℝ × ℝ`。
  - 另外输出 `MapsTo h U U`（`slideMapLong` 保 `slideSupportLong`，两层共轭后保 `K`，`U` 外恒等），
    §47 的双点集等式要用它。
- 两条**已经排掉的写法**，记下来免得重犯：
  1. 不交条款里的 `P, Q` 若有一个取成"贴合用的源余片"，`Disjoint (h '' (D '' P)) (D '' Q)` 恒假——
     缝 `P ∩ Pc` 的像在 `h` 下不动，且同时落在两边的像里。§44 的 `P, Q` 必须是**两条原像弧的两张细条带**，
     逐片贴合用的第二块是另取的余片 `Pc`（`P ∪ Pc = D.domain`）。
  2. 把位置条件写成 `D '' P ⊆ E.symm '' (e.symm '' slideBandA c)` 会让假设集**自相矛盾**：由 `0 ≤ d`、
     `c + 2*d ≤ R` 可得 `slideBandA c ⊆ slideSupportLong R`，于是 `D '' P ⊆ K ⊆ W`，与"缝像避开 `W`"
     一起逼出 `P ∩ Pc = ∅`，定理变空。正确的写法只约束**支撑内**的部分：
     `D '' P ∩ K ⊆ A₀`、`D '' Q ∩ K ⊆ B₀`，再加 `D '' P ∩ D '' Q ⊆ K`（两张条带只在支撑内相交）。
     不交性按 `p ∈ K` / `p ∉ K` 两种情形证：支撑外 `h` 恒等，交点会被第三条假设逼进 `K`。
- `isPLOn_piecewise_postcomp_of_separated`：把 `Pasting.exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective`
  的存在量词消掉（由 `EqOn g (h ∘ F) P` 与 `EqOn g F Pᶜ` 逐点认出 `g = P.piecewise (h ∘ F) F`），
  直接给出逐片映射的 PL 性、局部单射、纤维至多二与支撑外纤维不变。
- `doublePointSet_piecewise_postcomp`：抽象层的双点集等式，两个包含都证了，见 §47。
- 聚焦检查 `BranchSlideConjugation` exit=0（10.0 秒）、零 warning。

## 47. 2026-09-18 E3-M2：`exists_separated_along_branch` 与割开后的双点集精确等式

状态：done，相对于 §44 的乘积图卡数据（该数据是 F 的义务，这里写成**显式假设**，全文无 `sorry`）。
新模块 `BranchSeparation.lean`。

- `NormalSingularCellData.exists_separated_along_branch`：对 `hD : NormalSingularCellData D BdM B`、
  分支 `cb : hD.singularSet.Branch`、`W`、两张细条带 `P Q ⊆ D.domain`，在乘积图卡数据下输出 `U` 与 `h`，满足
  `IsOpen U`、`branchCarrier cb ⊆ U`、`closure U ⊆ W`、`IsPL 3 3 h`、`Function.Injective h`、
  `EqOn h id Uᶜ`、`MapsTo h U U`、`∀ x, h x ∈ BdM ↔ x ∈ BdM`、`Disjoint (h '' (D '' P)) (D '' Q)`。
  §44 列的八条全部给出，边界一条给的是双向 iff，强于所要求的 `h (U ∩ BdM) ⊆ BdM`。
- 乘积图卡数据（显式假设，逐条都是"位置/尺度"陈述，没有结论型假设）：PL 图卡 `E` 与模型拉直 `e`、
  `e.source ⊆ E.target`、`0 ≤ d`、`c + 2*d ≤ R`、`c - d < a`、三个 band 落在 `e.target` 里、
  `branchCarrier cb ⊆ K`（`K := E.symm '' (e.symm '' slideSupportLong R)`）、`W ∈ 𝓝ˢ K`、
  `D '' P ∩ K ⊆ A₀`、`D '' Q ∩ K ⊆ B₀`、`D '' P ∩ D '' Q ⊆ K`、边界的两层乘积表示 `Bd₁`/`T`。
- `NormalSingularCellData.exists_separated_cell_along_branch`：再加贴合数据
  `P ∪ Pc = D.domain`、`IsPolyhedron P`、`IsPolyhedron Pc`、`InjOn D P`、`InjOn D (Q ∩ D ⁻¹' W)`、
  `Pc ∩ D ⁻¹' W ⊆ Q`（`W` 上方的余片只有第二张条带）、`∀ x ∈ P ∩ Pc, D x ∉ W`（缝像避开 `W`）、
  `doublePointSet D D.domain ∩ W ⊆ branchCarrier cb`（`W` 避开其余分支）。这些都写在 `W` 上而不是输出的 `U` 上，
  再由 `U ⊆ closure U ⊆ W` 降下来，避免自指。输出除上面的条款外还给 `g := P.piecewise (h ∘ D) D` 的
  `IsPLOn 2 3 g D.domain`、`IsLocallyInjective (D.domain.domRestrict g)`、纤维至多二、
  `∀ y ∉ U, g ⁻¹' {y} = D ⁻¹' {y}`，以及
  `doublePointSet g D.domain = doublePointSet D D.domain \ branchCarrier cb`。
- 双点集等式**两个包含都证了**，"不产生邻近的新交线"那一半就在 `⊆` 里：
  - `⊆`：取 `x ≠ z ∈ D.domain` 且 `g x = g z = y`。两点都在 `P`：`h` 单射加 `InjOn D P` 直接矛盾。
    一点在 `P` 一点不在：若 `D x ∈ U`，由 `MapsTo h U U` 得 `y ∈ U`，于是另一点落进 `Pc ∩ D ⁻¹' U ⊆ Q`，
    与 `Disjoint (h '' (D '' P)) (D '' Q)` 矛盾——**这正是"没有新交线"**；若 `D x ∉ U` 则 `h` 在该点恒等，
    `y` 是旧双点且 `y ∉ U ⊇ branchCarrier cb`。两点都不在 `P`：是旧双点，且若 `y ∈ branchCarrier cb ⊆ U`
    则两点同属 `Q ∩ D ⁻¹' U`，被 `InjOn D (Q ∩ D ⁻¹' U)` 否掉。
  - `⊇`：`y` 是旧双点且 `y ∉ branchCarrier cb`，由 `doublePointSet ∩ U ⊆ branchCarrier cb` 得 `y ∉ U`，
    故 `h y = y`，于是两个原像在 `g` 下仍同取 `y`（在 `P` 里的那个经 `h y = y`）。
- 验证：`BranchSlideConjugation` 与 `BranchSeparation` 聚焦检查均 exit=0（10.0 / 10.4 秒）、零 warning；
  `fresh.py` 报 2 个改动模块全部 fresh，forbidden=0、stale=0、missing=0；
  `.lake/scratch/AuditE3BranchSeparation.lean` 的 9 条 `#print axioms` 全部只含
  `propext`、`Classical.choice`、`Quot.sound`。
- **仍未闭合的确切义务**（归 F，§44 的生产者，现在形状比 §44/§45 设想的简单得多）：给出上面那组乘积图卡数据本身，
  即对紧致触边分支 `branchCarrier cb` 造出单张 PL 图卡 `E` 与模型拉直 `e`，使分支拉直成
  `{p | p.2 = 0}` 上的一段，两张片在支撑内分别成为 `slideBandA c` 与 `slideBandQ a b`，边界呈
  `{p | p.2 ∈ T}` 形，且 `slideSupportLong R ⊆ e.target` 时 `R` 仍大到满足 `c + 2*d ≤ R`、`c - d < a`。
  §45 的 `BranchSignChain` 只在需要多张图卡时才用；单图卡路线用不到它，但若 F 改走多图卡，链版本仍然可用。
- 另外未做：§44 把两张细条带 `P, Q` 列为**输出**，这里它们是输入（属于图卡数据的一部分：条带在支撑内必须正好是两条标准 band）。
  由这条结果接 Case 3/4 的 `D₁`、`D₂`、`L₁`、`L₂` 字等式与复杂度严格下降尚未接线；按主人指定的顺序，Case 1/2 未开始。

## 48. 2026-09-18 E3-M2：边界条款改成带数据的蕴含（触边分支下模型边界的确切限制）

- §46/§47 最初把边界数据 `Bd₁ ⊆ EuclideanSpace ℝ (Fin 3)`、`T ⊆ ℝ × ℝ` 写成定理的假设。这会让
  **触边分支的情形变空**，理由如下，必须记下来：
  - F §19.110 的做法是让 `Bd M` 在模型里呈 `{p | p.2 ∈ T}`，由 `slideMapLong_snd` 保持。
    但 `{p | p.2 ∈ T}` 永远是一族**平行于 x 轴**的直线之并，而 x 轴正是分支方向与滑动方向。
  - `SingularGeneralPosition.HasPLBoundaryCrossingAt` 的局部模型是：存在 `ℓ`，`M = {ℓ ≥ 0}`，
    两张片是 `P ∩ {ℓ ≥ 0}`、`Q ∩ {ℓ ≥ 0}`，且 `∃ u ∈ P ⊓ Q, ℓ u = 1`——即**双点线与 `Bd M` 横截**。
  - 两者不相容：若把分支端点放进图卡，`hbde` 会逼出 `0 ∈ T`，于是整条分支都落在 `Bd M` 里，与
    "只有端点在 `Bd M` 上"矛盾；只剩 `T = ∅`（图卡避开 `Bd M`）这一支，而它与 `S ⊆ E.source`
    在触边分支下冲突。
- 因此把 `Bd₁`、`T` 移进结论，边界条款改写成
  `∀ Bd₁ T, (∀ x ∈ E.source, x ∈ BdM ↔ E x ∈ Bd₁) → (∀ y ∈ e.source, y ∈ Bd₁ ↔ (e y).2 ∈ T) →
   ∀ x, h x ∈ BdM ↔ x ∈ BdM`。
  主结论（`IsOpen U`、`S ⊆ U`、`closure U ⊆ W`、`IsPL`、单射、支撑外恒等、`MapsTo h U U`、不交、
  逐片映射的 PL/局部单射/纤维≤2/双点集等式）因此**对触边分支也非空**，边界保持则在边界确实有乘积
  表示时自动给出（内部分支取 `T = ∅`；`Bd M` 平行于分支时取相应的 `T`）。
- **确切的剩余义务（新增，归 F 或需要新模型）**：滑动模型 `slideMapLong` 沿分支方向推，无法在
  与分支横截的 `Bd M` 处保持 `Bd M`（把 `Bd M = {x = 0}`、`M = {x ≥ 0}` 代进去，`(0,y,0)` 被推到
  `x = -slideAmount < 0`，直接出 `M`）。所以 §44 的"边界端点处 `h (U ∩ BdM) ⊆ BdM`"在触边分支端点
  仍未真正解决：要么给端点一个另外的、与 `Bd M` 相切的收尾模型（锥度在 `Bd M` 处归零），
  要么把分离改成先把端点挪开的两步构造。这条是本次交付**没有**闭合的部分，不要当成已完成。
- 两条模块的聚焦检查在改动后重跑：`BranchSlideConjugation` exit=0（9.2 秒）、
  `BranchSeparation` exit=0（10.3 秒），均零 warning；审计 9 条依旧只含标准三公理；
  `fresh.py` forbidden=0、stale=0、missing=0。

## 49. 2026-09-18 E3-M2：与 F 同名模块的分工（重名已让路，无重复声明）

- F 在同一天把 `BranchSlideSeparation.lean` 推到同一路径，整合分支上 add/add 冲突。本车道的模块改名为
  `BranchSlideConjugation.lean`，F 的文件保持原名。两者内容不重叠：
- F 的文件全程带 `variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]`（几条 `omit` 只去掉
  `NormedSpace`，`NormedAddCommGroup` 留着），所以只能用在**赋范模型**上，不能以三维流形作源。
  本车道补的三条正是为了跨过这一层，逐条对应：
  - `OpenPartialHomeomorph.injective_conjugateMap` ← `ChartSlideLong.injective_chartSlideLong`；
  - `OpenPartialHomeomorph.disjoint_conjugateMap_image` ← `ChartSlideLong.disjoint_chartSlideLong_image`；
  - `isPL_conjugateMap` ← `ChartConjugate.isPL_conjugateHomeomorph`（后者只收 `Homeomorph`）。
  前两条把 `M` 放宽到任意拓扑空间，因此外层可以用流形图卡 `E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))`
  作共轭；第三条把待共轭映射放宽到任意逐片仿射映射，因为 `slideMapLong` 只有双射、没有逆的连续性。
- 逐条对照结论：**本车道没有任何声明因 F 的文件而变成多余，无可删项。**
  - F 的 `eqOn_chartSlideLong_id_compl`、`mapsTo_chartSlideLong_of_forall_mem_iff`、
    `mapsTo_chartSlideLong_boundary`、`mapsTo_chartSlideLong_halfSpace`：本车道没有同名/同形的独立声明，
    对应位置直接用了已有的 `Homeomorph/Conjugate.lean` 的 `conjugateMap_eqOn_compl`、`conjugateMap_mem_iff`
    （后者给的是 iff、且对任意拓扑空间成立，比 `MapsTo` 版强，并可两层串用）。
  - F 的 `isCompact_symm_image_slideSupportLong`、`symm_image_subset_source`：本车道只在证明内部有两行同内容的
    `have`，没有独立声明；它们对本车道**内层**的 `e`（源是 `EuclideanSpace ℝ (Fin 3)`，赋范）确实适用，
    将来可以改成消费 F 的版本，但那会让本模块依赖 F 的模块，本轮按协调者要求不做。
  - F 的 `exists_supported_separation_of_isBranchSlideChart`：赋范层的打包版，结论是
    `IsPiecewiseAffineOn h univ` 而非 `IsPL 3 3 h`，也不给 `U`、`closure U ⊆ W`、`MapsTo h U U`。
    与本车道的 `exists_separated_slide` 不是同一条。
- **给未来消费者的警告**：F 的 `IsBranchSlideChart` 里 `sheet_eq : P = e.symm '' slideBandA c` 是**等号**。
  若把这个 `P` 直接当成逐片贴合用的条带，就会撞上 §46 记的第二条矛盾（`slideBandA c ⊆ slideSupportLong R`，
  于是条带整个落进 `W`，与"缝像避开 `W`"冲突）。F 的 `P` 是模型带本身，贴合用的条带必须另取，
  位置条件只能写成支撑内的包含。
- **共享 olean 隐患（需要 F 或协调者处理，本车道未动）**：`E:\...\lib\lean\...\BranchSlideSeparation.olean`
  当前是本车道改名前编译的产物（06:09:26，427584 字节），而该路径的源码已换成 F 的文件（6395 字节，06:14:26）。
  现在 `import ...BranchSlideSeparation` 拿到的是本车道的旧内容而不是 F 的声明。需要由该模块的属主重编一次。
  本车道没有删除它，因为 S 车道正在运行，不擅自动别人的共享产物。

## 50. 2026-09-18 E3-M2：割开后单纯复杂度的严格下降（Case 3/4 的下降来源）

状态：done。新模块 `BranchComplexityDrop.lean`（`BranchSeparation.lean` 的直接下游，模块名在四条车道分支上都不存在，无重名）。

- §43 记录的障碍是：顺序交叉贴合**保留**了所选分支（`branchCarrier c ⊆ doublePointSet G G.domain`），
  因此不可能有复杂度下降。本节走的是 §47 的路线而不是 §42/§43 的源侧重贴：`g := P.piecewise (h ∘ D) D`
  的双点集精确等式 `doublePointSet g D.domain = doublePointSet D D.domain \ branchCarrier cb`
  **真的删掉了**被选分支，下降就是从这条等式直接出来的，没有把分支留在新奇点集里。
- 抽象层（同一源盘、同一有限复形、顶点映射取恒等，因此不能用 §32 的跨复形比较层，
  那一层要求新拉回像遗漏一个旧碰撞顶点，而这里新旧源盘完全相同）：
  - `eq_of_separated_fiber`：若 `v ≠ w` 都在 `Δ` 里且 `g v = g w`，则 `g v ∉ U`，且 `D v = D w = g v`。
    证明先由 `g v ∈ doublePointSet g Δ ⊆ doublePointSet D Δ \ S` 得 `g v ∉ S`，
    再由 `doublePointSet D Δ ∩ U ⊆ S` 得 `g v ∉ U`，最后用支撑外的纤维等式 `g ⁻¹' {y} = D ⁻¹' {y}` 把两个原像搬回 `D`。
  - `vertexCollisionPairs_subset_of_doublePointSet_subset_sdiff`：`vertexCollisionPairs K g ⊆ vertexCollisionPairs K D`。
  - `simplicialComplexity_lt_of_doublePointSet_subset_sdiff`：再给一对不同顶点 `v ≠ w` 满足
    `D v = D w ∈ S`（`S ⊆ U`），则 `{v,w}` 是 `D` 的碰撞对而不是 `g` 的碰撞对，于是
    `simplicialComplexity K g < simplicialComplexity K D`。`g v ≠ g w` 的理由正是上一条：
    若 `g v = g w` 则 `g v ∉ U`，但 `D v = g v ∈ S ⊆ U`。
- 生产者 `exists_simplicialComplexity_lt_of_doublePointSet_subset_sdiff`：只要
  `S ∩ doublePointSet D D.domain` 非空，就从 `D.domain` 的多面体性取有限复形，再用
  `exists_isSubdivision_singleton_mem` 两次把该双点的两个不同原像细分成顶点，交付
  `K.space = D.domain` 与严格下降。适配三角剖分因此不是假设。
- 端点 `NormalSingularCellData.exists_separated_cell_simplicialComplexity_lt_along_branch`：
  沿用 §47/§48 的乘积图卡数据（仍是显式假设，属 F 的义务，未被伪造），输出 §47 的全部条款
  （`U`、`h`、`IsPL`、单射、支撑外恒等、边界蕴含、不交、逐片映射的 PL/局部单射/纤维≤2/纤维不变、双点集等式）
  再加上有限复形 `K`、`K.space = D.domain` 与
  `simplicialComplexity K (P.piecewise (h ∘ D) D) < simplicialComplexity K D`。
  分支非空由 `branchCarrier_isConnected` 给，双点性由 `branchCarrier_subset_doublePointSet` 给，
  两者都不是新假设。
- 验证：`BranchComplexityDrop` 聚焦检查 exit=0（9.9 秒）、零 warning；
  `.lake/scratch/AuditE3ComplexityDrop.lean` 的 5 条 `#print axioms` 全部只含
  `propext`、`Classical.choice`、`Quot.sound`。

## 51. 2026-09-18 E3-M2：Case 3/4 的四段边界字（书页 186–187 的 `σ τ υ φ`）

状态：done（源盘边界一侧的四段字、两端点配对二分与两条群论消费接口已闭合；把该字搬到
`NormalSystem.boundaryNeighborhoodSpace` 的基本群里仍未接线，见末条）。新模块 `BoundaryWordFourArcs.lean`
（模块名在四条车道分支上都不存在）。

- `exists_homeomorph_loopCircle_of_isLoop`：把 `CellGluing.exists_boundaryParam_paths_of_isCutPair_union`
  证明的后半段抽出来——只要给一条 `Path a' a'`（值在 `frontier P` 里）、一条 `Schoenflies.IsLoop`，
  以及两者的逐点等式与满射性，就得到 `ev : loopCircle ≃ₜ frontier P` 且 `ev θ = pathToCircle pth θ`。
- `exists_boundaryParam_four_paths`：**四段版**的边界参数化。输入是循环次序的四条弧
  `A₁ (p→q), A₂ (q→r), A₃ (r→s), A₄ (s→p)`、三条相遇条件与 `frontier P = A₁ ∪ (A₂ ∪ (A₃ ∪ A₄))`；
  输出四条道路 `σ τ υ φ`、它们的像集恰为四条弧，以及逐点等式
  `ev θ = pathToCircle (σ.trans (τ.trans (υ.trans φ))) θ`。
  关键是 `Path.trans` 不结合，所以模型侧必须用同样右嵌套的
  `concatenate f₁ (concatenate f₂ (concatenate f₃ f₄))`；`IsLoop` 由 `IsLoop.concatenate` 加两层
  `injOn_concatenate`/`continuousOn_concatenate`/`image_concatenate` 给出，逐点等式按 `t ≤ 1/2` 三次分叉对齐。
- `exists_four_arcs_of_two_disjoint_subarcs`：PL 1-球面 `J` 内两条不交子弧 `S₁ (p..q)`、`S₃ (r..s)`
  把 `J` 切成四段。证明先用 `exists_isCutPair_of_isArcBetween_subset_isPLSphere` 取 `S₁` 的补弧 `G`，
  再用 `IsArcBetween.exists_split` 在 `r` 处切 `G`，按 `s` 落在哪一半分两种情形第二次切，
  最后用 `IsArcBetween.eq_of_subset_arc` 证明中段恰是 `S₃`（不是另取的弧）。输出带
  `(u,v) = (r,s)` 或 `(s,r)` 的二分，正好是四段循环次序里 `S₃` 的走向。
- `NormalSingularCellData.exists_boundary_four_arc_word_of_boundaryBranch`：把上面两条接到实际触边分支。
  由 `exists_three_cells_of_boundaryBranch` 取三盘分解与两条 crosscut，`D₁ ∩ frontier D.domain` 与
  `D₃ ∩ frontier D.domain` 是两条不交的边界弧（不交性来自 `Disjoint D₁.domain D₃.domain`），
  于是得到 `frontier D.domain` 的四段字与 `ev`。同时由
  `IsPLHomeomorphOn.maps_arc_endpoints` 与 `EqOn D (D ∘ g) Ab` 得到端点配对的确切二分
  `(D u = D p ∧ D v = D q) ∨ (D u = D q ∧ D v = D p)`：前者是书页 186 的 Case 3（endpoint-reversing），
  后者是书页 187 的 Case 4（endpoint-preserving）。四种组合（弧次序二分 × `g` 的定向二分）都验算过，
  每一种都落进且只落进其中一支。
- 两条消费接口把四段字接到 §33 已证的群论引理，没有把道路字改写成假设：
  - `not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_reversing`：给出 `X` 中的四条道路
    `σ υ : Path a b`、`τ φ : Path b a`（它们的端点类型本身就强制了 reversing 配对）、逐点等式
    `σ t = f (σ₀ t)` 等、以及 `γ θ = f (ev θ)`，则由 `¬loopClassMeets γ` 得
    `¬loopClassMeets (συ⁻¹) ∨ ¬loopClassMeets (σφυτ)`。
  - `..._preserving` 同理给 `¬loopClassMeets (συ) ∨ ¬loopClassMeets (στ⁻¹υφ⁻¹)`。
  - 辅助 `trans_apply_eq_map`、`pathToCircle_eq_of_forall` 把 `f` 穿过 `Path.trans` 与 `pathToCircle`；
    `freeLoop X = C(loopCircle, X)`，所以母字等式用 `ext` 逐点即可。
- 验证：`BoundaryWordFourArcs` 聚焦检查 exit=0（11.0 秒）、零 warning；
  `.lake/scratch/AuditE3BoundaryWord.lean` 的 8 条 `#print axioms` 全部只含
  `propext`、`Classical.choice`、`Quot.sound`。
- **确切的未闭合部分**：四段字目前是 `frontier D.domain → M` 一侧的；Moise 的 `L`、`L₁`、`L₂` 是
  `NormalSystem.boundaryNeighborhoodSpace` 里的自由环类。把 `D` 限制到 `frontier D.domain` 的像落在
  `S.loopComplex.space` 里并与 `S.boundaryLoop` 逐点对齐（即为上面两条消费接口提供 `f`、`γ` 与
  `hγ : γ θ = f (ev θ)`），需要 `NormalSystem.boundaryParam` 与本节 `ev` 的比较，尚未接。
  这一步不改变本节结论，也没有被写成结论型假设。
