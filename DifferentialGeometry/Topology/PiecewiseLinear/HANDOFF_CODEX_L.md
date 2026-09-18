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

## 52. 2026-09-18 E3-M2：Case 3/4 的合并端点（同一条分支同时给四段字与复杂度下降）

状态：done（相对于 §47/§48 的乘积图卡显式假设）。新模块 `BranchCaseThreeFour.lean`。

- `NormalSingularCellData.exists_four_arc_word_and_simplicialComplexity_lt_of_boundaryBranch`
  对**同一条**触边分支 `cb` 同时交付 §51 的四段边界字（含 Case 3/Case 4 的端点配对二分）与 §50 的
  分离胞腔 `g := P.piecewise (h ∘ D) D`，后者带 `doublePointSet g = doublePointSet D \ branchCarrier cb`
  与 `simplicialComplexity K g < simplicialComplexity K D`。这正是 §25.1 Case 3/4 一步所需的两半：
  被切掉的分支就是产生 `σ τ υ φ` 四段字的那条，也是使复杂度严格下降的那条。
- §43 的教训在这里是决定性的：顺序交叉重贴给的 `L₂` 保留了分支，所以不能用；本端点的降复杂度一侧走
  §47 的环境分离（真的把两片推开），双点集等式两个包含都证过，因此"分支被删掉"不是断言而是结论。
- 验证：`BranchCaseThreeFour` 聚焦检查 exit=0（10.6 秒）、零 warning；
  `.lake/scratch/AuditE3CaseThreeFour.lean` 的 1 条 `#print axioms` 只含
  `propext`、`Classical.choice`、`Quot.sound`。`fresh.py`（相对 `7fcbcdd44`）报 3 个改动 Lean 模块全部
  fresh，forbidden=0、stale=0、missing=0；三次聚焦检查与两次审计前后全局都没有其它 `lean.exe`。
- **本轮没有做、归属明确的三条**：
  1. 乘积图卡数据本身（F 的义务，§47 已给出确切形状），以及 §48 记的触边分支端点处
     `Bd M` 与滑动方向横截的收尾模型。
  2. 把四段字搬进 `NormalSystem.boundaryNeighborhoodSpace` 的基本群（需要 `boundaryParam` 与 §51 的
     `ev` 的比较），从而真正调用 §51 的两条消费接口得到 `¬meets L₁ ∨ ¬meets L₂`。
  3. `L₁`、`L₂` 各自的实际正规奇异胞腔（`L₁` 由 §41 的
     `exists_boundary_surgery_cell_of_boundaryBranch` 已给；`L₂` 仍缺，§43 排除了顺序交叉重贴）。
  按主人指定的顺序，Case 1/2 未开始。

## 53. 2026-09-18 E3-M2：触边分支的前推分离（§48 的开放项被 F 的负结果否定地关掉）

状态：done（相对 §47 的乘积图卡显式假设）。新模块 `BranchSeparationBoundary.lean`
（模块名在四条车道分支上都不存在，无重名）。

- **§48 的开放项已关闭，且是被否定地关闭的。** F 车道 `ModelSlideFwd.lean` 的
  `not_disjoint_image_slideBandA_of_origin_fixed`：对**任意**映射 `h`，只要 `0 ≤ c`、`a ≤ 0`、`0 ≤ b`
  且 `h (0,0,0) = (0,0,0)`，就有 `¬Disjoint (h '' slideBandA c) (slideBandQ a b)`。原点是模型里的分支端点，
  它本身就是一个双点（两张标准 band 都含它）；"锥度在 `Bd M` 处归零"恰恰就是把这个端点钉死。
  于是 §48 设想的"与 `Bd M` 相切的收尾模型"**不存在**——任何方向、任何距离、任何锥度都不行。
  §48 所列的两条备选路线中，第一条（相切收尾模型）因此作废；只剩"先把端点挪开"，而这正是 F 的前推模型做的事。
- **双条件条款在触边分支上是可证不可得的，不是尚未证明。** 除上一条外，F 还直接证明了前推模型不保持边界平面：
  `not_mapsTo_chartSlideFwd_boundaryPlane`（对 `hd : 0 < d`、`hR : 0 < R`，`{p | p.1 = 0}` 不被保持）与
  它的打包版 `not_mapsTo_boundary_of_isBranchSlideChart_endpoint`。所以
  `∀ x, h x ∈ BdM ↔ x ∈ BdM` 与更弱的 `h (U ∩ BdM) ⊆ BdM` 在触边分支端点处都不可能成立。
  **能成立并且无附加假设的是闭半空间的保持**：`mapsTo_chartSlideFwd_halfSpace` 给出
  `MapsTo (e.conjugateMap (slideMapFwd d R)) N N`，其中模型侧是
  `slideEndpointHalfSpace = {p | 0 ≤ p.1}`。本节把边界条款换成 `MapsTo h N N`。
- 消费 F 的前向端点包（全部来自 `BranchSlideEndpoint.lean` / `ModelSlideFwd.lean`）：
  `injective_chartSlideFwd`、`eqOn_chartSlideFwd_id_compl`、`disjoint_chartSlideFwd_image`、
  `isPiecewiseAffineOn_chartSlideFwd`、`mapsTo_chartSlideFwd_halfSpace`、
  `OpenPartialHomeomorph.mapsTo_conjugateMap`、`mapsTo_slideMapFwd_of_subset`、
  `mapsTo_slideMapFwd_slideSupportLong`。分离常数从 §47 的 `c - d < a` 换成 `b < d`（远端越过 band Q）。
- 交付的三条：
  - `exists_separated_slide_fwd`：§46 `exists_separated_slide` 的前推版，外层流形 PL 图卡 `E`、
    内层模型拉直 `e` 的两层共轭 `h := E.conjugateMap (e.conjugateMap (slideMapFwd d R))`。
    输出 `IsOpen U`、`S ⊆ U`、`closure U ⊆ W`、`IsPL 3 3 h`、单射、`EqOn h id Uᶜ`、`MapsTo h U U`、
    `Disjoint (h '' A) B`，加上半空间条款
    `∀ N N₁, (∀ x ∈ E.source, x ∈ N ↔ E x ∈ N₁) → (∀ y ∈ e.source, y ∈ N₁ ↔ 0 ≤ (e y).1) →
     MapsTo h N N`。数据 `N`、`N₁` 与 §48 一样放在结论里，所以主结论对触边分支非空。
  - `NormalSingularCellData.exists_separated_along_boundary_branch`
  - `NormalSingularCellData.exists_separated_cell_along_boundary_branch`：与 §47 的两条逐条对应，
    只把边界条款换成上面的 `MapsTo`，并额外把 `MapsTo h U U` 也放进胞腔版的输出（§47 的胞腔版只在证明内部用它）。
    逐片映射的 `IsPLOn`、局部单射、纤维 ≤ 2、支撑外纤维不变与双点集精确等式
    `doublePointSet (P.piecewise (h ∘ D) D) D.domain = doublePointSet D D.domain \ branchCarrier cb`
    全部不变。
- **为什么 `MapsTo` 就够：逐条核对了双点集等式实际用到的假设。**
  `doublePointSet_piecewise_postcomp` 只用 `hhinj`（`h` 单射）、`hhfix`（`EqOn h id Uᶜ`）、
  `hhmap`（`MapsTo h U U`）、`hinjP`、`hinjQU`、`hPcQU`、`hdisj`、`hSU`、`hclean`；
  `isPLOn_piecewise_postcomp_of_separated` 只用 `hF`、两块多面体性、`hloc`、`hcard`、`hinjP`、
  `hhpl`、`hhinj`、`hhfix`、`hseamU`、`hinjPcU`。**两条都不碰边界条款。**
  在 `BranchComplexityDrop.lean` 与 `BranchCaseThreeFour.lean` 里，§48 的双条件条款也只是被原样转出，
  从未被消费（已 grep 核对：`hhbd` 只出现在 `obtain` 与 `exact` 的转出位置）。
- **确实需要比 `MapsTo` 更强的那一步，以及为什么：** 把割开后的 `g := P.piecewise (h ∘ D) D`
  重新认成同一对 `(BdM, B)` 上的 `NormalSingularCellData`。该结构的
  `image_inter_boundary : g '' g.domain ∩ BdM = Set.range g.boundary` 是一条**等式**，
  只有 `MapsTo h B B` 推不出来；而按上面两条负结果，在触边分支端点处它对前推模型是假的——
  端点被推离 `Bd M`，新胞腔的边界圆不再整条落在 `Bd M` 上。
  因此正确的下一步不是去找更强的条款，而是承认新胞腔的边界圆被推进了内部，
  按 Moise 的做法在 `Bd M` 的双领环里把它拉回（或改用"在 `Bd M` 上不动、只在内部推开"的两步构造）。
  这条现在是**明确的新义务**，不再是 §48 那条已被证伪的"相切收尾模型"。
  本次交付的三条结论都不依赖它。
- 未做（保持 §52 的分工）：`BranchComplexityDrop` 与 `BranchCaseThreeFour` 仍带 §48 的双条件形式，
  没有改成前推形式；改法是机械的（把两处的 `hhbd` 条款换成本节的 `MapsTo` 条款并改调本节的两条），
  但会动到已进整合分支的两个模块，按本轮范围未做。
- 验证：`BranchSeparationBoundary` 聚焦检查 exit=0（10.2 秒）、零 warning；
  `.lake/scratch/AuditE3BoundarySeparation.lean` 的 3 条 `#print axioms` 全部只含
  `propext`、`Classical.choice`、`Quot.sound`。合并 `origin/codex/moise-integration`（`e624b650b`）后
  `fresh.py` 报 forbidden=0、stale=0、missing=0；全程无其它 `lean.exe`。

## 54. 2026-09-18 E3-M2：四段字进入 `π₁`（`f`、`γ`、`hγ` 已接上，剩 `boundaryParam` 与 `ev` 的比较）

状态：done（相对一条显式的参数化比较假设 `hparam`）。新模块 `BoundaryWordLoopClass.lean`
（模块名在四条车道分支上都不存在，无重名）。这是 §52 第 2 条未做项的主体。

- `not_loopClassMeets_or_not_loopClassMeets_of_four_boundary_arcs_image`：把 §51 的两条消费接口
  合成一条，并且**自动构造**它们要的连接道路。输入是四段弧的道路 `σ₀ τ₀ υ₀ φ₀`、参数化 `ev` 与 `hev`、
  连续的 `f : Q → X`、`γ` 与 `hγ : ∀ θ, γ θ = f (ev θ)`、正规子群 `N` 与 `hL : ¬loopClassMeets γ x N`，
  外加**端点配对二分的像侧形式** `(f u' = f p' ∧ f v' = f q') ∨ (f u' = f q' ∧ f v' = f p')`。
  输出是两支并列的存在命题，Case 3（reversing）给 `σ υ : Path a b`、`τ φ : Path b a` 与
  `¬meets (συ⁻¹) ∨ ¬meets (σφυτ)`；Case 4（preserving）给 `σ : Path a b`、`τ : Path b b`、
  `υ : Path b a`、`φ : Path a a` 与 `¬meets (συ) ∨ ¬meets (στ⁻¹υφ⁻¹)`。两支都带
  `∀ t, σ t = f (σ₀ t)` 等四条逐点等式，所以这两个字确实是四段边界弧的像，不是另取的道路。
  - 实现要点：四条道路用 `Path.map σ₀ hf` 造，再用 `Path.cast` 沿 `f u' = f p'` 一类的等式调端点类型；
    `Path.map` 与 `Path.cast` 都不改 `toFun`，因此四条逐点等式全是 `rfl`。
    `qq : Path x a`、`cc : Path a b` 由 `PathConnectedSpace.somePath` 给，不必再当参数传。
  - 端点配对的**两支正好对应两条消费接口要求的端点类型**：Case 3 里 `f u' = f p'`、`f v' = f q'`
    使 `τ₀`、`φ₀` 的像成为 `Path b a`；Case 4 里 `f u' = f q'`、`f v' = f p'` 使 `τ₀` 的像成为
    `Path b b`、`φ₀` 的像成为 `Path a a`。这不是凑出来的，是书页 186/187 两种情形的类型层体现。
- `NormalSystem.singularMap_mem_boundaryNeighborhood`：`z ∈ frontier sourceComplex.space` ⟹
  `S.singularMap z` 落在 `boundaryNeighborhood` 的空间里。证明用 `boundaryParam` 的满射性取 `θ`，
  再由 `boundaryLoop_eq` 与 `(S.boundaryLoop θ).2` 得到。**这正是 §28 要求的"用参数化相容性而不是像集相等"**。
- `NormalSystem.not_loopClassMeets_boundaryLoop`：把结构字段 `loopClass_avoids_normal`
  （用 `normalSystemLoopConjugacyClass` 写的）翻成 `¬loopClassMeets S.boundaryLoop S.basepoint S.normalSubgroup`，
  桥是 `FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong S.connector S.boundaryBasedLoop`。
  需要 `[PathConnectedSpace S.boundaryNeighborhoodSpace]`（`loopClassMeets` 的类型类要求）。
- `NormalSystem.exists_boundary_word_loop_dichotomy_of_four_arcs`：实际的接线端点。
  取 `X := S.boundaryNeighborhoodSpace`、`x := S.basepoint`、`N := S.normalSubgroup`、
  `γ := S.boundaryLoop`，并**构造** `f : frontier D.domain → S.boundaryNeighborhoodSpace`，
  `f z = ⟨S.singularMap z, _⟩`；连续性由 `isPiecewiseAffineOn_simplicialMap` 的 `continuousOn`
  限制到 `frontier D.domain ⊆ D.domain = S.sourceComplex.space` 得到（`D.isPLBall_domain` 给闭性）。
  结论里的四条逐点等式写成 `(σ t : E) = S.singularMap (σ₀ t)`，所以两个字完全由 `S.singularMap`
  与四段弧决定，不引用内部的 `f`。
  - `hγ : ∀ θ, S.boundaryLoop θ = f (ev θ)` 由 `Subtype.ext` + `boundaryLoop_eq` + `hparam` 给出。
  - 端点配对从源侧 `(D u = D p ∧ D v = D q) ∨ (D u = D q ∧ D v = D p)`（§51 的输出）
    经 `hfactor` 搬到像侧。
- **两条显式假设，逐条说明它们是什么、为什么不是结论型假设：**
  1. `hfactor : ∀ z ∈ frontier D.domain, ∀ w ∈ frontier D.domain, D z = D w →
     S.singularMap z = S.singularMap w`。这是 `D`（`M` 里的奇异胞腔）与 `S.singularMap`（`E` 里的
     正规系统映射）在边界圆上的**相容性**，不是待证结论。§38 的
     `LemmaTwo.NormalSystem.exists_singular_two_cell_in_double` 给出的 `D` 满足
     `EqOn (fun x => (D x : E × E × ℝ)) (ι ∘ S.singularMap) S.sourceComplex.space`，其中
     `ι` 在 `K.space` 上是 PL 同胚（故单射），于是 `hfactor` 在那个实现里可直接消掉。
     本模块没有引入 double 机器，是为了不让接线依赖那一层。
  2. `hparam : ∀ θ, (S.boundaryParam θ : EuclideanSpace ℝ (Fin 2)) = (ev θ : _)`。
     这是**本节唯一真正未闭合的数学缺口**，见下条。
- **确切的未闭合义务（`hparam`）及其可行路线。** `S.boundaryParam` 与 §51 构造的 `ev` 都是
  `loopCircle ≃ₜ frontier D.domain`，但 `ev` 的起点是四段弧的切点 `p`，而 `S.boundaryParam 0`
  是生产者任选的点；两者相差一个圆自同胚 `ρ := ev.symm ∘ S.boundaryParam`。要消掉 `hparam`，
  必须证明 `loopClassMeets` 在圆的重参数化下不变。本树已有全部原料，**缺的是把它们拼起来**：
  - `Topology/LoopSpace/HomeomorphismOrientation.lean` 的 `circleHomeomorph_affineLift_or_neg`：
    任一 `ψ : loopCircle ≃ₜ loopCircle` 要么是 `affineCircleMap F`、要么是 `-affineCircleMap F`，
    其中 `F : ℝ ≃ₜ ℝ` 严格单调且 `F (t+1) = F t + 1`。
  - 保定向一支：`F_s t := (1-s) * F t + s * t` 仍满足 `F_s (t+1) = F_s t + 1`，给出
    `affineCircleMap F ≃ id`，故 `γ ∘ ψ` 与 `γ` 自由同伦；再用 `SingularCell.lean` 的
    `FreeLoop.conjugacyClass_eq_of_homotopic` 把 `loopClassMeets` 搬过去。
    要补的是 `G : C(I × loopCircle, loopCircle)` 的联合连续性；按
    `QuotientAddGroup.isOpenMap_coe` 与 `IsOpenMap.prodMap` 把它化到 `I × ℝ` 上即可。
  - 反定向一支：`γ ∘ (neg)` 的共轭类是原共轭类的逆，而 `N` 是子群（对逆封闭），
    所以 `conjugacyClassMeets` 仍不变；要补的是 `circleToPath (γ ∘ neg)` 与 `(circleToPath γ).symm`
    的同伦，以及 `ConjClasses.mk g⁻¹` 与 `N` 的相遇性等价。
  - `Topology/LoopSpace/Rotation.lean` 的 `pathToCircle_trans_homotopic_comm` 只处理"在已有拼接点处
    旋转半圈"，不足以处理 `boundaryParam 0` 落在某段弧**内部**的情形，所以不能替代上面的一般结论。
    这一点已试过并排除，记下免得重走。
- 【后补】上面那条 `hparam` 已在同一夜由 §55 完全消掉，不再是未闭合义务；本节描述的路线就是 §55 实际走的路线。
- 未做（保持主人指定的范围）：§43 的障碍仍在，`L₂` 的实际重贴胞腔没做；Case 1/2 未开始。
- 验证：`BoundaryWordLoopClass` 聚焦检查 exit=0（10.3 秒）、零 warning；
  `.lake/scratch/AuditE3BoundaryWordLoopClass.lean` 的 4 条 `#print axioms` 全部只含
  `propext`、`Classical.choice`、`Quot.sound`。全程无其它 `lean.exe`。

## 55. 2026-09-18 E3-M2：圆重参数化下 `loopClassMeets` 不变，§54 的 `hparam` 被消掉

状态：done。新模块 `LoopClassReparametrization.lean`（纯自由环/共轭类内容，暂放在
`PiecewiseLinear/` 下，因为它的终点要用 `LoopTheorem/SingularCell.lean` 的 `loopClassMeets`；
路线稳定后可以下沉到 `Topology/LoopSpace/`）。`BoundaryWordLoopClass.lean` 据此去掉 `hparam`，
并补上真正的装配端点。

- `loopClassMeets_comp_circleHomeomorph_iff`：对任意 `ψ : loopCircle ≃ₜ loopCircle`、
  `γ : freeLoop X`（`X` 道路连通）、`x : X` 与**任意子群** `N`（不需要正规性），
  `loopClassMeets (γ.comp ⟨ψ, ψ.continuous⟩) x N ↔ loopClassMeets γ x N`。
  这条正是 §54 缺的那块：`ev` 与 `S.boundaryParam` 相差一个圆自同胚，现在这个差别对结论没有影响。
- 证明分两支，用 `HomeomorphismOrientation.lean` 的 `circleHomeomorph_affineLift_or_neg`：
  - 保定向：`ψ = affineCircleMap F`，`F : ℝ ≃ₜ ℝ` 严格单调、`F (t+1) = F t + 1`。
    直线同伦 `F_s t := (1-s) * F t + s * t` **仍然**满足 `F_s (t+1) = F_s t + 1`（`affineInterpolate_periodic`），
    于是 `freeLoop_comp_affineCircleMap_homotopic` 给出 `γ.comp (affineCircleMap F) ≃ γ`。
    同伦的联合连续性用 `BasedCircle.lean` 的 `unitInterval_to_loopCircle_prod_quotient unitInterval`
    把 `I × loopCircle` 上的连续性化到 `I × I` 上，再用 `AddCircle.continuous_mk'`。
    自由同伦到共轭类相等走 `FreeLoop.conjugacyClass_eq_of_homotopic`。
  - 反定向：`ψ = -affineCircleMap F`，于是
    `γ.comp ⟨ψ,_⟩ = (γ.comp negLoopCircle).comp (affineCircleMap F)`，先用上一支消掉 `affineCircleMap F`，
    再证 `loopClassMeets (γ.comp negLoopCircle) x N ↔ loopClassMeets γ x N`：
    - `circleToPath_comp_negLoopCircle`：`circleToPath ⟨γ.comp negLoopCircle, _⟩` **逐点等于**
      `(circleToPath ⟨γ, rfl⟩).symm`，因为 `-(t : loopCircle) = ((1 - t : ℝ) : loopCircle)`
      （`1 - t = -t + 1` 加 `AddCircle.coe_period`）。不是同伦，是等号，省掉一层 rel 端点同伦。
    - `conjugacyClass_comp_negLoopCircle`：再用 `fundamentalGroupChangeBasepoint` 是 `≃*`（`map_inv`）
      与 `FundamentalGroup.inv_def`，得到共轭类是原代表元的**逆**的共轭类。
    - `conjugacyClassMeets_mk_inv_iff`：`N` 是子群就够（对逆封闭）；`IsConj r⁻¹ g⁻¹` 的见证是 `c⁻¹`
      而不是 `c`（第一次写成 `c`，`group` 留下 `c*c*g⁻¹*c⁻²=g⁻¹` 的假目标，记下免得重犯）。
- `NormalSystem.exists_boundary_word_loop_dichotomy_of_four_arcs` 因此**去掉了 `hparam`**。
  新证法：令 `γ₀ : freeLoop S.boundaryNeighborhoodSpace := ⟨fun θ => f (ev θ), _⟩`，
  `ψ := (S.boundaryParam.trans (Homeomorph.setCongr _)).trans ev.symm`，
  用 `boundaryLoop_eq` 逐点证 `S.boundaryLoop = γ₀.comp ⟨ψ, ψ.continuous⟩`，
  再用上面的不变性把 `¬loopClassMeets S.boundaryLoop` 搬成 `¬loopClassMeets γ₀`；
  这时 `hγ : ∀ θ, γ₀ θ = f (ev θ)` 是 `rfl`。两个 frontier 子类型的类型差由
  `Homeomorph.setCongr (congrArg frontier hdom)` 搬运，`(setCongr h z : _) = (z : _)` 是 `rfl`。
- `NormalSystem.exists_boundary_word_loop_dichotomy_of_boundaryBranch`：**装配端点**。
  输入只剩 `hD : NormalSingularCellData D BdM B`、`hc : IsBoundaryBranch c`、
  `hdom : D.domain = S.sourceComplex.space`、`hfactor`（`D` 与 `S.singularMap` 在边界圆上的相容性）
  与 `[PathConnectedSpace S.boundaryNeighborhoodSpace]`。输出四条边界弧 `A₁ A₂ A₃ A₄`、
  `frontier D.domain = A₁ ∪ (A₂ ∪ (A₃ ∪ A₄))`，以及 Case 3 / Case 4 两支的二分，
  每支都带四条**像集等式** `Set.range (fun t => (σ t : E)) = S.singularMap '' A₁` 等
  （辅助 `range_eq_image_of_forall_eq`），所以两个字确实由四段边界弧的像决定。
  Case 3 给 `¬meets (συ⁻¹) ∨ ¬meets (σφυτ)`，Case 4 给 `¬meets (συ) ∨ ¬meets (στ⁻¹υφ⁻¹)`，
  全部是 `π₁(S.boundaryNeighborhoodSpace, S.basepoint)` 里关于 `S.normalSubgroup` 的实际命题。
- **现在的确切剩余义务（只剩两条，都不是本层的缺口）：**
  1. `hdom` 与 `hfactor`：由 §38 的 `LemmaTwo.NormalSystem.exists_singular_two_cell_in_double`
     提供（它给 `D.domain = S.sourceComplex.space` 与
     `EqOn (fun x => (D x : E × E × ℝ)) (ι ∘ S.singularMap) S.sourceComplex.space`，`ι` 在 `K.space` 上单射）。
     接上去只需要在 `double 3 K` 环境里实例化，本轮没做是为了不把 double 机器拖进这一层。
  2. `L₁`、`L₂` 各自的实际正规奇异胞腔：`L₁` 由 §41 已给；`L₂` 仍缺，§43 排除了顺序交叉重贴。
     这是 §52 第 3 条，未变。
- 验证：`LoopClassReparametrization` 聚焦检查 exit=0（9.8 秒）、
  `BoundaryWordLoopClass` exit=0（11.5 秒），均零 warning；
  `.lake/scratch/AuditE3BoundaryWordLoopClass.lean` 的 16 条 `#print axioms` 全部只含
  `propext`、`Classical.choice`、`Quot.sound`（其中 `conjugacyClassMeets_mk_inv_of`、
  `conjugacyClassMeets_mk_inv_iff`、`range_eq_image_of_forall_eq` 只用到 `propext`、`Quot.sound`）。
  `fresh.py` 报 3 个改动模块全部 fresh，forbidden=0、stale=0、missing=0；全程无其它 `lean.exe`。

## 56. 2026-09-18 E3-M3：前推滑动不会把内点拉回 `Bd M`，边界分支分离胞腔的 `image_inter_boundary` 的 `⊆` 半边无条件闭合

状态：done（`⊆` 半边无条件闭合；`⊇` 半边给出确切的领环输入，并证明"有领环延拓即得等式"）。
改动 `BranchSeparationBoundary.lean`，新模块 `BranchBoundaryCollar.lean`（模块名在四条车道分支上都不存在）。
这一节回答 §53 末尾留下的那条新义务。

- **先把几何结论说清楚：`image_inter_boundary` 的两个包含方向命运不同。**
  §53 已证 `⊇`（即 `Set.range g.boundary ⊆ BdM`）对前推模型是**假**的：触边分支端点被推离 `Bd M`。
  本节证明另一半 `⊆` 是**真**的，而且不需要任何领环：**前推滑动只会把边界推进内部，
  绝不会把内点拉到 `Bd M` 上。** 这不与 §48/§53 的两条负结果冲突——负结果说的是
  `MapsTo h BdM BdM` 不成立，本节说的是 `h ⁻¹' BdM ∩ N ⊆ BdM`，方向相反。
- `mem_boundaryPlane_of_chartSlideFwd`：模型层的全部内容。
  `slideMapFwd d R p = (p.1 + slideAmountLong d R p, p.2)`，`slideAmountLong ≥ 0`；
  若 `0 ≤ (e x).1` 且 `(slideMapFwd d R (e x)).1 = 0`，则 `(e x).1 = 0`。一句 `linarith`。
  **半空间假设是必需的**：没有 `0 ≤ (e x).1` 时 `(e p).1 = -amount < 0` 是可能的
  （只要 `3|x| ≤ R`），所以这条与"保持闭半空间"那条用的是同一份坐标数据。
- `exists_separated_slide_fwd`、`NormalSingularCellData.exists_separated_along_boundary_branch`、
  `NormalSingularCellData.exists_separated_cell_along_boundary_branch` 三条各多出一条输出条款：
  `∀ (N Bd : Set M) (N₁ Bd₁ : Set (EuclideanSpace ℝ (Fin 3))),
   (∀ x ∈ E.source, x ∈ N ↔ E x ∈ N₁) → (∀ y ∈ e.source, y ∈ N₁ ↔ 0 ≤ (e y).1) →
   (∀ x ∈ E.source, x ∈ Bd ↔ E x ∈ Bd₁) → (∀ y ∈ e.source, y ∈ Bd₁ ↔ (e y).1 = 0) →
   ∀ x ∈ N, h x ∈ Bd → x ∈ Bd`。
  `Bd` 是泛的，用时取 `Bd := BdM`；`Bd₁` 用的是 `slideEndpointPlane` 的坐标形式
  `(e y).1 = 0`，正是 §53 的 `not_mapsTo_chartSlideFwd_boundaryPlane` 里那个平面。
- `preimage_boundary_subset_frontier_piecewise_postcomp`：**这条是本节的关键不变量。**
  若输入胞腔满足 `D.domain ∩ D ⁻¹' BdM ⊆ frontier D.domain`（"圆盘只在边界圆上碰 `Bd M`"，
  Moise 的对映射 `(Δ,∂Δ) → (M,Bd M)` 的标准正规性条件，比结构字段 `image_inter_boundary`
  的像集等式强，且是关于**输入** `D` 的假设，不是结论型假设），再加 `MapsTo D D.domain N` 与上面那条
  反向条款，则割开后的 `g := P.piecewise (h ∘ D) D` **仍然**满足
  `D.domain ∩ g ⁻¹' BdM ⊆ frontier D.domain`。证明是两支 `piecewise` 拆分：
  `x ∈ P` 支用反向条款把 `h (D x) ∈ BdM` 拉回 `D x ∈ BdM`，`x ∉ P` 支直接用 `hbdpre`。
  换句话说，**原像形式的边界条件在边界分支割开下是封闭的**，等式形式不是。
- `image_inter_boundary_subset_image_frontier_piecewise_postcomp`：上一条的直接推论，
  `g '' D.domain ∩ BdM ⊆ g '' frontier D.domain`。
- `image_inter_boundary_of_collarExtension`：**领环修正的成品。** 设 `G : SingularTwoCell M`
  在 `D.domain` 上与 `g` 相等（`hext`），并满足三条只与"新加的环带"有关的条款
  1. `houter : Set.range G.boundary ⊆ BdM`（外圈落到 `Bd M` 上）；
  2. `hannulus : G '' (G.domain \ D.domain) ∩ BdM ⊆ Set.range G.boundary`（环带只在外圈碰 `Bd M`）；
  3. `hseam : g '' frontier D.domain ∩ BdM ⊆ Set.range G.boundary`（老边界圆上没被推动的那段被带到外圈），
  则 `G '' G.domain ∩ BdM = Set.range G.boundary`，即 `image_inter_boundary` **被恢复**。
  盘面那一半（"圆盘内部不会碰 `Bd M`"）由上面两条提供，是本节真正证出来的部分；
  三条假设全部是环带自身的局部性质，没有一条是结论本身。
  `range_boundary_subset_of_collarExtension` 顺带给出结构字段 `boundary_image_subset`
  （只要 `BdM ⊆ B`）。
- `NormalSingularCellData.exists_separated_cell_boundary_preimage_along_boundary_branch`：
  把上面接到实际的边界分支分离上。输入除 §53 的全部数据外，多要
  `hNE/hN₁/hBdE/hBd₁`（`N` 是闭半空间、`BdM` 是边界平面的图册相容性）、`hDN : MapsTo D D.domain N`
  与 `hbdpre`；输出是 §53 的全部条款，再加上面两条新结论。
- **确切的剩余义务（领环那一条到底缺什么）。** 需要的不是本树已有的任何一条 collar：
  `IsCombinatorialManifoldWithBoundary.exists_collar`（`CollarNeighborhood.lean`）、
  `exists_collar_of_boundary_subset`（`CollarRestriction.lean`）、
  `exists_collar_of_boundary_disk`（`DiskCollar.lean`）与 `BicollarManifold.lean` 的四条
  全部是 `E` 里单纯复形层面的，或者是内部二维子流形的双领环；
  **缺的是下面这个"环带扫掠"**，本树没有任何形式接近它：
  设 `Δ' ⊇ Δ` 是平面里的 PL 2-球，`Δ' \ int Δ ≅ frontier Δ × [0,1]`（**`Δ` 的外领环**，
  本树也没有；`DiskCollar.lean` 给的是 `Bd K` 里的圆盘在 `K` 中的领环，不是平面里球的外领环），
  并设 `Φ` 是 `BdM` 的领环里沿领环线的 PL 扫掠，把被推离的边界弧 `g '' (frontier Δ ∩ P ∩ D ⁻¹' U)`
  拉回 `BdM`；把 `g` 用 `Φ` 沿外领环延拓成 `G`，就得到上面三条 `houter / hannulus / hseam`。
  在本轮的坐标设定下 `Φ` 其实可以就取图册里的直线收缩
  `E.symm (e.symm ((1-t) * (e (E y)).1, (e (E y)).2))`——因为 `BdM` 在图册里就是 `{p.1 = 0}`，
  领环线就是第一坐标线——所以真正缺的只有：(i) 平面 PL 2-球的**外领环**；
  (ii) 把 `g` 与该扫掠沿缝隙粘起来后的 `IsPLOn`、局部单射与纤维 ≤ 2 的转移。
  这两条都是标准 PL 内容，但本树现在一条都没有。
- **一条不能走的路（记下免得重走）：不存在把新边界圆拉回去的环境同胚。**
  `h : M → M` 是 PL 嵌入但**不满**（前推把一块咬掉），所以它可以把 `Bd M` 的点送进内部而不与
  边界不变性矛盾；但任何 `M` 到自身的同胚都保持 `Bd M`，因此**不可能**用后复合一个环境同胚
  把被推进内部的边界弧送回 `Bd M`。修正必须改映射（沿外领环延拓），不能只改 `h`。
  这条排除了"再加一条更强的分离条款"和"在领环里做第二次滑动"两种想法。
- 验证：`BranchSeparationBoundary` 聚焦检查 exit=0（10.4 秒）、`BranchBoundaryCollar` exit=0（10.6 秒），
  均零 warning；审计见 §57 末尾（两节的声明放在同一个审计文件里）。全程无其它 `lean.exe`。

## 57. 2026-09-18 E3-M3：Case 3/4 整条链改走触边分支端点（§52 第 2 条未做项清掉）

状态：done。改动 `BranchComplexityDrop.lean` 与 `BranchCaseThreeFour.lean`，即 §53 里列为"本轮范围未做"的那条。

- `NormalSingularCellData.exists_separated_cell_simplicialComplexity_lt_along_branch`
  改名为 `..._along_boundary_branch`，并改调 §53 的
  `exists_separated_cell_along_boundary_branch`：参数 `hca : c - d < a` 换成 `hbd : b < d`
  （前推滑动把 A 带推过 Q 带，而不是把 A 带拉到 Q 带之前），输出里 §48 的双条件条款
  `∀ x, h x ∈ BdM ↔ x ∈ BdM` 换成三条前推形式：`MapsTo h U U`、半空间条款
  `MapsTo h N N` 与 §56 的反向条款。复杂度下降的证明**一行没改**——
  `exists_simplicialComplexity_lt_of_doublePointSet_subset_sdiff` 只吃
  `hgfib`、`hgdouble`、`hclean`、`hSU`，从不碰边界条款，这与 §53 里逐条核对的结论一致。
- `NormalSingularCellData.exists_four_arc_word_and_simplicialComplexity_lt_of_boundaryBranch`
  同样换参数与条款。它现在**在参数层就只对触边分支成立**（`hbd : b < d` 是触边分支的正规形），
  四段边界字那一支（`exists_boundary_four_arc_word_of_boundaryBranch hc`）原样转出。
  于是 Case 3/4 的整条链——四段字 + 分离胞腔 + 复杂度严格下降——跑在同一个触边分支端点上。
- `BranchComplexityDrop.lean` 的 import 由 `BranchSeparation` 改为 `BranchSeparationBoundary`
  （后者 import 前者，内部分支版本仍可用）。内部分支（Case 1/2）的
  `exists_separated_cell_along_branch` 与 `exists_separated_along_branch` 留在
  `BranchSeparation.lean` 里没动。
- 验证：`BranchComplexityDrop` 聚焦检查 exit=0（10.6 秒）、`BranchCaseThreeFour` exit=0（10.4 秒），
  均零 warning。`.lake/scratch/AuditE3BoundaryCollar.lean`（同时 import
  `BranchBoundaryCollar` 与 `BranchCaseThreeFour`，因此也顺带验证这两支没有重名声明）
  的 11 条 `#print axioms` 全部只含 `propext`、`Classical.choice`、`Quot.sound`。
  全程无其它 `lean.exe`。

## 58. 2026-09-18 E3-M3：§55 的 `hdom` 与 `hfactor` 被 §38 的 double 生产者消掉

状态：done。新模块 `BoundaryWordDoubleCell.lean`（模块名在四条车道分支上都不存在）。
这是 §55 末尾列出的"确切剩余义务"里的第 1 条。

- `NormalSystem.exists_boundary_word_loop_dichotomy_in_double`：在
  `double 3 S.manifoldComplex` 的 charted space 里**取出** §38 的
  `NormalSystem.exists_singular_two_cell_in_double` 给的那个 `D`，于是
  `hdom : D.domain = S.sourceComplex.space` 直接是它的第一条输出；
  `hfactor` 由它的第二条输出 `EqOn (fun x => (D x : E × E × ℝ)) (ι ∘ S.singularMap)
  S.sourceComplex.space` 加上 `ι` 在 `K.space` 上的单射性得到，其中
  `ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)`，单射性由
  `isPLHomeomorphOn_embedComplex K (glueEmbed₂ B id) (glueSnd E E) (fun _ _ _ _ => rfl)`
  的 `.bijOn.injOn` 给出（与 `LemmaTwo.lean` 内部用的是同一条），
  `frontier D.domain ⊆ D.domain = S.sourceComplex.space` 由 `SingularTwoCell.frontier_subset_domain`
  加 `hdom` 给出，两个点都落在 `K.space` 里靠 `S.singularMap_mapsTo_manifoldComplex`。
- 输出形状：`∃ D, D.domain = S.sourceComplex.space ∧ ∀ BdM Bn (hD : NormalSingularCellData D BdM Bn)
  (c : hD.singularSet.Branch), IsBoundaryBranch c → <§55 的四段弧二分>`。
  也就是说 §55 的端点在这两个输入上**已经无条件**；还需要的只有该 `D` 上的
  `NormalSingularCellData`（正规化数据）与一个触边分支，这是另一层的义务，不是本节的缺口。
- 实现上的两个坑（记下免得重走）：
  1. §38 的陈述以 `let K := …; letI : Finite K.faces := …; letI := combinatorialChartedSpace …`
     开头，但两条 `letI` 的实例在 elaboration 时被 zeta 约简掉，目标里**只剩 `K` 一个 `let`**。
     证明里要写 `intro K`（不是 `intro K _ _`），再自己用 `let _ : Finite K.faces := …`
     与 `let _ := combinatorialChartedSpace …` 把两个实例放回局部上下文，否则
     `Finite K.faces` 与 `ChartedSpace (EuclideanSpace ℝ (Fin 3)) ↑(double 3 K).space` 都合成不出来。
  2. 这两条要写 `let _ :=` 而不是 `letI :=`：目标是命题时 `linter.style.haveILetI` 会对 `letI` 报警。
- 未做（保持主人指定的范围）：§43 的障碍仍在，`L₂` 的实际重贴胞腔没做；Case 1/2 未开始。
- 验证：`BoundaryWordDoubleCell` 聚焦检查 exit=0（11.0 秒）、零 warning；
  `.lake/scratch/AuditE3BoundaryCollar.lean`（同时 import `BranchBoundaryCollar`、
  `BranchCaseThreeFour` 与 `BoundaryWordDoubleCell`）的 12 条 `#print axioms` 全部只含
  `propext`、`Classical.choice`、`Quot.sound`。全程无其它 `lean.exe`。

## 59. 2026-09-18 E3-M3：平面 PL 2-球的外部延拓（§56 两条缺口里的第 1 条）

状态：done。新模块 `PlanarBallExterior.lean`（模块名与全部声明名在四条车道分支上都不存在）。
这是 §56 末尾"确切剩余义务"里的 (i)：**平面里 PL 2-球的外领环**。本节把它闭掉，
但交付的形状不是乘积领环 `Δ' \ int Δ ≅ frontier Δ × [0,1]`，而是**外部延拓 + PL 坍缩**，
理由见下面"为什么不是乘积领环"。

- **入口（本树里此前没有找到的那一条）：`PlanarSchoenflies.lean` 的环境化直化定理**
  `exists_isPLHomeomorphOn_straighten_of_isPLBall_two`：任意 `IsPLBall 2 D ⊆ Plane` 都有
  平面自身的 PL 同胚 `h : Plane ≃ₜ Plane`（`IsPLHomeomorphOn h univ univ`）把 `D` 送成一个
  **三角形** `C`，并且 `h '' frontier D = frontier C`、`EqOn h id Uᶜ`。
  §56 记的"本树没有任何形式接近它"对领环本身成立，但**对这条直化定理不成立**——
  有了它，平面外部延拓只需要对三角形做，而三角形上的一切都能显式写出来。
- `exists_exteriorCollapse_of_isPLBall_two`（端点）：对任意 `IsPLBall 2 D ⊆ Plane` 给出
  `D' ⊇ D`、`r : Plane → Plane`、`t : Plane → ℝ`，满足
  `IsPLBall 2 D'`、`D ⊆ interior D'`、`IsPiecewiseAffineOn r D'`、`IsPiecewiseAffineOn t D'`、
  `MapsTo r D' D`、`EqOn r id D`、`MapsTo r (D' \ D) (frontier D)`、
  `frontier D ⊆ r '' frontier D'`、`EqOn t 0 D`、`EqOn t 1 (frontier D')`、
  `∀ z ∈ D', t z ∈ Icc 0 1`。
  `exists_exteriorCollapse_of_isTriangle` 是三角形情形，端点由它经 `h` 搬运得到。
- **三角形模型（显式，无任何单纯复形构造）。** 取仿射基 `b : AffineBasis (Fin 3) ℝ Plane`
  （由 `AffineIndependent` 加 `Fintype.card (Fin 3) = finrank ℝ Plane + 1` 得 `affineSpan = ⊤`），
  重心坐标 `b.coord i` 是仿射映射，`C = {∀ i, 0 ≤ b.coord i}`、`interior C = {∀ i, 0 < b.coord i}`
  （Mathlib 的 `AffineBasis.convexHull_eq_nonneg_coord` 与 `AffineBasis.interior_convexHull`）。
  - `D' := ` 以重心为中心的 4 倍位似像，`exists_isPLBall_two_exteriorBall_of_affineBasis` 证明它
    等于 `{∀ i, -1 ≤ b.coord i}`，内部是 `{∀ i, -1 < b.coord i}`，边界是
    `{∀ i, -1 ≤ b.coord i} ∩ {∃ i, b.coord i = -1}`。关键计算是
    `b.coord i (homothety c 4 z) = 4 * b.coord i z - 1`（`c` 是重心，`b.coord i c = 1/3`）。
  - `planarRetract b z := b 0 + planarClamp (b.coord 1 z) • (b 1 - b 0)
      + min (planarClamp (b.coord 2 z)) (1 - planarClamp (b.coord 1 z)) • (b 2 - b 0)`，
    其中 `planarClamp x = min (max x 0) 1`。这是"先截断第一坐标、再用剩余额度截断第二坐标"的
    **顺序截断**，不是径向投影。
  - `planarSweepParam x y z := planarClamp (-(min x (min y z)))`，即 `t = clamp(-min_i λ_i)`。
  - PL 性完全由 `GeneralPosition.lean` 的 `IsPiecewiseAffineOn.max / .min / .add / .affine_comp`
    组合出来，不需要任何显式的 H-多胞形分片。
- **为什么不是乘积领环（记下免得重走）。** 平面里三角形 `C` 与它的位似放大 `C'` 之间的
  "径向投影"**不是 PL**：仿射映射在有内点的片上纤维必须平行，而从重心出发的射线不平行，
  所以任何有限分片都做不出径向收缩。真正的乘积领环要手工三角剖分环带（每条边两个三角形，
  共 6 片）并逐片给仿射映射，代价远高于本节的顺序截断，而且
  **下游 `image_inter_boundary` 根本不需要单射性**：它只用到
  `MapsTo r (D' \ D) (frontier D)` 与 `frontier D ⊆ r '' frontier D'`。
  因此本节交付坍缩形；若将来需要真正的乘积领环（例如为了 `fiber_le_two`），
  那是另一件事，见下面一条。
- **一条必须记下的负结论：任何"环带 + 沿领环线扫掠"的延拓都不可能保住 `fiber_le_two`。**
  设 `Φ` 是 `Bd M` 的领环扫掠，`G` 在环带上取 `(z, s) ↦ Φ (g z) s`。对已经落在 `Bd M` 上的
  边界点 `z`（即没有被前推滑动推离的那一段，占 `frontier Δ` 的绝大部分），
  `Φ (g z) s = g z` 对一切 `s` 成立，于是整条领环线段 `{z} × [0,1]` 被压成一个点，
  纤维是无限的。**这与领环是否单射无关**，换成真正的乘积领环也一样。
  所以 `NormalSingularCellData` 的 `locallyInjective` 与 `fiber_le_two` 不可能由环带延拓恢复；
  能恢复它们的只有**只贴在被推离弧上的"月牙"（沿弧贴一个圆盘）**，
  `IsPLBall 1 (C ∩ D) → IsPLBall 2 (C ∪ D)`（`BallGluingTwo.lean` / `PlanarDiskUnion.lean`）
  正是月牙的粘合工具。这一条不影响 `image_inter_boundary`（它不要求单射），
  但决定了 §56 第 (ii) 条"缝隙转移"的正确形状。
- 验证：`PlanarBallExterior` 聚焦检查 exit=0（13.2 秒）、零 warning；
  `.lake/scratch/AuditE3PlanarExterior.lean` 的 32 条 `#print axioms` 全部只含
  `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。全程无其它 `lean.exe`。

## 60. 2026-09-18 E3-M3：`houter / hannulus / hseam` 三条全部由扫掠的点态性质推出（§56 第 (ii) 条的可做部分）

状态：partial（三条结论型假设全部消掉；剩下的唯一义务是**扫掠在环带上的 `IsPLOn`**，
它不是结论型假设，见末尾"确切剩余义务"）。新模块 `BranchBoundarySweep.lean`
（模块名与全部声明名在四条车道分支上都不存在）。

- **本节做掉的事。** §56 的 `image_inter_boundary_of_collarExtension` 要三条关于 `G` 的假设
  `houter`（外圈落进 `Bd M`）、`hannulus`（环带只在外圈碰 `Bd M`）、`hseam`（老边界圆上的
  `Bd M` 点被带到外圈）。这三条都是**关于结论的**，所以 §56 只是"有领环修正即得等式"。
  本节把它们全部换成扫掠 `Φ : M → ℝ → M` 的**四条点态性质**：
  `hΦ0 : ∀ y, Φ y 0 = y`、`hΦ1 : ∀ z ∈ frontier D.domain, Φ (g z) 1 ∈ BdM`、
  `hΦfix : ∀ y ∈ BdM, ∀ s, Φ y s = y`、
  `hΦmem : ∀ z ∈ frontier D.domain, ∀ s, Φ (g z) s ∈ BdM → g z ∈ BdM ∨ s = 1`，
  再加 §59 的平面外部延拓数据（`exists_exteriorCollapse_of_isPLBall_two` 无条件给出）。
  四条都是领环收缩的真实局部性质：在图册模型 `Φ y s` 的第一坐标是 `(1-s) * (e (E y)).1`，
  四条逐条成立，且没有一条是"环带只在外圈碰 `Bd M`"这种结论。
- 三条推导（`range_boundary_subset_boundary_of_boundarySweep`、
  `image_sdiff_inter_boundary_subset_of_boundarySweep`、
  `image_frontier_inter_boundary_subset_of_boundarySweep`）的共同机制是
  **`frontier D.domain ⊆ ρ '' frontier Δ'`**：环带上任何落进 `Bd M` 的点 `G x`，
  都能在外圈找到 `x'` 使 `ρ x' = ρ x`，再用 `hΦmem`/`hΦfix` 把 `Φ y (τ x)` 化成 `Φ y 1 = G x'`。
  所以 §59 交付"坍缩形"而不是乘积领环是够用的：**只用到 `ρ` 在外圈上满射到 `frontier D.domain`，
  完全不用单射**。
- `exists_singularTwoCell_of_boundarySweep`：由 `IsPLOn 2 3 g D.domain` 与环带上的
  `IsPLOn 2 3 (fun x => Φ (g (ρ x)) (τ x)) (Δ' \ interior D.domain)` 拼出 `G : SingularTwoCell M`，
  `G.domain = Δ'`，盘上等于 `g`，环带上等于扫掠公式。
- `exists_collarExtension_image_inter_boundary_of_exteriorCollapse`（显式传入 `Δ' ρ τ`）与
  `exists_collarExtension_image_inter_boundary_of_boundarySweep`（`Δ' ρ τ` 由 §59 内部产生）
  是两个成品：输出 `∃ G, D.domain ⊆ G.domain ∧ EqOn G g D.domain ∧
  Set.range G.boundary ⊆ BdM ∧ G '' G.domain ∩ BdM = Set.range G.boundary`。
- **`Pasting` / `SingularPasting` 各自承担了什么（主人问的那一条）。**
  - **承担：缝隙上的 `IsPLOn`。** `Pasting.lean` 的 `IsPLOn.piecewise_of_isClosed`
    正好是缝隙转移：`D.domain`（闭）与 `Δ' \ interior D.domain`（闭）的并是 `Δ'`，
    交是 `frontier D.domain`，两支在交上相等（因为 `ρ = id`、`τ = 0`、`hΦ0`），
    于是 `Set.piecewise` 的 `IsPLOn` 直接得到。本节 `exists_singularTwoCell_of_boundarySweep`
    就是这一行。`PLMap.lean` 的 `IsPLOn.piecewise_postcomp_of_isClosed` 是同一族的后复合版本。
  - **不承担：环带映射自身的 `IsPLOn`。** `SingularPasting.lean` 全部是
    "在二重点附近取 `IsPLBall` 补片"，与扫掠无关。把 `IsPLOn` 与平面上的
    `IsPiecewiseAffineOn` 复合的引理确实存在，但是
    `LoopTheorem/CellGluing.lean:181` 的 `IsPLOn.comp_isPiecewiseAffineOn` 是 **`private`**，
    外部模块用不了；需要时要在本车道重证一份（约 20 行，证明见该处）。
  - **不承担：局部单射与纤维 ≤ 2。** 见 §59 的负结论——环带延拓根本不可能保住 `fiber_le_two`，
    所以这两条不该由缝隙转移来提供，只能靠"月牙"式延拓。本节因此不碰它们，
    也没有把它们写进任何输出条款。
- **一条不能走的路（本轮新发现，覆盖 §56 末尾对 `Φ` 的建议）。**
  §56 建议 `Φ` 取图册里的直线收缩
  `Φ y s = E.symm (e.symm ((1-s) * (e (E y)).1, (e (E y)).2))`。
  作为**逐点定义**它没问题，四条点态性质都成立；但把它代进环带映射后，
  图册坐标的第一分量是 `(1 - τ x) * a x`，其中 `a x = (e (E (g (ρ x)))).1` 与 `τ x`
  都是 `x` 的分片仿射函数——**两个非常值分片仿射函数的乘积，在有内点的片上不是仿射的**，
  所以 `fun x => Φ (g (ρ x)) (τ x)` 在环带上**不是 PL**。
  这与 §59 里"径向投影不是 PL"是同一个现象（仿射映射在有内点的片上纤维必须平行 /
  双线性不是仿射）。因此 `hann` 不能靠直线收缩兑现，必须换成
  **沿被推离弧的棱柱（prism）构造**：把 `ᾱ × [0,1]` 三角剖分，逐片给仿射映射。
  本树已有的 `Prism.lean`、`PrismArc.lean`、`PrismArcPatch.lean`、`PrismProdCollar.lean`
  （特别是 `exists_isPiecewiseAffineOn_prism_of_arcs_height` 与
  `exists_isPiecewiseAffineOn_glue_collar_prod`）是这条路的起点，本轮没有走。
- **确切剩余义务。** 只剩一条，形状是
  `IsPLOn 2 3 (fun x => Φ (P.piecewise (h ∘ D) D (ρ x)) (τ x)) (Δ' \ interior D.domain)`，
  即"扫掠在环带上是 PL"。兑现它需要：(a) 被推离弧 `g '' (frontier Δ ∩ P ∩ D ⁻¹' U)`
  的一个 PL 弧参数化；(b) 该弧与它在 `Bd M` 上的落点之间的棱柱的分片仿射实现
  （`PrismArc*` 一族）；(c) `IsPLOn` 与平面 `IsPiecewiseAffineOn` 复合的公开版引理
  （`CellGluing.lean` 里那条的非 private 副本）。
  其中 **(c) 本节已经做了**：`isPLOn_comp_isPiecewiseAffineOn_of_mapsTo` 与
  `isPLOn_of_isPiecewiseAffineOn_factorization`（后者直接把 `hann` 化成
  “找到平面棱柱区域 `R`、分片仿射的 `μ : Plane → Plane` 与 `IsPLOn 2 3 Ψ R`，
  使 `Ψ ∘ μ` 在环带上等于扫掠公式”），证明照抄 `CellGluing.lean` 那条 private 引理；
  待有独占刷新窗口时应下沉到 `PLMap.lean`。
  未经验证的代价估计：剩下的 (a)+(b) 约 400–900 行、2–4 个工作段；(a) 中等，
  (b) 是主要部分且取决于 `PrismArc*` 现有引理与本处形状的匹配程度（本轮没有逐条核对）。
- 本轮**按主人指定的范围未做**：割开胞腔的 `singularSet` / `crossing`、`L₂` 的重贴胞腔、
  Case 1/2。
- 验证：`BranchBoundarySweep` 聚焦检查 exit=0（10.2 秒）、零 warning；
  `.lake/scratch/AuditE3PlanarSweep.lean`（同时 import `PlanarBallExterior` 与
  `BranchBoundarySweep`，因此也顺带验证两支没有重名声明）的 41 条 `#print axioms`
  全部只含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。全程无其它 `lean.exe`。

## 61. 2026-09-18 E3-M3：§60 的 `hann` 化到弧上棱柱（(a)(b) 两条做掉，`hΦmem` 的棱柱高度分级是唯一剩项）

状态：partial（`hann` 本身已不再是假设：`exists_collarExtension_image_inter_boundary_of_prism_over_arc`
输出与 §60 同一个结论，且不带 `hann`；剩下的唯一未闭合项是棱柱的"只在顶面碰 `Bd M`"，见末尾）。
新模块 `BranchCollarPrism.lean`（模块名与 11 条声明名在四条车道分支上都不存在）。

- **先做主人要求的逐条核对，结论：§60 点名的 `exists_isPiecewiseAffineOn_prism_of_arcs_height`
  不匹配，同一文件里它的祖先 `exists_isPiecewiseAffineOn_prism_of_isPLHomeomorphOn` 完全匹配。**
  `..._of_arcs_height`（`PrismProdCollar.lean:34`）有三条子句对不上本处形状：
  1. `hunion : A ∪ B = J` 与 `hinter : A ∩ B = {p, q}` 要求底面是**圆**（两条弧在两个端点粘起来）。
     本处底面是**一条弧**（被推离弧 `frontier Δ ∩ P ∩ D ⁻¹' U`），无法退化成两弧并。
  2. `(L : SimplicialComplex ℝ F)` 与 `hfaceγ / hfaceκ`：要求一个目标单纯复形，并且每段短子弧的
     四个点 `f (γ a), f (γ b), g (γ a), g (γ b)` 落进**同一个闭面**。本处根本没有这样的 `L`
     （要有就得先把滑移带三角剖分），而真正需要的目标约束只是"留在滑移图卡的凸区域里"。
  3. 结论只有底/顶两条 `Φ (y,0) = f y`、`Φ (y,h) = g y`，**没有端点竖边的控制**。
     把棱柱扇区与常值扇区沿 `ρ ⁻¹ {p,q}` 粘起来恰恰需要竖边子句。
  `exists_isPiecewiseAffineOn_prism_of_isPLHomeomorphOn`（`PrismArc.lean:12`）三条全中：
  单弧 `IsPLHomeomorphOn θ (Icc 0 1) J`；无 `L`、目标约束是**任意凸集**的 `MapsTo` 子句；
  并且给出 `Φ (θ 0, t) = f (θ 0) + t • (g (θ 0) - f (θ 0))`（`θ 1` 同）。
  因此 §60 末尾"400–900 行、2–4 个工作段"的估计（当时明说未核对）被推翻：实际 296 行、一个工作段。
- (a) **被推离弧的 PL 弧参数化。** `isPLBall_one_image_chart_of_isPLOn`：平面弧 `J` 是 `IsPLBall 1`、
  `q` 在 `J` 上 `IsPLOn 2 3`、在 `J` 上单射、像落在图卡 `ec` 的 source 里 ⟹ `IsPLBall 1 ((ec ∘ q) '' J)`；
  `exists_isPLHomeomorphOn_Icc_image_chart_of_isPLOn` 给出 `γ` 与 `IsPLHomeomorphOn γ (Icc 0 1) ((ec ∘ q) '' J)`。
  关键入口是 `PLMap.lean` 的 `isPLOn_iff_isPiecewiseAffineOn_comp_chart`（把 `IsPLOn 2 3` 换成
  图卡坐标里的 `IsPiecewiseAffineOn`，要 `HasGroupoid M (plGroupoid 3)` 与 `MapsTo q J ec.source`）
  加 `PolygonalSchoenflies.lean` 的 `isPLBall_image_Icc_of_isPiecewiseAffineOn` 与
  `exists_isPLHomeomorphOn_Icc_of_isPLBall_one`。**弧本身是弧（`IsPLBall 1 J`）不是可证的，是输入。**
- (b) **弧与它在 `Bd M` 上落点之间的棱柱。** `exists_isPiecewiseAffineOn_prism_arc_landing`：
  底面 `b`（= `ec ∘ q`）在 `J` 上分片仿射、落点用一个仿射映射 `π`（图卡里到边界平面的投影），
  在两个端点上 `π (b (θ i)) = b (θ i)`，则得 `Ψ` 在 `J ×ˢ Icc 0 1` 上分片仿射，
  底 `Ψ (z,0) = b z`、顶 `Ψ (z,1) = π (b z)`、**两条竖边是常值** `Ψ (θ i, t) = b (θ i)`，
  以及对任意凸集的 `MapsTo`。竖边常值正是靠端点固定把 `f + t • (g - f)` 里的差压成 0。
- **环带装配（`hann` 的形状）。** `isPLOn_prism_comp_of_mapsTo_chart`：
  `(ρ, τ)` 在扇区 `A` 上分片仿射且 `MapsTo` 到 `J ×ˢ Icc 0 1`，`Ψ` 落在 `ec.target` 里 ⟹
  `IsPLOn 2 3 (fun x => ec.symm (Ψ (ρ x, τ x))) A`。
  `isPLOn_collarSweep_of_prism_over_arc`：环带切成两个多面体扇区 `A`（在弧上）与 `B`（不在弧上），
  `A` 上等于上式、`B` 上等于 `q ∘ ρ`（由 `isPLOn_of_isPiecewiseAffineOn_factorization`，即 §60 的 (c)），
  用 `IsPLOn.piecewise_of_isClosed` 粘起来。
  **缝隙上的 `EqOn` 是免费的**：两支都写成同一个 `F x` 的等式，交上两条同时成立，直接得相等——
  这就省掉了"棱柱竖边 = 常值"的单独核对（那条仍由 (b) 提供，供调用者兑现 `hΦprism`）。
  `isPLOn_boundarySweep_annulus_of_prism` 把它写成 §60 `hann` 的**逐字形状**
  `IsPLOn 2 3 (fun x => Φ (P.piecewise (h ∘ D) D (ρ x)) (τ x)) (Δ' \ interior D.domain)`。
- **扫掠的生产者（`Φ` 不再是参数）。** `prismSweep q J ec Ψ y s :=`
  `if y ∈ q '' J then ec.symm (Ψ (invFunOn q J y, s)) else y`（`InjOn q J` 给 `prismSweep_of_mem`）。
  `exists_boundarySweep_of_prism_over_arc` 一次给出 §60 的四条点态性质加 `hann`：
  `hΦ0` 用棱柱底 `Ψ (z,0) = ec (q z)` 与 `ec.left_inv`；`hΦfix` 用"弧像不碰 `Bd M`"；
  `hΦ1` 弧上用棱柱顶、弧外用 `q z ∈ Bd M`；`hΦmem` 弧外走左析取、弧上走 `hmeet`。
  `exists_collarExtension_image_inter_boundary_of_prism_over_arc` 接上 §60 的
  `exists_collarExtension_image_inter_boundary_of_exteriorCollapse`，输出
  `∃ G, G.domain = Δ' ∧ EqOn G g D.domain ∧ range G.boundary ⊆ BdM ∧ G '' G.domain ∩ BdM = range G.boundary`，
  **不再带 `hann`**。`frontier D.domain` 的多面体性由 `IsPLBall.isPLSphere_frontier` 得到。
- **确切剩余义务（唯一一条）。** `hmeet : ∀ z ∈ J, ∀ s : ℝ, ec.symm (Ψ (z, s)) ∈ BdM → s = 1`，
  即"棱柱只在顶面碰 `Bd M`"。它**在几何上对现有棱柱构造成立**，算式是显式的：
  `PrismMap.lean` 的 `prismSquareMap` 在上三角是 `(1-t) a + (t-l) c + l d`、
  下三角是 `(1-l) a + (l-t) b + t d`，顶面两点 `c, d` 的权重之和恰好是 `t`；
  取图卡里割出 `Bd M` 的线性泛函 `ℓ`（`ℓ c = ℓ d = 0`、`ℓ a, ℓ b < 0`）得
  `ℓ (prismSquareMap _ z) ≤ (1 - z.2) * max (ℓ a) (ℓ b) ≤ 0`，等号迫使 `z.2 = 1`。
  **但现有 API 取不到它**：`PrismHomotopy.lean` 的 `exists_isPiecewiseAffineOn_prism` 的胞腔子句是
  `Φ z ∈ convexHull {f (s i), f (s (i+1)), g (s i), g (s (i+1))}`，**内部高度信息被丢掉**，
  只能推出 `ℓ (Φ z) ≤ 0`，推不出 `< 0`。本轮试过三条绕路（把凸集换成 `F × ℝ` 里的半空间、
  把高度塞进第二分量、把 `ℓ` 塞进第二分量），都因为 `Φ` 的第二分量与 `z.2` 没有联系而失败。
  **正确的下一步是把胞腔子句升级成分级形式**：
  `(Φ z, z.2) ∈ convexHull {(f (s i), 0), (f (s (i+1)), 0), (g (s i), 1), (g (s (i+1)), 1)}`
  （`PrismInterval.lean` 的 `exists_isPiecewiseAffineOn_prism_of_partition` 一路到
  `PrismHomotopy.lean` 与 `PrismArc.lean`）。这三个文件不是本车道的，按 `AGENTS.md` §4
  应该协调后改，不单方面动。
- 另外两条**输入而非缺口**（调用者提供，不是本节欠的）：`IsPLBall 1 J`（被推离弧确实是一条弧，
  取决于 `frontier Δ ∩ P ∩ D ⁻¹' U` 的连通性）与环带的多面体扇区分解 `A ∪ B = Δ' \ interior D.domain`
  （§59 的显式三角形模型里可以直接写出来）。
- 本轮**按主人指定的范围未做**：割开胞腔的 `singularSet` / `crossing`、月牙构造、`L₂` 的重贴胞腔、
  Case 1/2。§60 的两条负结论（直线收缩不是分片仿射；环带延拓保不住 `fiber_le_two` /
  `locallyInjective`）已在案，本轮未重走。
- 验证：`BranchCollarPrism` 聚焦检查 exit=0（10.6 秒）、零 warning；
  `.lake/scratch/AuditE3CollarPrism.lean` 的 11 条 `#print axioms` 全部只含
  `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。全程无其它 `lean.exe`。

## 62. 2026-09-18 E3-M3：`hmeet` 用"对既有棱柱做水平校正"闭掉，环带扇区的多面体分解补齐，§61 的一处真空假设修好

状态：done（`hmeet` 不再是假设；端点 `exists_collarExtension_image_inter_boundary_of_levelPrism_over_arc`
只剩几何输入）。新模块 `BranchCollarPrismLevel.lean`、`CollarSectorPolyhedron.lean`
（模块名与 19 条新声明名在四条车道分支上都不存在）。

- **主人要求的第 1 步（谁丢掉了 witness）。** `PrismMap.lean` 是**定义层**：`prismSquareMap`、
  `prismStripMap`、`verticalPrismAffine` 与它们的 `*_mem_convexHull` 都是可加引理的对象。
  **第一个丢掉 witness 的层是 `PrismInterval.lean:44` 的
  `exists_isPiecewiseAffineOn_prism_of_partition`**：它内部的 `key : ∀ k ≤ n, ∃ Φ, …` 是
  **存在量词上的归纳**，每一步从 `ih` 取出一个 witness 再用 `Set.piecewise` 粘，
  所以拼好的棱柱在任何地方都不是一个具名函数。它上面的
  `PrismHomotopy.lean:13`、`PrismArc.lean:12/70`、`PrismProdCollar.lean:34` 只是转发这个存在量词。
  因此"关于那张棱柱映射的分级胞腔引理"在 `PrismInterval` 及以上都写不出来，
  对那个文件的最小改动是把 `key` 与定理的结论多加一条
  `(Φ z, z.2) ∈ convexHull {(f (s i), 0), (f (s (i+1)), 0), (g (s i), 1), (g (s (i+1)), 1)}`
  （保留原 `himg`，投影即得，故不破坏任何 consumer）。**但本轮不需要它，见下。**
- **进一步的负结论：就算加了分级子句，也推不出 `hmeet`。** 端胞腔是退化的：
  弧的端点落在边界平面上（`ℓ a = 0`），而 `π` 固定它，于是 `c = π a = a`，
  `prismSquareMap` 的上三角 `a + t(c-a) + l(d-c) = a + l(d-a)` **与 `t` 无关且整片落在 `{ℓ = 0}`**。
  所以对端胞腔内部的底点（`q z ∉ Bd M`）存在 `s < 1` 使 `Ψ (z,s) ∈ Bd M`，`hΦmem` 对
  三角剖分棱柱**本身就是假的**。分级子句只把界改进到 `ℓ ≤ (1 - z.2) · max (ℓ a) (ℓ b)`，
  在 `ℓ a = 0` 的端胞腔上仍然只给 `≤ 0`。
- **真正的可加解法（本轮走的）：对既有棱柱做一次水平校正，全部写在自己的模块里。**
  取图卡里割出 `Bd M` 的线性泛函 `ℓ` 与 `ℓ n = 1` 的向量 `n`：
  - `boundaryDrop ℓ n := (LinearMap.id - ℓ.smulRight n).toAffineMap`，即 `w ↦ w - ℓ w • n`，
    这就是"落到边界平面"的仿射映射，`ℓ (boundaryDrop w) = 0`，且在 `ℓ w = 0` 处是恒等。
    §61 的 (b) 里那个抽象的 `π` 现在有了显式取法。
  - `arcLevel ℓ c b (z,s) := min (c * |1 - s|) (-(ℓ (b z)))`，
    `levelPrism ℓ n c b Φ (z,s) := Φ (z, planarClamp s) + (-(ℓ (Φ (z, planarClamp s)) + arcLevel …)) • n`。
    `planarClamp` 来自 §59。**校正后 `ℓ (levelPrism … (z,s)) = -(arcLevel … (z,s))` 是恒等式**
    （`apply_levelPrism`），于是
    `ℓ (Ψ (z,s)) = 0 ↔ c|1-s| = 0 ∨ ℓ (b z) = 0 ↔ s = 1 ∨ q z ∈ Bd M`，**对一切实数 `s`**。
    这正是 `hΦmem`。`|1 - s|`（不是 `1 - s`）保证 `s > 1` 一侧也不碰边界；
    `planarClamp` 保证底面那一侧只用到棱柱在 `[0,1]` 上的已知子句，
    于是**两条竖边对一切实数 `s` 都是常值**，`hΦfix` 也随之成立。
    这两处正是 §61 里直接用 `min (…) 0` 或 `-(1-s)c` 会互相冲突的地方。
  - 底/顶不变：`s = 0` 时 `arcLevel = -ℓ (b z)`（要 `-ℓ (b z) ≤ c`，即弧的深度有上界 `c`），
    校正量为 0，`Ψ (z,0) = b z`；`s = 1` 时 `arcLevel = 0`，`Ψ (z,1) = boundaryDrop (b z)`。
  - `MapsTo` 由 `levelPrism_eq_boundaryDrop_sub`（`Ψ = boundaryDrop (Φ …) - arcLevel • n`）
    加 `arcLevel ∈ [0, c]` 给出，而且**对一切实数 `s` 都成立**（clamp 把底点留在棱柱里），
    所以 `hΦmem` 里那个"对一切 `s`"的量词不再有漏洞。
  - 分片仿射性只用 `GeneralPosition.lean` 的 `.min / .abs / .add / .affine_comp / .prod_mk`
    与 `PLHomeomorph.lean` 的 `.mono_of_isPolyhedron`，**没有碰任何 `Prism*` 文件**。
  端点 `exists_collarExtension_image_inter_boundary_of_levelPrism_over_arc` 输出与 §60/§61 相同的
  `∃ G, G.domain = Δ' ∧ EqOn G g D.domain ∧ range G.boundary ⊆ BdM ∧ G '' G.domain ∩ BdM = range G.boundary`，
  **既不带 `hann` 也不带 `hmeet`**。
- **修好 §61 的一处真空假设（必须记下）。** §61 的 `exists_boundarySweep_of_prism_over_arc` 里
  `hJoff : ∀ z ∈ J, q z ∉ BdM` 与 `hBbd`、`hmapA` 合起来**强迫 `A ∩ B = ∅`**，
  而 `A`、`B` 是覆盖环带的两个闭多面体，环带连通 ⟹ 必有一个是空的，
  在目标构型（`J` 是真子弧）里假设集不可满足。
  原因是几何上**弧的两个端点必然落在 `Bd M` 上**（滑移在弧端渐变为零）。
  现改成 `hfixJ : ∀ z ∈ J, q z ∈ BdM → ∀ s, ec.symm (Ψ (z,s)) = q z`，
  并把 `hmeet` 的结论改成 `q z ∈ BdM ∨ s = 1`（与 `hΦmem` 逐字一致）。
  两条都由 §62 的水平校正棱柱的竖边子句兑现。
- **环带扇区的多面体分解（§61 列为"输入"的第 2 条，本轮补齐）。**
  `CollarSectorPolyhedron.lean`：
  - `IsPiecewiseAffineOn.isPolyhedron_inter_preimage_of_isPolyhedron`：`f` 在多面体 `P` 上分片仿射、
    `Q` 是多面体 ⟹ `P ∩ f ⁻¹' Q` 是多面体。证明用
    `PiecewiseAffineSimplicial.lean` 的 `exists_isSubdivision_affineOn_faces` 取出**有限**的
    单纯剖分（每个闭面上 `f` 等于一个仿射映射），再用 `Polytope.lean` 的
    `IsHPolytope.inter_preimage` 逐面逐块。（`ChartPolyhedron.lean` 的
    `isPolyhedron_of_isCompact_of_eventuallyEq` 是 `private`，本轮没走那条路。）
  - `exists_polyhedral_sectors_of_isPiecewiseAffineOn`：`Δ'`、`D` 是 PL 2-球、`ρ` 在环带上分片仿射、
    `J ∪ Jc` 盖住 `ρ` 的像 ⟹ 给出 `A = 环带 ∩ ρ ⁻¹' J`、`B = 环带 ∩ ρ ⁻¹' Jc`，
    两个多面体、并等于环带、`MapsTo` 与 `IsPiecewiseAffineOn` 齐全。
    环带本身的多面体性直接用树里已有的 `IsPolyhedron.sdiff_interior_of_isPLBall`（`BallComplement.lean`），
    不需要 §59 的三角形模型，比 §61 里估计的路线短。
- **`hJ : IsPolyhedron J` 也消掉了**：由 `hθ` 经 `(isPLBall_Icc _).of_isPLHomeomorphOn hθ` 得到。
  于是 §61 列的两条输入里只剩一条真正的几何输入：**被推离弧是一条弧**（`IsPLHomeomorphOn θ (Icc 0 1) J`），
  它取决于 `frontier Δ ∩ P ∩ D ⁻¹' U` 的连通性，不是本层能证的。
- 其余几何输入（都在端点的假设里，都是滑移模型的直接性质）：
  `hBd`（图卡里 `Bd M ↔ ℓ = 0`）、`hle/hge`（弧在边界平面下方、深度 ≤ c）、
  `hend0/hend1`（弧端在边界平面上）、`hends`（弧上只有两个端点在边界平面上）、
  `hS/hbS/hdS/hslab`（滑移图卡的凸区域与它到边界平面的板状邻域落在 `ec.target` 里）。
- 本轮**按主人指定的范围未做**：割开胞腔的 `singularSet` / `crossing`、月牙构造、`L₂` 的重贴胞腔、
  Case 1/2。
- 验证：`BranchCollarPrism`（改后）、`BranchCollarPrismLevel`、`CollarSectorPolyhedron`
  三个聚焦检查全部 exit=0（10.3 / 11.1 / 9.8 秒）、零 warning；
  `.lake/scratch/AuditE3CollarPrismLevel.lean` 的 30 条 `#print axioms` 全部只含
  `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。全程无其它 `lean.exe`。

## 63. 2026-09-18 E3-M3：被推离弧确实是一条弧（`IsPLBall 1 J` 在本层可证），剩下的只有"被推离集连通"

状态：done（`IsPLHomeomorphOn θ (Icc 0 1) J` 不再是假设，由 `IsConnected W` 加两条平凡条件推出）。
新模块 `DisplacedArcConnected.lean`（模块名与 6 条声明名在四条车道分支上都不存在）。

- **先做核对，结论：圆层已经把需要的东西都给了，不必新证任何弧识别定理的核心。**
  `ArcSubset.lean` 有两条正好接得上的：
  - `IsPLSphere.exists_isPLBall_one_superset_of_ssubset`：PL 1-球面的**闭真子集**被某条弧包住；
  - `IsPLBall.isPLBall_one_of_isCompact_of_isConnected`：弧里的**紧致、连通、非平凡**子集**本身就是弧**
    （不要求该子集是多面体）。
  两条串起来即 `IsPLSphere.isPLBall_one_of_isClosed_of_isConnected_of_ssubset`：
  **PL 1-球面里闭、连通、非平凡的真子集是一条弧**。`CircleIntersection.lean` 与
  `ArcDecomposition.lean` 是另一类问题（自交点、不交弧覆盖），本处用不上。
- **取 `J := closure W`，其中 `W` 是被推离集 `{z ∈ frontier D.domain | g z ∉ Bd M}`。**
  `IsPLSphere.isPLBall_one_closure_of_isConnected_of_ssubset` 与
  `IsPLSphere.exists_isPLHomeomorphOn_Icc_closure_of_isConnected_of_ssubset` 由
  `IsConnected W`、`W.Nontrivial`、`closure W ⊂ frontier D.domain` 直接给出 `θ`。
  `frontier D.domain` 是 PL 1-球面用 `IsPLBall.isPLSphere_frontier`。
  取闭包是必须的：`W` 由"滑移量 ≠ 0"切出来，是相对开集，不闭。
- **`sdiff_subset_endpoints_of_isConnected_of_closure_eq`：`closure W \ W ⊆ {θ 0, θ 1}`。**
  证明不走同胚搬运，直接在 `E` 里做：设 `z ∈ J \ W` 且 `z ≠ θ 0, θ 1`，记 `t = invFunOn θ _ z`。
  `invFunOn θ _` 在 `J` 上连续且单射，所以 `invFunOn θ _ '' W` 连通且不含 `t`，
  由 `IsPreconnected.subset_or_subset`（`Iio t`、`Ioi t`）落进一侧；
  那一侧的闭包 `J ∩ invFunOn θ _ ⁻¹' Iic t` 是闭集（`ContinuousOn.preimage_isClosed_of_isClosed`），
  于是 `J = closure W` 落进去，与 `invFunOn θ _ (θ 1) = 1 > t` 矛盾（另一侧对称）。
  这条把端点 `hends` 从"θ 相关"化成"θ 无关"：
  `hends z hz h = hJW ⟨hz, (hWdisp z hz).mp h⟩`。
- **`exists_isPLHomeomorphOn_Icc_displacedArc_of_isConnected`**（胞腔版）与
  **`exists_collarExtension_image_inter_boundary_of_displacedArc`**（接上 §62 端点）：
  后者只保留 `hconn : IsConnected W` 与 `hθ`（由前者产生），把 §62 的
  `hends` 完全消掉，`hend0 / hend1` 化成 `θ 0 ∉ W`、`θ 1 ∉ W`
  （经 `hWdisp : ∀ z ∈ closure W, ℓ (ec (g z)) = 0 ↔ z ∉ W`）。
- **确切剩余义务与它所属的层。** 只剩 **`IsConnected W`**，即
  `IsConnected (frontier D.domain ∩ {z | P.piecewise (h ∘ D) D z ∉ BdM})`，
  通俗说"胞腔边界圆与该分支的滑移支撑交成一段区间"。
  **本层证不出来**：`W` 是 `frontier D.domain ∩ P ∩ (e ∘ E ∘ D) ⁻¹' {p | |p.2.1| + |p.2.2| < 1}`，
  即边界圆与一个开凸区域的交，圆可以反复进出支撑，连通性不是拓扑必然。
  它属于**选取 `U`、`P`、`h` 的分支分离层**：
  `BranchSeparationBoundary.lean:175` 的 `exists_separated_cell_along_boundary_branch`
  与 `BranchBoundaryCollar.lean` 里的边界包装
  `exists_separated_cell_boundary_preimage_along_boundary_branch`，
  应作为它们输出条款里的一条新结论加进去（那里有 `hA : D '' P ∩ support ⊆ … slideBandA c`
  与 `hinjP : InjOn D P`，但两条都只是包含关系，不蕴含连通）。
  其余两条 `W.Nontrivial`、`closure W ⊂ frontier D.domain` 同层，且是"该分支非空且不吞掉整条边界圆"，
  在分支分离的构造里显然。`θ 0 ∉ W`、`θ 1 ∉ W` 是"滑移在弧端渐变为零"，同层同理。
- **`NormalSingularCellData` 六条字段对当前状态的准确清单**（主人要的目标重述）：
  - `image_inter_boundary`：**已恢复**。就是本链端点的结论
    `G '' G.domain ∩ BdM = Set.range G.boundary`（§56 → §60 → §62 → §63）。
  - `boundary_image_subset`：**已恢复**（`Set.range G.boundary ⊆ BdM`，再用 `BdM ⊆ B` 经
    `range_boundary_subset_of_collarExtension`）。
  - `locallyInjective`、`fiber_le_two`：**不可能由领环延拓恢复**，§59 的负结论：
    对已在 `Bd M` 上的边界点 `z`，`Φ (g z) s = g z` 对一切 `s`，整条径向线段压成一点，纤维无限。
    只有**月牙**（只沿被推离弧贴一个圆盘）能恢复它们。（本轮范围外。）
  - `singularSet`：**同样被领环破坏**。`doublePointSet G G.domain` 除了原有的还包含整段
    `g '' (frontier D.domain \ closure W)`（上一条的压缩造成），所以
    `map_space : piece.map '' complex.space = doublePointSet G G.domain` 对 `G` 不成立。
    它也只能在月牙版本上谈。
  - `crossing`：**未触及且非边界专有**。它是双点集上的局部法向交叉标准形，与本链无关；
    在月牙版本上要重新给。
  - 结论：**领环延拓的作用就是给出边界条款那两条**，它与单射性三条互斥；
    下一轮的正确目标是月牙（沿 `closure W` 贴 2-胞腔），不是继续加强领环。
- 本轮**按主人指定的范围未做**：月牙、`L₂` 的重贴胞腔、Case 1/2。
- 验证：`DisplacedArcConnected` 聚焦检查 exit=0（10.7 秒）、零 warning；
  `.lake/scratch/AuditE3DisplacedArc.lean` 的 6 条 `#print axioms` 全部只含
  `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。全程无其它属于本车道的 `lean.exe`。

## 64. 2026-09-18 E3-M3：`IsConnected W` 归位到分支分离层（位移判据在生产者处被证出来），月牙的接口

状态：step 1 done（`IsConnected W` 不再悬在两层之间；位移判据是**已证的输出条款**，
连通性本身是**分离层的显式假设**，且写成 `h` 出现之前的图卡形式）；
step 2 只做了 grep 与接口陈述，没有动工（月牙是一个项目，不是一轮，见末尾）。
改动文件：`BranchSeparationBoundary.lean`、`BranchBoundaryCollar.lean`、`BranchComplexityDrop.lean`
（三个都是本车道的）。无新模块。

- **位移判据（新输出条款，已证，不是假设）。** `exists_separated_slide_fwd` 的结论末尾加一条：
  给定边界模型 `hBdE / hBd₁` 与 `0 < d`、`0 < R`，对一切 `x ∈ Bd`，
  `h x ∉ Bd ↔ x ∈ E.source ∧ E x ∈ e.source ∧ |(e (E x)).2.1| + |(e (E x)).2.2| < 1`。
  证明是直接计算：`h = E.conjugateMap (e.conjugateMap (slideMapFwd d R))`，
  在两层图卡里 `e (E (h x)) = slideMapFwd d R (e (E x))`，第一坐标是
  `(e (E x)).1 + slideAmountLong d R (e (E x))`，而 `x ∈ Bd` 给 `(e (E x)).1 = 0`，
  于是 `h x ∈ Bd ↔ slideAmountLong d R (e (E x)) = 0`；再把 `slideAmountLong` 展开成
  `max 0 (min (d * (1 - |p.2.1| - |p.2.2|)) ((R - |p.1|)/2))`，`|p.1| = 0` 使 taper 项为 `R/2 > 0`，
  所以它为零当且仅当 `1 ≤ |p.2.1| + |p.2.2|`。两个退化情形（`x ∉ E.source`、`E x ∉ e.source`）
  都给 `h x = x ∈ Bd`，与右边同时为假。
  这条顺着 `exists_separated_along_boundary_branch`（term-mode 转发）与
  `exists_separated_cell_along_boundary_branch` 传下去；`BranchComplexityDrop` 的 obtain 多一个 `-`。
- **连通性归位。** `exists_separated_cell_boundary_preimage_along_boundary_branch` 新增
  `hdpos : 0 < d`、`hRpos : 0 < R` 与
  `hconnA : IsConnected (frontier D.domain ∩ P ∩ {z | D z ∈ E.source ∧ E (D z) ∈ e.source ∧
    |(e (E (D z))).2.1| + |(e (E (D z))).2.2| < 1})`，
  新增输出条款 `IsConnected {z | z ∈ frontier D.domain ∧ P.piecewise (h ∘ D) D z ∉ BdM}`。
  两者之间的集合等式由位移判据加"边界圆整体落在 `Bd M` 上"
  （`hD.image_inter_boundary` ⟹ `range D.boundary ⊆ BdM`）逐点得出：
  `z ∉ P` 时 `piecewise = D z ∈ BdM`，不在左边也不在右边；`z ∈ P` 时两边由判据互推。
  **一句话说生产者还要证什么**：边界圆 `frontier D.domain` 与该分支滑移截面的开 ℓ¹-球
  `{|p.2.1| + |p.2.2| < 1}` 的交（先经 `D`、`E`、`e` 拉回，再交上 `P`）是**连通的**，
  即"边界圆与滑移支撑交成一段区间"。它不是拓扑必然（圆可以反复进出支撑），
  只能由分支的具体选取给出，所以留在分离层作显式假设是正确的归位，而不是缺口下沉。
- **月牙的 grep 结果（动工前的核对，主人要求）。**
  - **引擎已经有了**：`LoopTheorem/CellGluing.lean:375`
    `exists_glue_of_isPLHomeomorphOn_boundary_arc`：两个 `SingularTwoCell` `D₁`、`D₂`，
    一条 `IsPLBall 1 A ⊆ frontier D₁.domain`、`IsArcBetween A a₀ a₁`、
    `IsPLHomeomorphOn g A B`、`B ⊆ frontier D₂.domain`、`EqOn D₁ (D₂ ∘ g) A`，
    输出单个 `SingularTwoCell D`，`D.domain = P ∪ Q` 是 `IsPLBall 2`，
    `IsPLHomeomorphOn f₁ P D₁.domain`、`IsPLHomeomorphOn f₂ Q D₂.domain`、
    `EqOn D (D₁ ∘ f₁) P`、`EqOn D (D₂ ∘ f₂) Q`，并给出新边界的割对结构
    `frontier D.domain = R ∪ T` 与四个端点的对应。**正好是"沿一条边界弧贴一个 2-胞腔"。**
    `BallGluingTwo.lean` 的 `isPLBall_union_of_boundary_arc_of_ambient` 与
    `IsCombinatorialManifoldWithBoundary.isPLBall_union_of_inter_isPLBall_one` 是它的平面粘合底层。
    `CrosscutExtension.lean`、`BoundaryDiskExtension.lean`、`DiskCrosscutExtension.lean`
    是割线/边界片的 PL 同胚延拓，属于 `D₂` 的构造工具，不是粘合本身。
    `CutAndPaste.lean` 不存在。
  - **引擎不给的**：`exists_glue_of_isPLHomeomorphOn_boundary_arc` 只给域层与 `EqOn`，
    `NormalSingularCellData` 的四条都要另证。
  - **月牙的确切接口（下一轮的目标陈述）。**
    消费：(i) 分离后的盘映射 `g = P.piecewise (h ∘ D) D`，连同已交付的
    `IsPLOn`、`IsLocallyInjective`、`fiber_le_two`、`doublePointSet` 下降；
    (ii) 被推离弧 `closure W ⊆ frontier D.domain`（§63 已产出，`IsPLBall 1` 且有参数化）；
    (iii) 一个**月牙胞腔** `D₂`：`IsPLBall 2 D₂.domain`，其边界分成弧 `B`（经 `γ` 与
    `closure W` 匹配且 `EqOn g (D₂ ∘ γ) (closure W)`）与互补弧（像落在 `Bd M` 里）；
    (iv) **新的几何假设：月牙是嵌入的且只沿该弧碰旧胞腔**，即
    `D₂ '' (D₂.domain \ B) ∩ g '' D.domain = ∅` 与 `InjOn D₂ D₂.domain`。
    恢复：`image_inter_boundary` 与 `boundary_image_subset`（新边界 `R ∪ T`：
    `R` 来自旧边界去掉 `closure W` 的部分，已在 `Bd M` 里；`T` 是月牙外弧，按 (iii) 在 `Bd M` 里）；
    `locallyInjective` 与 `fiber_le_two`（两片各自成立，交叉纤维由 (iv) 排除）；
    `singularSet`（由 (iv) 得 `doublePointSet D' D'.domain = doublePointSet g D.domain`
    经 `f₁` 搬运，后者已等于 `doublePointSet D D.domain \ branchCarrier cb`）。
  - **唯一缺的通用引理**：`crossing` 的**源侧**搬运。
    `SingularNormalForm.lean` 只有 `HasPLNormalDoubleCrossingAt.postcomp_openPartialHomeomorph`
    （目标侧后复合），没有沿源侧 PL 同胚 `f₁ : P ≃ D.domain` 的前复合版本，
    而 `crossing` 的陈述是关于 `e ∘ D` 在**源平面子集**上的，所以必须新证一条
    `HasPLNormalDoubleCrossingAt.precomp_isPLHomeomorphOn`。这是月牙里唯一的通用层新引理。
  - **结论：月牙是一个项目而不是一轮**（域层引擎已有，但四条字段的恢复加上源侧搬运引理
    与 (iv) 的几何输入，是完整的一轮以上）。按主人给的回退条款，本轮交付 step 1 与本接口，停在此处。
- 验证：`BranchSeparationBoundary`、`BranchComplexityDrop`、`BranchBoundaryCollar` 以及全部下游
  `BranchBoundarySweep`、`BranchCollarPrism`、`BranchCollarPrismLevel`、`DisplacedArcConnected`、
  `BranchCaseThreeFour` 共 8 个聚焦检查全部 exit=0、零 warning
  （11.7 / 12.2 / 11.0 / 10.5 / 10.8 / 11.6 / 10.8 / 11.4 秒）；
  `.lake/scratch/AuditE3BranchDisplacement.lean` 的 5 条 `#print axioms` 全部只含
  `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。

## 65. 2026-09-18 E3-M3：法向双点交叉的**源侧**搬运（月牙的第一块，独立可复用）

状态：done。新模块 `SingularCrossingPrecomp.lean`（模块名与 6 条声明名在四条车道分支上都不存在）。

- **先答主人的问题：目标侧的证明骨架不转移，源侧确实不一样。**
  `SingularGeneralPosition.lean:3438` 的 `HasPLDoubleCrossingAt.postcomp_openPartialHomeomorph`
  **完全不动源侧的见证** `a, b, A, B`，只把目标侧的数据推过 `e`，
  所以它只需要现成的 `IsPLHomeomorphOn.postcomp_openPartialHomeomorph` 与
  `HasPLCrossingAt.image_openPartialHomeomorph`。
  源侧必须**把见证拉回**：`a' = invFunOn φ Q a`、`A' = Q ∩ φ ⁻¹' A`（`B` 同）。
- **一度以为的障碍，以及它为什么不是障碍（记下免得重走）。**
  拉回后要 `IsPLHomeomorphOn (f ∘ φ) A' ((f ∘ φ) '' A')`。若先把 `φ` 限制到 `A'` 再复合，
  就需要 `IsPiecewiseAffineOn φ A'`，而 `IsPiecewiseAffineOn` 的限制只对**多面体或开集**成立
  （`mono_of_isPolyhedron` / `mono`），偏偏定义里的 `A` 只是 `𝓝[P] a` 里的一个邻域，
  既不开也不是多面体。定义无法记录这条正则性，改定义又要动 `SingularGeneralPosition.lean`。
  **不必走那条路**：直接对复合用 `IsPiecewiseAffineOn.comp`，
  `hfA.isPiecewiseAffineOn.comp hφ.isPiecewiseAffineOn` 的定义域正好是 `Q ∩ φ ⁻¹' A = A'`，
  根本不需要限制 `φ`。逆映射同理：`invFunOn (f ∘ φ) A'` 在 `f '' A` 上等于
  `invFunOn φ Q ∘ invFunOn f A`（两边都落在 `A'` 里且被 `f ∘ φ` 送到同一点，用 `A'` 上的单射性），
  而后者由两条 `isPiecewiseAffineOn_invFunOn` 复合得到。所以**不需要收缩见证，也不需要多面体性**。
- 交付的三条（外加三条可复用的辅助）：
  - `image_inter_preimage_of_bijOn`：`BijOn φ Q P`、`A ⊆ P` ⟹ `φ '' (Q ∩ φ ⁻¹' A) = A`。
  - `isPLHomeomorphOn_comp_inter_preimage`：上面那条复合引理。
  - `mem_nhdsWithin_inter_preimage`：`A ∈ 𝓝[P] a` ⟹ `Q ∩ φ ⁻¹' A ∈ 𝓝[Q] (invFunOn φ Q a)`
    （用 `ContinuousWithinAt.tendsto_nhdsWithin`，`ContinuousOn φ Q` 来自分片仿射）。
  - `HasPLDoubleCrossingAt.precomp_isPLHomeomorphOn`、
    `HasPLBoundaryDoubleCrossingAt.precomp_isPLHomeomorphOn`、
    `HasPLNormalDoubleCrossingAt.precomp_isPLHomeomorphOn`：
    `IsPLHomeomorphOn φ Q P` ⟹ 交叉性质从 `(f, P)` 搬到 `(f ∘ φ, Q)`，
    **目标侧的 `y`、`Bd`、`f '' A`、`f '' B` 全部不变**，所以交叉子句原样保留。
    纤维覆盖子句也原样：`x ∈ Q`、`f (φ x) = z` ⟹ `φ x ∈ P ∩ f ⁻¹' {z} ⊆ A ∪ B` ⟹ `x ∈ A' ∪ B'`。
  三条都是 `φ : G → E` 的一般形式（源可以换空间），不含任何月牙专有内容。
- 验证：`SingularCrossingPrecomp` 聚焦检查 exit=0（10.5 秒）、零 warning；
  `.lake/scratch/AuditE3CrossingPrecomp.lean` 的 6 条 `#print axioms` 全部只含
  `propext`、`Classical.choice`、`Quot.sound`（`image_inter_preimage_of_bijOn` 连
  `Classical.choice` 都不用），无 `sorryAx`。

## 66. 2026-09-18 E3-M3：月牙第二块——粘合胞腔的 `boundary_image_subset`，以及嵌入输入的确切写法

状态：partial（四条字段里第一条 `boundary_image_subset` 闭合；停在第二条
`image_inter_boundary` 的 `⊆` 半边，见末尾"确切下一步"）。
新模块 `GluedCellBoundaryImage.lean`（模块名与 2 条声明名在四条车道分支上都不存在）。

- **`image_sdiff_subset_of_cutPair`**：`IsPLHomeomorphOn f P C`（`P`、`C` 闭）加
  `IsCutPair (frontier P) p q A₁ A₂` ⟹ `A₂ ⊆ frontier P`、`f '' A₂ ⊆ frontier C`，
  并且 `A₂` 上只有 `p`、`q` 两点的像落进 `f '' A₁`。
  用 `PLHomeomorphTopology.lean` 的 `IsPLHomeomorphOn.image_frontier`（同维、两端闭）
  与 `IsCutPair` 的 `union_eq / inter_eq`，加 `f` 在 `P` 上的单射性。
- **`range_boundary_subset_of_glue_boundary_arc`**（第一条字段）：
  输入是 `exists_glue_of_isPLHomeomorphOn_boundary_arc` 的输出原样
  （`IsPLBall 2 P/Q`、`IsPLHomeomorphOn f₁ P D₁.domain`、`f₂`、`EqOn D (D₁ ∘ f₁) P`、
  `EqOn D (D₂ ∘ f₂) Q`、两个 `IsCutPair`、`frontier D.domain = R ∪ T`、
  `f₁ '' (P ∩ Q) = A`、`f₂ '' (P ∩ Q) = B`），加四条几何输入
  `hD₁bd`（旧边界圆去掉被推离弧后落在 `Bd M`）、`hD₂bd`（月牙外弧落在 `Bd M`）、
  `hend₁`、`hend₂`（弧的两个端点在 `Bd M`）；结论 `Set.range D.boundary ⊆ BdM`。
  证法：`frontier D.domain = R ∪ T`，`R ⊆ frontier P ⊆ P` 上 `D = D₁ ∘ f₁`，
  `f₁ '' R ⊆ frontier D₁.domain`；若 `f₁ z ∈ A` 则由割对的 `inter_eq` 得 `z ∈ {p, q}`，
  走端点条款，否则走 `hD₁bd`。`T` 侧对称。
  配合 `BranchBoundaryCollar.lean` 已有的 `range_boundary_subset_of_collarExtension`
  （`BdM ⊆ B'`），`NormalSingularCellData.boundary_image_subset` 即得。
- **嵌入输入的确切写法（主人要的 step 3，按 `hconnA` 的风格，生产者能兑现的形式）。**
  不写成抽象的"月牙嵌入"，而写成两条可检查的条款：
  - `hD₂inj : InjOn D₂ D₂.domain`（月牙本身是嵌入的 2-胞腔，不是奇异的）；
  - `hD₂disj : ∀ x ∈ D₂.domain, x ∉ B → ∀ y ∈ D₁.domain, D₂ x ≠ D₁ y`
    （月牙除了粘合弧 `B` 以外不碰旧胞腔的像；写成逐点不等式而不是集合不交，
    是为了让生产者直接用月牙所在的图卡坐标去验，与 `hconnA` 同风格）。
  这两条正是 `locallyInjective` 与 `fiber_le_two` 在两片之间唯一缺的东西：
  片内的单射性与纤维界由 `D₁`（已交付）与 `hD₂inj` 给出，
  跨片纤维由 `hD₂disj` 排除；`singularSet` 的
  `doublePointSet D D.domain = doublePointSet D₁ D₁.domain` 经 `f₁` 搬运也只用这两条。
- **确切下一步（停在这里的理由）。** 第二条字段 `image_inter_boundary` 的 `⊇` 半边由上面这条
  加 `range D.boundary ⊆ D '' D.domain` 直接得到；`⊆` 半边还差一条几何输入：
  **被推离弧的像只在两个端点碰 `Bd M`**，写成
  `hAoff : ∀ z ∈ A, D₁ z ∈ BdM → z = f₁ p ∨ z = f₁ q`。
  这与 §63 的 `hWdisp`（`ℓ (ec (g z)) = 0 ↔ z ∉ W`）是同一件事，只是换到 `A = closure W` 的坐标里，
  所以它不是新缺口，但要把 §63 的形式搬过来。
  有了它，`⊆` 半边的论证是：`P` 的内点经 `D₁` 落进 `Bd M` 时，由 `D₁` 自己的
  `image_inter_boundary` 得它在 `frontier D₁.domain` 上，于是它的 `f₁` 原像在
  `frontier P = (P ∩ Q) ∪ R` 里；`R` 已在 `frontier D.domain` 里，
  `P ∩ Q` 的点由 `hAoff` 只能是 `p`、`q`，而 `p, q ∈ (P ∩ Q) ∩ R ⊆ R` 也在 `frontier D.domain` 里。
  `Q` 侧对称，另需月牙自己的 `D₂ '' D₂.domain ∩ BdM ⊆ D₂ '' frontier D₂.domain`。
  这一条与其后的 `locallyInjective / fiber_le_two / singularSet / crossing`
  （后者用 §65 的 `HasPLNormalDoubleCrossingAt.precomp_isPLHomeomorphOn` 沿 `f₁` 搬运）
  是下一轮的内容。
- 验证：`GluedCellBoundaryImage` 聚焦检查 exit=0（10.0 秒）、零 warning；
  `.lake/scratch/AuditE3GluedBoundary.lean` 的 2 条 `#print axioms` 只含
  `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。

## 67. 2026-09-18 E3-M3：粘合胞腔的 `image_inter_boundary`（四条字段里的第二条）

状态：done。`GluedCellBoundaryImage.lean` 新增 2 条声明（名字在四条车道分支上都不存在）。

- **`mem_range_boundary_of_mem_frontier_glue`**：`w ∈ frontier D₁.domain` 且 `D₁ w ∈ BdM` ⟹
  `D₁ w ∈ Set.range D.boundary`。关键是**不需要** `f₁ x ∈ frontier D₁.domain`
  （`D₁` 是奇异胞腔，不单射，所以 `D₁ '' D₁.domain ∩ BdM ⊆ D₁ '' frontier D₁.domain`
  只给"某个边界点取到同一个值"，不给原像在边界上）。
  用 `image_frontier` 把 `w` 写成 `f₁ z`（`z ∈ frontier P = S ∪ R`），
  `z ∈ R` 直接完；`z ∈ S` 时 `f₁ z ∈ A` 且 `D₁ (f₁ z) ∈ BdM`，由 `hAoff` 得 `z ∈ {p, q}`，
  而 `p, q ∈ S ∩ R ⊆ R` 也在 `frontier D.domain` 里。
  形参把缝隙集写成一般的 `S`（不是 `P ∩ Q`），于是 `T` 侧原样复用，不必 `inter_comm`。
- **`image_inter_boundary_of_glue_boundary_arc`**：`D '' D.domain ∩ BdM = Set.range D.boundary`。
  `⊇` 由 §66 的 `range_boundary_subset_of_glue_boundary_arc` 加
  `frontier D.domain ⊆ D.domain`；`⊆` 按 §66 末尾写的论证，两片各用一次上面那条。
- **`hAoff` 的来历（主人问的"能不能不是新假设"）。**
  `hAoff : ∀ z ∈ A, D₁ z ∈ BdM → z = f₁ p ∨ z = f₁ q` 与 §63 的
  `hends : ∀ z ∈ closure W, ℓ (ec (g z)) = 0 → z = θ 0 ∨ z = θ 1` 是同一条，
  只差把弧的参数化端点 `θ 0, θ 1` 与割点的像 `f₁ p, f₁ q` 认同。
  `CellGluing.lean:305` 的 `IsPLHomeomorphOn.maps_arc_endpoints` 正是做这件事的
  （两条 `IsArcBetween` 加一个 PL 同胚 ⟹ 端点成对对应，可能交换），
  所以**它不是新缺口**；但要真正消掉这个形参，还差一步
  "`IsPLHomeomorphOn θ (Icc 0 1) A` ⟹ `IsArcBetween A (θ 0) (θ 1)`"。
  本轮按割点 `f₁ p, f₁ q` 的形式留作形参（调用者用上面两条一行兑现），没有引入新的数学缺口。
- 验证：`GluedCellBoundaryImage` 聚焦检查 exit=0（11.1 秒）、零 warning。

## 68. 2026-09-18 E3-M3：粘合胞腔的 `fiber_le_two` 与 `locallyInjective`（第三、四条字段）

状态：done。新模块 `GluedCellInjectivity.lean`（模块名与 4 条声明名在四条车道分支上都不存在）。

- **嵌入输入按 §66 step 3 的写法用上了**：`hD₂inj : InjOn D₂ D₂.domain` 与
  `hD₂disj : ∀ x ∈ D₂.domain, x ∉ B → ∀ z ∈ D₁.domain, D₂ x ≠ D₁ z`。
- `mem_seam_of_image_mem_of_injOn`：`f₂` 在 `Q` 上单射、`f₂ '' S = B` ⟹
  `x ∈ Q` 且 `f₂ x ∈ B` ⟹ `x ∈ S`。这条把"月牙点落在粘合弧上"翻译成"它在缝隙里"，
  是 `hD₂disj` 能用的前提。
- **`fiber_le_two_of_glue_boundary_arc`**：对每个 `y` 分两种情形。
  若某个 `x ∈ Q` 满足 `D x = y` 且 `f₂ x ∉ B`，则 `hD₂disj` 把 `P` 一侧的纤维清空，
  剩下的落在 `Q` 里，由 `hD₂inj` 与 `f₂` 的单射性得**纤维至多一点**（`encard_le_one_iff`）。
  否则 `Q` 一侧的纤维点的 `f₂` 像都在 `B` 里，由上一条它们都落在缝隙 `P ∩ Q ⊆ P` 里，
  于是整条纤维落在 `P` 中，经 `f₁` 的单射像等于 `D₁.domain ∩ D₁ ⁻¹' {y}`，用 `D₁` 的界。
- **`locallyInjective_of_glue_boundary_arc`**：`x ∈ P`（含缝隙点）时取
  `U = (P ∩ W) ∪ (Q \ P)`，其中 `W` 是把 `D₁` 的单射邻域 `V` 拉回的开集
  （拉回用 §65 的 `mem_nhdsWithin_inter_preimage`，再用 `invFunOn f₁ P (f₁ x) = x`）。
  `U ∈ 𝓝[P ∪ Q] x` 因为 `W ∩ (P ∪ Q) ⊆ U`。`U` 上的单射性分三种：
  两点都在 `P ∩ W` 用 `V` 上的 `D₁` 单射加 `f₁` 单射；两点都在 `Q \ P` 用 `hD₂inj`；
  一点在 `P`、一点在 `Q \ P` 由 `hD₂disj` 直接排除（`hcross`）。
  `x ∈ Q \ P` 时用 `P` 是 PL 2-球故闭，取 `U = Q \ P`，单射性全由 `hD₂inj` 给出。
  `injOn_of_subset_second_piece` 是 `Q` 的任意子集上单射性的公共出口。
- 验证：`GluedCellInjectivity` 聚焦检查 exit=0（10.5 秒）、零 warning。

## 69. 2026-09-18 E3-M3：粘合胞腔的 `singularSet`（第五条字段）与 `crossing` 的确切障碍

状态：partial（`singularSet` 闭合；**`crossing` 不闭合**，原因不是证明缺口而是缺一条
我无法当场验证可满足性的几何输入，按主人的规矩停在这里不弱化字段）。
`GluedCellInjectivity.lean` 新增 3 条声明（名字在四条车道分支上都不存在）。

- `mem_first_piece_of_glue_boundary_arc`：`P ∪ Q` 里两个不同点取同一值时，两点**都在 `P` 里**。
  （落在 `Q \ P` 的点与 `P` 的点由 `hD₂disj` 不可能同值；两点都在 `Q \ P` 时由 `hD₂inj` 推出相等。）
- `doublePointSet_of_glue_boundary_arc`：`doublePointSet D D.domain = doublePointSet D₁ D₁.domain`。
  `⊆` 用上一条把见证拉到 `P` 里再经 `f₁`；`⊇` 把 `D₁` 的见证经 `f₁` 的满射拉回 `P`。
- `normalSingularSetTriangulation_congr`：`NormalSingularSetTriangulation` 的八个字段里
  只有 `map_space` 与 `map_boundary` 提到 `D`，而且**只通过 `doublePointSet D D.domain`**，
  所以双点集相等时整份三角剖分可以原样搬过去。于是 `singularSet` 由上一条直接得到。
- **`crossing` 的确切障碍（记下，不要重走）。** 想法是用 §65 的
  `HasPLNormalDoubleCrossingAt.precomp_isPLHomeomorphOn` 沿 `f₁` 把 `D₁` 的交叉搬到 `D`。
  搬运本身没问题，**卡在定义域上**：`crossing` 的集合参数是 `D.domain ∩ D ⁻¹' e.source`，
  它含有 `Q` 一侧的点，而 `f₁` 只是 `P ≃ D₁.domain`，不是这两个集合之间的 PL 同胚。
  `HasPLDoubleCrossingAt` 的纤维覆盖子句 `∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} ⊆ A ∪ B`
  要求 **`y` 附近的纤维完全避开 `Q \ P`**。这不是自动的：缝隙点 `s ∈ P ∩ Q` 是 `Q \ P` 的极限点，
  所以 `y` 附近的 `z` 的纤维可以含 `Q \ P` 的点，除非 `y` 与月牙有正距离。
  兑现它需要一条形如
  `hD₂far : ∀ y ∈ doublePointSet D₁ D₁.domain, y ∉ closure (D₂ '' D₂.domain)`
  的**新几何输入**。在目标构型里它**大概率成立**（被推离弧在边界圆上，而 `g` 的双点集是
  §50/§52 的分支割除后的内部集合），但我**没有当场验证它的可满足性**——
  而今天正好有两个"看着可满足其实不成立"的例子（F 车道的盘状片、本车道 §61 的 `hJoff`），
  所以按主人的规矩不写进去。下一轮应先在分支分离层确认
  `doublePointSet (P.piecewise (h ∘ D) D) D.domain` 与 `closure W` 的位置关系，
  再决定 `hD₂far` 的正确形状（可能是"双点集与 `closure W` 有正距离"，
  也可能要把月牙做得足够细，使 `D₂ '' D₂.domain` 落在 `Bd M` 的一个不含双点的邻域里）。
- **当前 `NormalSingularCellData` 五条字段的状态与假设清单（主人要的表）。**
  已闭合 5 条中的 5 条里的 4 条字段 + 1 条结构：
  `boundary_image_subset`（§66）、`image_inter_boundary`（§67）、
  `fiber_le_two`、`locallyInjective`（§68）、`singularSet`（本节）；未闭合：`crossing`。
  假设逐条标注（**几何输入** = 生产者必须去验的；**构造产物** = 粘合定理自己给出的）：
  - `hPball / hQball / hf₁ / hf₂ / hDP / hDQ / hcutP / hcutQ / hdom / hfrontier / hA / hB`
    ——全部是**构造产物**，`exists_glue_of_isPLHomeomorphOn_boundary_arc` 的输出原样，
    可满足性不用验（它们就是那条定理的结论）。
  - `hD₁bd`（旧边界圆去掉弧后落在 `Bd M`）——**几何输入**，即 §62 的 `hfr`，
    可满足：`D '' frontier D.domain ⊆ BdM` 加滑移只动 `closure W`。
  - `hend₁ / hend₂`（弧端在 `Bd M`）——**几何输入**，即 §62 的 `hend0/hend1`，
    可满足：滑移量在弧端渐变为零（§64 的位移判据给出等价刻画）。
  - `hD₂bd`（月牙外弧落在 `Bd M`）——**几何输入**，由月牙的构造保证。
  - `hAoff / hBoff`（弧只在两端碰 `Bd M`）——**几何输入**，即 §63 的 `hends`，
    可满足性与 §63 同；§67 记了它与割点像的认同只差 `maps_arc_endpoints` 一步。
  - `hD₁img / hD₁fib / hD₁loc`——**几何输入但已经有产者**：分别是 `D₁` 自己的
    `image_inter_boundary`（§60 的领环链给出）、`fiber_le_two`、`locallyInjective`
    （分支分离 `exists_separated_cell_along_boundary_branch` 直接输出）。
  - `hD₂inj / hD₂disj`——**几何输入**，§66 step 3 的写法。
    可满足性检查：两者**不互相矛盾也不强制空集**（与 §61 的 `hJoff` 不同）：
    `hD₂disj` 只约束 `D₂.domain \ B` 上的点，而 `B = f₂ '' (P ∩ Q)` 是 `frontier Q` 的一条弧，
    `D₂.domain \ B` 非空且其像可以整体落在 `Bd M` 的另一侧；缝隙上两支公式一致，
    §68 的三条证明里没有任何一条要求 `A ∩ B = ∅` 这类会逼出空集的条件。
- 验证：`GluedCellInjectivity` 聚焦检查 exit=0（10.9 秒）、零 warning；
  `.lake/scratch/AuditE3GluedFields.lean` 的 11 条 `#print axioms` 全部只含
  `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。

## 70. 2026-09-18 E3-M3：分离后的双点集与滑移支撑邻域**不交**，于是 `crossing` 要的输入换了形状

状态：step 1 done，step 2 done（形状定了），step 3 未做（缺三族通用引理，见末尾）。
新模块 `BranchDoublePointSeparation.lean`（模块名与 3 条声明名在四条车道分支上都不存在）。

- **step 1 的结论，而且它不是新输入。** 分支分离层本来就有
  `hclean : doublePointSet D D.domain ∩ W ⊆ branchCarrier cb`（**假设**）与
  `hgdouble : doublePointSet (P.piecewise (h ∘ D) D) D.domain =
   doublePointSet D D.domain \ branchCarrier cb`（**结论**）。
  两条一合：
  `doublePointSet (P.piecewise (h ∘ D) D) D.domain ∩ W = ∅`。
  即**分离后的胞腔的双点集与整个滑移支撑邻域 `W` 不交**——
  比"离月牙远"强得多，而且**完全不需要新的几何输入**，纯是已有两条的集合代数
  （`doublePointSet_inter_eq_empty_of_eq_sdiff`、`disjoint_doublePointSet_of_eq_sdiff`、
  以及取 `f = D`、`g = P.piecewise (h ∘ D) D` 的
  `NormalSingularCellData.disjoint_doublePointSet_separated_of_subset_nbhd`）。
- **step 2：`crossing` 要的输入因此换了形状，也变弱了。**
  §69 里我拒绝写的那条
  `∀ y ∈ doublePointSet D₁ D₁.domain, y ∉ closure (D₂ '' D₂.domain)`
  **形状是错的**：它把条件挂在双点集上（不可当场验证），而真正该约束的是**月牙**。
  正确的输入是 `hluneW : D₂ '' D₂.domain ⊆ W`，即
  **月牙建在滑移支撑的那个邻域 `W` 里面**——这本来就是月牙该待的地方
  （被推离弧的像落在 `U ⊆ closure U ⊆ W` 里，月牙沿它贴到 `Bd M`），
  是一条**构造要求**，生产者建月牙时直接满足，不是关于双点集位置的断言。
  有了它，step 1 直接给
  `Disjoint (doublePointSet (P.piecewise (h ∘ D) D) D.domain) (D₂ '' D₂.domain)`。
  另外 §69 里那条还**多要了一个闭包**：`D₂.domain` 是 PL 2-球（紧），`D₂` 连续，
  `M` 是 T2，所以 `D₂ '' D₂.domain` 本身就闭，`closure` 是多余的。
- **step 3 未做，缺的是三族通用引理（已按"数一数再读"的规矩清点）。**
  把 `D₁` 在 `y` 处的 `crossing` 搬到粘合胞腔要五步：
  (1) 把源集合从 `D₁.domain ∩ D₁ ⁻¹' e.source` **放大**到 `D₁.domain`
      （靠 `e.source` 开、`D₁` 连续）；
  (2) 沿 `f₁ : P ≃ D₁.domain` 用 §65 的 `precomp_isPLHomeomorphOn`（这一步现成）；
  (3) 用 `EqOn D (D₁ ∘ f₁) P` 把函数从 `e ∘ D₁ ∘ f₁` 换成 `e ∘ D`；
  (4) 把源集合从 `P` **放大**到 `D.domain`（靠上面的 `Disjoint`，
      `D₂ '' D₂.domain` 闭且不含 `y`，所以 `y` 附近的纤维避开 `Q \ P`）；
  (5) 把源集合从 `D.domain` **缩小**到 `D.domain ∩ D ⁻¹' e.source`
      （**免费**：缩小 ambient 集合只会让 `𝓝[·]` 变细，而见证 `A, B` 在第 (2) 步后
      自动落在 `D ⁻¹' e.source` 里，因为它们的 `f₁` 像在 `D₁ ⁻¹' e.source` 里）。
  对这三个谓词清点现有引理，命中共 9 条：`postcomp_openPartialHomeomorph` ×3、
  §65 的 `precomp_isPLHomeomorphOn` ×3、`congr_target` ×1、
  `fiber_subset_frontier` 与 `fiber_subset_frontier_of_comp_openPartialHomeomorph` 各 1。
  **源集合的 `mono`（放大，带两条局部条件）、源集合的 `mono_subset`（缩小，免费）、
  以及源函数的 `congr` 都不存在**（只有目标集合的 `congr_target`）。
  这三族各要给 `HasPLDoubleCrossingAt` 与 `HasPLBoundaryDoubleCrossingAt` 两个版本
  再加法向版的分情形，是下一轮的内容；放大版的两条条件是
  `∀ a ∈ Pd, f a = y → ∃ V ∈ 𝓝 a, Pd' ∩ V ⊆ Pd` 与
  `∀ᶠ z in 𝓝 y, Pd' ∩ f ⁻¹' {z} ⊆ Pd`，第 (1)、(4) 步各兑现一次。
- 验证：`BranchDoublePointSeparation` 聚焦检查 exit=0（10.1 秒）、零 warning。
