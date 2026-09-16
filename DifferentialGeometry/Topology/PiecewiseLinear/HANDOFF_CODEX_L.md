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
