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
