# C 车道交接（§24 覆盖空间：C.1–C.3），接替 E3 车道的剩余义务

交接日期 2026-09-15。本文件是接手者的唯一入口。E3.2/E3.3 因表示层缺口（Moise 35.2 需要局部有限、可非紧的多面体
流形，见 §0.1）搁置；本车道转做 `PHASE3_APPROXIMATION_PLAN.md` §4.4 的 C.1、C.2、C.3，它们现在没有阻塞。

## 0. 任务与顺序

砖 C0（收尾 E3 的两件小事）→ 砖 C.1（24.1–24.4 的桥接）→ 砖 C.2（24.5 的组合构造：有限复形上的 ℤ₂ 1-上循环 ⟹
二重覆盖）→ 砖 C.3（24.6：三角剖分提升到有限覆盖，组合流形性保持）。C.4/C.5 需要车道 H（H.2、H.5），不做；
C.6（CST）视进度，先把 24.9 的陈述写进计划行再动手。

### 0.1 E3.2 的记录（只记录，不做）

Moise 36.1 的整体 PLH `f` 来自把 35.2 用于整个开集 `U`，而 `U` 靠 8.2 的**局部有限**三角剖分才是多面体；紧致穷竭
（`ExhaustionGeneral.lean`）只用于最后证 `f(U) = h(U)`。本树 `IsPolyhedralManifoldWithBoundary` 是有限片、必紧致，
所以 35.2 无法忠实陈述；对每个 `N i` 分别用紧致版得到互不兼容的 `f_i`。此缺口由计划 §8 R5 预警；解决方案
（F6.3：有限片上升塔、内核不再重分）留待车道 E 开工前设计。

## 1. 环境与硬规则

- 工作树 `D:\differential-geometry-moise-e3`，分支 `codex/moise-e3`（已含 E3.0、E3.1；继续在此分支提交并推送同名远程分支）。
  不合并进其它分支；绝不碰 main；不 force-push。
- 另两个 Codex 分别在 `D:\differential-geometry-moise-plan`（F 车道）和 `D:\differential-geometry-moise-s`（S 车道）：
  不要进入它们的目录；不改共享检出 `E:\differential-geometry-dev` 的源码或分支；不运行 `lake build`；不登记根聚合。
- 主机 Lean 进程配额 4 个，三条车道各 1 个：你**同时只跑 1 个**。
- 验证只用 `D:\differential-geometry-moise-e3\.lake\scratch\tools\` 的 `check-f.ps1`/`audit-f.ps1`（`$root` 指向本工作树，
  olean 写进共享库）。
- `AGENTS.md`（= `CLAUDE.md`）：零注释零 docstring；无 `sorry`/`axiom`/`nolint`/`maxHeartbeats`/`set_option`；
  Mathlib 标准 linter 集零警告；提交信息用英文描述数学结果。含 `IsCombinatorialManifold*`/`geometricLink` 的定理
  写成 `open Classical in theorem …`，不带 `[DecidableEq E]`，证明里 `classical`。
- 计划 D4：复用本树 `Topology/Covering/*`、`Topology/VanKampen/*` 或 Mathlib 覆盖 API 的每条声明，**首次使用时单独
  `#print axioms`**，结果记入 `MOISE_PLAN.md` §6（Phase 2 审计发现树中有 sorry 支撑的链；`Topology/Homology/HurewiczLowDegrees.lean`
  含 sorry，任何经它的链都不能用）。
- 不弱化目标：陈述按 §4 给的形式；证不出时报告确切缺口。
- 状态登记：`E:\differential-geometry-dev\WORKING_STATUS.md` 末尾加 "Moise smoothing C(Codex) 2026-09-15"（只编辑不提交）。

## 2. 验证配方

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File D:\differential-geometry-moise-e3\.lake\scratch\tools\check-f.ps1 `
  -Module DifferentialGeometry.Topology.PiecewiseLinear.CoveringLift *> D:\differential-geometry-moise-e3\.lake\scratch\cl.log
$env:PYTHONIOENCODING='utf-8'; python D:\differential-geometry-moise-e3\.lake\scratch\tools\errblocks.py D:\differential-geometry-moise-e3\.lake\scratch\cl.log
powershell -NoProfile -ExecutionPolicy Bypass -File D:\differential-geometry-moise-e3\.lake\scratch\tools\audit-f.ps1 -File '.lake/scratch/AuditC1.lean'
```
exit=0、零错误零警告；审计每条 `depends on axioms: [propext, Classical.choice, Quot.sound]`。
Moise 原书 `.lake/scratch/moise_gtm47.pdf`（书页 p = PDF 页 p+10；§24 在书页 174–181，§7 的 7.1 抽象复形实现在 52–57）。

## 3. 可用材料

Mathlib（`Mathlib/Topology/Homotopy/Lifting.lean`，命名空间 `IsCoveringMap`，`cov : IsCoveringMap p`）：
`exists_path_lifts`、`liftPath γ e γ_0 : C(I, E)`、`liftPath_lifts`、`liftPath_zero`、`eq_liftPath_iff`、`liftPath_trans`、
`liftHomotopy`/`liftHomotopyRel`、`homotopicRel_liftPath`、`liftPath_apply_one_eq_of_homotopicRel`、`monodromy`（道路同伦类作用于纤维）、
`liftPathQuotient`、`monodromy_bijective`、`monodromyPerm (x) : FundamentalGroup X x →* Equiv.Perm (p ⁻¹' {x})`、
`injective_path_homotopic_map (e₀ e₁ : E)`（24.2 的核心：覆盖映射在道路同伦类上单射）、
`existsUnique_continuousMap_lifts [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]`（24.1 的 2-胞腔提升）、
`existsUnique_continuousMap_lifts_of_range_le`（24.3 型提升判据：像子群包含于 `π₁` 的像）；`Mathlib/Topology/Covering/*`：
`IsCoveringMap`、`IsCoveringMap.isLocalHomeomorph`、`Trivialization`、`IsEvenlyCovered`。

本树（`DifferentialGeometry/Topology/Covering/`，33 文件，无 sorry；`VanKampen/`，51 文件，无 sorry；命名空间见各文件首行）：
- `BoolCocycle.lean`：`structure BoolCocycle (ι) (B) [TopologicalSpace B]`（`baseSet : ι → Set B` 开覆盖、`indexAt`、
  `parity : ι → ι → B → Bool`、`parity_self`、`continuousOn_parity`、`parity_comp`（xor 上循环条件））、
  `toFiberBundleCore : FiberBundleCore ι B Bool`、`isCoveringMap_proj : IsCoveringMap C.toFiberBundleCore.proj`、
  `exists_continuous_section`、`Coorientation`、`nonempty_coorientation`。
- `DoubleCoverComponents.lean`：`clopen_image_eq_univ`、`projection_homeomorph_of_clopen_split`、
  `exists_two_projection_homeomorphs_of_not_connected`、`exists_section_of_not_connected_double_cover`、
  `exists_exactly_two_components_of_not_connected`（二重覆盖不连通 ⟺ 有截面 ⟺ 平凡）。
- `Lifting.lean`（`discrete_fiber`、`lifts_unique`、`exists_unique_path_lift`、`squareLift`…）、`Sheets.lean`（`sheet (t : Trivialization F p) (o : F) : OpenPartialHomeomorph E B`、`sheet_disjoint`）、
  `SimplyConnectedCover.lean`（`homeomorphOfSimplyConnected`）、`Section.lean`、`FiniteDeckGroup.lean`、
  `SemilocallySimplyConnected.lean`（`manifold_semilocallySimplyConnectedSpace`）、`VanKampen/SimplyConnectedUnion.lean`
  （`simplyConnectedSpace_of_open_cover`）。
- PL 层：`OpenStar.lean`（`openStar K p = K.space \ avoidingUnion K p`、`isClosed_avoidingUnion`、`exists_vertex_mem_openStar`）、
  `Star.lean`（`closedStar`、`closedStar_mem_nhdsWithin`）、`Mesh.lean`（`exists_isSubdivision_diam_lt`、`iteratedBarycentricSubdivision`）、
  `Combinatorial.lean`（`exists_isSubdivision_closedStar_subset`：细分到每个闭星落在给定开覆盖的一员内——正是 24.6 需要的"足够细"）、
  `SimplexComplex.lean`/`SimplexBoundary.lean`（`simplexComplex T hT`、`stdVertices n`：标准单形的顶点）、`Subcomplex.lean`（`restrict`）、
  `SimplicialMap.lean`（`simplicialMap`、`isPLHomeomorphOn_simplicialMap`）、`Gluing.lean`（`IsGlueIso`）、`StarComplex.lean`
  （`IsGlueIso.isPLHomeomorphOn`）、`ManifoldWithBoundary.lean`（`IsGlueIso.isCombinatorialManifoldWithBoundary`、`IsGlueIso.isCombinatorialManifold`）、
  `FaceLink.lean`（`mem_geometricLink_faces_iff`）、`PLBallSphere.lean`（`IsPLHomeomorphOn.homeomorph : P ≃ₜ Q`）、
  `SimplexBall.lean`（`isPLBall_convexHull_of_affineIndependent`）、`VertexChart.lean`/T1（`combinatorialManifoldPLStructure`）。
- 抽象复形实现：`Topology/SimplicialComplex/OrderedSimplicialSet.lean`（`PreAbstractSimplicialComplex ι`、`link`、`facesOfCard`、`cofaces`）、
  `GeometricRealizationHomeomorphism.lean`（有限几何复形的实现同胚）。对 C.3 更简单的做法：有限顶点集 `V`（`Fintype`）上的
  抽象复形直接实现为标准单形复形 `simplexComplex (stdVertices)` 的子复形（顶点 `v ↦ Pi.single v 1`，面 = 抽象面的像），
  `restrict`/`simplexComplex` 已给出所有复形公理。

## 4. 砖块

### 砖 C0 收尾

1. `BoundaryInvariance.lean` 第 67、72、73、103、104 行的 `letI`/`haveI` 改为 `let`/`have`（重编译当前有 5 条 "Try this" 警告），
   重新检查并提交。
2. 计划记录留到最后一次提交（见 §5）。

### 砖 C.1 `CoveringLift.lean` —— 24.1–24.4 桥接（约 1k）

```lean
-- 24.1：PL 2-球（更一般：PL 球）上的映射沿覆盖唯一提升
theorem IsPLBall.simplyConnectedSpace [FiniteDimensional ℝ E] {n : ℕ} {D : Set E} (hD : IsPLBall n D) : SimplyConnectedSpace D
theorem IsPLBall.locPathConnectedSpace … : LocPathConnectedSpace D
theorem IsCoveringMap.exists_unique_lift_of_isPLBall {X̃ X : Type*} [TopologicalSpace X̃] [TopologicalSpace X] {p : X̃ → X}
    (hp : IsCoveringMap p) [FiniteDimensional ℝ E] {n : ℕ} {D : Set E} (hD : IsPLBall n D) (f : C(D, X)) (x₀ : D) (e₀ : X̃)
    (h₀ : p e₀ = f x₀) : ∃! g : C(D, X̃), p ∘ g = f ∧ g x₀ = e₀
-- 24.2：诱导同态单射（用 Mathlib `injective_path_homotopic_map`；给出 `FundamentalGroup` 形式）
theorem IsCoveringMap.injective_fundamentalGroup_map (hp : IsCoveringMap p) (e : X̃) :
    Function.Injective (FundamentalGroup.map? …)      -- 以 Mathlib 现有的 π₁ 映射 API 为准，写成消费者能用的形式
-- 24.3：闭道路可提升为闭道路 ⟺ 其类在像子群中（Mathlib `existsUnique_continuousMap_lifts_of_range_le` 或 monodromy 直接给）
theorem IsCoveringMap.liftPath_one_eq_iff_mem_range …
-- 24.4：连通全空间的 k-重覆盖 ⟹ 像子群指标为 k（`monodromyPerm` 的轨道–稳定子；先证纤维上作用传递）
theorem IsCoveringMap.card_fiber_eq_index [PathConnectedSpace X̃] [PathConnectedSpace X] (hp : IsCoveringMap p) (x : X) (e : X̃) (he : p e = x) :
    Nat.card (p ⁻¹' {x}) = (image subgroup of π₁(X̃, e) in π₁(X, x)).index
```
路线：PL 球 `D ≃ₜ stdSimplex`（`IsPLHomeomorphOn.homeomorph`）；`stdSimplex` 凸紧非空 ⟹ `Convex.contractibleSpace` ⟹ 单连通；
局部道路连通经同胚搬运（凸集的 `LocPathConnectedSpace`：搜索 Mathlib，缺则用凸性与球邻域证）。24.4 用
`monodromyPerm` 的轨道 = 纤维（全空间道路连通 ⟹ 任意两纤维点由道路相连，投影为闭道路）与稳定子 = 像子群，
`MulAction` 的轨道–稳定子（`MulAction.card_orbit_mul_card_stabilizer_eq_card_group` 或 `Subgroup.index` 版本）。
消费者只在 `k = 2` 用（§25 L.4："`g*` 指标 2 不满"），若一般 `k` 太重，先给 `k = 2` 的精确形式并记录。

### 砖 C.2 `DoubleCoverComplex.lean` —— 24.5（`k = 2`）：有限复形上的 ℤ₂ 1-上循环 ⟹ 二重覆盖（3k–5k）

```lean
structure SimplicialBoolCocycle (K : Geometry.SimplicialComplex ℝ E) where
  parity : E → E → Bool
  symm : ∀ a b, {a, b} ∈ K.faces → parity a b = parity b a
  self : ∀ a, {a} ∈ K.faces → parity a a = false
  cocycle : ∀ a b c, {a, b, c} ∈ K.faces → Bool.xor (parity a b) (parity b c) = parity a c
def SimplicialBoolCocycle.IsCoboundary (ε) : Prop := ∃ δ : E → Bool, ∀ a b, {a, b} ∈ K.faces → parity a b = Bool.xor (δ a) (δ b)
-- 由 ε 得到本树的 BoolCocycle：指标集 = 顶点，baseSet v := openStar K v（作为 K.space 子类型的开集），parity v w := 常值 ε v w
noncomputable def SimplicialBoolCocycle.toBoolCocycle [Finite K.faces] (ε) : BoolCocycle {v // {v} ∈ K.faces} K.space
-- 二重覆盖（Bool 纤维）
theorem SimplicialBoolCocycle.isCoveringMap (ε) : IsCoveringMap (ε.toBoolCocycle.toFiberBundleCore.proj)
theorem SimplicialBoolCocycle.card_fiber (ε) (x) : Nat.card (proj ⁻¹' {x}) = 2
-- 连通性判据
theorem SimplicialBoolCocycle.connectedSpace_iff [ConnectedSpace K.space] (ε) :
    ConnectedSpace ε.toBoolCocycle.toFiberBundleCore.TotalSpace ↔ ¬ ε.IsCoboundary
```
路线：`openStar K v ∩ openStar K w ≠ ∅ ⟹ {v, w} ∈ K.faces`、三个开星相交 ⟹ 三角形是面（`OpenStar.lean`、载体面），
于是 `parity_comp` 来自 `cocycle`；`continuousOn_parity` 因常值。连通性：不连通 ⟹ `exists_section_of_not_connected_double_cover`
给连续截面 ⟹ 在每个 `openStar v` 上截面的坐标常值（`isLocallyConstant_sectionCoord`）⟹ 顶点函数 `δ` 使 ε 为上边界；
反向：`δ` 给出全局截面 ⟹ 总空间是两个同胚于 `K.space` 的开集之并，不连通。

### 砖 C.3 `CoveringTriangulation.lean` —— 24.6：三角剖分提升到有限覆盖（4k–6k）

```lean
theorem exists_lift_simplicialComplex [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {X̃ : Type*} [TopologicalSpace X̃] {p : X̃ → K.space} (hp : IsCoveringMap p) (hfin : ∀ x, (p ⁻¹' {x}).Finite) :
    ∃ (N : ℕ) (K̃ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))) (e : K̃.space ≃ₜ X̃),
      K̃.faces.Finite ∧
      (∀ s ∈ K̃.faces, ∃ t ∈ K.faces, ∃ A : EuclideanSpace ℝ (Fin N) →ᵃ[ℝ] E, Set.EqOn (Subtype.val ∘ p ∘ e ∘ Subtype.mk?) A (convexHull ℝ ↑s) ∧ A '' convexHull ℝ ↑s = convexHull ℝ ↑t) ∧
      ∀ n, IsCombinatorialManifoldWithBoundary n K → IsCombinatorialManifoldWithBoundary n K̃
```
（`p ∘ e` 在每个单形上仿射且把它同胚地送到 `K` 的一个单形；把上面的"`Subtype.mk?`"按实际类型整理成可读陈述，
写进计划行 C.3 的"拟定 Lean"列。）
路线（Moise 24.6 证明）：(i) 用 `exists_isSubdivision_closedStar_subset` 型引理把 `K` 细分成 `K'`，使每个顶点的闭星落在
一个均匀覆盖开集（`IsEvenlyCovered`）内；组合流形性在细分下不变（`ManifoldSubdivision.lean`、`ManifoldInvariance.lean`）。
(ii) 抽象提升复形：顶点集 `Ṽ := Σ v, p ⁻¹' {v}`（有限），面 = 一个单形 `s ∈ K'.faces` 上同一叶（`Sheets.lean` 的 `sheet`）内的
纤维点集合；用标准单形实现（§3 末）得几何复形 `K̃`。(iii) `e`：每个面上用叶同胚的逆与 `simplicialMap` 逐单形定义，连续性由
有限闭覆盖上的粘接，双射由覆盖的叶结构。(iv) 顶点 link 的单纯同构 `lk(ṽ, K̃) ≅ lk(v, K')`（同一叶内），用 `IsGlueIso.isPLHomeomorphOn`
搬运球/球面性，得 `IsCombinatorialManifoldWithBoundary n K̃`。
消费者 §25 L.4 只需 `k = 2`（C.2 的覆盖）；先做 C.2 的总空间这一情形也可以，但陈述保持一般有限叶。

## 5. 记录与汇报

- 每砖通过后更新计划行 C.1–C.3 的状态列、`MOISE_PLAN.md` §6（含 D4 审计结果）；最后一次提交同时把 E3.2 的记录写入：
  F6.2 行改为 partial（穷竭已做，局部有限三角剖分未做，→ 新行 F6.3 "局部有限三角剖分塔"，状态 new）；E.2 行"拟定 Lean"列写入
  35.2 的陈述（`K` 局部有限可非紧，`h` 为 `Topology.IsEmbedding`，结论仅 φ-逼近的 PLH，无 `f(K)` 附加条款）；E.3 行标注
  "blocked on F6.3"；§8 加 R9 记录本次发现。这些文件 F、S 车道也在改：先 `git fetch origin`，在 `origin/codex/moise-smoothing`
  上 rebase 后再推。
- 审计文件 `AuditC<k>.lean` 递增；报告：模块、端点、审计（含复用声明的 D4 审计）、检查退出码、未闭合项。

## 6. Lean 坑

- `rw` 关闭目标后再 `rfl` 报 "No goals"；`rcases … with rfl` 会消去固定变量；`▸` 高阶合一易选错实例，用 `have … := by rw [heq]; exact h`。
- `open Classical` 下 `not_imp` 有歧义，用 `Classical.not_imp`；Git Bash 无 `grep -P`，用 `sed`。
- `theorem PLPieceIn.foo`/`IsCombinatorialManifoldWithBoundary.foo` 内部裸名会解析到同命名空间的定理，写全名 `PiecewiseLinear.x`。
- 子类型 `K.space` 上的拓扑：开星是相对开集，用 `isOpen_induced_iff`/`Subtype` 引理搬运；`FiberBundleCore.proj` 的纤维用
  `Bool` 的 `Fintype` 得 `Nat.card = 2`。
