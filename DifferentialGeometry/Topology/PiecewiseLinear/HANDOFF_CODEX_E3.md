# E3 车道交接：§23 边界引理（M.1–M.3）与 36.1 过渡的条件版（E.3）

交接日期 2026-09-14。本文件是接手者的唯一入口。任务是用 F 车道与 E.0 已有的产出，把
`PHASE3_APPROXIMATION_PLAN.md` 的 M.1、M.2、M.3 证成"已证生产者"，再把 E.3（Moise 36.1 的过渡）
证成"以 35.2 的陈述为显式假设的条件性定理"，从而提前冻结 E.2 的签名并验证接口能拼成 E.4。

## 0. 任务与顺序

砖 E3.0 边界点集的 PL 不变性 → 砖 E3.1 M.1/M.2/M.3 → 砖 E3.2 把 35.2 形式化为 `Prop`、证 E.3 条件版 →
砖 E3.3 E.4 的条件版（`Moise352 → PLApproximationManifold 3`）。全程不使用 `sorry`：未证的 35.2 只能作为
命名的显式假设出现在陈述里，并在报告中标注"条件性"。

## 1. 环境与硬规则

- 工作树 `D:\differential-geometry-moise-e3`，分支 `codex/moise-e3`（从 `codex/moise-e0` 的 c33ee6ff6 分出，
  含 F 车道至 b9f0cc102 与 E.0）。只在此工作树工作、只提交到此分支并推送同名远程分支；不合并进其它分支；绝不碰 main。
- 另两个 Codex 分别在 `D:\differential-geometry-moise-plan`（F 车道）和 `D:\differential-geometry-moise-s`（S 车道）
  工作：不要进入它们的目录；不改共享检出 `E:\differential-geometry-dev` 的源码或分支；不运行 `lake build`；
  不登记根聚合 `DifferentialGeometry.lean`。
- 主机 Lean 进程配额 4 个，三条车道各 1 个：你**同时只跑 1 个**。
- 验证只用 `D:\differential-geometry-moise-e3\.lake\scratch\tools\` 的 `check-f.ps1`/`audit-f.ps1`（`$root` 已指向本工作树，
  olean 写进共享库 `E:\differential-geometry-dev\.lake\build\lib\lean`）。
- `AGENTS.md`（= `CLAUDE.md`）：零注释零 docstring；无 `sorry`/`axiom`/`nolint`/`maxHeartbeats`/`set_option`；
  Mathlib 标准 linter 集零警告；提交信息用英文描述数学结果；绝不 force-push。
- 可判定性约定：`IsCombinatorialManifold*` 定义在 `open Classical in` 下；凡陈述含这些谓词或 `SimplicialComplex.geometricLink`
  的定理写成 `open Classical in theorem …`，不带 `[DecidableEq E]`，证明里用 `classical`。
- 状态登记：`E:\differential-geometry-dev\WORKING_STATUS.md` 末尾加 "Moise smoothing E3(Codex) 2026-09-14"（只编辑不提交）。

## 2. 验证配方

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File D:\differential-geometry-moise-e3\.lake\scratch\tools\check-f.ps1 `
  -Module DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance *> D:\differential-geometry-moise-e3\.lake\scratch\bi.log
$env:PYTHONIOENCODING='utf-8'; python D:\differential-geometry-moise-e3\.lake\scratch\tools\errblocks.py D:\differential-geometry-moise-e3\.lake\scratch\bi.log
powershell -NoProfile -ExecutionPolicy Bypass -File D:\differential-geometry-moise-e3\.lake\scratch\tools\audit-f.ps1 -File '.lake/scratch/AuditE3a.lean'
```
exit=0、零错误零警告；被 import 的新模块先通过检查。审计模板 `.lake/scratch/AuditTemplate.lean`；期望
`depends on axioms: [propext, Classical.choice, Quot.sound]`。Moise 原书 `.lake/scratch/moise_gtm47.pdf`
（书页 p = PDF 页 p+10；§23 在书页 165–173，§35–§36 在 247–255，§8 的 8.2–8.4 在 58–64）。

## 3. 可用产出（都已审计，只含标准三公理）

- F4.1（`BoundaryOfBall.lean`、`BoundaryFaces.lean`、`ManifoldWithBoundary.lean`）：`IsCombinatorialManifoldWithBoundary n K`、
  `boundaryComplex n K`（面 = 有球 link 的面的面），`IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_faces_iff`，
  `geometricLink_boundaryComplex`，`isCombinatorialManifold_boundaryComplex`，`boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex
  (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n+2))) L.space) : (boundaryComplex (n+1) L).space = f '' (simplexBoundary (stdVertices n) _).space`，
  `isPLSphere_boundaryComplex_space_of_isPLBall`；`StdSimplexCone.lean`：`isPLBall_closedStar`、`IsCombinatorialManifold.isPLBall_closedStar`；
  `StarJoin.lean`：`isPLBall_geometricLink_of_isPLBall_geometricLink`、`isPLSphere_geometricLink_of_isPLSphere_geometricLink`
  （细分顶点 `x ∈ openSimplex t` 的 link ≅ `∂t ∗ lk t`）；`ManifoldSubdivision.lean`、`ManifoldInvariance.lean`
  （细分两个方向与 PL 同胚下 `IsCombinatorialManifoldWithBoundary` 不变，`exists_isGlueIso_of_isPLHomeomorphOn`）；
  `PLBallSphere.lean`：`IsPLBall.not_isPLSphere`；`JoinBall.lean`/`JoinInvariance.lean`：球∗球、球∗球面、球面∗球面。
- F6.1（`PolyhedronIn.lean`、`PieceTransition.lean`、`PieceRestrict.lean`、`PolyhedralManifold.lean`）：`PLPieceIn E n X Y`、
  `PLPiece n X Y`、`PLPieceIn.isPLHomeomorphOn_transition`（同一集合两个片之间的过渡是 PL 同胚）、`PLPieceIn.restrict`、
  `IsPolyhedralManifoldWithBoundary (n := n) m P := ∃ T : PLPiece n X P, IsCombinatorialManifoldWithBoundary m T.piece.complex`
  及选片无关性 `IsPolyhedralManifoldWithBoundary.isCombinatorialManifoldWithBoundary_of_piece`。
- F6.2（`Exhaustion.lean`、`ExhaustionGeneral.lean`）：`exists_exhaustion_of_isOpen {m} {X} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) X] [T2Space X] [SecondCountableTopology X] [Nonempty X] [HasGroupoid X (plGroupoid (m+1))]
  {U : Set X} (hU : IsOpen U) : ∃ N : ℕ → Set X, (∀ i, IsCompact (N i) ∧ IsPolyhedralManifoldWithBoundary (n := m+1) (m+1) (N i) ∧
  N i ⊆ interior (N (i+1))) ∧ ⋃ i, N i = U`；`exists_isPolyhedralManifoldWithBoundary_neighborhood`；`PLPieceIn.image_mem_nhds_of_mem_nhds`。
- E.0（`Topology/InvarianceOfDomainManifold.lean`，命名空间 `DifferentialGeometry.Topology`）：
  `invariance_of_domain_isOpen_image {E} [..内积、有限维..] {U : Set E} (hU : IsOpen U) {f : E → E} (hf : ContinuousOn f U) (hinj : InjOn f U) : IsOpen (f '' U)`，
  `isOpen_image_of_continuousOn_injOn {E} [..] {M₁ M₂} [TopologicalSpace M₁] [ChartedSpace E M₁] [TopologicalSpace M₂] [ChartedSpace E M₂]
  {U : Set M₁} (hU : IsOpen U) {f : M₁ → M₂} (hf : ContinuousOn f U) (hinj : InjOn f U) : IsOpen (f '' U)`，
  `isOpenMap_of_continuous_injective`，`isInteriorPoint_iff_any_chart_real`，`isBoundaryPoint_iff_any_chart_real`；
  `Topology/FixedPoint/Brouwer.lean`：`exists_fixedPoint_closedBall_of_continuous`。
- 流形层词汇（`Manifold.lean`）：`IsPLAt`、`IsPLOn n m f s`、`IsPL n m f`（`ChartedSpace.LiftProp (piecewiseAffineProperty n m) f`）、
  `PLApproximationManifold n`（§0 的 A′）：`∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
  [MetricSpace M₂] [SecondCountableTopology M₂] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace … M₂]
  [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)] (h : M₁ ≃ₜ M₂) (φ : M₁ → ℝ), Continuous φ → (∀ x, 0 < φ x) →
  ∃ f : M₁ ≃ₜ M₂, IsPL n n f ∧ ∀ x, dist (f x) (h x) < φ x`；`ApproximationManifold.lean`：`subtypeChartedSpace_hasGroupoid (s : Opens X)`
  （开子集是 PL 流形）、`plApproximation_of_plApproximationManifold`。
F 车道交接文档 `HANDOFF_CODEX_F.md` §5 有更全的签名表。

## 4. 砖块

### 砖 E3.0 `DifferentialGeometry/Topology/PiecewiseLinear/BoundaryInvariance.lean` —— 边界点集的 PL 不变性

```lean
open Classical in
theorem mem_boundaryComplex_space_iff_of_isPLHomeomorphOn [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {f : E → F} (hf : IsPLHomeomorphOn f K.space L.space) {x : E}
    (hx : x ∈ K.space) : x ∈ (boundaryComplex (n + 1) K).space ↔ f x ∈ (boundaryComplex (n + 1) L).space
-- 推论：同一集合 P ⊆ X 的任意两个 PL 片给出同一边界集；定义
def polyhedralBoundary (n) (P : Set X) (h : IsPolyhedralManifoldWithBoundary (n := n) (m) P) : Set X   -- 取任一片 T 的
--   T.piece.map '' (boundaryComplex m T.piece.complex).space，并证明与片的选取无关（`polyhedralBoundary_eq_of_piece`）
```
路线：先证细分不变性：`K'` 细分 `K`，`x ∈ K'.space` 是 `K'` 的顶点且在 `K` 的面 `t` 的开单形中；`x ∈ ∂K'` ⟺ `lk(x, K')` 是球
⟺（`StarJoin`：`lk(x,K') ≅ ∂t ∗ lk(t,K)`；`lk(t,K)` 是球或球面（面 link 二分法）；若是球面则 `∂t ∗ 球面` 是球面，与
`IsPLBall.not_isPLSphere` 矛盾）⟺ `lk(t, K)` 是球 ⟺ `t ∈ ∂K` 的面 ⟺ `x ∈ (boundaryComplex K).space`
（`mem_boundaryComplex_faces_iff`）。非顶点的 `x` 先细分使之成为顶点（`exists_isSubdivision_singleton_mem`）。
再用 `exists_isGlueIso_of_isPLHomeomorphOn` 把 PL 同胚变成同构细分之间的单纯同构，边界面在单纯同构下对应
（`IsGlueIso.isCombinatorialManifoldWithBoundary` 的证明里有 link 的搬运）。

### 砖 E3.1 `DifferentialGeometry/Topology/PiecewiseLinear/FrontierBoundary.lean` —— M.2、M.3、M.1

```lean
-- M.2（ℝⁿ 中的组合流形带边）
theorem frontier_space_eq_boundaryComplex_space {n : ℕ} {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1)))}
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) :
    frontier K.space = (boundaryComplex (n + 1) K).space
-- M.3（流形内的多面体流形带边）
theorem frontier_eq_polyhedralBoundary {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) X]
    [T2Space X] [HasGroupoid X (plGroupoid (n + 1))] {P : Set X} (h : IsPolyhedralManifoldWithBoundary (n := n + 1) (n + 1) P) :
    frontier P = polyhedralBoundary (n + 1) P h
-- M.1（边界点的胞腔邻域）
theorem exists_isPLBall_closedStar_inter_boundary … : ∀ x ∈ (boundaryComplex (n+1) K).space, ∃ C, IsPLBall (n+1) C ∧ C ∈ 𝓝[K.space] x ∧
    IsPLBall n (C ∩ (boundaryComplex (n+1) K).space)
```
路线（M.2）：内部点：顶点 `v` 的 link 是球面 ⟹ 闭星是 PL 球，`v` 的开星在 `K.space` 中开；`invariance_of_domain_isOpen_image`
（开星 ≅ ℝⁿ⁺¹ 的开集？不直接——改用：闭星 `B = f(Δ)`，`v = f(c)`，`c` 内点；`f` 在 `interior Δ`（开集）上连续单射，
像 `f '' interior Δ ⊆ B ⊆ K.space` 在 ℝⁿ⁺¹ 中开且含 `v`）。边界点 `x`（link 球）：闭星 `B = f(Δ)`，`x = f(y)`，`y ∈ ∂Δ`；
若 `K.space ∈ 𝓝 x`，取 `K.space` 内含 `x` 的开集 `O ⊆ closedStar`（`closedStar_mem_nhdsWithin`），`f⁻¹`（`invFunOn`）在 `O` 上
连续单射，像是 ℝⁿ⁺¹ 的开集且含 `y`，但像 `⊆ Δ`，与 `y ∈ frontier Δ` 矛盾。非顶点先细分（细分不变性由 E3.0）。
（M.3）：在图卡里做同样论证，`isOpen_image_of_continuousOn_injOn`；用 `PLPieceIn.image_mem_nhds_of_mem_nhds`。
（M.1）：`C := closedStar` 在细分后的复形中；`C ∩ ∂` = `x` 在 `boundaryComplex` 中的闭星（`geometricLink_boundaryComplex`），
它是 `n`-球（`isPLBall_closedStar` 于 `∂K`，`isCombinatorialManifold_boundaryComplex`）。

### 砖 E3.2 `DifferentialGeometry/Topology/PiecewiseLinear/Transition361.lean` —— 35.2 的陈述与 36.1 过渡的条件版

先读 Moise §35–§36（书页 247–255）与 §8 的 8.2–8.4（书页 58–64，36.1 说"与 8.4 从 6.4 的过渡完全一样"）。
把 35.2 形式化为一个 `Prop`（不证明）：
```lean
def Moise352 (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁] [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)] {K : Set M₁} (hK : IsPolyhedralManifoldWithBoundary (n := n) n K)
    {h : M₁ → M₂} (hh : ContinuousOn h K) (hinj : Set.InjOn h K) (φ : M₁ → ℝ) (hφ : ContinuousOn φ K) (hpos : ∀ x ∈ K, 0 < φ x),
    ∃ f : M₁ → M₂, IsPLOn n n f K ∧ Set.InjOn f K ∧ (∀ x ∈ K, dist (f x) (h x) < φ x) ∧ <35.2 结论中关于 f(K) 的条款>
```
（按书精确写出 35.2 的全部结论；若 35.2 在书中是相对/带边界条款的形式，照写；把最终选定的陈述写进计划行 E.2 的"拟定 Lean"列。）
然后证明 E.3：
```lean
theorem exists_plh_approx_of_isOpen (h352 : Moise352.{u} 3) {M₁ M₂ : Type u} [..同上..]
    {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂} (hh : ContinuousOn h U) (hinj : Set.InjOn h U) (hopen : IsOpen (h '' U))
    (φ : M₁ → ℝ) (hφ : ContinuousOn φ U) (hpos : ∀ x ∈ U, 0 < φ x) :
    ∃ f : M₁ → M₂, IsPLOn 3 3 f U ∧ Set.InjOn f U ∧ f '' U = h '' U ∧ ∀ x ∈ U, dist (f x) (h x) < φ x
```
路线（Moise 8.4/36.1）：`exists_exhaustion_of_isOpen` 给 `N i`；对每个 `i` 用 `h352` 于 `N (i+1)`，得 PL 逼近 `f_i`；
按书构造 `φ'`（(a)–(d)）使 `f_{i+1}` 在 `N i` 上与 `f_i` 相容并极限存在；`h '' U` 开（假设 `hopen`，由 E.0 的
`isOpen_image_of_continuousOn_injOn` 对同维流形自动成立——在 E3.3 里去掉这个假设）；`f(Bd N_{i+1}) = Fr f(N_{i+1})`（M.3 + E.0）；
连通性得 `N'_i ⊆ f(N_{i+1})`；并集给 `f '' U = h '' U`。凡书中一步在本树没有工具，就在报告里写出确切缺口，不要绕过。

### 砖 E3.3 `Endgame.lean` —— E.4 的条件版

```lean
theorem plApproximationManifold_three_of_moise352 (h352 : Moise352.{u} 3) : PLApproximationManifold.{u} 3
```
E.3 取 `U = univ`、`h` 为同胚（`hopen` 由 E.0 或 `h` 满射给出）；`f` 双射且 `IsPLOn 3 3 f univ` ⟹ `IsPL 3 3 f`；
逆映射的 PL 性来自图卡上的 `IsPiecewiseAffineOn.symm`（`PiecewiseAffine.lean`）或 F 车道的逆映射引理；
组装成 `M₁ ≃ₜ M₂`。审计：`#print axioms plApproximationManifold_three_of_moise352` 只含标准三公理（`Moise352` 是显式假设，不是公理）。

## 5. 记录与汇报

- 每砖通过后更新计划行 M.1–M.3、E.2（拟定 Lean）、E.3、E.4 的状态列与 `MOISE_PLAN.md` §6；F、S 车道也在改这两个
  文件：最后一次提交前 `git fetch origin` 并 rebase 到 `origin/codex/moise-smoothing`。
- 审计文件 `AuditE3<k>.lean` 递增；报告：模块、端点、审计、检查退出码、`Moise352` 的最终陈述、未闭合的书中步骤。

## 6. Lean 坑

- `rw` 关闭目标后再 `rfl` 报 "No goals"；`rcases … with rfl` 会消去固定变量；`▸` 高阶合一易选错实例。
- 在 `theorem IsCombinatorialManifoldWithBoundary.foo` 内部裸写 `secondDerived`/`barycentricSubdivision` 会解析到同名定理，
  写 `PiecewiseLinear.secondDerived K`；`theorem PLPieceIn.foo` 内部裸写 `isPolyhedron_space` 同理。
- `open Classical` 下 `not_imp` 有歧义，用 `Classical.not_imp`；Git Bash 无 `grep -P`，用 `sed`。
- `Finite (joinComplex K L).faces` 之类实例要在使用前显式 `have`，并给显式复形参数。
