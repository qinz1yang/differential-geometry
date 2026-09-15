# F 车道交接（Moise 光滑化 · Phase 3 · 车道 F：PL 基础）

交接日期 2026-09-14。上一任：Claude（Fable 5.1）。本文件是接手者的唯一入口：先读完，再读
`PHASE3_APPROXIMATION_PLAN.md` §4.0 的 F 行（第 117–157 行），最后读涉及的源文件。

## 0. 任务

接手 F 车道，从 F6.1 剩余部分开始，按 §4 的砖块顺序持续推进直到 F 车道全部完成。每块砖的
闭环：写文件 → 聚焦检查（exit=0、零 warning）→ `#print axioms` 审计 → 提交并推送 →
更新计划行（§7）。不要在砖块之间等待用户确认；遇到 §1 列出的硬性障碍才停下并报告。

## 1. 环境与硬规则

- 工作树 `D:\differential-geometry-moise-plan`，分支 `codex/moise-smoothing`（已推送到 origin，
  基线 origin/main 806b541e9）。只在此工作树工作、只提交到此分支。
- 共享检出 `E:\differential-geometry-dev` 归其他任务使用（当前在 `codex/post-merge-review`）：
  不切换它的分支、不改它的源文件、不在它里面运行 `lake`。它的唯一用途是提供已构建的 oleans；
  本车道的聚焦检查脚本把新模块的 olean/ilean 写进 `E:\differential-geometry-dev\.lake\build\lib\lean`
  （Lean 从包含 `DifferentialGeometry` 目录的第一个搜索路径项解析所有 `DifferentialGeometry.*`
  模块，所以单独的 D: lib 不可行；这是既定做法）。
- 不运行任何完整或广义的 `lake build`（用户明确要求，机器被其他任务占用）。不把本车道模块
  注册进根聚合文件 `DifferentialGeometry.lean`（集成推迟到用户另行安排）。
- 遵守 `AGENTS.md`（与 `CLAUDE.md` 相同）：非 vendored Lean 文件零注释、零 docstring；不用
  `sorry`/`axiom`/`nolint`/`maxHeartbeats`/`set_option`；Mathlib 标准 linter 集零警告（脚本已开
  `weak.linter.mathlibStandardSet=true`，`autoImplicit=false`）；提交信息描述数学结果（英文，
  一行主题 + 可选正文）；绝不 push main、绝不 force-push。
- 数学纪律：不弱化目标、不把结论藏进新假设；缺失的上游只能作为显式 `sorry` 接口暴露并在
  报告中列出；本车道目前全部端点公理干净（仅 `propext`、`Classical.choice`、`Quot.sound`），保持。
- Schoenflies（`smooth_schoenflies_three` 等）有专门负责人：不重复实现、不消费。
- 每个 lean.exe 进程峰值可达数 GB，主机上同时 ≤ 4 个 Lean 进程：聚焦检查一次一个。
- 状态登记：在 `E:\differential-geometry-dev\WORKING_STATUS.md` 末尾维护一条简短的
  "Moise smoothing(Codex) <日期>" 条目（只编辑该文件、不提交它，与此前 Claude 条目做法一致）。
  不要动其他任务的条目或锁。

## 2. 验证配方（必读）

工具在 `D:\differential-geometry-moise-plan\.lake\scratch\tools\`（`.lake/` 被 gitignore）：

```powershell
# 聚焦检查一个模块（写 olean 到 E: 的 lib；10–90 s；要求 exit=0 且输出中没有 "warning:"）
powershell -NoProfile -ExecutionPolicy Bypass -File D:\differential-geometry-moise-plan\.lake\scratch\tools\check-f.ps1 `
  -Module DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition *> D:\differential-geometry-moise-plan\.lake\scratch\pt.log
# 只看错误块
$env:PYTHONIOENCODING='utf-8'; python D:\differential-geometry-moise-plan\.lake\scratch\tools\errblocks.py D:\differential-geometry-moise-plan\.lake\scratch\pt.log
# 公理审计：新建 .lake/scratch/AuditF18.lean（模板见 AuditF17.lean），然后
powershell -NoProfile -ExecutionPolicy Bypass -File D:\differential-geometry-moise-plan\.lake\scratch\tools\audit-f.ps1 -File '.lake/scratch/AuditF18.lean'
```

- 依赖顺序：被 import 的新模块必须先通过检查（olean 已生成），下游模块才能检查。
- 审计文件写法：`import <模块>`、`open DifferentialGeometry.Topology.PiecewiseLinear`、逐条
  `#print axioms <端点>`；期望每条输出 `... depends on axioms: [propext, Classical.choice, Quot.sound]`。
- 超时或不完整输出不是通过；重跑并查看日志。
- Moise 原书 PDF 副本：`D:\differential-geometry-moise-plan\.lake\scratch\moise_gtm47.pdf`
  （书页 p = PDF 页 p+10；§32 从书页 223 开始）。

## 3. 现状（2026-09-14）

已完成（全部公理干净）：F1.1、F1.2、F2.1–F2.3、F3.1、F3.2、F3.3、F3.4（锥形式；frontier 形式
仍推迟）、F4.1、F4.2、T1、T2，以及 F6.1 的前半（`PolyhedronIn.lean`）。最近提交：cc2dbae8a
（F4.2 主定理）、bc60e840e（计划行）。计划行 F4.1/F4.2 的"状态"列已写明模块与路线，先读它们。

关键端点：
- F4.1：`isCombinatorialManifold_boundaryComplex`（`BoundaryOfBall.lean`）。
- F4.2：`IsCombinatorialManifoldWithBoundary.derivedNeighborhood`（`DerivedNeighborhoodManifold.lean`）：
  `derivedNeighborhood K L`（`secondDerived K` 中所有链元素都含 `L'` 顶点的面）是带边组合流形。
- T2：`plManifoldTriangulation : ∀ n, PLManifoldTriangulation n`（`Combinatorial.lean`）。
- `IsPolyhedralBall/IsPolyhedralSphere`（`PolyhedronIn.lean`）：`∃ T : PLPiece n X P, IsPLBall m T.piece.complex.space`。

剩余 F 行：F6.1 剩余（本文件砖 1–4）、F6.2（砖 5）、F4.3（砖 6）、F5.1/F5.2（一般位置，之后）、
F3.4 的 frontier 形式（需要区域不变性，继续推迟；F4.1 用组合边界替代）。

## 4. 砖块（按顺序；每砖一个新文件，放在 `DifferentialGeometry/Topology/PiecewiseLinear/`）

### 砖 1 `PieceTransition.lean` —— 同一集合的两个 PL 片之间的过渡映射是 PL 同胚

`import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronIn`

```lean
namespace DifferentialGeometry.Topology.PiecewiseLinear
universe u
variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem PLPieceIn.isPiecewiseAffineOn_transition {Y : Set X} (T₁ : PLPieceIn E n X Y)
    (T₂ : PLPieceIn F n X Y) :
    IsPiecewiseAffineOn (Function.invFunOn T₂.map T₂.complex.space ∘ T₁.map) T₁.complex.space

theorem PLPieceIn.isPLHomeomorphOn_transition {Y : Set X} (T₁ : PLPieceIn E n X Y)
    (T₂ : PLPieceIn F n X Y) :
    IsPLHomeomorphOn (Function.invFunOn T₂.map T₂.complex.space ∘ T₁.map) T₁.complex.space
      T₂.complex.space

theorem IsPolyhedralBall.isPLBall_of_piece {m : ℕ} {P : Set X}
    (hB : IsPolyhedralBall (n := n) m P) (T : PLPiece n X P) : IsPLBall m T.piece.complex.space
theorem IsPolyhedralSphere.isPLSphere_of_piece ...  -- 同上
theorem isPolyhedralBall_of_pieceIn {m : ℕ} {P : Set X} (T : PLPieceIn E n X P)
    (hT : IsPLBall m T.complex.space) : IsPolyhedralBall (n := n) m P
theorem isPolyhedralSphere_of_pieceIn ...  -- 同上
```

路线（第一条）：`intro x hx`；`e := chartAt (EuclideanSpace ℝ (Fin n)) (T₁.map x)`，
`chart_mem_atlas`、`mem_chart_source`。`h1 := T₁.isPiecewiseAffineOn_chart e he x ⟨hx, hxe⟩`
（`e ∘ T₁.map` 在 `T₁.complex.space ∩ T₁.map ⁻¹' e.source` 上）；
`h2 := T₂.isPiecewiseAffineOn_chart_symm e he _ ⟨e.map_source hxe, _⟩`
（`invFunOn T₂.map _ ∘ e.symm` 在 `e.target ∩ e.symm ⁻¹' Y` 上，点 `e (T₁.map x)`；第二个成员用
`e.left_inv hxe` 与 `T₁.bijOn.mapsTo hx`）；`h2.comp h1` 给出复合在
`(T₁.space ∩ T₁.map ⁻¹' e.source) ∩ (e ∘ T₁.map) ⁻¹' (e.target ∩ e.symm ⁻¹' Y)` 上的局部 PL 性；
证明该集合就是 `T₁.space ∩ T₁.map ⁻¹' e.source`（第二因子自动成立）；`congr`（在该集合上
`e.symm (e (T₁.map z)) = T₁.map z`）；局部化：`continuousOn_iff'.mp T₁.continuousOn e.source e.open_source`
给出开集 `O` 使 `T₁.map ⁻¹' e.source ∩ T₁.space = O ∩ T₁.space`，改写后用
`IsPiecewiseAffineWithinAt.of_inter_of_mem_nhds _ (hO.mem_nhds hxO)`。
第二条：`BijOn` 用 `Set.BijOn.comp` 与 `Set.BijOn.symm T₂.bijOn.invOn_invFunOn.symm T₂.bijOn`
（Mathlib：`BijOn.symm {g} (h : InvOn f g t s) (hf : BijOn f s t) : BijOn g t s`）；逆映射的 PL 性：
把第一条用于 `(T₂, T₁)` 得 `invFunOn T₁.map _ ∘ T₂.map` 在 `T₂.space` 上 PL，再 `congr`：
对 `z ∈ T₂.space`，`invFunOn g T₁.space z`（`g` 为过渡映射）与 `invFunOn T₁.map _ (T₂.map z)` 都
在 `T₁.space` 内且被 `g` 送到 `z`，用 `hbij.injOn` 得相等。
球/球面推论：`hT.of_isPLHomeomorphOn (T₀.piece.isPLHomeomorphOn_transition T.piece)`；
`PLPieceIn.exists_pLPiece` 把 `PLPieceIn` 变成 `PLPiece`。

### 砖 2 `ManifoldInvariance.lean` —— 组合流形性在细分（反向）与 PL 同胚下不变

`import DifferentialGeometry.Topology.PiecewiseLinear.IsomorphicSubdivision`
`import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubdivision`

```lean
open Classical in
theorem isCombinatorialManifoldWithBoundary_of_isSubdivision [FiniteDimensional ℝ E] {n : ℕ}
    {K K' : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite K'.faces]
    (hK' : IsSubdivision K' K) (h : IsCombinatorialManifoldWithBoundary n K') :
    IsCombinatorialManifoldWithBoundary n K
open Classical in
theorem isCombinatorialManifold_of_isSubdivision ...  -- 同上，IsCombinatorialManifold
open Classical in
theorem IsCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} {L : Geometry.SimplicialComplex ℝ F} [Finite K.faces]
    [Finite L.faces] (h : IsCombinatorialManifoldWithBoundary n K) {f : E → F}
    (hf : IsPLHomeomorphOn f K.space L.space) : IsCombinatorialManifoldWithBoundary n L
open Classical in
theorem IsCombinatorialManifold.of_isPLHomeomorphOn ...  -- 同上
open Classical in
theorem IsPLBall.isCombinatorialManifoldWithBoundary [FiniteDimensional ℝ E] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (hK : IsPLBall (n + 1) K.space) :
    IsCombinatorialManifoldWithBoundary (n + 1) K
open Classical in
theorem IsPLSphere.isCombinatorialManifold [FiniteDimensional ℝ E] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (hK : IsPLSphere (n + 1) K.space) :
    IsCombinatorialManifold (n + 1) K
```

路线：`n+1` 情形：`v` 是 `K` 顶点 ⟹ `hK'.singleton_mem hv : {v} ∈ K'.faces`；
`exists_isPLHomeomorphOn_geometricLink_of_isSubdivision hK' hv : ∃ f, IsPLHomeomorphOn f (lk K' {v}).space (lk K {v}).space`
（需要 `classical`），把 `h v hv'` 的球/球面用 `.of_isPLHomeomorphOn f` 搬过去。`0` 情形：先证
`K'` 的面都是单点（若 `s ∈ K'.faces` 有两点 `v ≠ w`，则 `s.erase v ∈ (lk K' {v}).faces`，与
`(lk K' {v}).faces = ∅` 矛盾；`mem_geometricLink_faces_iff`），于是 `K'.space` 是有限集
（`convexHull_singleton`、`Set.Finite.biUnion`），`K.space = K'.space` 有限；若 `K` 有含两点 `v ≠ w`
的面 `u`，`convexHull ℝ {v, w} ⊆ convexHull ℝ ↑u ⊆ K.space` 却无限（`infinite_convexHull_pair`），
矛盾；故 `K` 的面都是单点，link 为空。
PL 同胚版本：`classical`；`obtain ⟨K₁, L₁, φ', hK₁, hK₁fin, hL₁, hL₁fin, hiso, -⟩ :=
exists_isGlueIso_of_isPLHomeomorphOn K L hf`；`haveI := hK₁fin.to_subtype` 等；
`isCombinatorialManifoldWithBoundary_of_isSubdivision hL₁ (hiso.isCombinatorialManifoldWithBoundary (h.of_isSubdivision hK₁))`。
球/球面：`fun v hv => isPLSphere_or_isPLBall_geometricLink_of_isPLBall K hK hv`、
`fun v hv => isPLSphere_geometricLink_of_isPLSphere K hK hv`。

### 砖 3 `PieceRestrict.lean` —— PL 片限制到子复形

`import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece`

```lean
theorem IsPiecewiseAffineOn.inter_of_isPolyhedron [FiniteDimensional ℝ E] {f : E → F} {u : Set E}
    (hf : IsPiecewiseAffineOn f u) {P : Set E} (hP : IsPolyhedron P) : IsPiecewiseAffineOn f (u ∩ P)
theorem IsPiecewiseAffineOn.inter_preimage_of_isPolyhedron [FiniteDimensional ℝ E] {f : E → F}
    {u : Set E} (hf : IsPiecewiseAffineOn f u) {P : Set F} (hP : IsPolyhedron P) :
    IsPiecewiseAffineOn f (u ∩ f ⁻¹' P)
def PLPieceIn.restrict {Y : Set X} (T : PLPieceIn E n X Y) (L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ T.complex.faces) : PLPieceIn E n X (T.map '' L.space)
-- 附带 rfl 引理 restrict_complex、restrict_map
```

路线：`IsPolyhedron P` 的定义是 `∃ (ι : Type) (_ : Finite ι) (C : ι → Set E), (∀ i, IsHPolytope (C i)) ∧ P = ⋃ i, C i`
（`Polyhedra.lean:13`）；`IsPiecewiseAffineWithinAt f s x` 是"有限个 H-多胞形 `C i ⊆ s`，`f` 在每个上仿射，
`⋃ C i ∈ 𝓝[s] x`"。`inter_of_isPolyhedron`：仿照 `IsPiecewiseAffineOn.mono_of_isPolyhedron`
（`PLHomeomorph.lean:22`）的证明——取 `hf x hx.1` 的族 `D j`，新族 `D j ∩ C i`（只取 `x ∈ C i`
的 `i`），邻域性：`⋃_{x∈C i} C i` 在 `u ∩ P` 内是 `x` 的邻域，因为它包含
`(u ∩ P) ∩ (⋃_{x∉C i} C i)ᶜ`，后者的第二因子是含 `x` 的开集（`IsHPolytope.isClosed`、`isClosed_iUnion_of_finite`）。
`inter_preimage_of_isPolyhedron`：仿照 `IsPiecewiseAffineWithinAt.inter_preimage_of_isHPolytope`
（`PLPiece.lean`）并用 `(hf x hx.1).continuousWithinAt` 说明 `f ⁻¹' (⋃_{f x ∉ C i} C i)ᶜ` 是 `u` 内
`x` 的邻域。`restrict` 的字段：`hsub : L.space ⊆ T.complex.space`（由 `mem_space_iff`）；
`bijOn := (T.bijOn.injOn.mono hsub).bijOn_image`；`continuousOn := T.continuousOn.mono hsub`；
chart 字段：对 `T.isPiecewiseAffineOn_chart e he` 用 `.inter_of_isPolyhedron (PiecewiseLinear.isPolyhedron_space L)`
（需要 `haveI := (T.finite_faces.subset hL).to_subtype`）再改写集合；chart_symm 字段：对
`T.isPiecewiseAffineOn_chart_symm e he` 用 `.inter_preimage_of_isPolyhedron`，证明
`(e.target ∩ e.symm ⁻¹' Y) ∩ (invFunOn T.map T.space ∘ e.symm) ⁻¹' L.space = e.target ∩ e.symm ⁻¹' (T.map '' L.space)`
（用 `T.bijOn.invOn_invFunOn`、`T.bijOn.injOn.leftInvOn_invFunOn`），最后 `congr` 到
`invFunOn T.map L.space ∘ e.symm`（`(T.bijOn.injOn.mono hsub).leftInvOn_invFunOn`）。
注意：`theorem PLPieceIn.foo` 内部命名空间 `PLPieceIn` 已打开，裸写 `isPolyhedron_space` 会解析成
`PLPieceIn.isPolyhedron_space`（whnf 超时）——写 `PiecewiseLinear.isPolyhedron_space`。

### 砖 4 `PolyhedralManifold.lean` —— 流形中的多面体流形（带边）

`import` 砖 1–3。

```lean
open Classical in
def IsPolyhedralManifoldWithBoundary (m : ℕ) (P : Set X) : Prop :=
  ∃ T : PLPiece n X P, IsCombinatorialManifoldWithBoundary m T.piece.complex
open Classical in
def IsPolyhedralManifold (m : ℕ) (P : Set X) : Prop :=
  ∃ T : PLPiece n X P, IsCombinatorialManifold m T.piece.complex
-- 与片的选取无关：
theorem IsPolyhedralManifoldWithBoundary.isCombinatorialManifoldWithBoundary_of_piece
    (h : IsPolyhedralManifoldWithBoundary (n := n) m P) (T : PLPiece n X P) :
    IsCombinatorialManifoldWithBoundary m T.piece.complex
theorem isPolyhedralManifoldWithBoundary_of_pieceIn (T : PLPieceIn E n X P)
    (hT : IsCombinatorialManifoldWithBoundary m T.complex) : IsPolyhedralManifoldWithBoundary (n := n) m P
-- 同样两条给 IsPolyhedralManifold；再加
theorem IsPolyhedralManifoldWithBoundary.isCompact ... : IsCompact P      -- PLPieceIn.isCompact
theorem IsPolyhedralBall.isPolyhedralManifoldWithBoundary (hB : IsPolyhedralBall (n := n) (m + 1) P) :
    IsPolyhedralManifoldWithBoundary (n := n) (m + 1) P
theorem IsPolyhedralSphere.isPolyhedralManifold ...
theorem IsPolyhedralManifold.isPolyhedralManifoldWithBoundary ...
```

可判定性约定（必须遵守）：`IsCombinatorialManifold*` 定义在 `open Classical in` 下；凡陈述里出现这
两个谓词（或 `SimplicialComplex.geometricLink`）的定理，都写成 `open Classical in theorem ...`
且**不带** `[DecidableEq E]` 约束，证明内需要时用 `classical`；否则实例不匹配、whnf 超时。
在 `theorem IsCombinatorialManifoldWithBoundary.foo` 内部，裸写 `secondDerived`/`barycentricSubdivision`
会解析到同名定理——写 `PiecewiseLinear.secondDerived K`。

### 砖 5 `Exhaustion.lean` —— F6.2（紧致情形）

目标（计划行 F6.2 的 `exists_exhaustion`，先做紧致 PL 流形；一般第二可数情形需要局部有限
三角剖分或 F4.2 的局部版本，做完紧致版后在计划行注明剩余）：

```lean
theorem exists_exhaustion [CompactSpace X] [T2Space X] [SecondCountableTopology X] [Nonempty X]
    [HasGroupoid X (plGroupoid (n + 1))] {U : Set X} (hU : IsOpen U) :
    ∃ N : ℕ → Set X, (∀ i, IsCompact (N i) ∧ IsPolyhedralManifoldWithBoundary (n := n + 1) (n + 1) (N i) ∧
      N i ⊆ interior (N (i + 1))) ∧ ⋃ i, N i = U
```
（`X` 的 `ChartedSpace` 模型是 `EuclideanSpace ℝ (Fin (n + 1))`；维数 0 的版本可选。）

路线（全部在一个固定三角剖分内完成）：
1. `plManifoldTriangulation (n + 1)`（`Combinatorial.lean`；`PLManifoldTriangulation` 的定义见
   `Polyhedron.lean`）给 `T : PLTriangulation (n+1) X` 与 `hK : IsCombinatorialManifold (n+1) T.complex`。
   写一个 `PLTriangulation.toPieceIn : PLPieceIn E n X univ`（字段几乎逐字相同，`bijOn` 的目标
   `univ`，chart_symm 字段的集合 `e.target ∩ e.symm ⁻¹' univ` 用 `preimage_univ, inter_univ`）。
   记 `K := T.complex`，`g := T.map`，`E := EuclideanSpace ℝ (Fin T.ambientDim)`。
2. `U' := K.space ∩ g ⁻¹' U`；由 `continuousOn_iff'.mp T.continuousOn U hU` 得开集 `O` 使
   `g ⁻¹' U ∩ K.space = O ∩ K.space`。
3. `K_j := iteratedBarycentricSubdivision K j`（`Mesh.lean`；有 `IsSubdivision (K_j) K`、`Finite`
   实例、`diam_le_of_mem_iteratedBarycentricSubdivision_faces K hcard hM m`：直径 ≤ `((N:ℝ)/(N+1))^m * M`，
   其中面顶点数上界 `hcard : ∀ s ∈ K.faces, s.card ≤ N + 1` 取 `N := n + 1`，来自
   `IsCombinatorialManifold.card_le K hK`）。`K_j` 是带边组合流形：
   `hK.isCombinatorialManifoldWithBoundary.of_isSubdivision (iteratedBarycentricSubdivision_isSubdivision K j)`。
4. 内核子复形：`Q_j := {x | ∀ t ∈ K_j.faces, x ∈ convexHull ℝ ↑t → convexHull ℝ ↑t ⊆ U'}`，
   `L_j := restrict K_j Q_j`（`Subcomplex.lean`：面 = `s ∈ K_j.faces ∧ convexHull ℝ ↑s ⊆ Q`）。
   `N_j := derivedNeighborhood K_j L_j`（`DerivedNeighborhood.lean`），由 F4.2 是带边组合流形。
5. `N_j.space ⊆ U'`：`u ∈ N_j.faces` 是 `bK_j` 的链 `D` 的形心像，`D` 的每个元素都含某个
   `σ ∈ L_j.faces` 的形心；取 `D` 的最大元 `e_top`（`exists_max_of_chain`，`FaceNeighborhoodBall.lean`），
   `convexHull ↑u ⊆ convexHull ↑e_top`（每个顶点 `centroid e ∈ convexHull ↑e ⊆ convexHull ↑e_top`，
   `centroid_mem_convexHull_of_subset`），再用 `(barycentricSubdivision_isSubdivision K_j).exists_face_subset`
   得 `τ ∈ K_j.faces` 含 `convexHull ↑e_top`；`e_top` 含某 `σ̂`（`σ ∈ L_j`），`σ̂ ∈ convexHull ↑σ ⊆ Q_j`
   且 `σ̂ ∈ convexHull ↑τ`，于是 `convexHull ↑τ ⊆ U'`。
6. 邻域性：`derivedNeighborhood_mem_nhdsWithin (restrict_faces_subset _ _) hx : N_j.space ∈ 𝓝[K_j.space] x`
   对 `x ∈ L_j.space`；`K_j.space = K.space`。
7. 紧致集被吞：对紧致 `C ⊆ U'`，存在 `j` 使 `C ⊆ L_j.space`：`C ⊆ O`，
   `IsCompact.exists_cthickening_subset_open hC hO hCO : ∃ δ, 0 < δ ∧ cthickening δ C ⊆ O`；取 `m` 使
   `K_m` 的面直径 < δ/2（`exists_pow_lt_of_lt_one`）；`x ∈ C` 落在某 `s ∈ K_m.faces` 的凸包中；
   任何与 `convexHull ↑s` 相交的 `t ∈ K_m.faces` 的凸包中的点到 `x` 距离 < δ，故在
   `cthickening δ C ⊆ O`（`Metric.mem_cthickening_of_dist_le`）且在 `K.space`，即在 `U'`；所以
   `convexHull ↑s ⊆ Q_m`，`x ∈ L_m.space`。
8. 序列：不要依赖 `L_j` 关于 `j` 的单调性（它不成立）。用紧致穷竭
   `C k := {x ∈ K.space | ∀ y ∈ K.space, y ∉ U' → (1 : ℝ) / (k + 1) ≤ dist x y}`（闭子集故紧致，
   `⊆ U'`，`⋃ k, C k = U'`：`K.space \ U'` 紧致，若非空则 `y ↦ dist x y` 在其上取到正的最小值）。
   递归选 `j 0 := 0`，`j (i+1) :=` 第 7 步对紧致集 `N_{j i}.space ∪ C i` 给出的下标。
9. 搬到 `X`：`N i := g '' N_{j i}.space`。紧致：`(PiecewiseLinear.isPolyhedron_space _).isCompact.image_of_continuousOn`；
   多面体流形：`isPolyhedralManifoldWithBoundary_of_pieceIn ((T.toPieceIn.subdivide (secondDerived K_{j i}) h hfin).restrict N_{j i} (derivedNeighborhood_faces_subset _ _))`
   （`PLPieceIn.subdivide` 在 `PLPiece.lean`；`secondDerived K_j` 是 `K` 的细分：`(secondDerived_isSubdivision _).trans (iteratedBarycentricSubdivision_isSubdivision K j)`）；
   `N i ⊆ interior (N (i+1))`：证一个引理——`g` 在紧致 `K.space` 上连续、双射到 `univ`，
   若 `A ∈ 𝓝[K.space] x` 则 `g '' A ∈ 𝓝 (g x)`（`mem_nhdsWithin` 取开集 `O'`，
   `g '' (K.space \ O')` 紧致故闭（`IsCompact.diff`、`IsCompact.isClosed`），其补集是含 `g x` 的开集
   且包含于 `g '' A`）；`⋃ i, N i = U`：`⊆` 由第 5 步，`⊇` 由 `C i ⊆ N (i+1)` 与 `g` 满射。

### 砖 6 F4.3（管的对偶胞腔与分裂盘）—— 先出方案，再实现

Moise §32 开头（书页 223）的定义：`K` 是 PL 3-流形 `M` 中的 1 维复形，`N` 是 `K` 的正则邻域；对每
条边 `σ¹` 有 2-胞腔 `D`"在中点 `P` 处正交于 `σ¹`"，`D ∩ K = {P}`；这些 `D` 把 `N` 分成多面体
3-胞腔 `C_v`（对偶胞腔），每个恰含 `K` 的一个顶点；适当细分后边与 `C_v` 可任意小。
消费者（§32 定理 32.1、Q.1–Q.5、G.6、S.7）用到：`C_v` 是 3-胞腔、`C_v ∩ C_w = D_e`、
`D_e ∩ |K| = {P}`、`Int(C₁ ∪ C₂)` 是 PL 3-流形、`Bd N`、`Int D` 在 `Int(C₁ ∪ C₂)` 中分离 `v₁, v₂`。

已分析的两条路线（都以 `K` 为组合 3-流形、`L ≤ K` 为 1 维子复形、`bK := barycentricSubdivision K`）：

(a) 忠实于 Moise：`N := derivedNeighborhood K L`（F4.2）。可以证明（组合上）：
`C_v := N` 中落在 `closedStar v bK` 内的面，即链 `D`（`bK` 面的链）满足每个元素都是含 `v` 的
`K`-面链且含 `v` 或某 `ê`（`e ∈ L`，`v ∈ e`）；`N = ⋃_v C_v`（取链的最小元）；
`C_v ∩ C_w = D_e :=` `ê` 在 `b(dualCell K e)` 中的闭星（`dualCell K e` = 含 `e` 的 `K`-面链，
= `ê` 对 `upperLink K e` 的锥，`UpperLink.lean`），`D_e` 是 PL 2-球（锥的闭星），`D_e ∩ |L| = {ê}`；
`v ≠ w` 不相邻时 `C_v ∩ C_w = ∅`。**未解决**：`C_v` 是 PL 3-球。它等于锥 `v ∗ Λ`
（`Λ := lk v bK`，PL 2-球面或 2-球）中"蜘蛛" `v ∗ A`（`A` = `L` 在 `v` 处各边的中点）的导出邻域；
用最大重心坐标刻画（`mem_faceNeighborhood_space_iff`，`DerivedWeights.lean`）可见它是
`closedStar v K''`（3-球）加上每个 `a ∈ A` 处的"触手"，触手沿 `closedStar v K''` 的边界盘粘接。
证明它是球需要"两个 PL 球沿公共边界盘并起来是球"或正则邻域定理（RS 3.26），本树都还没有。

(b) 锥式胞腔（推荐）：直接定义 `C_v := {v + t (z - v) | z ∈ Λ, 0 ≤ t ≤ ρ_v z}`，其中
`ρ_v : |Λ| → (0,1]` 是连续 PL 函数，在每个 `a ∈ A` 的小盘 `Λ_a := closedStar a (secondDerived Λ)`
上恒为 1，远处为 1/2，中间线性过渡（`secondDerived` 提供自然的环带）。则 `C_v` 是 `v` 对
"`ρ_v` 的图像"的锥，由锥延拓（`exists_isPLHomeomorphOn_coneComplex`、`IsConeBase`）与
`Λ` 是球面/球得到 `C_v` 是 PL 3-球（`IsConeBase.isPLBall_of_isPLSphere`）；
`D_e := C_v ∩ C_w = Λ_ê = closedStar ê (secondDerived (dualCell K e))`（`dualCell K e ⊆ Λ_v ∩ Λ_w`，
关于 `v, w` 对称）是 PL 2-球，`D_e ∩ |L| = {ê}`，不同边的 `D_e` 两两不交；`N := ⋃_v C_v` 是
`|L|` 的邻域、直径 ≤ 2·mesh(K)。仍需：`N`（以及 `Int(C_v ∪ C_w)`）是多面体 3-流形（带边）：
用"两个 PL 3-球沿边界盘粘接后，盘内点的 link 是两个 2-球沿公共边界圆的并 = 2-球面"，其中
"两 PL `m`-球沿公共边界球面粘接是 PL `m`-球面"可用现有工具证明：F4.1 的
`boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex`（PL 球的边界是模型边界的像）、锥延拓、
`simplexAvoiding` 把标准单形边界写成两个球的并。
建议：先把 (b) 写成计划行 F4.3 的"拟定 Lean"与引理清单，再实现；把 `N` 的这种结构作为
"正则邻域"的**定义**提供给 Q 车道（消费者只用上面列出的性质）。

### 之后

F5.1、F5.2（一般位置，`new`，见计划行 154–155）；F3.4 的 frontier 形式继续推迟（需要区域不变性）。

## 5. API 速查（精确签名，已核对）

```lean
-- PiecewiseAffine.lean
def IsPiecewiseAffineWithinAt (f : E → F) (s : Set E) (x : E) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (C : ι → Set E) (A : ι → E →ᵃ[ℝ] F),
    (∀ i, IsHPolytope (C i) ∧ C i ⊆ s ∧ EqOn f (A i) (C i)) ∧ (⋃ i, C i) ∈ 𝓝[s] x
def IsPiecewiseAffineOn (f : E → F) (s : Set E) : Prop := ∀ x ∈ s, IsPiecewiseAffineWithinAt f s x
theorem IsPiecewiseAffineWithinAt.congr (hf) {g} (hfg : EqOn g f s) : IsPiecewiseAffineWithinAt g s x
theorem IsPiecewiseAffineWithinAt.inter_of_mem_nhds [FiniteDimensional ℝ E] (hf) (ht : t ∈ 𝓝 x) :
    IsPiecewiseAffineWithinAt f (s ∩ t) x
theorem IsPiecewiseAffineWithinAt.of_inter_of_mem_nhds (hf : IsPiecewiseAffineWithinAt f (s ∩ t) x)
    (ht : t ∈ 𝓝 x) : IsPiecewiseAffineWithinAt f s x
theorem IsPiecewiseAffineWithinAt.continuousWithinAt [FiniteDimensional ℝ E] (hf) : ContinuousWithinAt f s x
theorem IsPiecewiseAffineWithinAt.comp [FiniteDimensional ℝ E] {g : F → G} {t : Set F}
    (hg : IsPiecewiseAffineWithinAt g t (f x)) (hf : IsPiecewiseAffineWithinAt f s x) :
    IsPiecewiseAffineWithinAt (g ∘ f) (s ∩ f ⁻¹' t) x
theorem IsPiecewiseAffineOn.mono [FiniteDimensional ℝ E] (hf : IsPiecewiseAffineOn f u) {v} (hv : IsOpen v)
    (hvu : v ⊆ u) : IsPiecewiseAffineOn f v
theorem IsPiecewiseAffineOn.congr {g} (hf : IsPiecewiseAffineOn f u) (hfg : EqOn g f u) : IsPiecewiseAffineOn g u
theorem IsPiecewiseAffineOn.continuousOn [FiniteDimensional ℝ E] (hf) : ContinuousOn f u
theorem IsPiecewiseAffineOn.comp [FiniteDimensional ℝ E] {g : F → G} {v : Set F} (hg : IsPiecewiseAffineOn g v)
    (hf : IsPiecewiseAffineOn f u) : IsPiecewiseAffineOn (g ∘ f) (u ∩ f ⁻¹' v)
-- PLPiece.lean
theorem IsPiecewiseAffineWithinAt.union (hs : … f s x) (ht : … f t x) : IsPiecewiseAffineWithinAt f (s ∪ t) x
theorem IsPiecewiseAffineOn.union_of_open / union_of_isClosed
theorem IsPiecewiseAffineWithinAt.inter_preimage_of_isHPolytope [FD] (hf) {C : Set F} (hC : IsHPolytope C) :
    IsPiecewiseAffineWithinAt f (s ∩ f ⁻¹' C) x
theorem IsPiecewiseAffineOn.inter_preimage_of_isHPolytope / inter_of_isHPolytope
structure PLPieceIn (E) [..] (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    (Y : Set X) where
  complex : Geometry.SimplicialComplex ℝ E
  finite_faces : complex.faces.Finite
  map : E → X
  bijOn : BijOn map complex.space Y
  continuousOn : ContinuousOn map complex.space
  isPiecewiseAffineOn_chart : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (e ∘ map) (complex.space ∩ map ⁻¹' e.source)
  isPiecewiseAffineOn_chart_symm : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (Function.invFunOn map complex.space ∘ e.symm) (e.target ∩ e.symm ⁻¹' Y)
structure PLPiece (n) (X) [..] (Y : Set X) where
  ambientDim : ℕ
  piece : PLPieceIn (EuclideanSpace ℝ (Fin ambientDim)) n X Y
def PLPiece.toPLTriangulation (T : PLPiece n X univ) : PLTriangulation n X
def PLPieceIn.subdivide {Y} (T : PLPieceIn E n X Y) (K') (h : IsSubdivision K' T.complex) (hfin : K'.faces.Finite) :
    PLPieceIn E n X Y
theorem PLPieceIn.isCompact [FD E] (T : PLPieceIn E n X Y) : IsCompact Y
theorem PLPieceIn.isPolyhedron_space [FD E] (T) : IsPolyhedron T.complex.space
theorem PLPieceIn.exists_pLPiece [FD E] (T : PLPieceIn E n X Y) : Nonempty (PLPiece n X Y)
-- Polyhedron.lean
def IsPLHomeomorphOn (f : E → F) (P : Set E) (Q : Set F) : Prop :=
  BijOn f P Q ∧ IsPiecewiseAffineOn f P ∧ IsPiecewiseAffineOn (Function.invFunOn f P) Q
def IsPLBall (n) (P : Set E) : Prop := ∃ f : (Fin (n+1) → ℝ) → E, IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n+1))) P
def IsPLSphere (n) (P : Set E) : Prop := ∃ f : (Fin (n+2) → ℝ) → E, IsPLHomeomorphOn f (stdSimplexBoundary (n+1)) P
open Classical in def IsCombinatorialManifold : ℕ → Geometry.SimplicialComplex ℝ E → Prop
  | 0, K => ∀ v, {v} ∈ K.faces → (SimplicialComplex.geometricLink K {v}).faces = ∅
  | n + 1, K => ∀ v, {v} ∈ K.faces → IsPLSphere n (SimplicialComplex.geometricLink K {v}).space
structure PLTriangulation (n) (X) [..] where   -- 同 PLPieceIn，但 bijOn 到 univ，chart_symm 集合是 e.target
def PLManifoldTriangulation (n : ℕ) : Prop := ∀ {X} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [CompactSpace X] [Nonempty X] (C : ChartedSpace (EuclideanSpace ℝ (Fin n)) X), (letI := C; HasGroupoid X (plGroupoid n)) →
    letI := C; ∃ T : PLTriangulation n X, IsCombinatorialManifold n T.complex
-- ManifoldWithBoundary.lean
open Classical in def IsCombinatorialManifoldWithBoundary : ℕ → Geometry.SimplicialComplex ℝ E → Prop
  | 0, K => ∀ v, {v} ∈ K.faces → (SimplicialComplex.geometricLink K {v}).faces = ∅
  | n + 1, K => ∀ v, {v} ∈ K.faces → IsPLSphere n (lk K {v}).space ∨ IsPLBall n (lk K {v}).space
theorem IsCombinatorialManifold.isCombinatorialManifoldWithBoundary (h : IsCombinatorialManifold n K) : … n K
theorem IsGlueIso.isCombinatorialManifoldWithBoundary {F} [..] [FD E] [FD F] {n} {K} {L} [Finite K.faces] [Finite L.faces]
    {φ : E → F} {φ' : F → E} (h : IsGlueIso K L φ φ') (hK : IsCombinatorialManifoldWithBoundary n K) : … n L
theorem IsGlueIso.isCombinatorialManifold  -- 同上
-- ManifoldSubdivision.lean（都是 open Classical in）
theorem IsCombinatorialManifoldWithBoundary.card_le_one (h : … 0 K) (hs : s ∈ K.faces) : s.card ≤ 1
theorem IsCombinatorialManifoldWithBoundary.card_le [FD E] (K) [Finite K.faces] (h : … (n+1) K) (hs) : s.card ≤ n + 2
theorem IsCombinatorialManifold.card_le  -- 同上
theorem IsCombinatorialManifoldWithBoundary.of_isSubdivision [FD E] {K K'} [Finite K.faces] [Finite K'.faces]
    (h : … n K) (hK' : IsSubdivision K' K) : … n K'
theorem IsCombinatorialManifold.of_isSubdivision  -- 同上；.barycentricSubdivision / .secondDerived 推论
-- LinkSubdivision.lean / Subdivision.lean / Mesh.lean
theorem IsSubdivision.singleton_mem (h : IsSubdivision K' K) (hp : {p} ∈ K.faces) : {p} ∈ K'.faces
theorem exists_isPLHomeomorphOn_geometricLink_of_isSubdivision [FD E] [DecidableEq E] {K' K} [Finite K'.faces]
    (h : IsSubdivision K' K) (hp : {p} ∈ K.faces) : ∃ f : E → E, IsPLHomeomorphOn f (lk K' {p}).space (lk K {p}).space
def IsSubdivision (K' K) : Prop := K'.space = K.space ∧ ∀ s ∈ K'.faces, ∃ t ∈ K.faces, convexHull ℝ ↑s ⊆ convexHull ℝ ↑t
theorem IsSubdivision.refl / space_eq / exists_face_subset / trans (h₁ : IsSubdivision K'' K') (h₂ : IsSubdivision K' K)
noncomputable def iteratedBarycentricSubdivision [DecidableEq E] (K) : ℕ → Geometry.SimplicialComplex ℝ E
theorem iteratedBarycentricSubdivision_isSubdivision [DecidableEq E] (K) (m) : IsSubdivision (… K m) K
instance [DecidableEq E] (K) [Finite K.faces] (m) : Finite (iteratedBarycentricSubdivision K m).faces
theorem card_le_of_mem_iteratedBarycentricSubdivision_faces [DecidableEq E] (K) {N} (hK : ∀ s ∈ K.faces, s.card ≤ N + 1) (m) :
    ∀ f ∈ (… K m).faces, f.card ≤ N + 1
theorem diam_le_of_mem_iteratedBarycentricSubdivision_faces [DecidableEq E] (K) {N} (hK) {M : ℝ}
    (hM : ∀ s ∈ K.faces, diam (convexHull ℝ ↑s) ≤ M) (m) : ∀ f ∈ (… K m).faces, diam (convexHull ℝ ↑f) ≤ ((N : ℝ) / (N + 1)) ^ m * M
-- IsomorphicSubdivision.lean / Gluing.lean / StarComplex.lean
theorem exists_isGlueIso_of_isPLHomeomorphOn [FD E] [FD F] [DecidableEq E] [DecidableEq F] (K₀) [Finite K₀.faces]
    (K) [Finite K.faces] {f : E → F} (hf : IsPLHomeomorphOn f K₀.space K.space) :
    ∃ K₀' K' (φ' : F → E), IsSubdivision K₀' K₀ ∧ K₀'.faces.Finite ∧ IsSubdivision K' K ∧ K'.faces.Finite ∧
      IsGlueIso K₀' K' f φ' ∧ EqOn (simplicialMap K₀' f) f K₀.space
structure IsGlueIso (A₁ A₂ ψ ψ') : Prop where image₁ image₂ left right   -- 面的像互为面、顶点上互逆
theorem IsGlueIso.symm / singleton_mem;  theorem IsGlueIso.isPLHomeomorphOn [FD] [Finite] (h) : IsPLHomeomorphOn (simplicialMap K φ) K.space L.space
-- PLHomeomorph.lean
theorem IsPiecewiseAffineOn.mono_of_isPolyhedron (hf : IsPiecewiseAffineOn f u) (hv : IsPolyhedron v) (hvu : v ⊆ u) : IsPiecewiseAffineOn f v
theorem IsPLHomeomorphOn.bijOn / isPiecewiseAffineOn / isPiecewiseAffineOn_invFunOn / image_eq / symm
theorem IsPLHomeomorphOn.trans [FD E] [FD F] [FD G] (hf : IsPLHomeomorphOn f P Q) (hg : IsPLHomeomorphOn g Q R) : IsPLHomeomorphOn (g ∘ f) P R
theorem IsPLBall.of_isPLHomeomorphOn [FD E] [FD F] {n} {P} (hP : IsPLBall n P) {f} {Q} (hf : IsPLHomeomorphOn f P Q) : IsPLBall n Q
theorem IsPLSphere.of_isPLHomeomorphOn  -- 同上
-- BallSphereLink.lean（section 里有 [FiniteDimensional ℝ E] [DecidableEq E]）
theorem isPLSphere_geometricLink_of_isPLSphere {n} (K) [Finite K.faces] (hK : IsPLSphere (n+1) K.space) (hu : {u} ∈ K.faces) :
    IsPLSphere n (lk K {u}).space
theorem isPLSphere_or_isPLBall_geometricLink_of_isPLBall {n} (K) [Finite K.faces] (hK : IsPLBall (n+1) K.space) (hu) :
    IsPLSphere n (lk K {u}).space ∨ IsPLBall n (lk K {u}).space
theorem isPLBall_geometricLink_iff_of_isSubdivision {K' K} [Finite K'.faces] (h : IsSubdivision K' K) (hp : {p} ∈ K.faces) {n} :
    IsPLBall n (lk K' {p}).space ↔ IsPLBall n (lk K {p}).space
-- FaceLink.lean / LinkDimension.lean / Star.lean / Subcomplex.lean / DerivedNeighborhood.lean
theorem mem_geometricLink_faces_iff {s t} : t ∈ (lk K s).faces ↔ t.Nonempty ∧ Disjoint s t ∧ s ∪ t ∈ K.faces
theorem infinite_convexHull_pair {a b : E} (hab : a ≠ b) : (convexHull ℝ ({a, b} : Set E)).Infinite
def closedStar (K) (x : E) : Set E := ⋃ s ∈ {s ∈ K.faces | x ∈ convexHull ℝ ↑s}, convexHull ℝ ↑s
theorem closedStar_mem_nhdsWithin (K) [Finite K.faces] (x) : closedStar K x ∈ 𝓝[K.space] x
def restrict (K) (Q : Set E) : Geometry.SimplicialComplex ℝ E   -- faces := {s ∈ K.faces | convexHull ℝ ↑s ⊆ Q}
theorem mem_restrict_faces_iff / restrict_faces_subset / restrict_faces_finite / restrict_space_subset
def derivedNeighborhood [DecidableEq E] (K L) : Geometry.SimplicialComplex ℝ E
theorem mem_derivedNeighborhood_faces_iff {u} : u ∈ (derivedNeighborhood K L).faces ↔ ∃ D : Finset (Finset E),
    IsFlag (barycentricSubdivision K) D ∧ D.Nonempty ∧ (∀ e ∈ D, ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ e) ∧ u = D.image fun e => e.centroid ℝ id
theorem derivedNeighborhood_faces_subset (K L) : (derivedNeighborhood K L).faces ⊆ (secondDerived K).faces
theorem derivedNeighborhood_faces_finite [Finite K.faces] / derivedNeighborhood_space_subset (K L) : … ⊆ K.space
theorem closedStar_subset_derivedNeighborhood (hL : L.faces ⊆ K.faces) (hx : x ∈ L.space) : closedStar (secondDerived K) x ⊆ (derivedNeighborhood K L).space
theorem derivedNeighborhood_mem_nhdsWithin (hL : L.faces ⊆ K.faces) [Finite K.faces] (hx : x ∈ L.space) : (derivedNeighborhood K L).space ∈ 𝓝[K.space] x
open Classical in theorem IsCombinatorialManifoldWithBoundary.derivedNeighborhood [FD E] {n} {K} [Finite K.faces]
    (h : IsCombinatorialManifoldWithBoundary (n+1) K) (L) : IsCombinatorialManifoldWithBoundary (n+1) (PiecewiseLinear.derivedNeighborhood K L)
-- RegularNeighborhood.lean: secondDerived K := barycentricSubdivision (barycentricSubdivision K); secondDerived_isSubdivision K
-- Polyhedra.lean: def IsPolyhedron (P : Set E) : Prop := ∃ (ι : Type) (_ : Finite ι) (C : ι → Set E), (∀ i, IsHPolytope (C i)) ∧ P = ⋃ i, C i
--   IsHPolytope.isPolyhedron; IsPolyhedron.iUnion; IsHPolytope.isClosed; isPolyhedron_space [FD E] (K) [Finite K.faces] : IsPolyhedron K.space
-- PolyhedronIn.lean: abbrev PolyhedronIn n X P := PLPiece n X P; IsPolyhedralBall/IsPolyhedralSphere; PLPieceIn.isPLHomeomorphOn_chart_image;
--   isPolyhedralBall_of_isPLBall_chart [HasGroupoid X (plGroupoid n)] (e) (he) (hC : IsHPolytope C) (hCe : C ⊆ e.target) (hB : IsPLBall m C) : IsPolyhedralBall m (e.symm '' C)
-- TriangulationExistence.lean: exists_pLTriangulation [CompactSpace X] [T2Space X] [Nonempty X] [HasGroupoid X (plGroupoid n)] : Nonempty (PLTriangulation n X)
-- Combinatorial.lean: plManifoldTriangulation (n) : PLManifoldTriangulation n
-- FaceNeighborhoodBall.lean: exists_max_of_chain; centroid_mem_convexHull_of_subset (hfT : f ⊆ T) (hf : f.Nonempty) : f.centroid ℝ id ∈ convexHull ℝ ↑T
-- Mathlib: Set.BijOn.comp, Set.BijOn.symm (h : InvOn f g t s) (hf : BijOn f s t) : BijOn g t s, Set.BijOn.invOn_invFunOn,
--   Set.SurjOn.mapsTo_invFunOn, Set.InjOn.leftInvOn_invFunOn, Set.InjOn.bijOn_image, continuousOn_iff' (∀ t, IsOpen t → ∃ u, IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s),
--   IsCompact.exists_cthickening_subset_open, Metric.mem_cthickening_of_dist_le, IsCompact.image_of_continuousOn, IsCompact.diff, IsCompact.isClosed,
--   Geometry.SimplicialComplex.mem_space_iff : x ∈ K.space ↔ ∃ s ∈ K.faces, x ∈ convexHull 𝕜 ↑s
```

## 6. Lean 坑（本车道实测）

- `rw` 关闭目标后再写 `rfl` 报 "No goals"：去掉 `; rfl`。
- `Finset.erase_eq_empty_iff` 的 `s a` 是显式参数；`⟨a, ha⟩.ne_empty` 会被当成 `Exists`：写 `Finset.Nonempty.ne_empty ⟨a, ha⟩`。
- linter `unusedDecidableInType`/`unusedSectionVars`：`[DecidableEq E]` 只放在真正需要的陈述上，证明里用 `classical`；
  纯 Finset 引理用 `omit [NormedAddCommGroup E] [NormedSpace ℝ E] in`；`include` 的顺序决定参数顺序。
- `rcases h with rfl | h'`（`h : x = e`）会消去固定变量 `e`：改用 `rw [h] at …` 或 `Finset.forall_mem_insert`。
- `▸` 高阶合一可能选错实例：写显式 `have h' : … := by rw [heq]; exact h`。
- `rw [← foo]` 在依赖证明项里 motive 失败：改写假设（`rwa [foo] at h`）。
- `open Classical` 下 `not_imp` 有歧义：用 `Classical.not_imp.mp`。
- `Finite (joinComplex K L).faces` 之类的实例要在用它的 `have` 之前显式声明，并给出显式复形参数。
- `set x := … with hx` 的变量会被 `abel`/`ring_nf` zeta 展开：先 `clear_value x`。
- `variable (x) in` 重声明已有节变量会打乱参数顺序：在节首一次性声明。
- `≫ₕ` 需要 `open scoped Manifold`；`open unitInterval` 使 `σ` 成为保留记号。

## 7. 记录与汇报

- 每砖通过后：更新 `PHASE3_APPROXIMATION_PLAN.md` 对应行的"状态"列（模块名、端点、路线要点、审计
  编号），提交信息示例：`Exhaustion of open subsets of compact PL manifolds by polyhedral submanifolds`；
  推送 `codex/moise-smoothing`。
- 保持 `.lake/scratch/AuditF<k>.lean` 递增（下一个是 AuditF18）。
- 汇报时给出：完成的砖、端点名、审计结果、聚焦检查退出码、未完成项与确切障碍（目标/错误）。

## 9. 砖 6 之后的计划（2026-09-14 晚追加；砖 1–5 已完成，砖 6 收尾中）

### 9.0 砖 6 的收尾方式（F4.3）

Codex 按路线 (a) 已闭合：`upperLink` 球面性、`dualCell`/`splittingDisk` 球性、与图的载体交集、
`graphDualCell`（顶点胞腔 = 导出邻域限制到 `closedStar v bK`）的覆盖与交集。**未闭合且不要硬做**：
`graphDualCell K L v` 是 PL 3-球。分析（最大重心坐标刻画，`mem_faceNeighborhood_space_iff`）：
`C_v = closedStar v K'' ∪ ⋃_{a} T_a`，`T_a` 是沿 `v` 出发的射线、在屋顶盘 `R_a ⊆ ∂(closedStar v K'')` 之上
的"烟囱"（棱柱）；因此 `C_v` 是球 ⟺ "PL 3-球沿边界上的 2-盘附加棱柱仍是 3-球"，这是计划行 S.5
（Moise 23.9–23.11）的实例，其标准证明需要 S.4（ℝ³ 的 PL Schoenflies）或正则邻域定理（RS 3.26），
本树都没有。两条可行路线：
- (S) 等车道 S 的 S.5（推荐；§32 的消费者 Q 车道在 C、S、H 之后才开工，不急）。
- (X) 显式坐标拉直：在锥坐标 `(θ, r, t)`（`Λ = lk v bK` 上 `St(a, Λ) = a ∗ lk(a, Λ)` 的极坐标 `(θ, r)`，
  射线参数 `t`）里写出锥 `v ∗ Λ` 到 `C_v` 的分片仿射同胚（烟囱墙 `{r = r₀(θ), t ∈ [t₀, 1]}` 由顶面
  一段拉直而来），估计 2k–4k 行，只解决这一实例。
结论：F4.3 记为 **partial**，剩余项 = "顶点胞腔球性（依赖 S.5）"；Q 车道陈述在 S.5 完成前以
显式假设 `hcell : ∀ v, {v} ∈ L.faces → IsPLBall 3 (graphDualCell K L v).space` 携带（条件性定理，
报告中注明），**不用 sorry**。在计划 §8 增加 R8："F4.3 的胞腔球性依赖 S.5；早先行数估计未含此项"。
砖 6 提交后把上述决定写入计划行 F4.3 的状态列。

### 9.1 砖 7 `LocalManifold.lean` —— F4.2 的局部版本（F6.2 一般情形的前置）

动机：§0.1 要求 A′ 覆盖非紧致 `M₁`（开子集）。非紧 PL 流形 `X` 中紧致集 `C` 的多面体流形邻域只能
在一个紧致多面体 `Q ⊇ C`（有限个图卡多胞形之并，`exists_pLPiece_biUnion`）内用导出邻域构造，而 `Q`
的三角剖分 `K` 只在 `Int Q` 内是流形，所以需要 F4.2 只假设"靠近 `L` 处是流形"的版本。现有证明里
整体假设只在以下地方使用，且都只需要"含该面的某个顶点的 link 是球/球面"：
`IsCombinatorialManifoldWithBoundary.card_le`（`ManifoldSubdivision.lean`，取面的一个顶点）、
`.isPLSphere_or_isPLBall_geometricLink`（`BoundaryFaces.lean`，取面的一个顶点）、`.of_isSubdivision`
（在 `x ∈ openSimplex t` 处用 `t` 的面 link 二分法与 `card_le`；`k > m` 分支用
`isPLSphere_geometricLink_of_forall_card_le`，其证明经 `starAvoiding_eq_simplexBoundary_of_forall_card_le`
只需要**包含 `t` 的面**的顶点数上界——先核实，若不是则加一个 `_of_subset` 变体）、
`IsCombinatorialManifoldWithBoundary.derivedNeighborhood` 与 `upperLink_faces_eq_empty_of_card`
（`DerivedNeighborhoodManifold.lean`，对与 `V(L')` 相交的 `K'` 面 `e` 用 `card_le` 与面 link 二分法，
对 `e ⊆ V(L')` 的顶点用 `h.secondDerived`）。

```lean
open Classical in
def IsLocallyCombinatorialManifoldWithBoundary (n : ℕ) (K : Geometry.SimplicialComplex ℝ E)
    (A : Set E) : Prop :=
  ∀ v, {v} ∈ K.faces → (∃ s ∈ K.faces, v ∈ s ∧ (convexHull ℝ (s : Set E) ∩ A).Nonempty) →
    IsPLSphere n (SimplicialComplex.geometricLink K {v}).space ∨
      IsPLBall n (SimplicialComplex.geometricLink K {v}).space
-- 含义：与 A 相交的每个单形的每个顶点都有好 link（流形维数 n+1）。
theorem IsCombinatorialManifoldWithBoundary.isLocally (h : … (n+1) K) (A) : IsLocally… n K A
theorem IsLocallyCombinatorialManifoldWithBoundary.mono (h : … n K A) (hBA : B ⊆ A) : … n K B
theorem IsLocallyCombinatorialManifoldWithBoundary.card_le (h : … n K A) (hs : s ∈ K.faces)
    (hsA : (convexHull ℝ ↑s ∩ A).Nonempty) : s.card ≤ n + 2
theorem IsLocallyCombinatorialManifoldWithBoundary.isPLSphere_or_isPLBall_geometricLink (h) (hs) (hsA)
    (hcard : s.card = k + 1) (hk : k ≤ n) : IsPLSphere (n - k) (lk K s).space ∨ IsPLBall (n - k) (lk K s).space
theorem IsLocallyCombinatorialManifoldWithBoundary.of_isSubdivision [Finite K.faces] [Finite K'.faces]
    (h : … n K A) (hK' : IsSubdivision K' K) : … n K' A
-- 证明：K' 的顶点 x 落在 K 的某个面 t 的开单形中；x 所在的与 A 相交的 K'-单形 s' ⊆ convexHull ↑t'（细分），
-- 于是 t' 与 A 相交、t ⊆ t'（`face_subset_of_mem_openSimplex_of_mem_convexHull`），t 的顶点都有好 link；
-- 其余照抄 `IsCombinatorialManifoldWithBoundary.of_isSubdivision`。
theorem IsLocallyCombinatorialManifoldWithBoundary.derivedNeighborhood [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) (h : IsLocallyCombinatorialManifoldWithBoundary n K L.space) :
    IsCombinatorialManifoldWithBoundary (n + 1) (PiecewiseLinear.derivedNeighborhood K L)
-- 证明：照抄 `DerivedNeighborhoodManifold.lean`，把 `h.barycentricSubdivision`/`h.secondDerived`
-- 换成 `of_isSubdivision` 两次，把 `hK'.card_le`/`hK'.isPLSphere_or_isPLBall_geometricLink` 换成局部版
-- （与 `V(L')` 相交的面与 `L.space` 相交：`σ̂ ∈ convexHull ↑σ ⊆ L.space`）。
```
新文件不改动现有公共定理；`hL` 只在需要 `V(L') ⊆ L.space` 时使用。

### 9.2 砖 8 `ExhaustionGeneral.lean` —— F6.2 一般情形（非紧、第二可数）

```lean
theorem PLPieceIn.isPLSphere_geometricLink_of_image_mem_nhds [FiniteDimensional ℝ E] [DecidableEq E]
    {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X]
    [T2Space X] {Y : Set X} (T : PLPieceIn E (m + 1) X Y) {v : E} (hv : {v} ∈ T.complex.faces)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin (m + 1))))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin (m + 1))) X)
    (hstar : closedStar T.complex v ⊆ T.map ⁻¹' e.source)
    (hnhds : T.map '' closedStar T.complex v ∈ 𝓝 (T.map v)) :
    IsPLSphere m (SimplicialComplex.geometricLink T.complex {v}).space
-- 把 `Combinatorial.lean` 的 `PLPieceIn.isPLSphere_geometricLink`（`Y = univ`）推广：`univ` 只用来得到
-- `hnhds`。核心仍是 `LinkEuclidean.lean` 的 `isPLSphere_geometricLink_of_mem_nhds`。
theorem PLPieceIn.image_mem_nhds_of_mem_nhds [FiniteDimensional ℝ E] [T2Space X] {Y : Set X}
    (T : PLPieceIn E n X Y) {x : E} (hx : x ∈ T.complex.space) (hY : Y ∈ 𝓝 (T.map x)) {A : Set E}
    (hA : A ∈ 𝓝[T.complex.space] x) : T.map '' A ∈ 𝓝 (T.map x)
-- 推广 `Exhaustion.lean` 的 `PLPieceIn.image_mem_nhds`（同一证明，最后与 `hY` 取交）。
theorem exists_pLPiece_of_isCompact [T2Space X] [Nonempty X] [HasGroupoid X (plGroupoid n)]
    {C U : Set X} (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ Q : Set X, IsCompact Q ∧ Nonempty (PLPiece n X Q) ∧ C ⊆ interior Q ∧ Q ⊆ U
-- 每点 x ∈ C 取图卡 `chartAt`、`e.target ∩ e '' (e.source ∩ U)` 内含 `e x` 的小方体 `C_x`（H-多胞形、
-- `e x` 的邻域），`V x := e.symm '' C_x`；紧致性取有限子覆盖；`exists_pLPiece_biUnion`。
theorem PLPieceIn.exists_isPolyhedralManifoldWithBoundary_neighborhood_of_subset_interior
    [FiniteDimensional ℝ E] {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X] [T2Space X] {Q : Set X}
    (T : PLPieceIn E (m + 1) X Q) {C : Set X} (hC : IsCompact C) (hCQ : C ⊆ interior Q) :
    ∃ P : Set X, IsCompact P ∧ IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P ∧
      C ⊆ interior P ∧ P ⊆ interior Q
-- 路线 = `IsCombinatorialManifoldWithBoundary.exists_isSubdivision_neighborhood` 的证明，其中 `O` 取
-- `T.map ⁻¹' interior Q` 对应的开集（`continuousOn_iff'`），`K'` 细分、`L := restrict K' Q'`（Codex 的内核
-- 条件保证与 `L.space` 相交的单形整体落在 `O` 内），流形性用砖 7：`IsLocally… m K' L.space` 由
-- `isPLSphere_geometricLink_of_image_mem_nhds` 在 `O` 内的顶点处给出（`T.map v ∈ interior Q`，
-- `closedStar` 经 `image_mem_nhds_of_mem_nhds` 是邻域）；然后 `(T.subdivide K' …).restrict N …`。
theorem exists_isPolyhedralManifoldWithBoundary_neighborhood {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X] [T2Space X] [Nonempty X]
    [HasGroupoid X (plGroupoid (m + 1))] {C U : Set X} (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ P : Set X, IsCompact P ∧ IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P ∧
      C ⊆ interior P ∧ P ⊆ U
theorem exists_exhaustion_of_isOpen {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X] [T2Space X] [SecondCountableTopology X]
    [Nonempty X] [HasGroupoid X (plGroupoid (m + 1))] {U : Set X} (hU : IsOpen U) :
    ∃ N : ℕ → Set X, (∀ i, IsCompact (N i) ∧
      IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) (N i) ∧
      N i ⊆ interior (N (i + 1))) ∧ ⋃ i, N i = U
-- 紧致穷竭：`X` 局部紧（`ChartedSpace.locallyCompactSpace`），开子集 `↥U` 局部紧、第二可数，
-- Mathlib 实例 `sigmaCompactSpace_of_locallyCompact_secondCountable` 给 `SigmaCompactSpace ↥U`，
-- `CompactExhaustion.choice ↥U`（字段 `isCompact`、`subset_interior_succ`、`iUnion_eq`），经 `Subtype.val`
-- 搬回 `X`（`U` 开，子类型内部 = `X` 内部）；递归：`N (i+1)` 取 `N i ∪ C (i+1)` 的多面体流形邻域。
-- `U = ∅` 或 `X` 空的退化情形单独处理（`PLPieceIn.empty`）。
```
完成后把 `Exhaustion.lean` 的紧致版保留为特例，计划行 F6.2 改为 done，并在 E.3 行注明消费的名字。

### 9.3 砖 9 `BoundaryExtension.lean` —— F3.4 的组合边界形式（PL Alexander 技巧）

```lean
open Classical in
theorem exists_isPLHomeomorphOn_of_boundaryComplex [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (hK : IsPLBall (n + 1) K.space) (hL : IsPLBall (n + 1) L.space) {g : E → F}
    (hg : IsPLHomeomorphOn g (boundaryComplex (n + 1) K).space (boundaryComplex (n + 1) L).space) :
    ∃ G : E → F, IsPLHomeomorphOn G K.space L.space ∧ EqOn G g (boundaryComplex (n + 1) K).space
```
路线：`hK`、`hL` 给 `f₁ : stdSimplex → K.space`、`f₂`；`boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex`
（`BoundaryOfBall.lean`）把两个边界复形空间写成 `f_i '' (simplexBoundary (stdVertices n) _).space`；
`h := invFunOn f₂ _ ∘ g ∘ f₁` 是模型边界到自身的 PLH；`StdSimplexCone.lean`："标准单形 = 中心对其边界
的锥"，`simplexBoundary` 是 `IsConeBase`；`exists_isPLHomeomorphOn_coneComplex` 把 `h` 延拓为
`H : stdSimplex → stdSimplex`，在边界上等于 `h`；`G := f₂ ∘ H ∘ invFunOn f₁ _`，用 `IsPLHomeomorphOn.trans`
与 `.congr`。消费者：S.7、P.2（`n = 1`）、后续所有"边界同胚延拓到胞腔"。计划行 F3.4 改为
"done（组合边界形式）；`frontier` 形式待 E.0 不变域后由 S.1 给出"。

### 9.4 砖 10–11：车道 S 前半开工与 F4.3 收尾（依赖顺序 P.1 → S.5 → F4.3 胞腔球性）

- 砖 10 = P.1（多边形 Schoenflies，Moise 3.6/5.3）：`theorem isPLBall_of_isPLSphere_one {J : Set (EuclideanSpace ℝ (Fin 2))}
  (hJ : IsPLSphere 1 J) : ∃ D, IsPLBall 2 D ∧ (∂D = J) ∧ Bornology.IsBounded D`（边界用砖 9 的组合边界，
  或 `frontier`——二者在 ℝ² 中等价需要 S.1 型论证，先用组合边界）。路线按 Moise §3 组合证明：多边形有
  对角线（§3.4 型引理，用本树 `Topology/PlanarJordan/*` 的分离性质）、沿对角线切成两个更小多边形归纳、
  "两个 PL 2-盘沿公共边界弧并起来是 PL 2-盘"（用砖 9 的 `n = 1` 实例 + "PL 1-球面去掉开弧是弧"的组合
  引理）。不依赖 vendored 拓扑 Schoenflies。估计 2k–4k 行。
- 砖 11 = S.5-lite：`isPLBall_union_of_isPLBall_inter`（两个 PL 3-球沿边界 2-盘之并是 3-球）。Moise 的证明
  用 S.4；若 S.4 尚远，可先做 (X) 路线的显式实例仅供 F4.3。二者之一完成后补 `isPLBall_graphDualCell`
  并把 Q 车道的 `hcell` 假设去掉。

### 9.5 砖 12–13：F5.1 / F5.2 一般位置（计划 R2）

先定表示再推广，样板取 §26.6（B.6，最简单的曲面对情形）：
- 表示：`S₁ S₂ ⊆ EuclideanSpace ℝ (Fin 3)` 紧致多面体 2-流形（`IsPolyhedron` + 三角剖分是组合 2-流形带边）；
  结论对象"横截的有限多边形/折线之并"用 1 维组合流形 `IsCombinatorialManifoldWithBoundary 1` 陈述。
- 机制：把 `S₁` 的三角剖分顶点做微小通用扰动（顶点映射的 `simplicialImage`；小扰动保持仿射无关与复形
  公理需要专门引理），扰动量避开有限个"坏"仿射子空间（Mathlib：真子空间 Lebesgue 测度零、
  `MeasureTheory.Measure.addHaar_submodule` 型引理 + 平移；开球测度正），得到分片仿射同胚 `h`（在给定闭集外
  恒同、`ε`-接近恒同）；横截性 ⟹ 每对三角形交于线段 ⟹ 交集是 1 维组合流形。
- F5.2（奇异 2-胞腔正规形式）复用同一扰动引理，多出"至多 2 对 1"的奇点集分析（§25 L2 前言）。
估计 6k–10k + 4k–8k；这是 F 车道最后的大项，做完后 F 车道只剩 F4.3 的 S.5 依赖项。

### 9.6 可并行/待用户决定

- E.0（D6 不变域移植，`theorem invariance_of_domain_open_map` 与流形版）：树里目前没有不变域，独立于 F，
  可交给第二个 worker；导入源须先 `#print axioms`。
- 车道 H 开工前的 R3 决定（单纯链 vs 本库奇异同调）：本车道已用本库奇异同调的 Euler 示性数桥
  （`IsPLBall.not_isPLSphere`），建议 H 也走奇异同调 + `Homology/Subdivision*` 的比较素材；需用户确认。
- 车道 S 的 S.1（`Bd M = Fr M`）需要 E.0；S.2–S.4 是 §17，与 F5.1 的平面族变体互相依赖：F5.1 先做。

### 9.7 顺序

砖 6 收尾 → 砖 7 → 砖 8（F6.2 done）→ 砖 9（F3.4 done）→ 砖 10（P.1）→ 砖 12（F5.1）→ 砖 13（F5.2）
→ 砖 11（S.5-lite 或 (X)）→ F4.3 done。E.0 随时可并行。每砖闭环与记录规则同 §0、§7。

## 10. 2026-09-15 追加：砖 10 之后的安排（读完再动手）

### 10.0 先停下的两件事

- **砖 11（S.5-lite）取消**：S.5 及 §17 全部由 S 车道（`codex/moise-s`）负责，不要在本车道做任何 S.* 或 P.* 的项。
  F4.3 的顶点胞腔球性继续等 S 车道的 S.5。
- **P.1 重复**：S 车道已用 vendored 外部仓库 + 原生桥接把 P.1 和 3.7 相对形式做完（`External/ClassificationOfSurfaces/…`、
  `PlanarSchoenflies` 桥接）。本车道原生的 `PolygonalSchoenflies.lean`（`isPLBall_of_isPLSphere_one`、`exists_polyhedral_region_of_isPLSphere_one`
  等）保留为 P.1 的规范陈述；在计划行 P.1 的状态列注明"两条证明：F 车道原生（规范）；S 车道 vendored 给出 3.7 相对形式"。
  不要动 `External/`。
- 你的 `check-f.ps1` 已改为把 olean 写进私有目录 `.lake\scratch\f-lib`。其它三条车道（S、C、H）从共享库
  `E:\differential-geometry-dev\.lake\build\lib\lean` 读本车道模块的 olean，所以你 05:08 之后的新模块它们看不到。
  请恢复交接原版脚本（写共享库；模块名与其它车道不重叠，无冲突）；若改脚本是因为遇到了具体问题，在汇报里写明。

### 10.1 砖 14：F6.3 局部有限三角剖分塔（表示层，E.1/E.2/E.3 的前置；先设计后实现，中途有一次检查点）

背景：Moise 35.2 的 `K` 与 36.1 的 `U` 是**局部有限、可非紧**的多面体流形；36.1 的整体 PLH `f` 来自把 35.2 用于整个 `U`
（`U` 由 8.2 的局部有限三角剖分成为多面体），紧致穷竭只用于最后证 `f(U) = h(U)`。本车道的 `IsPolyhedralManifoldWithBoundary`
是有限片、必紧致，E3 车道因此把 E.2/E.3 标为 blocked on F6.3（见其在 `codex/moise-e3` 上的计划行 E.2、E.3、F6.3、§8 R9）。
Moise 第 8 章定理 3 的证明模式给出了不需要"单一无限复形"的表示：有限片的**上升塔**，每一阶段的"内核"在后续阶段不再重分。

```lean
structure LocallyFinitePieceTower (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (U : Set X) where
  N : ℕ → Set X
  piece : ∀ i, PLPiece n X (N i)
  subset_nhdsWithin : ∀ i, ∀ x ∈ N i, N (i + 1) ∈ 𝓝[U] x      -- 相对 U 的内部；U 开时即 interior，紧致单阶段塔（N i := K = U）时平凡成立
  iUnion_eq : ⋃ i, N i = U
  core : ∀ i, Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (piece i).ambientDim))
  core_le : ∀ i, (core i).faces ⊆ (piece i).piece.complex.faces
  subset_core : ∀ i, N i ⊆ (piece (i + 1)).piece.map '' (core (i + 1)).space
  embed : ∀ i, EuclideanSpace ℝ (Fin (piece i).ambientDim) → EuclideanSpace ℝ (Fin (piece (i + 1)).ambientDim)
  embed_inv : ∀ i, EuclideanSpace ℝ (Fin (piece (i + 1)).ambientDim) → EuclideanSpace ℝ (Fin (piece i).ambientDim)
  embed_isGlueIso : ∀ i, IsGlueIso (core i) (restrict-to-image …) (embed i) (embed_inv i)   -- core i 同构地嵌入 piece (i+1) 的复形，且像 ⊆ core (i+1)
  embed_image_le_core : ∀ i, (image of core i under embed i).faces ⊆ (core (i + 1)).faces
  map_embed : ∀ i, ∀ x ∈ (core i).space, (piece (i + 1)).piece.map (simplicialMap (core i) (embed i) x) = (piece i).piece.map x
```
（把 `restrict-to-image` 写成显式子复形：`simplicialImage`/`IsGlueIso` 的既有词汇；字段可按需要调整，但语义不变：
阶段 `i` 的内核单形在阶段 `i+1` 中原样出现且映射一致；每个 `N i` 落在下一阶段内核的像里；并集是 `U`。）

```lean
def IsLocallyFinitePolyhedralManifoldWithBoundary (m : ℕ) (U : Set X) : Prop :=
  ∃ T : LocallyFinitePieceTower n X U, ∀ i, IsCombinatorialManifoldWithBoundary m (T.piece i).piece.complex
-- 紧致特例：单阶段塔（N i := P，piece i := 同一片，core i := 全复形，embed := id）
theorem IsPolyhedralManifoldWithBoundary.isLocallyFinite … : IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) m P
-- 基本 API
theorem LocallyFinitePieceTower.exists_core_of_isCompact (T) {C : Set X} (hC : IsCompact C) (hCU : C ⊆ U) : ∃ i, C ⊆ (T.piece i).piece.map '' (T.core i).space
theorem LocallyFinitePieceTower.core_space_eventually … -- 内核像单调
-- 阶段一致的映射族给出 U 上的映射：f : U → Y 由 f_i : N i → Y 拼成，若 f_{i+1} ∘ embed = f_i 于 core i
```
存在定理（8.2 的塔版本；`X` 为 T2、第二可数、非空 PL `(m+1)`-流形，`U` 开）：
```lean
theorem exists_locallyFinitePieceTower_of_isOpen {U : Set X} (hU : IsOpen U) :
    ∃ T : LocallyFinitePieceTower (m + 1) X U, ∀ i, IsCombinatorialManifoldWithBoundary (m + 1) (T.piece i).piece.complex
```
构造（Moise 第 8 章定理 3 的模式）：
1. 相对导出邻域（F4.2-rel）：`derivedNeighborhood` 的变体，给定子复形 `K₀ ≤ L ≤ K` 且 `|K₀|` 与 `L` 的边界（在 `K` 中）不相交，
   在**相对** `K₀` 的二次导出细分（`RelativeDerived.lean` 的 `relDerived`，固定 `K₀`）中取 `L` 的导出邻域；结论：它是带边组合流形
   （证明沿用 `DerivedNeighborhoodManifold.lean`：`K₀` 深处顶点的 link 就是 `K` 中的 link，其余顶点与原证明一样），且 `K₀` 的单形
   原样保留在其中。
2. 图卡拼接的局部性：`ChartGlue.lean` 的 `exists_glue_chart` 把一个图卡多胞形粘到片上；证明一个附加引理：粘接后，片中闭星与多胞形
   原像不相交的子复形 `K₀` 在新片中原样（`IsGlueIso` 嵌入、映射一致）出现（依据 `Gluing.lean` 用相对导出细分只重分重叠区域）。
3. 递推：阶段 `i` 有 `T_i`（`N i`），`core i` := `T_i` 中闭星不碰 `∂T_i` 的单形；取 `Q :=` 用 2 把有限个小图卡方体（覆盖
   `N i ∪ C (i+1)` 且避开 `|core i|`，`C k` 为 `U` 的紧致穷竭）粘到 `T_i` 得到的片；用 1 在 `Q` 中取内核子复形 `L`（`ExhaustionGeneral.lean`
   的内核条件）相对 `core i` 的导出邻域，得 `T_{i+1}`、`N (i+1)`；`subset_core` 由网格控制（`N i` 与 `∂N (i+1)` 有正距离）。
4. 组装 `⋃ N i = U` 与 `IsCombinatorialManifoldWithBoundary`。
检查点：先做 `LocallyFinitePieceTower`、紧致特例、基本 API 与 F4.2-rel（1），聚焦检查 + 审计后**先汇报再继续** 2–4；
若 2 的局部性在现有 `Gluing.lean` 里不成立，报告并提出替代（例如把方体先细分到与 `core i` 的闭星不交）。
完成后：计划行 F6.3 改为 done（写明结构名与存在定理名），E.2/E.3 行的 "blocked on F6.3" 改为 "F6.3 done，待 E 车道"，
并把 C 车道计划行 E.2 里的条件命题 `Moise352` 中的谓词名对齐到这里的 `IsLocallyFinitePolyhedralManifoldWithBoundary`。

### 10.2 之后

F 车道到此完成（F4.3 球性等 S.5）。若 F6.3 做完仍有余力，先汇报，不要自行进入其它车道的行。

### 10.3 2026-09-15 范围确认（回答 F 车道的询问）

- §10 的改派**有效**，取代 §9.7 的旧顺序：砖 11 取消；P.1 已完成；下一砖是 F6.3（§10.1）。
- §10.1 的塔结构已修正：`subset_interior` 改为相对 `U` 的邻域条件 `subset_nhdsWithin`（感谢指出：常值紧致塔特例不能要求
  紧致带边片是开集）。存在定理里 `U` 开，二者一致。
- F5.2 暂停于当前状态，计划行 F5.2 记为 partial 并写明确切缺口：欧氏端点与一般 PL 流形的双点局部正规化、误差无关的固定邻域、
  双点集紧致已证；未证的是多图卡拼接时保持既有区域的 `HasPLDoubleCrossingAt`（相对扰动接口不控制固定子复形的边缘，
  任意小平移可产生切触）。消费者是 §25 L.3（C 车道后期），届时再决定路线；一个备选设计记入计划行：奇异 2-胞腔的像紧致，
  用 F6.2 的 `exists_isPolyhedralManifoldWithBoundary_neighborhood` 取一个含像的紧致多面体流形 `N` 及其片 `T`，把问题整体搬到
  `T` 的复形空间上做（不再逐图卡拼接）；代价是欧氏端点需要把"目标是 3 维欧氏空间"推广为"目标是高维欧氏空间中的 3 维多面体流形"。
- 恢复写共享库的原版 `check-f.ps1` 后**不需要**重检旧模块：整合分支 `origin/codex/moise-integration`（已含本车道 651f6153e 与
  C、S、H、E.0 的全部成果）在整合时已把这些模块的 olean 刷进共享库。请在下一个检查点执行
  `git fetch origin && git merge --no-ff origin/codex/moise-integration`（计划文件冲突两边都保留），然后继续 F6.3。

## 11. 2026-09-15 收尾：F6.3 完成

§10.3 确认的 F 车道范围已闭环。F6.3 的全部源文件与计划更新已在 `codex/moise-smoothing` 提交并推送；
不继续进入 E、S、P 车道。F4.3 的顶点胞腔球性仍等 S.5；F5.2 保持 partial 并暂停，确切缺口及备选设计见计划行与 §10.3。

最终端点：

- `LocallyFinitePieceTowerExistence.lean`：`exists_locallyFinitePieceTower_of_isOpen`、
  `isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen`（`bfd458cdc`）。任意 T2、第二可数、非空 PL 正维流形的开集
  有有限带边流形片组成的相容塔，上一阶段落入下一内核；内核以实际单纯映射同构嵌入，映射一致，并集恰为开集。
- `RelativeExhaustion.lean`：`PLPiece.exists_manifold_neighborhood_with_core` 将保留内核的有限图卡扩张和相对流形
  邻域抽取接成递推步骤；局部性依赖 `RelativeGluing.lean`、`ChartGlue.lean`、`PieceTransport.lean`。
- `RelativePieceNeighborhood.lean`：`PLPieceIn.exists_manifold_neighborhood_preserving_subcomplex`（`d14f605dd`）
  保留固定内核的原单形，覆盖指定紧集，并使新内核的闭星像位于新流形片内部。`RelativeMesh.lean` 控制固定闭星外的网格。
- `LocallyFinitePieceTower.lean`：塔定义、常值紧致特例、紧致捕获和内核映射拼接；
  `RelativeDerivedNeighborhood.lean`：F4.2-rel、支撑等式与保留原单形的 API。

验证：各次修改均用 §2 脚本逐模块单进程检查，exit=0、零 warning。最终两个修改模块为
`RelativeExhaustion` 与 `LocallyFinitePieceTowerExistence`；AuditF114 共 83 项，全部仅含
`propext`、`Classical.choice`、`Quot.sound`，包含最终存在端点及全部 F6.3 检查点接口。
下一个审计文件是 `.lake/scratch/AuditF115.lean`。未运行 `lake build`，未登记根聚合。

计划 F6.2/F6.3 已记为 done；E.2/E.3 已改为「F6.3 done，待 E 车道」，`Moise352` 的源域谓词已对齐到
`IsLocallyFinitePolyhedralManifoldWithBoundary`；R9 的表示层阻塞已解除。35.2/36.1 的逼近证明仍未由本车道实现。

## 12. 2026-09-15 追加：F6.3 已独立复核；改派 E.3/E.4（条件版），之后闭合 F5.2

### 12.0 复核结果（本方独立执行）

- 重编 `LocallyFinitePieceTowerExistence`：exit=0、零 warning；独立重跑 `AuditF114`：83 项全部只含
  `propext`、`Classical.choice`、`Quot.sound`。非 vendored 源码禁用模式扫描干净。共享库含本车道全部 137 个
  PiecewiseLinear 模块的 olean，无缺失。
- 整合分支 `codex/moise-integration` 已快进到 `4593e7746`（= 本车道 HEAD）。其它车道从这里取用 F6.3。
- `.lake\scratch\f-lib` 可删可留，不要再改脚本。

### 12.1 砖 15/16：E.3 与 E.4 的条件版（`Transition361.lean`、`Endgame.lean`）

改派理由：塔表示是本车道的，36.1 的证明就是"对整个 `U` 用一次 35.2，再用塔的各阶段 `N i` 证 `f(U) = h(U)`"。
原 E3 线程转去 §24 后半与 §25（有自己的交接文档），不再做 E.3/E.4。

先读（顺序不能变）：
1. `HANDOFF_CODEX_E3.md` 砖 E3.2/E3.3（原设计与路线）；计划行 E.2、E.3、E.4。
2. Moise §35–§36（书页 247–255 = PDF 257–265）与 8.2–8.4（书页 58–64 = PDF 68–74）。36.1 说"过渡与 8.4 从 6.4 完全一样"。
3. `InvarianceOfDomainManifold.lean`（E.0：`isOpen_image_of_continuousOn_injOn`、`isOpenMap_of_continuous_injective`、
   `isInteriorPoint_iff_any_chart_real`）、`FrontierBoundary.lean`（M.1–M.3：`frontier_eq_polyhedralBoundary` 等）、
   `PolyhedralBoundary.lean`、`BoundaryInvariance.lean`（`polyhedralBoundary_eq_of_piece`）。
4. `Manifold.lean` 第 55–58 行（`IsPLOn`、`IsPL`）与第 149 行（端点 `PLApproximationManifold`）。

砖 15 `DifferentialGeometry/Topology/PiecewiseLinear/Transition361.lean`：

1. 到像的双向 PL 同胚接口（计划行 E.2 要求 E 车道明确定义）：
   ```lean
   def IsPLHomeomorphInto (n : ℕ) (f : M₁ → M₂) (K : Set M₁) : Prop :=
     IsPLOn n n f K ∧ Set.InjOn f K ∧ ∃ g : M₂ → M₁, IsPLOn n n g (f '' K) ∧ Set.LeftInvOn g f K
   ```
   若 `IsPLOn` 对非开集 `f '' K` 的语义不合适，改成逐点 `IsPLWithinAt` 形式，并把最终定义写进计划行 E.2。
2. 35.2 的显式命题（只陈述，不证；把 E3.2 草稿的源域谓词换成 F6.3 的）：
   ```lean
   def Moise352 (n : ℕ) : Prop :=
     ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
       [MetricSpace M₂] [SecondCountableTopology M₂]
       [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
       [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
       {K : Set M₁} (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n K)
       {h : M₁ → M₂} (hh : Topology.IsEmbedding (K.restrict h))
       (φ : M₁ → ℝ) (hφ : ContinuousOn φ K) (hpos : ∀ x ∈ K, 0 < φ x),
       ∃ f : M₁ → M₂, IsPLHomeomorphInto n f K ∧ ∀ x ∈ K, dist (f x) (h x) < φ x
   ```
   结论只有 φ-逼近的到像 PLH，没有关于 `f '' K` 的附加条款（计划行 E.2 的决定）。`K` 不要求闭或紧。
3. 36.1 的过渡（E.3）：
   ```lean
   theorem exists_plh_approx_of_isOpen (h352 : Moise352.{u} 3) {M₁ M₂ : Type u} [...同上...]
       {U : Set M₁} (hU : IsOpen U) {h : M₁ → M₂} (hh : Topology.IsEmbedding (U.restrict h))
       (φ : M₁ → ℝ) (hφ : ContinuousOn φ U) (hpos : ∀ x ∈ U, 0 < φ x) :
       ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f U ∧ f '' U = h '' U ∧ ∀ x ∈ U, dist (f x) (h x) < φ x
   ```
   E3.2 草稿里的 `hopen : IsOpen (h '' U)` 不要作为假设：由 E.0 的 `isOpen_image_of_continuousOn_injOn` 推出。
   路线：`isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen hU` 给 `h352` 的源域假设，**对整个 `U` 用一次** `h352`
   得到 `f`；`f '' U = h '' U` 按书用穷竭：塔 `T := exists_locallyFinitePieceTower_of_isOpen hU` 的 `T.N i`
   是紧致多面体带边流形、`T.subset_interior hU`、`T.iUnion_eq`（或 `exists_exhaustion_of_isOpen`，二者皆可），
   `φ'` 按 8.4 的 (a)–(d) 取（`φ' ≤ φ`，在 `Bd N (i+1)` 上小于 `h '' (Bd N (i+1))` 与 `h '' (N i)` 的距离等），
   `f '' (Bd N (i+1)) = Fr (f '' (N (i+1)))` 由 M.3 + `polyhedralBoundary_eq_of_piece`（`f` 在 `N (i+1)` 上是到像的 PLH，
   像是多面体带边流形），`h '' U` 开由 E.0，连通性论证得 `h '' (N i) ⊆ f '' (N (i+1))`，并集给等式。
   书中某一步若本树无工具，报告确切缺口，不要绕过、不要把缺口做成假设。
   空 `U`、空 `M₁` 的情形单独处理（塔存在定理要求 `[Nonempty X]`）。

砖 16 `DifferentialGeometry/Topology/PiecewiseLinear/Endgame.lean`：
```lean
theorem plApproximationManifold_three_of_moise352 (h352 : Moise352.{u} 3) : PLApproximationManifold.{u} 3
```
E.3 取 `U = univ`、`h` 为同胚（`Topology.IsEmbedding` 由 `Homeomorph.isEmbedding`）；`f` 连续单射且 `f '' univ = univ`，
用 E.0 的 `isOpenMap_of_continuous_injective` 得开映射，组装 `M₁ ≃ₜ M₂`；`IsPL 3 3 f` 由 `IsPLOn 3 3 f univ`。
审计：`#print axioms plApproximationManifold_three_of_moise352` 只含标准三公理（`Moise352` 是显式假设，不是公理）。

检查点：砖 15 的两个定义与 E.3 的陈述通过聚焦检查、第一个子引理证完后先汇报，再继续。完成后：计划行 E.3、E.4 改为
"done（条件于 `Moise352 3`，2026-09-15）"并写明定理名；E.2 的"拟定 Lean"列改为最终陈述；`MOISE_PLAN.md` §6 加一条验证记录。
文件名、命名空间与 §2 配方不变；下一个审计文件 `AuditF115.lean`。

### 12.2 砖 17：F5.2 闭合（§10.3 备选设计的具体化；做完 12.1 再开始）

消费者是 §25 L.3（Moise 书页 184 Lemma 2 前言）：`D : Δ → M` PL、局部同胚、至多 2 对 1；任意小扰动后
奇点集是有限个互不相交的多边形（在 `Int M`）与折线（恰在端点处碰 `Bd M`，端点落在给定的 `B'`）之并，处处 crossing。
本车道已闭合单张边界图卡内的完整正规形式；多图卡归纳的缺口（先前保护区域的 crossing 在新扰动下不保持）不再攻，改走下面的整体路线。

1. 整体搬运。像 `D '' Δ` 紧致：`exists_isPolyhedralManifoldWithBoundary_neighborhood`（`ExhaustionGeneral.lean:234`）
   给紧致多面体带边流形 `P ⊇ D '' Δ` 及片 `T : PLPiece`，`K_T ⊆ ℝ^d` 有限带边组合 3-流形。令 `D_T := T.map⁻¹ ∘ D : Δ → |K_T|`，
   细分 `Δ` 使 `D_T` 对 `K_T` 单纯（本车道的单纯化与细分搬运词汇）。之后所有扰动都在 `ℝ^d` 里对 `Δ'` 的顶点像做，
   **每个顶点像限制在其载体单形 `carr(v) ∈ K_T` 的相对内部**（约束 = `carr(v)` 的仿射包；这是半空间版本"边界顶点留在零平面"
   的推广：`exists_small_affineIndependent_subsets_in_submodule`、`exists_small_vertexMap_transverse_in_halfSpace` 的
   核平面约束改为载体仿射子空间约束）。这样每个源单形的像仍在原来那个 `K_T` 单形里，映射保持进 `|K_T|`。
2. 双点的三种位置。(i) 在某四面体 `σ` 内部：两片像都在 `aff σ ≅ ℝ³`，现有欧氏 crossing 理论原样适用；
   (ii) 在内部 2-面 `τ = σ₁ ∩ σ₂` 的相对内部：两片各沿一条"接缝"（映入 `τ` 的源边的像）折叠，两条接缝在 `τ` 内横截相交于双点，
   两片在 `σ₁` 内、在 `σ₂` 内分别横截；需要一条**折叠 crossing 引理**：在 `σ₁ ∪ σ₂` 的逐单形仿射图卡（双锥）中，
   两张各由两个仿射片沿同一平面折叠的曲面，若在两个闭半空间内分别横截、接缝在折叠平面内横截相交，则满足 `HasPLCrossingAt`
   （显式构造：两个在折叠平面上一致的线性映射拼成的 PL 同胚，把两张折叠曲面同时拉直为标准的两平面模型；
   平面上的映射由 `ℓ₁ ↦ y` 轴、`ℓ₂ ↦ z` 轴决定，各半空间再用 `e_x` 的像解两个线性方程并取 `x` 分量为正）；
   (iii) 1-骨架与 `K_T` 的顶点：一维奇点集通用地避开（余维数计数），须作为通用性条件的一部分证明，不能假设。
   边界：映到 `Bd M` 的顶点约束在 `Bd K_T` 的面上，边界四面体内用已有的半空间理论（`HasPLBoundaryCrossingAt`、
   `..._in_boundary_neighborhood` 的 `B'` 控制）；`Bd K_T` 的 2-面只属于一个四面体，折叠情形只出现在内部 2-面；
   奇点集与 `Bd M` 的交是孤立点且通用地避开 `Bd K_T` 的边。
3. 目标是 `|K_T| ⊆ ℝ^d` 时的 crossing 概念：用 `|K_T|` 的 PL 图卡（双点所在单形之星是 PL 球）把 `HasPLCrossingAt`
   搬进去（`HasPLCrossingAt.image_openPartialHomeomorph` 一类的搬运引理已有），再沿 `T.map` 搬回 `M`；
   最终对抽象 `M` 的陈述用现有 `..._in_chart` 的图卡形式，crossing 的语义不变。
4. 端点（抽象度量 PL 3-流形带边 `M`，源为任意有限带边组合 2-流形，不只圆盘）：任意小 PL 扰动，保持 PL 性、局部单射、
   纤维 ≤ 2、源边界映入 `Bd M` 且像留在指定 `B'`，精确奇点集是有限带边一维组合流形、每点 `HasPLDoubleCrossingAt`（图卡版），
   奇点集的组合边界 = 奇点集 ∩ `Bd M`。这是 L.3 要消费的全部；写进计划行 F5.2 与 §4 接口表后签名冻结。
不得增加结论型假设；若第 2 步 (ii) 的折叠引理或第 1 步的载体约束扰动出现本车道无法闭合的缺口，先汇报确切缺口再决定。
估计 4k–8k 行。检查点：第 1 步（搬运 + 载体约束扰动的存在性）做完先汇报。

## 13. 2026-09-15：砖 15/16 条件版完成

- `Transition361.lean` 的两个定义与第一子引理已按 §12.1 检查点汇报、提交并推送（`9fb803198`）。
  `IsPLHomeomorphInto` 最终采用逐点逆映射的 `IsPLWithinAt` 形式；原因是空源、非空目标不存在总逆函数。
  `isPLHomeomorphInto_iff_exists_inverse` 证明源非空时与草稿单个总逆映射形式等价。E.2 行已记录完整定义。
- 砖 15 的 `exists_plh_approx_of_isOpen` 已完成并推送（`a5e0d27a1`）；一般正维版本为
  `Moise352.exists_approx_image_eq_of_isOpen`。F6.3 塔给紧致穷竭，局部有限前沿的连续正距离控制与连通分支控制
  合成误差函数；整个 U 只应用一次 35.2。紧致路径捕获与前沿分离给像集相等，不假设穷竭阶段连通。
  `IsPLHomeomorphInto.image_polyhedralBoundary` 由 M.3 与不变域证明精确边界像公式；拓扑层前沿搬运不需要先三角剖分像。
- 砖 16 的 `Endgame.lean` 已证明 `plApproximationManifold_three_of_moise352`：
  `Moise352.{u} 3 → PLApproximationManifold.{u} 3`。由全空间上的 36.1 得连续双射，经不变域组装同胚。
- 两模块分别聚焦检查 exit=0、零 warning。AuditF115 为十项检查点，AuditF116 为十五项砖 15 接口，
  AuditF117 为包含最终端点的十六项；全部仅标准三公理。E.3/E.4 已记为条件版 done，35.2 本身仍未证。
  未运行 lake build、未登记根聚合。下一项为 §12.2 的 F5.2；下一个审计文件 `AuditF118.lean`。

## 14. 2026-09-15：F5.2 的最小载体约束存在数学障碍，按 §12.2 汇报后暂停

砖 16 已提交并推送（`f173af7fb`）。随后检查 §12.2 第 1 步时发现：若 `carr(v)` 使用现有的
`carrierFace K_T (D_T v)`，即包含原映射值于其相对内部的唯一最小单形，则所要求的约束没有足够自由度。

### 14.1 已证明的障碍

新文件 `CarrierPerturbation.lean` 有六个已验证声明：

- `carrierFace_eq_singleton`：目标顶点 q 的载体为 `{q}`。
- `eq_of_mem_affineSpan_carrierFace_of_mem_vertices`：属于该载体仿射包的点只能等于 q。
- `eqOn_vertices_of_mem_affineSpan_carrierFace`：若 φ 将源顶点映到目标顶点，且 ψ 的每个顶点像留在 φ 原值的
  载体仿射包，则 ψ 与 φ 在所有源顶点上相等。
- `simplicialMap_eqOn_of_mem_affineSpan_carrierFace`：上述条件推出两个实际 `simplicialMap` 在整个源复形空间相等。
- `doublePointSet_simplicialMap_eq_of_mem_affineSpan_carrierFace`：两个实际双点集精确相等。
- `not_disjoint_doublePointSet_vertices_of_mem_affineSpan_carrierFace`：若两个不同源顶点原来映到同一目标顶点，
  任何这样的 ψ 的双点集都与目标顶点集相交，因而不能满足 §12.2(iii) 的避开 1-骨架要求。

这里仅要求 `MapsTo φ K.vertices L.vertices`，这是单纯映射必有的性质。约束只用仿射包，已经比所要求的相对内部
更宽；刚性结论因此也适用于 §12.2 的相对内部约束。不要求有限维、有限复形或流形假设，故也覆盖该路线的有限流形情形。

具体几何反例：目标为立方体 `[-1,1]^3`，源为两张不交的正方形 `[-1,1]^2`，两张均用 `(x,y) ↦ (x,y,0)` 映入目标。
取含原点的相容有限三角剖分，使目标原点及两个源原点都是顶点。该映射 PL、局部单射、每个非空纤维恰有两点，
两张源边界均映入目标边界；源允许任意有限带边组合 2-流形时包括这种不连通源。两个原点的像被载体单点条件固定，
无法消掉目标顶点处的双点；单纯化后所有顶点都受此约束时，整个重合正方形双点集原样不变。
上面的六个 Lean 声明形式化了载体刚性与双点保留机制；此立方体/双正方形构型的完整实例未另行形式化。

### 14.2 需要先修订的设计

§12.2 第 1 步“固定原最小载体”的约束与第 2(iii) 步“奇点集一般地避开目标低维骨架”不能同时用于任意原映射。
继续需要允许原先落在低维骨架的源点跨出该骨架，并证明扰动后仍位于 `|K_T|`、源公共面上的定义兼容、边界条件保持。
例如可研究在目标闭星内移动并同时重剖分的设计；仅把载体随意换成一个包含该点的高维单形不足以保证相邻源单形同时留在目标片。
若 `carr(v)` 原意是另选的高维载体，须先给出其选择与公共面兼容条件。不得假设初始双点已避开骨架来补此缺口。

按 §12.2 最后一段，在此报告真正的数学障碍后暂停。没有继续旧多图卡 crossing 保持路线，没有进入折叠 crossing 引理，
没有把第 1 步检查点或 F5.2 标成完成，也没有改动现有 crossing 定义。F5.2 状态列与 §8 R10 已记录此停点。

验证：`CarrierPerturbation` 聚焦检查 exit=0、零 warning；AuditF118 审计该文件六项并复审砖 15/16 十六项，
共二十二项全部仅 `propext`、`Classical.choice`、`Quot.sound`。未运行 lake build、未登记根聚合。
下一个审计文件为 `.lake/scratch/AuditF119.lean`；后续先读本节，再根据用户修订的载体设计继续。
