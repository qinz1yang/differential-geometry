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
