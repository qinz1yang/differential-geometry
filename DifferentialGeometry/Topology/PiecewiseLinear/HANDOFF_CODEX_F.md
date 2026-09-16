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

## 15. 2026-09-15 追加：§12.2 的错误在"单纯"一词；F5.2 改为球图卡归纳（读完 §14 再读本节）

### 15.0 复核

砖 15/16 与 `CarrierPerturbation` 已由本方独立重编（三模块 exit=0、零 warning）并独立重跑 AuditF118（22 项，三公理）。
E.3/E.4 条件版成立，计划行与 `MOISE_PLAN.md` §6 的记录准确。整合分支已快进到 `7bbb71fec`。

§14 的障碍成立，且根源在 §12.2 第 1 步的措辞："细分 `Δ` 使 `D_T` 对 `K_T` **单纯**"要求顶点映到顶点，于是每个顶点像的
最小载体都是 `K_T` 的顶点，约束当然把整个映射钉死。§12.2 原意是"逐单形仿射映入 `K_T` 的单形"，但即使改成这样，
在 `ℝ^d` 里用 `K_T` 的直单形也走不通：把一个顶点像移出 `K_T` 的低维面后，相邻源单形的直像会离开 `|K_T|`
（`K_T` 在 `ℝ^d` 中不凸），而"同时重剖分"就等于放弃 `ℝ^d` 的直线结构。所以整体搬到 `|K_T| ⊆ ℝ^d` 这条路作废，
`CarrierPerturbation.lean` 保留为该路线的反证记录。§14.2 提出的"在目标闭星内移动并同时重剖分"是对的，下面把它定型。

### 15.1 修订设计：有限个 PL 球图卡上的归纳，每步在图卡的线性结构里做顶点的通用位移，图卡外一律不动

记 `D : Δ → M`（`Δ` 有限带边组合 2-流形，`M` 度量 PL 3-流形带边），PL、局部单射、纤维 ≤ 2，`D '' (Bd Δ) ⊆ Bd M`。

1. 覆盖。`D '' Δ` 紧致，取有限个 PL 3-球图卡 `B_1, …, B_k`（内部点用 `IsPLBall` 的闭星图卡，边界点用
   `SingularChart.lean` 的半空间边界图卡；图卡像取凸集，如标准单形或半空间中的立方体），以及 `B_i' ⋐ B_i`
   使 `⋃ B_i'` 仍覆盖像。取 Lebesgue 数 `λ`，源三角剖分的网格（按像的直径）小于 `λ/4` 且小于 `dist(B_i', ∂B_i)/2`。
2. 第 `i` 步。当前映射记 `f`。把源三角剖分细分为 `Δ_i`，使 `f` 在每个映入 `B_i` 的单形上于图卡坐标下仿射
   （`f` 是 PL 的，这样的细分存在；§9 的单纯化与细分搬运词汇）。**可动顶点** = 闭星整个映入 `B_i` 的顶点；其余顶点固定。
   在图卡的线性坐标里对全部可动顶点做一次**通用**小位移（相对于全部固定顶点、固定单形的平面与折线通用：
   `exists_small_affineIndependent_subsets_relative` 一类的相对生产者），边界顶点留在零平面（半空间理论现成）。
   凸性保证位移后的单形像仍在图卡像内；固定顶点不动，所以含固定顶点的单形只在其可动顶点处变化，公共面上自动兼容。
   位移量小于 F5.2 已有的稳定阈值（闭星注入半径、三点构型的紧致最小值），保持局部单射与纤维 ≤ 2；小于
   `_in_boundary_neighborhood` 的阈值，保持边界像留在 `B'`。
3. 每步的结论（欧氏相对正规形式，在图卡坐标里证）：位移后，凡涉及至少一个可动单形的双点都是 crossing
   （`HasPLDoubleCrossingAt` / `HasPLBoundaryDoubleCrossingAt`），双点集在这些点附近是一维带边组合流形；
   只涉及固定单形的双点处映射未变。证明分三类：(动, 动) 是现有欧氏定理；(动, 固定) 与 (固定, 动) 需要
   **折叠 crossing 引理**：通用位置下，双点 `p` 处至多一张曲面折叠（两张都折叠要求两条折线相交，是余维 2 事件），
   折叠张的两个仿射片与另一张平片在各自半空间内横截、折线横穿平片 ⟹ `HasPLCrossingAt`。显式构造：
   在折叠平面上，由 `ℓ₁ ↦ y` 轴、`ℓ₂ ↦ z` 轴决定平面上的线性映射；两侧各解一个关于 `e_x` 像的线性方程组并取
   `x` 分量为正，拼成两侧仿射、在折叠平面上一致的 PL 同胚，把两张曲面同时拉直为标准双平面模型。
   通用位置还保证 `p` 避开固定曲面的折点（顶点）与可动曲面的顶点，故局部只有"平/平、折/平、平/折"三种情形。
   注意固定曲面在第 `i` 步图卡坐标下一般是折叠的（它可能在别的图卡坐标下仿射）；这没有关系，只用到它在
   `p` 附近由至多两个仿射片组成。
4. 归纳不变量。第 `i` 步后：映射 PL、局部单射、纤维 ≤ 2、`D '' (Bd Δ) ⊆ Bd M`、边界像在 `B'`；
   `B_1' ∪ … ∪ B_i'` 内的每个双点都是 crossing。保持性：第 `i` 步只改动可动顶点的闭星，像在 `B_i` 内；
   `B_i` 外的双点附近映射不变；`B_i` 内 (固定, 固定) 的双点映射不变，其 crossing 由图卡变换不变性保留
   （`HasPLCrossingAt.image_openPartialHomeomorph` 一类搬运引理）；其余双点由第 3 条重新成为 crossing。
   `B_i'` 内每个双点的两个原像所在单形的顶点闭星都映入 `B_i`（网格条件），故都是可动的，第 `i` 步后是 crossing。
5. 终局。`k` 步后所有双点都是 crossing。全局奇点集的一维带边组合流形性与"组合边界 = 奇点集 ∩ `Bd M`"
   由局部结论经 `isCombinatorialManifoldWithBoundary_one_of_locally_eq` 一类的径向不变性传给精确奇点图。
   端点陈述与 §12.2 第 4 条相同（源为任意有限带边组合 2-流形；crossing 用图卡形式，语义不变）。

### 15.2 执行顺序与检查点

- 砖 18 `FoldCrossing.lean`：折叠 crossing 引理（纯欧氏、线性代数），先做；聚焦检查 + 审计后汇报。
- 砖 19 `RelativeNormalForm.lean`：欧氏相对正规形式（第 2–3 条：固定顶点集 + 可动顶点的通用位移，
  结论含 (动, 固定) 双点的 crossing）。含边界零平面版本。汇报。
- 砖 20 `SingularNormalForm.lean`：有限覆盖归纳（第 1、4、5 条），端点写进计划行 F5.2 并冻结签名。
每砖照 §2 配方；不得增加结论型假设；若第 3 条的"通用位置下 `p` 处至多一张曲面折叠"或第 4 条的搬运在现有定义下
不能闭合，汇报确切缺口。估计 5k–9k 行。

## 16. 2026-09-15：球图卡路线的检查点

### 16.1 砖 18：折叠 crossing

`FoldCrossing.lean` 提供两个不依赖复形的端点：

- `exists_isPLHomeomorphOn_straighten_fold`：给定互补子空间 S、T 及 u、v 不在 S 中，若对所有 c > 0 有
  v − c u 不在 S 中，则构造全空间 PL 同胚，固定 S、保持 T，并把沿 S 的两个闭半平面之并送到一个线性子空间。
  此定理不限制维数。证明把两方向沿 S 投到 T，调用已有剪切拉直构造；正逆映射的 PL 性由已有构造实际提供。
- `hasPLCrossingAt_of_fold`：S 一维、T 二维时，若 A 在 x 的芽恰为上述两半平面之并，B 的芽恰为 x + T，
  则 `HasPLCrossingAt A B x`。互补性表示折线横穿平片，不重合商方向表示折叠张的两侧不重叠；
  没有假设所求 crossing 或预先存在所求拉直同胚。交换两张可直接使用已有 `HasPLCrossingAt.symm`。

验证：`check-f.ps1` 聚焦检查 exit=0、零 warning（10.1 秒）；`AuditF119.lean` 检查两个公开声明的完整类型与
公理闭包，均仅 `propext`、`Classical.choice`、`Quot.sound`。未重检旧模块、未运行 lake build、未登记根聚合。
F5.2 仍为 partial。下一项为砖 19，须从固定顶点与可动顶点的相对通用位置实际推出适用本引理的局部分类。
下一个审计文件为 `.lake/scratch/AuditF120.lean`。

### 16.2 砖 19：固定折边阻止 §15.1(3) 的分类，按约定报告后暂停

砖 18 已提交并推送（`82852d2fb`）。`RelativeNormalForm.lean` 当前只有下面四个已验证的支撑声明，
不是砖 19 的正规形式端点；砖 19、砖 20 和 F5.2 均未标完成。

- `simplicialMap_eqOn_convexHull_of_eqOn_vertices`：固定一张源面的顶点就固定该面的整个实际单纯延拓。
- `doublePointSet_simplicialMap_subset_of_eqOn_subcomplex`：固定子复形顶点时，其已有双点集包含于扰动后全源的双点集。
- `mem_doublePointSet_simplicialMap_of_fixed_faces`：两个固定面的不同原像若原来有相同的像，则此实际双点仍保留。
- `exists_small_relative_vertexMap_with_coincident_edges`：给定两组各自仿射独立的四点，共有第 0、1 点，
  对任意 ε > 0 实际调用 `exists_small_affineIndependent_subsets_relative`，得到任意小扰动，固定这四个端点标签，
  保持两条边重合，两组四点仍分别仿射独立，并保留该生产者的全部相对通用位置条件。
  初始两组四点可以不同；没有假设 crossing 或任何所求正规形式。

**不能推出的确切步骤。** 令固定标签集为 B，源中两条不交边 e、e′ 的端点全部属于 B，而它们的邻接三角形有
可动的对顶点。若原来 f(e) = f(e′)，任何固定 B 的顶点位移都保留这条共同像边。相对通用位置还使每张片的
四点组仿射独立，所以两张片各自的两个邻接三角形不共面；共同边内部的双点处两张均折叠。
这正是上述最后一个声明提供的点族，再由前三个声明传给实际单纯延拓。四个固定端点标签的像有重复，
因此它们不满足相对生产者的“固定部分仿射独立”前提；“两条折线相交是可避免的余维 2 事件”在此固定参数族中失效。
即使只要求两条固定边相交而不重合，固定顶点也不能消除原交点。

具体坐标模型：在 ℝ³ 中取 p₋ = (0,−1,0)、p₊ = (0,1,0)，第一张片的两个对顶点为 (1,0,1)、(−1,0,1)，
第二张为 (1,0,2)、(−1,0,2)；每张片由公共边 p₋p₊ 与各自两个对顶点组成的两三角形构成。
原点附近两张分别为 z = |x|、z = 2|x|。只固定两份 p₋、p₊ 的标签时，共同折边始终保留。
两组四点均仿射独立，故上面的相对生产者适用；在垂直共同边的截面中，两张片的四条射线按 A、B、B、A 排列，
充分小的对顶点位移保留此严格次序，不能得到横交的交替次序。这个坐标图及射线次序的非 crossing 判断是数学说明，
未另行形式化为 `¬ HasPLCrossingAt`；Lean 已验证的是实际固定面双点保留和满足完整相对通用位置条件的双折点族存在性。

**§15.1(4) 的关联缺口。** 若“可动单形”包括带可动顶点的混合三角形，上述构型直接落在第 3 条所要求处理的情形中。
若改按双点的最小载体边把它归到“固定/固定”，也只能推出该边上的值不变，不能推出附近曲面芽不变：
邻接三角形的可动对顶点仍在改变这两个芽。`HasPLCrossingAt.congr` 需要邻域中的集合成员关系相同，
`HasPLCrossingAt.image_openPartialHomeomorph` 需要同一个环境图卡变换；单纯的固定边逐点相等不能提供二者。
闭星全含于 Bᵢ 的可动顶点规则没有排除混合三角形的固定边；Bᵢ′ 的网格条件只保证核心内全可动，
没有自动控制 Bᵢ 内与先前保护区域相交的过渡部分。

这不否定整个 F5.2 的存在定理；需要修订的是一步相对引理和保持不变量。下一设计必须实际处理固定折边的双折构型，
或安排原像上的恒同邻域和缓冲层，使这些点的曲面芽整体不变，并证明覆盖、误差和边界条件仍成立。
不能把“固定边原来横交”或“扰动后该处仍横交”直接添加为未生产的假设，也不能以忽略固定边双点来弱化端点。
按用户及 §15.2 的停点规则在此报告数学缺口，不进入砖 20，不改 crossing 定义，不冻结尚未证明的全局签名。

验证：`RelativeNormalForm` 聚焦检查 exit=0、零 warning（9.6 秒）；更新后的 `AuditF120.lean` 审计本文件四项和
砖 18 两项，共六项全部仅 `propext`、`Classical.choice`、`Quot.sound`。两文件均零注释、无 sorry 或预算覆盖；
未运行 lake build、未登记根聚合。计划 F5.2 的状态及 §8 R11 已同步。下一个审计文件为 `.lake/scratch/AuditF121.lean`。

## 17. 2026-09-15：砖 18/19 已复核；F5.2 搁置并记录方向；新里程碑 = S.4（Moise 17.12）

### 17.0 复核

`FoldCrossing`、`RelativeNormalForm` 由本方独立重编 exit=0、零 warning；AuditF120 六项只含标准三公理。
§16.2 的障碍成立：§15.1 第 3 条所述"任意固定顶点集下混合双点皆 crossing"不成立，反例即重合固定折边。

### 17.1 F5.2 搁置（不是放弃）

可行方向只记录不展开：取 F6.2 的紧致片 `K_T`，把有限个星图卡各自的仿射细分与 `K_T` 取公共细分 `K*`，
使所有图卡变换在 `K*` 的单形上仿射，折痕集 `Ξ` = `K*` 的 2-骨架固定已知；通用位置改为"相对于 `Ξ` 的分层通用位置"
（半空间理论从一个约束平面推广到有限平面族，顶点限制在所在层内通用）；折叠引理推广到两张沿同一平面内两条不同折线折叠
的曲面；归纳不变量 = 已处理区域上 crossing 且 `Ξ`-分层通用。在该不变量下 §16.2 的重合固定折边不会出现在已处理区域。
估计 6k–12k 行。消费者 L.3 还在等 C.4/C.5，所以先做下面的 S.4。L.3 要消费的端点形状仍是 §12.2 第 4 条。

### 17.2 新里程碑：S.4 = Moise 17.12（PL Schoenflies），从 S 车道改派到本车道

理由：S.5（23.9–23.11）是 E3 的 B.3/L.2 与本车道 F4.3 的前置，S 单线程做 S.3 → S.4 → S.5 太慢；17.12 的证明主体是
水平平面族的一般位置与 `Ind S` 归纳，正是 F5.1 的机器（`exists_generalPosition_height_fibers`）。S 车道同时做
S.3（17.9–17.11）和 P.3 的一般 17.2。书页 122–125（PDF 132–135）。

先 `git fetch origin && git merge --no-ff origin/codex/moise-integration`（`bc4b635eb`，含 S.2 的 `IsSimplyEmbedded`、
`HasPushProperty`、17.5–17.8 端点）。全部用 S 的词汇，不另造。

端点（签名冻结后写进计划行 S.4）：
```lean
theorem isSimplyEmbedded_of_isPLSphere_two (I : SchoenfliesInput) {S : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsPLSphere 2 S) : IsSimplyEmbedded S
theorem exists_isPLBall_of_isPLSphere_two (I : SchoenfliesInput) {S : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsPLSphere 2 S) : ∃ B, IsPLBall 3 B ∧ frontier B = S ∧ Bornology.IsBounded B
```
`SchoenfliesInput` 是显式接口结构（不是 sorry），字段恰为 17.12 的证明实际使用而 S 车道尚未交付的书中定理，预计：
17.9（凸多面体 3-胞腔的边界单嵌入）、17.10（2-胞腔与点的 join 的边界单嵌入）、17.11（两个单嵌入球面沿平面 2-胞腔
拼合仍单嵌入）、17.2 的一般胞腔分解形式（Lemma 6 用）。每个字段由你写成 S 词汇的精确 Lean 命题，写进计划行
S.3 / P.3 的"拟定 Lean"列并标"F 的 S.4 接口，S 车道证明"；S 交付后去掉字段。证明中若还需要别的书中定理，同样加字段并登记，不绕过。

里程碑与检查点：
- M1：`SchoenfliesInput` 与两个端点的陈述通过检查；`Ind S` 的定义与 Lemma 1（`n = 0` 归约：凸化、轴旋转、指标计算）闭合。汇报。
- M2：Lemma 2–3（顶底层单点、中间层多边形）与 Lemma 4–6（各 `Bd M_i` 单嵌入）。汇报。
- M3：用 17.11 拼装出两个端点；审计；计划行 S.4 改为 done（条件于 `SchoenfliesInput`）。
其余按 §2 配方；具体路线自定。

## 18. 2026-09-15：S.4 接口与水平指标基础检查点（M1 尚未闭合）

已合并 `origin/codex/moise-integration` 的 `bc4b635eb`，合并提交 `ee824b3a7`，计划文件无冲突。
F5.2 按 §17.1 搁置，本节没有推进它。

### 18.1 已检查源码

- `SchoenfliesInput.lean`：四个字段分别为 17.9、17.10、17.11、一般 17.2；没有加入 Lemma 1 或端点结论字段。
  `IsPLDiskDecomposition` 用共同有限三角剖分、PL 2-盘胞腔、覆盖、交集的边界条件和点/弧条件表达一般胞腔分解。
  `IsFreeDiskCell` 使用 `boundaryComplex` 的内在边界；17.11 使用参数化边界像，未使用环境 `interior D`。
  `.exists_free_disk_cell_ne` 从两个自由胞腔选出不同于指定胞腔的一个，未宣称一般 17.3 已证。
  S.3/P.3 计划行已登记为“F 的 S.4 接口，S 车道证明”。仍无此接口的实例。
- `HeightIndex.lean`：`levelPolygons` 枚举整层的 PL 圆周；`heightSingularPoints` 排除 crossing 点和孤立层点。
  `heightSingularPoints_subset_vertices` / `finite_heightSingularPoints` 复用 F5.1 的非顶点 crossing。
  `levelPolygons_image` / `encard_levelPolygons_image` 给保高度的环境 PL 同胚下的精确集合与基数搬运。
  `exists_extreme_height_fibers` 对任何非空有限复形及顶点上单射的线性高度给全空间高度界和顶底层单点。
  `heightIndex` 定义为奇异点上的扩展自然数和；下一层已证明一般位置下有限，尚待与原书奇异层分解指标的对应。
  扩展自然数定义避免无限族被 `Set.ncard` 默认为零。`natCast_toNat_heightIndex` 给有限情形的无损自然数还原。

- `HeightChange.lean`：`heightSingularPoints_image`、`heightIndex_image` 给全局保高度环境 PL 同胚下的精确搬运；不要求搬运后的剖分仍在一般位置。
- `ManifoldSubspace.lean`：`eventually_mem_space_iff_sub_mem_submodule` 用区域不变性证明同维组合流形局部包含于仿射子空间时，两者的芽相等。
- `FiniteGraphCircles.lean`：`restrict_space_eq_of_isPLSphere_one` 证明有限线性图中每个 PL 圆周是原图子复形；
  `finite_isPLSphere_one_subsets`、`finite_levelPolygons` 给有限性；`heightIndex_lt_top` 与 `natCast_toNat_heightIndex` 闭合指标有限性。
  后三模块均 exit=0、零 warning；AuditF122 十二项均仅标准三公理。

### 18.2 验证与未完成部分

两模块聚焦检查 exit=0、零 warning；`AuditF121.lean` 二十六项均只含 `propext`、`Classical.choice`、`Quot.sound`。
审计同时对 §17.2 两个最终命题作类型检查；源码中没有相应的占位定理，类型检查不等于证明。
M1 仍需：一般位置层的有限多边形分解、顶点处非奇异层的 crossing 判据、与原书指标对应、
保持支持控制的平面凸化和三维保高度延拓、轴旋转后两片的严格降指标。M2 的中间层多边形性和 slab 删除、
M3 的端点拼装均未完成。本层之后的审计记录见 §18.3。

### 18.3 保高度延拓与双锥邻域（M1 支撑层，未完成 Lemma 1）

- `ConeAmbientExtension.lean` 增加 `exists_isPLHomeomorphOn_extension_coneComplex_union_radial`，
  保留两个锥顶及两侧所有径向线的精确公式。原 `exists_isPLHomeomorphOn_extension_coneComplex_union`
  签名不变，由此强版推出；未改公共定义语义。
- `ConeNeighborhood.lean`：中心投影的代数与连续性；相对底面内部给单锥内部与双锥接合处内部；
  `frontier_coneComplex_union_subset_of_mem_nhdsWithin` 实际证明三维边界包含于边缘的两侧锥。
  `isConeBase_of_subset_fiber` 和 `coneComplex_space_inter_of_subset_fiber` 从上下高度条件构造锥及其精确交。
- `HeightExtension.lean` 端点 `exists_isPLHomeomorphOn_extension_preserving_height`：给定有限水平底面复形 L、
  边缘子复形 B，L 中不在 B 的每一点都有底面内的相对邻域；若底面 PL 自同胚固定 B，则对任意包含 L 的凸开集 W，
  构造全空间 PL 延拓，固定 W 的补集，逐点保持高度，且对所有集合保持 `heightIndex`。
  证明在 W 内实际选择上下锥顶并验证边界；没有把三维延拓、边界包含或高度指标结论作为额外假设。
  这里的底面相对邻域条件还须在后续平面凸化的具体底盘上实例化。

三模块聚焦检查均 exit=0、零 warning；原直接消费者 `SimplexCornerExtension.lean` 兼容检查 exit=0、零 warning。
`AuditF123.lean` 审计十八项（包含保留的旧接口），全部仅标准三公理。检查用时分别为 13.1、10.6、11.3、10.8 秒。
M1 仍未验收：未完成带指定临界点的平面凸化、整层多边形分解及小幅转轴后的严格降指标；
M2/M3 与两个最终端点仍未完成。下一层结果见 §18.4。

### 18.4 水平盘的保高度凸化（未控制指定临界点，M1 仍进行中）

- `HeightExtension.lean` 的强版 `exists_isPLHomeomorphOn_extension_preserving_height_of_eqOn_compl`
  只要求底面自同胚固定 `L.space \ W`，允许外层底盘超出 W。径向公式证明：锥点若在 W 外，其底面点也在 W 外，
  因而被固定。上一层“整个底盘位于 W”版保留签名，由强版推出。
- `FiberCoordinates.lean` 的 `exists_affine_coordinates_of_linear_fiber` 在任意有限维空间中构造非零线性形式
  水平层的欧氏仿射坐标与线性左逆；`image_openSimplex_affineMap` 给精确开单形像。
- `LevelConvexification.lean` 的 `exists_isPLHomeomorphOn_convex_image_of_subset_fiber`：对任意三维有限维实范数空间、
  非零线性形式 ℓ、同一水平层内的 PL 2-盘 D，以及包含 D 的凸开集 W，构造全空间 PL 同胚 h，固定 W 外部，
  逐点保持 ℓ，令 `h '' D` 凸，并对每个集合保持 `heightIndex`。实际使用 S 的平面整直定理，构造大三角形底盘、
  固定边界与平面坐标共轭，再调用保高度延拓；已在具体底盘上消去上一层的相对邻域条件。

三模块最终检查分别为 11.0、10.2、13.6 秒，均 exit=0、零 warning。
`AuditF124.lean` 八项（含保留旧接口）全部仅标准三公理；最外层凸化端点只假定维数、非零高度、PL 盘、水平层及凸开邻域。
本结果没有控制指定临界点 P：若 P 位于 D 的边界，尚未保证 h(P) 是凸像盘的暴露点。因此仍缺
“去掉 h(P) 后凸盘严格位于经过 h(P) 的某直线一侧”的增强，以及球面沿层圆周切盘、轴旋转与严格降指标。
整层多边形分解及与原书奇异指标的对应也仍未闭合；M1/M2/M3 均未验收。下一审计文件 `AuditF125.lean`。

### 18.5 带指定点的保高度凸化（M1 的凸化部分闭合）

- `Homogeneity.lean`：单形内点间固定边界的 PL 自同胚、固定区间/弧端点的移动；
  `exists_isPLHomeomorphOn_simplex_vertex_star_map_eq` 在任意满维单形的同一开顶点星内移动两点，保持整个单形，固定给定开邻域外部。
  `exists_isPLHomeomorphOn_simplex_boundary_mem_vertices` 将任意边界点送到某个顶点。
- `PointedConvexification.lean`：`exists_linearMap_lt_on_convexHull_sdiff_singleton` 实际构造暴露单形顶点的非零线性形式；
  `exists_isPLHomeomorphOn_convex_image_strict_separation` 对平面 PL 2-盘 D 和任意不在其内部的指定点 p，构造支持在指定开邻域内的环境 PL 同胚，
  使像盘凸，且除去 h(p) 后严格位于过 h(p) 的直线一侧。p 在盘外的情形用严格分离，在边界的情形用顶点星移动。
- `LevelConvexification.lean` 的新强版 `exists_isPLHomeomorphOn_convex_image_strict_separation_of_subset_fiber`：
  三维空间、非零高度 ℓ、同一水平层内的 PL 2-盘 D，指定点 p 在该层且 `D ∉ 𝓝[{x | ℓ x = r}] p`；
  对包含 D 的任意凸开 W，构造全空间 PL 同胚 h 和非零线性形式 m，使 h 固定 W 外部、逐点保持 ℓ、像盘凸，
  并满足 `∀ x ∈ h '' D \ {h p}, m (h p) < m x`，同时对每个集合保持 `heightIndex`。
  外层底盘实际包含 D 与 p，因此对指定点的搬运有精确公式。旧的无指定点端点保留签名，并由强版推出。

三个模块最终聚焦检查分别为 10.1、12.5、12.8 秒，均 exit=0、零 warning。
`AuditF125.lean` 九项均仅标准三公理，并检查了强版的完整参数；没有修改或增加 `SchoenfliesInput` 字段。
M1 的凸化与指定点控制已经闭合；仍缺球面沿水平圆周切成 PL 盘、一般位置层的多边形分解与指标对应、
小幅转轴后每片的严格降指标。M1 尚未验收；M2/M3 和两个最终端点均未完成。下一审计文件 `AuditF126.lean`。

### 18.6 严格半空间条件下恢复一般位置（M1 旋转的几何输入）

`HeightPerturbation.lean` 的 `exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace_of_isPolyhedron`：
给定任意有限维实范数空间、有限集合 A/B、非零连续线性高度 ℓ、同层有限多面体 D，以及严格分离 `D \ {p}` 与 p 的线性形式 m，
对任意 ε > 0 构造高度 f，使算子距离 `dist f ℓ < ε`，f 非零且在 A 上单射，保持 B 上原有的一切严格高度次序，
并对所有 `x ∈ D \ {p}` 保证 `f p < f x`。证明先沿 m 小幅改变 ℓ，再在保持有限严格不等式的开邻域内调用 F5.1 的一般位置选择。
用有限三角剖分的顶点凸包控制整个 D，不要求 D 是单形或凸集；对相反高度应用本定理给另一侧的倾斜。
`linearMap_lt_on_convexHull_sdiff_singleton` 不要求仿射独立；`eventually_preserves_strict_order` 不要求有限维。

聚焦检查 exit=0、零 warning、12.5 秒；`AuditF126.lean` 四项均仅标准三公理。
本结果只控制高度函数与侧别，没有宣称新旧奇异点的包含关系或多边形数不增；这些才是严格降指标尚待证明的几何部分。
球面 PL 切盘仍需实现：Moise 10.2 原陈述只给拓扑 2-盘，现有平面 P.1 不能直接作为球面 PL 切盘证明。
尚未增加接口字段。M1/M2/M3 均未验收，下一审计文件 `AuditF127.lean`。

### 18.7 正则水平层的有限不交多边形分解

- `SimplicialComplex/EdgeGraph.lean`：任意几何复形的边图、有限顶点集、图邻点与几何邻点的精确对应及基数相等。
  边图仅使用复形定义所需的代数结构，没有增加实数、拓扑或有限维假设。
- `PolygonalCycles.lean`：`exists_polygonalCircle_of_isCycle` 将边图中的单环构造成实际 `PolygonalCircle`，
  显式验证相邻边交点与非相邻边不交；顶点像恰为图环顶点，每条图环边包含于所得多边形。
  `exists_polygonalCircle_decomposition` 对有限平面一维闭组合流形，以图连通分量索引多边形，证明全空间覆盖与两两不交。
  `exists_finite_isPLSphere_decomposition` 给有限 PL 圆周族的内在表述，允许空流形。
- `LevelPolygons.lean`：`exists_finite_isPLSphere_decomposition_of_subset_fiber` 用仿射平面坐标与 PL 流形不变性搬运到三维空间中的平面。
  `exists_finite_isPLSphere_decomposition_fiber` 对任意有限三维空间中的二维闭组合流形、非零线性高度以及不经过任何剖分顶点的层，
  构造有限个两两不交的 PL 圆周，其并集恰为该水平截面；不需要高度在所有顶点上单射。

三个模块最终聚焦检查分别为 7.4、12.0、12.7 秒，均 exit=0、零 warning。
`AuditF127.lean` 十三项均仅标准三公理，核对了水平层端点的完整签名。
本层只闭合不经过顶点的正则水平层分解；含顶点层的一点分叉分解、与 `levelPolygons` 的精确对应、
球面 PL 切盘及严格降指标仍未完成。没有增加 `SchoenfliesInput` 字段，M1/M2/M3 均未验收。下一审计文件 `AuditF128.lean`。

### 18.8 正则层的规范圆周族与计数判据

- `CurveInclusion.lean`：有限一维闭组合流形的子流形具有相同邻点，任何与子流形相交的原单形都属于子流形，
  从而子流形在原流形中既开又闭。`eq_of_subset_of_isPLSphere_one` 据此证明同一有限维实范数空间中两个 PL 圆周若有包含关系即相等。
  `IsPLSphere.isConnected_one` 单独去除了目标空间的有限维假设。
- `Connected/FinitePartition.lean`：任意拓扑空间中，非空连通集若包含于有限个两两不交闭集的并，则恰包含于其中唯一一个成员。
- `CirclePartition.lean`：`setOf_isPLSphere_one_subset_sUnion_eq` 证明有限不交 PL 圆周族之并中的全部 PL 圆周恰为原族；
  并集是 PL 圆周当且仅当连通，也当且仅当该族的 `encard = 1`。
- `LevelPolygons.lean` 增加 `levelPolygons_eq_of_finite_disjoint_cover` 及不经过剖分顶点的层的规范族 API：
  `finite_levelPolygons_of_ne_vertex_heights`、`pairwiseDisjoint_levelPolygons_of_ne_vertex_heights`、
  `sUnion_levelPolygons_of_ne_vertex_heights`；`isPLSphere_one_fiber_iff_isConnected` 与
  `isPLSphere_one_fiber_iff_encard_levelPolygons_eq_one` 将正则层球性与连通性、原指标使用的计数精确对接。

四模块最终聚焦检查分别为 11.9、7.1、12.2、12.2 秒，均 exit=0、零 warning；
`AuditF128.lean` 十九项（含保留的两个分解端点）均仅标准三公理。
正则层的分解和规范计数已经闭合，含顶点层的一点分叉分解、奇异层指标对应、球面 PL 切盘与 Lemma 1 严格下降尚未闭合。
未增加 `SchoenfliesInput` 字段；M1/M2/M3 均未验收。下一审计文件 `AuditF129.lean`。

### 18.9 含顶点层的圆周覆盖

- `Combinatorics/EvenDegree.lean`：有限图中除一个指定顶点外均为偶度，则该顶点亦为偶度；全偶度图没有桥，
  每条边都落在一个单环上。特别地，除一个指定顶点外均为二度时，仍得到逐边的单环覆盖。
- `PlanarCycleRealization.lean`：`exists_isPLSphere_one_of_isCycle_of_subset_fiber` 将三维空间水平层中有限复形的图环
  搬运到仿射平面，构造实际 PL 圆周，并包含该图环的每条几何边。
- `SingularLevelPolygons.lean`：`exists_isPLSphere_one_of_mem_space_of_degree_eq_two_except` 对平面内除一点外均为二度的有限线性图，
  证明每个其他点均包含于图内的某个 PL 圆周。`fiber_eq_singleton_union_sUnion_levelPolygons` 将 F5.1 的精确层剖分代入，
  证明有限闭二维组合流形的顶点水平层恰为该顶点与全部层内 PL 圆周的并；没有添加层分解假设。

三个模块最终聚焦检查分别为 7.9、11.7、12.3 秒，均 exit=0、零 warning。
`AuditF129.lean` 八项均仅标准三公理，已核对水平层覆盖端点的完整签名。
本层尚未证明不同圆周只能相交于该顶点，也尚未将顶点 crossing 与局部二度完全对应。
球面 PL 切盘和 Lemma 1 严格降指标仍未闭合；M1/M2/M3 均未验收，`SchoenfliesInput` 未增加字段。下一审计文件 `AuditF130.lean`。

### 18.10 临界层中圆周的交集与孤立点

- `Connected/Loop.lean`：`isConnected_image_Icc_sdiff_singleton` 对稠密条件完备线序区间上的连续单闭曲线，
  证明像集去掉任意一点后仍连通；目标只需拓扑空间，不要求 Hausdorff，参数不限制为实数。
- `CurveInclusion.lean` 将邻点相等和面包含的主引理推广为只要求指定顶点在大复形中恰有两个邻点，
  原一维闭组合流形接口保留签名并由此推出。
- `CircleIntersection.lean`：PL 圆周去掉一点后连通且没有孤立点；除指定点外均为二度的有限线性图中，
  圆周在去掉该点的图中既开又闭。因此两个圆周若在其他点相交，必相等。
- `SingularLevelPolygons.lean`：`inter_subset_singleton_levelPolygons_of_ne` 与
  `pairwiseDisjoint_sdiff_singleton_levelPolygons` 证明顶点层中不同圆周只能在该顶点相交。
  `singleton_mem_nhdsWithin_fiber_iff_notMem_sUnion_levelPolygons` 精确刻画孤立顶点，
  `mem_sUnion_levelPolygons_of_mem_heightSingularPoints` 保证每个指标中的奇异点位于层圆周上。

四模块最终聚焦检查分别为 6.5、11.5、12.1、12.5 秒，均 exit=0、零 warning。
`AuditF130.lean` 十四项（含保留的两个旧接口）均仅标准三公理。
临界层的有限圆周覆盖、交点唯一性、孤立点与规范圆周族的对应现已闭合；尚未证明局部二度与顶点 crossing 等价。
球面 PL 切盘、轴旋转后的逐点指标比较及 Lemma 1 严格下降仍未闭合，M1/M2/M3 均未验收。
`SchoenfliesInput` 未增加字段；下一审计文件 `AuditF131.lean`。

### 18.11 球面沿 PL 圆周切成两个 PL 盘

- `ConvexFrontier.lean`：任意实范数空间中的紧集，若其 frontier 包含于非空开凸集，则整个紧集也包含于该开凸集。
  证明用严格分离与线性函数在紧集上的最大值，不增加有限维假设。
- `ClosedStarNeighborhood.lean`：任意有限闭组合流形的每个点，在任意指定环境邻域内有一个 PL 盘邻域；
  先把该点细分为顶点，再用两开集覆盖控制其闭星。
- `BallFrontier.lean` 新增 `IsPLHomeomorphOn.image_stdSimplexBoundary`，精确给出全维 PL 盘参数化的边界像。
- `SphereDisk.lean`：先在四面体边界上取避开圆周的小盘，用 S.2 的 17.5 将小盘整直到原始面，
  使圆周落入剩余顶点星的平面图；用 P.1 填盘及开凸集包含引理拉回第一片，再用一次 17.5 构造互补片。
  `exists_disk_decomposition_of_isPLSphere_one_subset_two` 对任意有限维实范数空间中的
  `IsPLSphere 2 S`、`IsPLSphere 1 J` 与 `J ⊆ S` 给出两个参数化 PL 2-盘，
  并集恰为 S、交集恰为 J，且两盘的标准单形边界像均恰为 J。
  另有任意维单形顶点星的参数化及其精确边界像。

四模块最终聚焦检查分别为 9.2、9.4、12.1、12.1 秒，均 exit=0、零 warning。
`AuditF131.lean` 九项（含原 `IsPLBall.isPLSphere_frontier`）仅标准三公理，已核对一般切盘端点完整签名。
本层没有扩充 `SchoenfliesInput`，没有使用 Moise 10.2 的拓扑盘陈述代替 PL 盘。
球面 PL 切盘已经闭合；下一步为封帽球性、局部二度与 crossing 的对应及转轴后的逐点指标比较。
Lemma 1 严格下降仍未闭合，M1/M2/M3 均未验收。下一审计文件 `AuditF132.lean`。

### 18.12 换盘与封帽球性

- `PLHomeomorph.lean` 增加任意有限多面体上恒等映射的 PL 接口，不需要有限维假设。
- `PLHomeomorphGluing.lean` 的新主定理 `exists_isPLHomeomorphOn_union` 允许源、目标位于不同有限维空间，
  两片的目标可以不同；要求重叠处相容并覆盖恰当的目标交集。旧接口签名保留，改为新主定理的特例。
- `BallReplacement.lean`：参数化盘的标准边界像是 PL 球面；两个盘的参数边界间任意 PL 同胚均可延拓至盘；
  `exists_isPLHomeomorphOn_replace_ball` 将一个盘换成具有同一边界的新盘，并逐点固定保留部分。
- `SphereCut.lean`：`exists_isPLSphere_pair_of_spanning_disk` 从 PL 2-球面 S 及参数化 PL 2-盘 D、
  `S ∩ D = g '' stdSimplexBoundary 2` 构造球面切开的两盘及两封帽 PL 2-球面；
  证明两封帽球面交集恰为 D，且从其并中删去 `D \ (g '' stdSimplexBoundary 2)` 后恰恢复 S。

四模块最终聚焦检查分别为 12.0、8.1、8.9、10.6 秒，均 exit=0、零 warning。
`AuditF132.lean` 七项（含旧拼接接口）仅标准三公理，已核对封帽端点完整签名。
没有增加 `SchoenfliesInput` 字段；封帽球性不作为输入假设。
仍缺奇异层的内最圆周选择、局部二度与 crossing 的对应、转轴后的逐点指标比较及 Lemma 1 严格下降。
M1/M2/M3 均未验收。下一审计文件 `AuditF133.lean`。

### 18.13 最内水平圆周与张成盘

- `PlanarJordan/Innermost.lean` 将最内 Jordan 圆周定理推广到不同圆周的交集仅能包含指定一点；
  去掉该点后的连通性及稠密性保证最小内域不包含其他圆周。原两两不交接口保持签名。
- `InnermostLevel.lean` 的 `exists_innermost_isPLBall` 给有限平面 PL 圆周族中的一条圆周及填充盘，
  整族与盘的交集恰为所选圆周。`exists_spanning_disk_of_mem_heightSingularPoints` 对三维空间中的有限闭二维组合流形、
  顶点上单射的非零高度及其奇异点，构造实际参数化水平 PL 2-盘；盘与流形交集恰为参数边界，
  位于指定的包含流形的凸开邻域内，且奇异点不在盘的平面相对内部。

两个模块最终聚焦检查分别为 9.6、12.4 秒，均 exit=0、零 warning。
检查时发现共享 `BallFrontier.olean` 缺少本车道已提交的边界像引理，按原脚本刷新后 exit=0（13.1 秒）。
`AuditF133.lean` 七项仅标准三公理，已核对张成盘端点完整签名。
没有增加 `SchoenfliesInput` 字段；奇异层最内圆周及张成盘已闭合。
局部二度与 crossing 的对应、转轴后的逐点指标比较及 Lemma 1 严格下降仍未闭合，M1/M2/M3 均未验收。
下一审计文件 `AuditF134.lean`。

### 18.14 切盘的层圆周计数与盘外奇异点

- `CircleIntersection.lean` 新增 PL 圆周去掉任意一点后在原圆周中稠密的 API；不要求环境有限维。
- `HeightCut.lean` 证明奇异点只依赖曲面局部集合芽、封帽盘之外的奇异点精确对应原曲面的保留部分。
  离开封帽高度，原层圆周族分成两片圆周族的不交并，其基数相加；在切割高度，不同原层圆周只在一个指定点相交时，
  每条其他圆周完整落在某一保留片中，两片圆周族交集恰为切割圆周，因此两片圆周数之和等于原数加一。
- `SingularHeightCut.lean` 的 `exists_isPLSphere_pair_of_mem_heightSingularPoints` 从有限 PL 2-球面三角剖分、
  顶点上单射的非零高度及奇异点出发，产生水平张成盘、两保留 PL 盘和两封帽 PL 球面；
  同时给出精确并、交、恢复原球面等式、切割高度与其他高度的圆周计数、盘外奇异点等式及指定凸开邻域控制。
  层圆周的交点条件由原剖分的一般位置引理推出，没有加入新假设。

三个模块最终聚焦检查分别为 12.3、11.2、13.7 秒，均 exit=0、零 warning。
`AuditF134.lean` 十四项（含原圆周交点端点）仅标准三公理，已核对组合端点完整签名。
没有增加 `SchoenfliesInput` 字段。本层的计数等式针对旋转前的保留片和封帽球面的非封帽高度，
尚不等于转轴后的逐点指标比较。局部二度与 crossing 的对应、小幅转轴后的严格下降及 Lemma 1 归约仍未闭合。
M1/M2/M3 均未验收；下一审计文件 `AuditF135.lean`。

### 18.15 小幅转轴的载体内顶点投影

- `HeightProjection.lean`：高度 ℓ 在原剖分顶点上单射时，旧临界层上除其原顶点外的每一点均有位于载体方向空间内的非水平向量。
  对足够接近 ℓ 的线性形式 f，沿该向量将点投影至 `f x = f p`，位移任意小且仍在原载体面的相对内部。
  有限点族可同时投影；固定族外、原剖分顶点及旧层外的点。前四个投影引理不需要有限维环境。
- `eventually_exists_isPLHomeomorphOn_move_fiber_vertices` 把任意给定有限共同剖分的这些顶点位移延拓为环境 PL 同胚，
  位移任意小，固定指定开邻域外；在该剖分每个面上仿射，旧层顶点映到新层，位于原曲面上的剖分顶点仍在各自载体面相对内部。
  这是原 `GeneralPosition.lean` 的小顶点扰动延拓定理的几何输入生产者，没有调用或扩充 `SchoenfliesInput`。

模块最终聚焦检查 exit=0（12.2 秒），零 warning；`AuditF135.lean` 五项仅标准三公理，已核对环境延拓端点完整签名。
本层尚未从顶点控制推出整个曲面的像集不变、整个层的搬运或奇异点稳定；这些仍需共同剖分与像集满射的证明。
局部二度与 crossing 的对应、小幅转轴后的逐点指标比较及 Lemma 1 严格下降仍未闭合，M1/M2/M3 均未验收。
下一审计文件 `AuditF136.lean`。

### 18.16 同维球面包含判据与转轴时保持整个球面

- `InvarianceOfDomainManifold.lean`：紧致非空流形到同维连通 Hausdorff 流形的连续单射必满射，由开像、紧像闭性和连通性推出。
- `PLBallSphere.lean`：标准单形的正维边界、任意 PL 盘及正维 PL 球面的连通性，均不要求目标环境有限维。
- `SphereInclusion.lean`：同维正维 PL 球面之间的连续单射，只要映入目标球面即满射；同维球面的包含关系必为相等。
  自映射的像集相等只要求连续、单射及映入，不要求额外 PL 假设。
- `CurveInclusion.lean` 保留两个原一维接口的完整签名，改为上述一般定理的推论，并移除其不再需要的平面整直导入。
- `CarrierInvariance.lean`：在原复形的细分上逐面仿射，且每个新顶点映入其原载体面的凸包，则每个原单形保持映入自身。
  对 PL 球面上的连续单射，该条件保证整个球面像集相等。
- `HeightStability.lean` 的 `eventually_exists_isPLHomeomorphOn_preserving_sphere_move_fiber` 将载体投影、环境延拓及满射判据拼合：
  对包含球面细分的给定有限共同剖分，足够小的转轴可由任意小的环境 PL 同胚实现，固定原顶点及指定开邻域外，
  保持整个球面，并将旧高度层中的整张共同剖分面映入新高度层。

六个改动模块最终聚焦检查分别为 11.1、11.1、9.7、10.0、11.3、11.7 秒，均 exit=0、零 warning。
受接口推广影响的 `CircleIntersection.lean` / `CirclePartition.lean` 复检分别为 11.6、11.9 秒，均 exit=0、零 warning。
`AuditF136.lean` 十三项（含保留的两个一维接口）仅标准三公理，已核对转轴端点完整签名。
没有增加 `SchoenfliesInput` 字段。还需要生产同时适配原剖分与高度分割的共同剖分，证明完整层的双向对应，
再证明 crossing / 奇异点稳定及封帽后选定高度附近的严格下降；M1/M2/M3 均未验收。
下一审计文件 `AuditF137.lean`。

### 18.17 共同高度剖分与完整临界层搬运

- `HeightSubdivision.lean` 从任意有限复形 K、有限多面体 D 和仿射高度构造共同三角剖分 R：
  空间恰为 K.space ∪ D，限制到 K.space 是原复形的细分，限制到 D 恰好覆盖 D，每个新单形完整位于指定高度平面的一侧。
- `HeightFiber.lean` 用正重心坐标证明：单形处于高度平面同侧时，相对内部点位于平面当且仅当全部顶点位于平面。
  从逐面仿射与顶点符号数据得到完整高度层的双向对应；层圆周族及基数的搬运只要求指定层的精确像集等式。
- `HeightStability.lean` 保留旧整面搬运接口，把共同剖分和顶点符号稳定拼入环境延拓。
  `eventually_exists_homeomorph_preserving_sphere_image_fiber` 对有限正维 PL 球面、顶点上单射的非零高度和一个原顶点，
  构造任意小的环境 PL 同胚，固定原顶点及指定开邻域外，保持整个球面，并将整个旧临界截面恰好映到新截面。
  同时在该顶点附近把整个旧平面的像与新平面对应为相同集合芽；证明让共同剖分包含一个环境多面体邻域，不另设平面满射假设。

三个模块最终聚焦检查分别为 12.1、10.8、11.7 秒，均 exit=0、零 warning。
`AuditF137.lean` 十一项（含保留的旧接口）仅标准三公理；已核对完整截面搬运端点签名。
没有增加 `SchoenfliesInput` 字段。下一步从本层推出 crossing、奇异点及指标的局部稳定，
再处理水平封帽后选定高度附近的严格指标下降；M1/M2/M3 均未验收。下一审计文件 `AuditF138.lean`。

### 18.18 一般位置高度附近的指标稳定

- `HeightRotation.lean` 从完整截面与平面芽的环境 PL 搬运推出：每个原顶点处的 crossing 性质和截面孤立性保持，
  因而是否属于 `heightSingularPoints` 保持；整层 `levelPolygons` 的基数也保持。
- 对有限 PL 2-球面、三维环境和顶点上单射的非零高度，有限交给同时适用于全部顶点的扰动邻域。
  小扰动仍非零且顶点单射；非顶点处的既有 crossing 定理排除额外奇异点，故新旧奇异点集合相等。
- `eventually_heightIndex_eq` 沿相等奇异点集的子类型等价搬运求和，给出任意足够小的线性高度扰动下的指标相等。
  没有把 crossing 稳定、指标比较或整层基数作为新假设。

模块最终聚焦检查 exit=0（14.0 秒）、零 warning；`AuditF138.lean` 三项仅标准三公理，端点完整签名已核对。
这是旧高度在原剖分顶点上单射时的稳定定理。水平封帽后多个顶点位于同一旧层，不能直接使用本定理；
仍需处理该退化层、凸化引入的剖分和封帽后的严格降指标。没有扩充 `SchoenfliesInput`，M1/M2/M3 均未验收。
下一审计文件 `AuditF139.lean`。

### 18.19 允许其他高度层退化的临界层稳定

- `HeightProjection.lean` 增加三个 `of_unique_vertex_in_fiber` 强版。它们只要求当前层的原顶点至多为 p：
  `∀ v ∈ K.vertices, ℓ v = ℓ p → v = p`，不要求不同高度层的所有顶点一般位置。
  若 x ≠ p 在当前层，则其载体必有一个不同高度的顶点 v；方向 v - x 属于载体方向空间且高度非零，给出所需投影。
- `HeightStability.lean` 将强版推广到保持球面、整层像集相等和原顶点处平面芽对应的环境 PL 同胚。
  `HeightRotation.lean` 的点态强版及 `eventually_heightSingularPoints_inter_eq_and_levelPolygons_encard_eq`
  给出任意满足上述单层唯一性的一族原顶点上，奇异性与整层圆周数同时保持。
- 所有旧的顶点单射接口保留完整签名，证明改为新强版的推论；既有全局 `eventually_heightIndex_eq` 不变。

三个改动模块最终聚焦检查分别为 10.9、12.1、11.2 秒，均 exit=0、零 warning。
`AuditF139.lean` 二十二项（含全部保留接口）仅标准三公理，强版端点签名已核对。
没有增加 `SchoenfliesInput` 字段。本层允许其他层退化，但不涵盖选定层的多顶点水平封帽；
还需证明封帽边缘的 crossing/孤立分类、凸化后的剖分控制及严格降指标。M1/M2/M3 均未验收。
下一审计文件 `AuditF140.lean`。

### 18.20 非水平面与保高度 PL 图卡下的 crossing 稳定

- `TransverseHeight.lean` 给仿射平面与高度层的 crossing 判据。对有限二维组合带边流形，只要求当前载体面的方向空间内
  有一个非水平向量，即可推出 crossing；不要求整份剖分一般位置。非水平条件在小幅线性高度扰动下保持。
- `CrossingStability.lean` 从一个 PL Lipschitz 映射 G 构造沿平面内非水平向量的位移：
  改变量为新旧线性形式之差作用于 G。扰动足够小时，位移的 Lipschitz 常数小于 1，因而得到环境 PL 同胚，
  固定原点并保持整个指定子空间，同时具有精确高度公式。
- `eventually_hasPLCrossingAt_of_height_preserving_chart` 对一个局部保高度的环境 PL 图卡，且曲面芽是非水平平面的图卡像，
  证明所有足够小的线性高度扰动仍在图卡中心 crossing。图卡只需局部保高度；其局部 PL 数据用既有延拓定理变成 Lipschitz 输入。
  该结论没有剖分顶点单射条件，可供凸化后的非临界点使用，但具体保高度图卡仍须由几何构造提供。

两模块最终聚焦检查分别为 11.9、10.5 秒，均 exit=0、零 warning；`AuditF140.lean` 六项仅标准三公理。
已核对图卡端点完整签名，没有将 crossing 或指标比较放入假设，也没有扩充 `SchoenfliesInput`。
下一步从原两上覆面整直构造中导出保高度图卡，随后处理水平封帽边缘与严格降指标。M1/M2/M3 均未验收。
下一审计文件 `AuditF141.lean`。
### 18.21 非水平载体面的实际保高度图卡

- `GeneralPosition.lean` 的射线、两半空间和两上覆面整直增加逐点位移属于指定子空间的强版；三个旧接口保留完整签名。
  在边的方向空间与高度核互补时，取该子空间为高度核，得到整直过程严格保持高度差。
- `HeightChart.lean` 的 `exists_height_preserving_chart_of_transverse_face` 对有限闭二维组合流形的任意非水平载体面，
  构造全空间 PL 同胚图卡，曲面芽是二维子空间的图卡像，且逐点满足精确高度公式。图卡生产者不要求环境恰为三维。
- `eventually_hasPLCrossingAt_image_fiber_of_notMem_vertices` 在三维环境中，从原剖分顶点上单射的高度出发，
  证明任意保高度环境 PL 同胚后，每个原非顶点的像都在充分小的转轴下保持 crossing。
  此结论适用于凸化时引入的有限新顶点，没有加入图卡存在性或 crossing 结论作为输入。

两个模块最终聚焦检查分别为 29.0、10.7 秒，均 exit=0、零 warning；`AuditF141.lean` 九项（含三个旧整直接口）仅标准三公理。
已核对两个图卡端点完整签名。没有扩充 `SchoenfliesInput`，M1/M2/M3 均未验收。
下一步用凸化支集与其他临界高度的分离控制整层圆周数，继续处理水平封帽边缘与严格降指标。
下一审计文件 `AuditF142.lean`。
### 18.22 凸化支集外的临界点与整层比较

- `HeightLocalization.lean` 证明紧集与旧高度层不交时，所有充分小的新高度扰动仍避开该紧集。
  若同胚固定紧支集外且封帽盘包含于支集，则支集外高度层的封帽圆周族恰为保留片的圆周族。
- `eventually_mem_heightSingularPoints_image_cap_iff_and_encard_levelPolygons_le` 对支集外的原临界层，
  证明新封帽曲面的奇异性等价于原曲面奇异且属于保留片，新层圆周数不超过原临界层圆周数。
- `eventually_heightSingularPoints_image_cap_sdiff_subset_vertices` 用实际保高度图卡及有限顶点族的一致扰动邻域，
  排除封帽盘之外的新奇异点：新高度在封帽剖分上一般位置时，盘外奇异点必是原剖分顶点的像。
- `exists_convex_open_neighborhood_disjoint_fibers` 实际构造含水平盘的凸开邻域 U 和包含 U 的紧集 C，
  同时让 C 避开有限个其他指定高度层。U 可限制在原指定凸开邻域内，可直接供保高度凸化使用。

模块最终聚焦检查 exit=0（10.1 秒）、零 warning；`AuditF142.lean` 六项仅标准三公理，两个生产端点完整签名已核对。
没有扩充 `SchoenfliesInput`。支集外的临界层比较与盘外的新奇异点排除已闭合；
接下来拼入实际封帽、局部凸化和有限剖分构造，再处理封帽边缘和选定临界点的严格指标下降。
M1/M2/M3 均未验收。下一审计文件 `AuditF143.lean`。
### 18.23 实际凸封帽与盘外比较的统一生产者

- `HeightLocalization.lean` 新增统一比较：若凸化支集避开除 p 外的原顶点高度，则转轴后封帽盘及 H(p) 之外的奇异点
  包含于原奇异点集；每个其他原顶点的奇异性恰对应其所在保留片，整层圆周数不增。
- `ConvexHeightCut.lean` 的 `exists_isPLSphere_pair_of_singular_height_with_convex_cap` 从原有限 PL 2-球面、
  一般位置高度、实际奇异点和指定凸开邻域出发，构造水平盘、两保留盘、两封帽球面及保高度凸化同胚。
  同胚固定邻域外和除 p 外的所有原顶点；像盘凸，且 H(p) 严格分离像盘除该点外的部分。
- 端点同时生产两份有限封帽球面剖分，并证明小幅一般位置转轴后，每片盘外的奇异点包含和其他原顶点的圆周计数比较。
  水平盘、凸化支集、图卡和新剖分均由证明产生，没有将这些存在性或比较结论放进假设。
  原切盘的交、并、恢复原球面以及切割层圆周数之和为原数加一的等式继续保留。

两模块最终聚焦检查分别为 10.1、10.2 秒，均 exit=0、零 warning；`AuditF143.lean` 两项仅标准三公理。
已核对端点参数及两片的返回条件，没有扩充 `SchoenfliesInput`。M1 尚缺封帽边缘的 crossing/孤立分类、
选定点处移去一条层圆周的严格比较与降指标归约；局部二度与 crossing 的对应还需为该分类及 M2 提供支撑。
M1/M2/M3 均未验收。下一审计文件 `AuditF144.lean`。
### 18.24 封帽相对内部的 crossing 与边界交集数据

- `FiberInterior.lean` 从参数化 PL 盘的标准边界像出发，证明不在该像中的盘点具有所在仿射高度层内的相对邻域。
  第一端点对余维一的任意正维 PL 盘成立；证明通过高度层的仿射坐标及已证盘的实际 frontier 定理搬运。
- 在三维空间中，封帽盘的相对内部附近若没有保留片，曲面芽就是该仿射平面。新高度在 q 与同旧高度层的指定 p 处不同，
  则 q-p 是平面内非水平向量，从而得到 crossing。若整个 D\{p} 都与 p 的新高度不同，盘内奇异点仅可能在参数边界或 p。
- `SingularHeightCut.lean` 的强版额外返回已有证明中的 `K.space ∩ D = g '' stdSimplexBoundary 2`；旧接口保留完整签名。
  `ConvexHeightCut.lean` 继续返回该精确交集，并将相对内部排除接入其实际构造的两片球面，异常集合从整盘缩小至像边界与 H(p)。
  新高度的分离条件是显式几何条件，已有 `HeightPerturbation.lean` 可通过任意小的严格单侧转轴产生。

三模块最终聚焦检查分别为 9.7、10.0、10.2 秒，均 exit=0、零 warning；`AuditF144.lean` 七项（含旧切盘接口）仅标准三公理。
已核对相对内部与盘内奇异点端点签名。没有增加 `SchoenfliesInput` 字段。
仍需封帽边缘的单侧接近与 crossing/孤立分类，以及选定点的圆周数严格下降；M1/M2/M3 均未验收。
下一审计文件 `AuditF145.lean`。
### 18.25 两保留盘沿水平圆周的相反单侧接近

- `BallFrontier.lean` 新增参数化正维 PL 盘去掉标准边界像后的稠密性，不要求目标环境与盘同维。
- `HeightSides.lean` 首先证明局部闭分割的半空间分类：在一个子空间附近，两闭集的交恰为线性高度零集，
  且两片去掉对方后都逼近中心，则两片各占正、负半空间。证明使用凸半球的连通性，不要求有限维环境。
- 对有限闭二维组合流形的一般位置高度，除唯一临界顶点外，任一所选层圆周与整个高度截面具有相同集合芽。
  实际保高度图卡将两保留盘搬到上述闭分割模型，得到逐点单侧分类。
- `eventually_mem_opposite_halfSpaces_along_levelPolygon_disk_partition` 从两盘的实际 PL 参数化和共同参数边界出发，
  用穿孔圆周的连通性排除侧别改变，证明沿整个 J\{p}，A、B 始终分别占相反的两个高度半空间，允许整体交换方向。
  因而原书“D₁ 从一侧接近 J\{p}，D₂ 从另一侧接近”的陈述已闭合，不作为新增输入假设。

两模块最终聚焦检查分别为 10.2、10.1 秒，均 exit=0、零 warning；`AuditF145.lean` 六项仅标准三公理。
已核对相反单侧端点的完整签名，没有扩充 `SchoenfliesInput`。
仍需将该侧别接入凸封帽后的局部图卡，证明转轴后封帽边缘的 crossing/孤立分类与选定点的圆周数严格下降。
M1/M2/M3 均未验收。下一审计文件 `AuditF146.lean`。

### 18.26 保持圆周及截弧给定值的平面盘延拓

- `CrosscutExtension.lean` 的 `exists_isPLHomeomorphOn_eqOn_crosscut` 将两圆周与其正规截弧之并上的任意 PL 同胚
  延拓到两个闭内域，逐点保持整个给定映射。证明以截弧切出两个 PL 盘，分别调用已证 P.1 和实际 frontier 延拓，再沿截弧拼合。
- `exists_isPLHomeomorphOn_eqOn_curve_and_crosscut` 允许圆周与截弧分别给定 PL 映射，只要求两端点值一致。
  `exists_isPLHomeomorphOn_map_crosscut_eqOn_curve` 保持给定圆周映射并将源截弧映到目标截弧；截弧参数匹配由现有区间 PL 接口产生。
- 本层复用原版 `PolygonalSchoenflies.lean`，没有修改或复制其他车道的文件，也没有增加 `SchoenfliesInput` 字段。

模块最终聚焦检查 exit=0（9.6 秒）、零 warning；`AuditF146.lean` 三项仅标准三公理，已核对两个相对端点完整签名。
下一步将相对截弧延拓用于顶点链环的 crossing 判据，再处理凸封帽边缘与严格降指标。
M1/M2/M3 均未验收。下一审计文件 `AuditF147.lean`。

### 18.27 嵌入任意有限维空间的 PL 盘相对截弧延拓

- `DiskCrosscutExtension.lean`（初名 `DiskCrosscut.lean`，整合时避免与 S 车道同名文件冲突而改名）证明平面 PL 1-盘满足 vendored Jordan API 的 polygonal 条件，并把实际区间参数化的正规盘内弧搬到平面截弧。
- `exists_isPLHomeomorphOn_eqOn_disk_crosscut` 允许源、目标盘位于不同的有限维实范数空间。两盘的边界均由实际标准盘参数化给出；
  源截弧带区间 PL 参数化，恰在两端点与边界相交。给定边界及截弧之并上的 PL 同胚若分别映到目标边界和目标盘内弧，
  则可延拓到整个盘，并逐点保持给定映射。目标弧的正规性和两端点对应由这些几何数据推出，没有额外假定。
- 证明构造两盘的平面坐标，调用上一层相对延拓，再搬回；适用于三维链环的半盘。

模块最终聚焦检查 exit=0（9.8 秒）、零 warning；`AuditF147.lean` 三项仅标准三公理，已核对主端点完整签名。
下一步构造一般 PL 圆周沿两个交点的弧分解，并接入链环整直；边缘 crossing 和严格降指标仍未完成。
没有扩充 `SchoenfliesInput`，M1/M2/M3 均未验收。下一审计文件 `AuditF148.lean`。

## 19. 夜间 F-M1–F-M6 接续（NIGHT_PLAN.md，整合基线 8fb887bb9）

已取入 `origin/codex/moise-integration` 的 `8fb887bb9`，按夜间计划顺序继续。本轮先前的相对延拓交付：
`4e30320a0`（`CrosscutExtension.lean`，AuditF146 三项）与 `b08bc4be9`（嵌入盘版本，AuditF147 三项）。
整合的 add/add 冲突保留 S 车道 `DiskCrosscut.lean` 原文件，本车道模块改名为 `DiskCrosscutExtension.lean`；
其 polygonal 桥接改为复用整合的 `PolygonalArc.lean`。联合导入审计发现盘内部稠密性同名声明后，撤下本车道旧副本，
`BallFrontier.lean` 保持整合版本，`HeightSides.lean` 改为直接消费更一般的 `BallInterior.lean` 端点。

最终四模块聚焦检查（合并的 BallFrontier、本车道 HeightSides、CrosscutExtension、DiskCrosscutExtension）均 exit=0、零 warning；
`AuditF148.lean` 联合导入 S 的 `SchoenfliesFoundations`，十一项全部仅标准三公理。
`schoenflies_input` 的四个字段已由 S 车道实际证明，现可实例化既有 `SchoenfliesInput`，不是新增假设。

F-M1 当前仍为 partial：本车道旧 M1 的严格降指标尚未验收，确切义务是凸封帽转轴后的边缘 crossing/孤立分类、
选定点整层圆周数严格下降以及由此给出的 Lemma 1 归约；随后还需 Lemma 2–6 和最终拼装。I1 尚未交付。
当前相对截弧延拓为顶点链环 crossing 判据提供已证输入，没有把此判据或降指标结论加入接口。
F-M2–F-M6 尚未开始；按用户指定顺序推进，只有出现 §1 接口之外的真实数学障碍时，按夜间 §0.4 记录后跳到下一里程碑。
下一审计文件 `AuditF149.lean`。

### 19.1 F-M1：PL 圆周的两弧分解与高度半空间参数化

`CircleArcs.lean` 已提交并推送为 `b68aa84de`。`exists_arc_decomposition_of_isPLSphere_one` 将任意有限维实范数空间中的 PL 圆周沿两个不同指定点分为两条带实际区间参数化的 PL 弧，端点、并、交均有精确等式。区间像去掉端点后的连通性和闭包接口不要求目标有限维。
`exists_isPLHomeomorphOn_Icc_inter_of_fiber_pair` 仅从圆周上的连续实值函数、恰含两点的指定层及两侧非空，产生上下闭半空间截弧的参数化；证明由穿孔弧连通性确定侧别。

聚焦检查 exit=0（10.6 秒）、零 warning；`AuditF149.lean` 五项仅标准三公理，并核对高度截弧端点完整签名。F-M1 仍为 partial：下一步将两弧与相对盘截弧延拓接成顶点链环图卡，随后完成封帽边缘 crossing、严格降指标及 Lemma 2–6。I1 尚未交付；下一审计文件 `AuditF150.lean`。

### 19.2 F-M1：沿共同边界拼合的两盘及两条截弧的相对 PL 等价

`CirclePair.lean` 已提交并推送为 `b5df0cbf6`。`exists_isPLHomeomorphOn_pair_of_isPLSphere_one` 在任意两个有限维实范数空间中的 PL 圆周之间对齐任意两个不同指定点；`exists_isPLHomeomorphOn_map_crosscut_eqOn_boundary` 保持整个给定边界映射并对齐盘中正规截弧；`exists_isPLHomeomorphOn_disk_pair_eqOn_boundary` 将两侧延拓沿共同边界拼合。
主端点 `exists_isPLHomeomorphOn_disk_pair_map_crosscuts` 从两盘实际参数化、恰为共同边界的交集，以及两侧具有共同端点的正规截弧出发，构造同时映射两盘、公共边界、两截弧和两指定端点的 PL 同胚。边界映射在证明中构造，不是额外假设。源、目标环境可不同。

最终聚焦检查 exit=0（10.0 秒）、零 warning；`AuditF150.lean` 四项仅标准三公理，已核对主端点完整签名。下一步从实际星的链环和高度半空间生产此定理的两盘、截弧输入，再锥延拓得到 crossing 图卡。F-M1 仍为 partial，严格降指标及 Lemma 2–6、I1 尚未交付。下一审计文件 `AuditF151.lean`。

### 19.3 F-M1：链环的半空间切盘及参数边界

`LinkSection.lean` 已提交并推送为 `11107a0a1`。先证明适配仿射半空间的剖分限制具有预期像集、凸限制与顶点链环交换。`IsConeBase.mem_frontier_combo_iff` 把严格射线内点位于锥边界转化为底点位于底盘的组合边界；`IsConeBase.boundaryComplex_space_of_halfSpace_germ` 由锥在顶点附近恰为线性半空间，推出底盘边界恰为零高度截面。
`exists_isPLHomeomorphOn_geometricLink_halfSpace` 从有限复形覆盖顶点的实际邻域、非零线性高度和逐面半空间适配出发，产生链环正半空间部分的标准盘参数化，参数边界精确等于整个链环的零高度截面。维数结论为一般 n+1 维链环盘，环境维数 n+2；两侧可由高度取负得到。不假定所需参数化或边界识别结论。

聚焦检查 exit=0（10.2 秒）、零 warning；`AuditF151.lean` 五项仅标准三公理，已核对主端点完整签名。下一步把曲面链环的二点零截面接入两盘映射和锥延拓；F-M1 的 crossing、严格降指标、Lemma 2–6 与 I1 仍未完成。下一审计文件 `AuditF152.lean`。

### 19.4 F-M1：二点零截面的曲面链环配对

`LinkPair.lean` 已提交并推送为 `b8814ee06`。`exists_isPLHomeomorphOn_geometricLink_pair` 在两个三维有限复形的内部顶点链环之间构造 PL 同胚：两边各有一条实际 PL 圆周，非零线性高度在该圆周上的零截面恰含两个不同点，且圆周两侧非空。结论同时对齐圆周、整个链环的零截面、上下半盘及两个指定交点。所需半盘和截弧参数化全部由前两层构造，不作为输入假设。

聚焦检查 exit=0（10.7 秒）、零 warning；`AuditF152.lean` 主端点仅标准三公理。下一步锥延拓并证明曲面星及高度零面的准确对应，再构造标准平面目标。F-M1 仍为 partial，尚未得到 crossing 主判据或 I1；F-M2–F-M6 尚未开始。下一审计文件 `AuditF153.lean`。

### 19.5 F-M1：链环配对延拓为保子复形与高度层的星映射

`StarPair.lean` 已提交并推送为 `8bbc98bad`。`image_coneComplex_of_radial_eq` 由逐射线的锥映射公式证明任意指定子复形锥的像集相等；`image_coneComplex_inter_fiber_of_radial_eq` 证明锥内线性零截面的像集相等，线性形式允许为零。
`exists_isPLHomeomorphOn_closedStar_pair` 将环境链环的 PL 同胚延拓到环境闭星，同时对齐指定子复形的闭星、锥顶和整个闭星内的高度零截面。证明复用已有锥延拓，并逐点核对双向像集，不增加局部映射结论假设。

聚焦检查 exit=0（10.7 秒）、零 warning；`AuditF153.lean` 三项仅标准三公理。下一步生产标准平面目标的链环数据，再提取开邻域上的 crossing 图卡；随后仍需封帽边缘分类、严格降指标及 Lemma 2–6。F-M1 仍 partial，I1 尚未交付。下一审计文件 `AuditF154.lean`。

### 19.6 F-M1：平面局部模型的链环二点截面

`LinkSubspace.lean` 已提交并推送为 `2c924bb73`。`eventually_mem_closedStar_iff` 给闭星与复形的相同集合芽；`geometricLink_space_eq_inter_submodule_of_eventually` 从子复形在顶点附近等于仿射子空间，推出子复形链环精确等于环境链环与该仿射子空间的交。`exists_pair_geometricLink_inter_span_singleton` 由环境复形覆盖顶点邻域和径向单射性，证明任意通过顶点的直线与链环恰交于两点；这些结论无需有限维环境。
`exists_pair_geometricLink_fiber_of_eventually_plane` 对二维平面局部模型和横截的线性高度，同时生产链环二点零截面与正负两侧非空。使用一维核及正负射线生产交点，不把二点截面或两侧非空作为新增输入。

聚焦检查 exit=0（11.9 秒）、零 warning；`AuditF154.lean` 四项仅标准三公理，核对主端点完整签名。下一步构造实际平面目标的共同剖分并提取开邻域 PL 图卡。F-M1 仍 partial；还需 crossing 主判据、封帽边缘分类、严格降指标及 Lemma 2–6，I1 尚未交付。下一审计文件 `AuditF155.lean`。

### 19.7 F-M1：从邻域 PL 映射搬回 crossing

`CrossingNeighborhood.lean` 已提交并推送为 `50b6c8d5c`。`HasPLCrossingAt.of_openPartialHomeomorph` 通过 PL 开图卡和两集合的芽搬回 crossing；`HasPLCrossingAt.of_isPLHomeomorphOn_mem_nhds` 从定义在任意实际邻域上的 PL 同胚及两截面精确像集出发，取内部、证明逆映射并搬回 crossing。
`HasPLCrossingAt.of_closedStar_pair` 将保持子复形闭星和第二集合截面的 PL 星映射用于完整子复形的 crossing。顶点处的集合芽与闭星相等由前一模块实际证明，目标 crossing 作为运输定理的原有几何性质保留，后续标准平面生产者将证明它。

聚焦检查 exit=0（11.2 秒）、零 warning；`AuditF155.lean` 三项仅标准三公理。下一步生产实际标准平面星并闭合二点链环截面的 crossing 判据。F-M1 仍 partial，严格降指标及 I1 未交付。下一审计文件 `AuditF156.lean`。

### 19.8 F-M1：二点链环截面的顶点 crossing 判据

`VertexCrossing.lean` 已提交并推送为 `ebf03f889`。主端点 `hasPLCrossingAt_fiber_of_geometricLink_section` 从三维有限环境复形、二维子复形顶点的 PL 圆链环、逐面适配高度、链环零截面恰为两个不同点及正负两侧非空，推出该子复形与零高度面的 `HasPLCrossingAt`。
证明在同一环境中实际构造过原点的平面三角形与三维单纯形邻域，插入原点并作适配横截高度的共同细分；目标曲面链环的 PL 圆周、二点零截面和两侧非空均由构造推出。随后用已证链环配对、径向闭星延拓和邻域运输，把标准平面与横截面的 crossing 搬回源顶点。没有增加目标 crossing、局部图卡或结论型假设。

聚焦检查 exit=0（12.9 秒）、零 warning；`AuditF156.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`，完整签名已核对。F-M1 仍为 partial：下一步从一般位置高度的顶点局部数据推出链环零截面恰含两点且两侧非空，再接入凸封帽边缘分类；选定点整层圆周数严格下降、Lemma 1、Lemma 2–6 和 I1 仍未交付。下一审计文件 `AuditF157.lean`。

### 19.9 F-M1：径向链环细分保持高度符号

`LinkHeightSubdivision.lean` 已提交并推送为 `ee366b46f`。主端点 `exists_isPLHomeomorphOn_geometricLink_of_isSubdivision_preserving_height_sign` 对保持每个细面落在指定高度闭半空间中的任意有限细分，构造原链环与细分链环之间的显式径向单纯 PL 同胚，并分别证明零截面、严格负部和严格正部的精确像集等式。证明由径向比例的正性逐顶点推出高度差同号，再用逐面仿射性扩展；没有依赖存在性定理中隐藏的映射选择，也没有把符号保持写入假设。

模块聚焦检查 exit=0（11.3 秒）、零 warning；`AuditF157.lean` 五项全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`，主端点完整签名已核对。该层允许把为高度半空间适配而取的细分链环数据搬回原星。F-M1 仍为 partial：下一步闭合凸封帽边缘的 crossing/孤立分类与选定点处的严格指标下降；Lemma 1、Lemma 2–6 和 I1 尚未交付。下一审计文件 `AuditF158.lean`。

### 19.10 F-M1：保高度凸化显式保留三角形载体

`TriangleConvexification.lean` 已提交并推送为 `d375040a1`。`exists_isPLHomeomorphOn_triangle_image_strict_separation` 加强平面指定点凸化，显式返回三元素仿射独立顶点集及其凸包，而不只返回抽象凸集。`exists_isPLHomeomorphOn_triangle_image_strict_separation_of_subset_fiber` 将该数据沿实际仿射纤维坐标嵌入三维，同时保留全空间 PL 同胚、凸开集外恒同、逐点保原高度、指定点严格分离及所有集合的高度指标不变。指定点允许在封帽盘外，覆盖原书“`D_J - {P}` 可能就是整个 `D_J`”的情形。

模块最终聚焦检查 exit=0（13.6 秒）、零 warning；`AuditF158.lean` 两个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`，完整签名已核对。F-M1 仍为 partial：下一步把显式三角形载体接入凸封帽切割，证明边缘顶点的 crossing/孤立分类，再闭合选定奇异层的圆周数严格下降。Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF159.lean`。

### 19.11 F-M1：奇异水平切割保留三角形封帽坐标

`TriangleHeightCut.lean` 已提交并推送为 `b1b43c61e`。主端点 `exists_isPLSphere_pair_of_singular_height_with_triangle_cap` 将上一层的三元素仿射独立顶点集及仿射嵌入接入完整奇异水平切割。结论保留两张封帽 PL 球面、原水平层圆周计数恒等式、其他原顶点的奇异性对应与圆周数不增、封帽盘外的奇点包含，同时给出 `H '' D = e '' convexHull ℝ T`、指定点严格分离、保高度与指标不变。三角形数据由实际凸化构造产生，没有加入输入假设。

模块聚焦检查 exit=0（13.5 秒）、零 warning；`AuditF159.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`，完整签名已核对。F-M1 仍为 partial：下一步利用三条仿射边及两保留盘的相反单侧接近证明封帽边缘的 crossing/孤立分类，并在指定高度处推出严格圆周数比较。Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF160.lean`。

### 19.12 F-M1：沿奇异点嵌入的高度指标严格比较

`HeightIndexComparison.lean` 已提交并推送为 `73c40fab6`。`tsum_lt_tsum_enat_of_embedding` 对两个有限类型上的有限 `ENat` 权重证明严格总和比较：嵌入所配对的权重逐点不增，且某个配对项严格下降或目标侧有未被命中的正项，即得严格不等式。证明把有限 `ENat` 权重转成自然数有限和并在嵌入像与其补集上比较，没有把总和不等式作为假设。
`heightIndex_lt_of_embedding` 将该结论专门化到两张有限 PL 二球的一般位置高度：只需构造新奇异点到旧奇异点的嵌入、逐点水平多边形数不增，以及一个严格下降或遗漏的正贡献，即可推出整个 `heightIndex` 严格下降。

模块聚焦检查 exit=0（11.5 秒）、零 warning；`AuditF160.lean` 两个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`，完整签名已核对。F-M1 仍为 partial：下一步完成封帽边缘链环的 crossing/孤立分类，由此构造奇异点嵌入并在被删去的最内圆周处给出严格见证。Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF161.lean`。

### 19.13 F-M1：空链环截面的顶点孤立判据

`VertexIsolation.lean` 已提交并推送为 `357f41c2c`。`singleton_mem_nhdsWithin_fiber_of_geometricLink_section_eq_empty` 从顶点闭星的实际锥表示证明：若几何链环与该顶点高度层不交，则曲面高度层在顶点处局部恰为单点。三个推论分别排除这种顶点成为高度奇点，并直接覆盖整个链环严格高于或严格低于顶点的两种符号情形。

模块聚焦检查 exit=0（11.1 秒）、零 warning；`AuditF161.lean` 四项均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。结合 `VertexCrossing.lean`，帽边分类现在只剩证明链环零截面为空，或恰为两个不同点且有正负两侧；下一层将从凸三角帽与保留盘的相反单侧性推出这一有限符号分类。F-M1 仍为 partial，Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF162.lean`。

### 19.14 F-M1：PL 圆周至多二点截面的奇偶分类

`CircleHeightSection.lean` 已提交并推送为 `dcd32cdd3`。`exists_lt_and_gt_of_mem_height_section_of_avoids_vertices` 证明连续线性高度若避开有限复形的全部顶点，则经过载体的任一点高度层在该点所在开单形两侧都有严格高低点。`isPLSphere_one_height_section_ne_singleton` 再用 PL 圆周删去一点仍连通和中值定理排除单点截面。`height_section_eq_empty_or_pair_of_encard_le_two` 因而把“截面至多两点”提升为精确的空集或两个不同点二分。

模块聚焦检查 exit=0（11.2 秒）、零 warning；`AuditF162.lean` 三项均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。帽边顶点一旦取得链环截面 `encard ≤ 2`，空分支由上一层给孤立，两点分支自动含正负两侧并可送入 `VertexCrossing`。下一步证明凸三角帽替换后的链环截面至多两点。F-M1 仍为 partial，Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF163.lean`。

### 19.15 F-M1：顶点 crossing 判据搬运到任意高度层

`VertexCrossingLevel.lean` 已提交并推送为 `7e92e2044`。`isGlueIso_affineImage`、`affineImage_faces_subset` 与 `geometricLink_affineImage_space` 给出有限复形沿仿射等价的面、子复形和顶点链环精确搬运。主端点 `hasPLCrossingAt_fiber_of_geometricLink_section_at` 将原点零高度版判据推广到任意顶点高度：把环境复形、曲面复形和链环整体平移到原点，逐面半空间、PL 圆周、二点截面及正负两侧全部随平移验证，再由全局 PL 平移把 crossing 搬回原高度层。

模块聚焦检查 exit=0（16.1 秒）、零 warning；`AuditF163.lean` 四项均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。因此三角帽边界顶点的两点链环截面可直接产生该顶点自身高度层的 crossing，无需额外假设顶点高度为零。下一步证明凸三角帽替换后的链环截面至多两点并闭合帽边分类。F-M1 仍为 partial，Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF164.lean`。

### 19.16 F-M1：至多二点链环截面的顶点正则性

`VertexSectionRegularity.lean` 已提交并推送为 `a984b8c98`。主端点 `notMem_heightSingularPoints_of_geometricLink_section_encard_le_two` 将前三层闭合成统一判据：若顶点链环是 PL 圆周、当前高度避开链环顶点且零截面 `encard ≤ 2`，则该顶点不属于高度奇点集。空截面由 `VertexIsolation` 给出局部孤立；非空截面由 `CircleHeightSection` 排除单点并产生两个不同点，同时从实际截面点导出高低两侧，再由 `VertexCrossingLevel` 得到当前任意高度层的 crossing。结论没有加入 crossing 或孤立作为假设。

模块聚焦检查 exit=0（11.3 秒）、零 warning；`AuditF164.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。三角帽边界分类现已归约为实际几何命题：帽与保留盘组成的顶点链环，其新高度零截面至多两点。下一步证明该上界并接入奇异点嵌入与严格指标下降。F-M1 仍为 partial，Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF165.lean`。

### 19.17 F-M1：凸三角帽顶点的链环等高截面至多一点

`ConvexCapLink.lean` 已提交并推送为 `0afbfdf0c`。`finrank_vectorSpan_inf_ker_eq_one_of_affineIndependent_card_three` 证明三元素仿射独立集的二维方向空间与在三顶点上单射的高度核恰交成一维。主端点 `geometricLink_section_subsingleton_of_simplex_vertex` 再用暴露指定凸顶点的线性函数排除该一维交线上的反向射线，并由几何链环的径向单射性推出：载体等于该三角形凸包的任意复形，在三角形顶点处的链环与该顶点等高层的交至多一点。

模块聚焦检查 exit=0（11.8 秒）、零 warning；`AuditF165.lean` 两个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。这已经覆盖封帽三角形的三个真实角点；帽边细分产生的直边内部顶点仍需结合保留盘一侧的链环弧证明至多二点。随后接入 `VertexSectionRegularity`，构造新旧奇异点嵌入并证明严格降指标。F-M1 仍为 partial，Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF166.lean`。

### 19.18 F-M1：支撑面与横向纤维控制凸帽链环

`ConvexBoundaryLink.lean` 已提交并推送为 `99b1121b8`。主端点 `geometricLink_section_subsingleton_of_supporting_fiber` 处理三角形凸包中任意支撑边界点：若线性支撑函数在整个三角形上于该点取最小值，且新高度纤维与支撑面的等值集只在该点相交，则复形几何链环与新高度层的交至多一点。证明用三角形方向平面与高度核的一维交、支撑函数排除反向比例，以及几何链环径向单射性；支撑条件真实约束凸帽，不包含目标结论。

模块聚焦检查 exit=0（11.8 秒）、零 warning；`AuditF166.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步从三角形仿射独立性为每条边构造支撑线性函数，并由高度在该边两端取值不同推出支撑面纤维唯一；这将覆盖帽边细分顶点的帽侧链环。保留盘侧的符号弧仍需随后拼接。F-M1 仍为 partial，Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF167.lean`。

### 19.19 F-M1：三角帽边内部点的链环等高截面至多一点

`TriangleEdgeLink.lean` 已提交并推送为 `55ed65b59`。`injOn_linearMap_convexHull_of_card_eq_two` 将线性高度在二元素顶点集上的单射性推广到整条边；`exists_linearMap_supporting_simplex_facet` 从单纯形的仿射无关性构造对边的规范支撑泛函，并精确刻画其最小值集合。主端点 `geometricLink_section_subsingleton_of_simplex_facet` 因而证明：三角形任一对边上的点，只要高度在三角形三个顶点上单射，则三角帽侧的几何链环与该点等高层的交至多一点。支撑泛函与对边纤维唯一性均在证明中构造，不作为新增输入。

模块聚焦检查 exit=0（12.9 秒）、零 warning；`AuditF167.lean` 三个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。帽侧链环弧已经覆盖真实角点和边内部点。下一步利用 `HeightSides.lean` 的相反单侧结论与小高度扰动控制保留盘侧链环弧，再将两侧合并为完整链环截面 `encard ≤ 2`。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF168.lean`。

### 19.20 F-M1：唯一越层边界端点控制一维盘截面

`BoundaryArcSection.lean` 已提交并推送为 `124c80557`。`height_section_subsingleton_of_unique_high_boundary_vertex` 证明有限一维组合带边流形中，若一个组合边界顶点严格高于指定高度且所有其他顶点严格低于该高度，则整个载体与该高度层至多交一点；低端点版本由高度取负得到。证明从边界顶点的唯一邻点刻画出发，先证明任一等高点只能落在该唯一边上，再用线性高度在边凸包上的单射性得到唯一性。没有假定载体是一条预先给定的参数弧，也没有把截面上界写入输入。

模块最终聚焦检查 exit=0（13.7 秒）、零 warning；`AuditF168.lean` 两个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步从保留盘的顶点链环构造实际一维带边子复形，证明其两个组合边界端点沿三角帽直边分居新高度两侧，并由小扰动保持其余顶点的旧高度严格侧别；随后与帽侧的 subsingleton 结论合并为完整链环 `encard ≤ 2`。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF169.lean`。

### 19.21 F-M1：保留链环弧的高度截面对小扰动稳定

`BoundaryArcStability.lean` 已提交并推送为 `89a746c29`。主端点 `eventually_height_section_subsingleton_of_boundary_segment` 处理有限一维组合带边流形的实际边界弧：两个不同边界顶点之间的开线段包含接缝点，旧高度在其余顶点上严格低于接缝高度。它证明在旧高度的一个邻域内，任何在接缝点与弧顶点上单射的新线性高度，其弧截面至多一点。证明先用有限集上的严格次序稳定性保持内部顶点的侧别；开线段在新高度下仍把接缝值夹在两个边界值之间，故恰有一个边界端点在高侧，再调用上一层唯一越层端点定理。

模块聚焦检查 exit=0（11.1 秒）、零 warning；`AuditF169.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步将保留盘的几何链环限制识别为此一维组合带边流形，证明旧单侧性给出其非边界顶点的严格同侧条件；随后与三角帽链环合并。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF170.lean`。

### 19.22 F-M1：保留盘顶点链环的稳定单点截面

`RetainedDiskLink.lean` 已提交并推送为 `ab191e998`。主端点 `eventually_geometricLink_section_subsingleton_of_boundary_segment` 从实际 PL 二球盘、其边界上的接缝顶点，以及边界链环中的两个不同方向构造保留盘顶点链环的一维带边流形。`geometricLink_boundaryComplex` 将这两个接缝方向识别为该链环的两个组合边界端点；其余链环顶点的旧高度严格同侧时，上一层稳定性定理给出所有充分小且在接缝点与链环顶点上单射的新高度的截面至多一点。

模块聚焦检查 exit=0（13.0 秒）、零 warning；`AuditF170.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步从 `HeightSides` 与接缝适配剖分实际推出非边界链环顶点的严格同侧条件和两个边界方向间的开线段关系，再把保留盘与三角帽的两个单点截面合并为完整链环的 `encard ≤ 2`。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF171.lean`。

### 19.23 F-M1：由单侧与边界集合芽推出保留链环严格高度

`BoundaryLinkGerm.lean` 已提交并推送为 `c0598e23c`。`map_le_of_mem_geometricLink_space_of_eventually` 以链环射线缩回接缝点，证明局部位于旧高度闭半空间会强制整个几何链环位于该闭半空间。`mem_geometricLink_boundaryComplex_of_height_eq_of_eventually` 证明任一等高链环顶点必属于边界链环：在对应边上选取足够靠近接缝点的开单形点，由边界等高集合芽把该点放入边界复形，再以开单形载体唯一性把整条边降到边界复形。PL 二球盘的边界链环是 PL 零球面，两个已知不同边界方向因而穷尽它。主端点 `geometricLink_vertices_lt_of_halfSpace_boundary_germ` 由此把所有其他链环顶点的闭侧不等式提升为严格不等式；`eventually_geometricLink_section_subsingleton_of_halfSpace_boundary_germ` 直接给充分小一般位置高度下的保留链环单点截面。

模块聚焦检查 exit=0（11.9 秒）、零 warning；`AuditF171.lean` 六个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步从 `HeightSides` 的相反半空间集合芽、水平圆周的局部等高识别以及接缝适配三角剖分构造本端点的两个 germ 输入和边界链环两方向。之后将保留盘与凸帽的两个单点截面合并。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF172.lean`。

### 19.24 F-M1：局部直线接缝的两个相反链环方向

`BoundaryLinkDirections.lean` 已提交并推送为 `48aa32b7c`。主端点 `exists_geometricLink_pair_openSegment_of_eventually_line` 处理有限一维组合流形在顶点附近等于一条仿射直线的情形。证明分别沿直线的正负方向进入载体，以几何链环的射线截取取得两个实际邻接顶点，再用一维组合流形的面维数界把链环点识别为单点面；两个正射线参数给出显式凸组合，证明原顶点位于这两个方向之间的开线段。结论同时返回不同性、两项面成员关系和开线段关系，不把任一项作为假设。

模块聚焦检查 exit=0（12.7 秒）、零 warning；`AuditF172.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步证明三元素仿射独立三角形的边界在任一对边相对内部点附近恰等于该对边的仿射直线，并通过保留盘边界空间等式实例化本端点。随后接入 `BoundaryLinkGerm`。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF173.lean`。

### 19.25 F-M1：二维面内部点产生边界链环的相反方向

`BoundaryFacetDirections.lean` 已提交并推送为 `b214ed095`。`exists_geometricLink_pair_openSegment_of_opposite_rays` 从一维组合流形载体沿某非零方向的正、负两条局部射线，构造几何链环中的两个不同单点面，并以显式正凸组合证明基点位于两方向的开线段中。`exists_geometricLink_pair_openSegment_of_openSimplex_two` 将其用于二元素面的开单形内部点：面方向空间同时包含某方向及其负方向，开单形在这些方向上局部稳定，故不必先证明整个接缝具有局部直线集合芽。

模块聚焦检查 exit=0（12.6 秒）、零 warning；`AuditF173.lean` 两个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步把接缝适配剖分中的实际二元素面送入该端点，并用 `BoundaryLinkGerm` 得到保留盘链环的稳定单点截面；随后证明帽侧与保留侧链环覆盖完整链环并合并为 `encard ≤ 2`。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF174.lean`。

### 19.26 F-M1：两片覆盖把链环单点截面合并为至多二点

`LinkUnionSection.lean` 已提交并推送为 `b066c360d`。`geometricLink_space_subset_union_of_faces_cover` 证明：若完整复形的每个面属于两个片复形之一，则顶点的完整几何链环空间包含于两片链环空间之并；证明直接对链环面连同顶点的并面应用面覆盖，不需要满子复形假设。`geometricLink_section_encard_le_two_of_faces_cover` 再把两片各自的等高链环截面 subsingleton 合并为完整截面的 `encard ≤ 2`，经 `encard_mono` 与 `encard_union_le` 得到精确上界。

模块聚焦检查 exit=0（11.6 秒）、零 warning；`AuditF174.lean` 两个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步加强共同三角剖分存在性，使其显式返回每个新面位于原保留盘或凸帽之一；这将提供本层所需的面覆盖，并允许分别接入 `BoundaryLinkGerm` 与 `TriangleEdgeLink`。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF175.lean`。

### 19.27 F-M1：共同细分显式保留两片面覆盖

`CoveredHeightSubdivision.lean` 已提交并推送为 `e0878ee1c`。主端点 `exists_triangulation_union_with_face_cover_and_halfSpace_faces` 加强高度半空间适配的共同三角剖分：除原有载体并集、原复形上的细分、第二多面体的精确限制空间和逐面高度侧别外，显式返回每个新面属于两个限制子复形之一。证明在共同 H-多胞形细分的重心所在载体中识别整个新单形；该载体从构造上来自原复形的某面或第二多面体的某个 H-多胞形，因此面覆盖是构造结论，不是附加假设。

模块聚焦检查 exit=0（11.9 秒）、零 warning；`AuditF175.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步在三角帽切割的每个保留盘上应用该端点，识别接缝边内部顶点的边界复形面、两条边界链环方向与相反半空间集合芽，再由两片单点截面和面覆盖推出完整链环 `encard ≤ 2`。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF176.lean`。

### 19.28 F-M1：接缝二维面内部点的保留链环稳定性

`BoundaryFacetLink.lean` 已提交并推送为 `e207e05dc`。主端点 `eventually_geometricLink_section_subsingleton_of_boundary_openSimplex_two` 将前述几层组装为一个可直接实例化的边界判据：PL 二球盘的边界复形若包含某二元素面凸包，接缝顶点位于该面的开单形中，且盘在该点具有旧高度单侧集合芽、边界复形恰为旧等高集合芽，则所有充分小且在该顶点链环上一般位置的新高度，其保留盘链环截面至多一点。证明从边界复形的一维组合流形性构造相反链环方向，再调用 `BoundaryLinkGerm`；没有把方向或截面上界加入输入。

模块聚焦检查 exit=0（11.3 秒）、零 warning；`AuditF176.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步从 `HeightSides`、保高度同胚及共同细分的边界空间等式验证该端点的两个集合芽，并与三角帽侧的 `TriangleEdgeLink` 经 `LinkUnionSection` 合并。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF177.lean`。

### 19.29 F-M1：奇异高度切割保留两盘参数化边界

`ParametricSingularHeightCut.lean` 已提交并推送为 `2b12885e2`。主端点 `exists_isPLSphere_pair_of_mem_heightSingularPoints_with_parameterized_boundary` 保留 `SphereCut` 构造实际产生的两张保留盘参数化 `fA`、`fB`，并分别给出其标准单形边界像等于共同水平圆周；原有两封帽球面、交集与恢复等式、临界层计数、其他层分拆和盘外奇异点等式全部同时保留。该加强只暴露原证明中已经构造但旧端点丢弃的数据。

模块聚焦检查 exit=0（11.9 秒）、零 warning；`AuditF177.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步沿三角凸化的保高度环境同胚搬运 `fA`、`fB`，再为每张保留盘与三角帽构造带显式面覆盖的共同细分；组合边界空间将由参数化和细分不变性直接识别。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF178.lean`。

### 19.30 F-M1：三角凸化保留切割盘参数与全部指标数据

`ParametricTriangleHeightCut.lean` 已提交并推送为 `5bfd5954a`。主端点 `exists_parameterized_triangle_cut_of_singular_height` 把上一层的两张盘参数化贯穿指定点三角凸化：返回原球面的两盘分拆及共同参数边界、水平张成盘、两张封帽球面、保高度且固定支集外和其他原顶点的环境 PL 同胚、三元素仿射独立三角形载体、指定点的严格线性分离，以及临界层圆周计数和所有集合的高度指标不变性。该端点不再提前选择任意三角剖分，后续可用显式参数边界构造适配共同细分。

模块聚焦检查 exit=0（12.4 秒）、零 warning；`AuditF178.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步对 `H '' A` 与 `H '' B` 分别建立有限三角剖分，再与 `H '' D` 做显式面覆盖共同细分；沿保高度同胚运输 `HeightSides` 的相反单侧集合芽，闭合接缝边内部顶点的 `encard ≤ 2`。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF179.lean`。

### 19.31 F-M1：共享参数边界的两盘共同细分

`ParameterizedDiskUnion.lean` 已提交并推送为 `dbd2d65c8`。主端点 `exists_triangulation_parameterized_disk_union` 从两张共享同一标准单形边界像的参数化 PL 二球盘构造其并集的有限共同三角剖分。结论同时给出两限制子复形的精确空间与 PL 球性、两侧组合边界复形空间都精确等于共享接缝、完整复形的逐面二片覆盖，以及相对于任意仿射高度层的逐面半空间适配。组合边界等式由参数化端点直接证明，不作额外输入。

模块聚焦检查 exit=0（14.1 秒）、零 warning；`AuditF179.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步把保高度同胚后的保留盘参数化与三角帽参数化送入该端点，并证明接缝边相对内部顶点的保留侧和帽侧链环截面各至多一点，从而经逐面覆盖得到完整链环 `encard ≤ 2`。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF180.lean`。

### 19.32 F-M1：保高度环境同胚运输单侧与边界集合芽

`HeightGermTransport.lean` 已提交并推送为 `33ceb84e0`。`eventually_image_mem_le_of_height_preserving_homeomorph` 与高侧版本把任一点处盘载体的旧高度单侧集合芽沿保高度环境同胚运输到像点；`eventually_image_boundary_fiber_iff_of_height_preserving_homeomorph` 同时运输“边界集合芽恰为盘内旧等高集合芽”。证明只用同胚逆映射在像点的连续性、双射像成员关系与逐点保高度等式。

模块聚焦检查 exit=0（11.4 秒）、零 warning；`AuditF180.lean` 三个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步把 `HeightSides` 的全接缝相反单侧结论逐点送入这三个运输端点，并在参数化两盘共同细分中调用 `BoundaryFacetLink`、`TriangleEdgeLink` 与 `LinkUnionSection`，得到接缝边内部顶点的完整链环 `encard ≤ 2`。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF181.lean`。

### 19.33 F-M1：三角接缝边内部顶点的完整链环至多二点

`TriangleSeamRegularity.lean` 已提交并推送为 `07afa25d8`。主端点 `eventually_geometricLink_section_encard_le_two_of_triangle_facet` 处理由保留盘与凸三角帽组成、逐面由两片覆盖的有限复形。对三角形任一边相对内部的共同边界顶点，保留侧由 `BoundaryFacetLink` 在旧单侧与边界集合芽下得到稳定单点截面，帽侧由 `TriangleEdgeLink` 的支撑泛函得到单点截面；`LinkUnionSection` 随后证明完整球面链环的新等高截面 `encard ≤ 2`。一般位置只要求在完整复形顶点与三个三角顶点的有限并上单射。

模块聚焦检查 exit=0（11.6 秒）、零 warning；`AuditF181.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步接入 `VertexSectionRegularity` 排除所有接缝边内部顶点；三角形三个真实角点将用 `ConvexCapLink` 和保留侧链环的端点结构单独分类。随后构造新旧奇异点嵌入与严格指标下降。F-M1 仍为 partial，Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF182.lean`。

### 19.34 F-M1：由原链环截面上界导出顶点正规性

`VertexSectionSubdivision.lean` 已提交并推送为 `f2697b701`。主端点 `notMem_heightSingularPoints_of_geometricLink_section_encard_le_two_of_injOn` 对有限 PL 二球面复形的任一顶点直接使用原复形顶点上的高度单射和原几何链环截面 `encard ≤ 2`。证明先在原链环排除单点截面；空截面分支直接给孤立正规性，两点分支自动构造含顶点邻域的三维多面体复形及高度半空间适配细分，再由径向链环同胚把零层、正侧和负侧搬到细分链环，最后调用 `VertexCrossingLevel` 得到 crossing。因此端点不要求调用者提供环境复形、逐面半空间条件或局部平坦性假设。

模块聚焦检查 exit=0（12.4 秒）、零 warning；`AuditF182.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步把该端点与 `TriangleSeamRegularity` 组合，排除三角接缝三条边相对内部的全部细分顶点；随后处理三个真实角点并构造新旧奇异点嵌入。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF183.lean`。

### 19.35 F-M1：三角接缝边内部顶点全部非奇异

`TriangleSeamNonsingular.lean` 已提交并推送为 `638d6e59f`。主端点 `eventually_notMem_heightSingularPoints_of_triangle_facet` 把 `TriangleSeamRegularity` 的稳定链环截面上界送入 `VertexSectionSubdivision`：对三角形任一边相对内部的共同边界顶点，所有充分小且在完整球面复形顶点与三角形三个顶点并集上单射的新高度都使该点不属于新球面的 `heightSingularPoints`。非零性由三角形三个互异顶点上的单射在证明中推出，没有新增假设。

模块聚焦检查 exit=0（11.1 秒）、零 warning；`AuditF183.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步处理三角帽三个真实角点：用 `ConvexCapLink` 的帽侧链环控制与保留盘边界顶点的链环区间结构证明完整链环截面至多二点，再复用本层的顶点正规性端点。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF184.lean`。

### 19.36 F-M1：一维保留链环的双端边截面计数

`BoundaryArcCardinality.lean` 已提交并推送为 `f4fdad40b`。`linearMap_level_section_convexHull_pair_subsingleton_of_apply_ne` 证明线性高度层与一条非退化线段至多交一点，只需其中一个端点避开该高度；端点同高时截面为空，端点异高时由线段上的高度单射得到唯一性。主端点 `height_section_encard_le_two_of_boundary_vertices` 对有限一维组合带边流形及两个组合边界顶点，若两端点都避开指定高度、其余顶点都严格位于低侧，则整个载体的等高截面至多两点。证明由每个边界顶点的唯一邻边刻画把任一等高点限制在两条端边之一，没有预设端点高低次序，也没有把截面上界写入输入。

模块聚焦检查 exit=0（12.0 秒）、零 warning；`AuditF184.lean` 两个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步从三角形严格分离点判断三个真实角点处两个边界链环方向的高度侧别：严格最低角点处保留链环用双端边计数，其余两个角点处至少一个端点严格较低并退化为单点截面；再与 `ConvexCapLink` 合并并调用顶点正规性端点。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF185.lean`。

### 19.37 F-M1：凸三角剖分的真实角点与边界链环端点

`TriangleBoundaryVertices.lean` 已提交并推送为 `ef0695ed4`。`boundaryComplex_space_eq_simplexBoundary_of_space_eq_convexHull` 用相同凸三角载体上的恒等 PL 同胚与组合边界不变性，证明任意有限复形实现的凸三角盘之组合边界恰为规范单形边界。`singleton_mem_boundaryComplex_of_mem_triangle_vertex` 进一步证明三个原始极端点在任意该类剖分中仍是组合边界顶点：若其载体面不含该点，严格支撑泛函会在该点的凸组合上产生矛盾。`segment_subset_boundaryComplex_of_space_eq_convexHull` 给出任意两原始角点间整条边属于组合边界。`exists_geometricLink_boundary_pair_of_isPLBall` 最后从 PL 二球盘和一个组合边界顶点自动构造边界链环的两个不同单点面，并证明它们穷尽边界链环空间；没有把端点存在性加入输入。

模块聚焦检查 exit=0（12.1 秒）、零 warning；`AuditF185.lean` 五个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步沿最低角点到另外两个角点的实际三角边取得保留链环中的低端方向：最低角点用双端边计数并证明帽侧截面为空，其余角点用一个低端方向证明保留侧截面至多一点；再与帽侧单点截面合并并排除三个角点的奇异性。F-M1 仍为 partial，严格降指标、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF186.lean`。

### 19.38 F-M1：三角帽真实角点的稳定非奇异性

`TriangleCornerRegularity.lean` 已提交并推送为 `4b3c685a1`。`height_section_subsingleton_of_boundary_vertices_of_one_low` 证明有限一维组合带边流形中，只要一个顶点严格位于目标高度以下、另一组合边界顶点避开该高度且其余顶点全在低侧，整个高度截面至多一点。`singleton_mem_boundaryComplex_of_common_triangle_boundary` 从两盘组合边界空间相等和其中一盘载体为仿射独立三角形推出原始角点也是另一盘的组合边界顶点。主端点 `eventually_notMem_heightSingularPoints_of_triangle_vertex` 随后对保留盘与三角帽逐面覆盖的 PL 二球面处理三角形真实角点：由保留盘边界链环的两个端点、局部半空间与边界等高集合芽控制保留侧；所选三角形最低点等于该角点时帽侧截面为空，否则最低点方向给出保留侧的严格低端而帽侧截面至多一点。两种情形都把完整链环截面压到 `encard ≤ 2`，再由顶点截面正规性排除新奇异点。

模块聚焦检查 exit=0（13.1 秒）、零 warning；`AuditF186.lean` 三个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步在 `exists_parameterized_triangle_cut_of_singular_height` 返回的两张保留盘与三角帽上分别构造共同细分，统一选择充分小的一般位置高度，并把接缝内部点与真实角点的排除结论拼装成帽内除指定旧奇异点像外无新奇异点；随后构造新旧奇异点嵌入并证明 `heightIndex` 严格下降。F-M1 仍为 partial，Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF187.lean`。

### 19.39 F-M1：共同细分的整条三角边界均非奇异

`TriangleBoundaryNonsingular.lean` 已提交并推送为 `587bbb0bc`。`mem_or_exists_mem_openSimplex_erase_of_mem_simplexBoundary_space` 对三元素仿射独立单形边界上的任一点给出精确分层：它或是原始角点，或位于唯一某条对边的开单形中。主端点 `eventually_notMem_heightSingularPoints_on_triangle_boundary` 对保留盘与凸三角帽逐面覆盖的有限 PL 二球面，把有限个共同边界顶点及三个可能最低的角点同时取有限邻域交；对原始角点调用 `TriangleCornerRegularity`，对边内部细分顶点调用 `TriangleSeamNonsingular`。因此任意充分小、在完整顶点集与三角顶点并上单射且具有某个严格最低三角顶点的新高度，都排除指定例外点以外的全部共同边界奇异点。

模块聚焦检查 exit=0（12.0 秒）、零 warning；`AuditF187.lean` 两个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步把本端点实例化到 `exists_parameterized_triangle_cut_of_singular_height` 返回的两张保留盘与三角帽共同细分，从 `HeightSides` 和保高度环境同胚导出统一的半空间及边界等高集合芽，并选择同时满足两张球面一般位置的充分小高度。F-M1 仍为 partial，严格指标下降、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF188.lean`。

### 19.40 F-M1：参数化三角切割显式保留相反高度侧芽

`ParametricTriangleHeightSides.lean` 已提交并推送为 `5acca1317`。主端点 `exists_parameterized_triangle_cut_with_opposite_height_sides` 从指定奇异高度重新暴露最内水平圆周成员关系，并把两张参数化保留盘沿该圆周去掉原奇异点后的统一相反半空间集合芽加入三角凸化输出。端点同时保留两盘与水平张成盘的参数边界、两封帽球面、临界层圆周计数、保高度环境同胚、显式仿射独立三角形、严格分离泛函及全部集合的 `heightIndex` 不变性。侧芽由 `HeightSides` 从实际球面分割推出，不是新增假设。

模块聚焦检查 exit=0（47.4 秒）、零 warning；`AuditF188.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步对两种统一侧别分别把保留盘的半空间芽与“共同边界等于盘内旧等高集合”芽沿保高度同胚搬运，调用 `exists_triangulation_parameterized_disk_union` 构造两张逐面覆盖的共同细分球面，并接入整条三角边界非奇异端点。F-M1 仍为 partial，严格指标下降、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF189.lean`。

### 19.41 F-M1：参数化三角帽共同细分的整边界正规性

`ParameterizedTriangleCap.lean` 已提交并推送为 `2b419419f`。`eventually_mem_inter_iff_left_and_eq_of_opposite_halfSpaces` 从两闭片的相反半空间集合芽直接推出共同边界等于左片内等高集合的芽。主端点 `exists_triangulation_triangle_cap_with_nonsingular_boundary` 把参数化保留盘与水平盘沿共同参数边界的并沿保高度环境同胚搬运，构造逐面由保留盘和凸三角帽覆盖的有限共同细分；仿射三角形顶点集随嵌入映到环境空间。半空间与边界等高芽沿同胚运输后接入上一层整边界定理。对每个新高度，证明在有限三角顶点上存在最低点，并由顶点单射把非严格最小提升为整个三角凸包上的严格最小，故结论不要求调用者预先指定最低角点。

模块聚焦检查 exit=0（12.5 秒）、零 warning；`AuditF189.lean` 两个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步对参数化奇异高度切割返回的 A、B 两张保留盘分别实例化本端点；再与 `TriangleHeightCut` 的帽内部奇异点定位及盘外旧奇异点比较合并，得到每张新球面除 `H p` 外的奇异点均嵌入原球面奇异点。F-M1 仍为 partial，严格指标下降、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF190.lean`。

### 19.42 F-M1：三角切割生产者暴露紧支集与旧高度纤维分离

`ParametricTriangleHeightSides.lean` 的主端点已加强并提交为 `e55b0a88a`。凸化证明内部原已构造的紧集 `C` 现在作为存在数据返回，同时给出 `D ⊆ C`、环境同胚在 `Cᶜ` 上恒等，以及 `C` 与每个旧顶点 `q ≠ p` 的高度纤维互不相交。该数据正是 `HeightLocalization` 对其他旧奇异点保持成员关系并控制层圆周数所需的真实几何输入；只返回逐点固定旧顶点不足以控制其邻域，因此没有用较弱条件替代。

加强后的模块聚焦检查 exit=0（12.1 秒）、零 warning；`AuditF190.lean` 主端点仍仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步把两张参数化三角帽共同细分的边界正规性与紧支集局部化合并，证明每张新球面除 `H p` 外的奇异点精确注入原球面的奇异点去掉 `p`，并保留逐点层圆周数不增。F-M1 仍为 partial，严格指标下降、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF191.lean`。

### 19.43 F-M1：三角封帽后的新奇异点注入旧奇异点去掉指定点

`TriangleCapSingularComparison.lean` 已提交并推送为 `13c88d977`。`mem_vertices_of_faces_subset_of_mem_space` 证明大复形的顶点若落在子复形载体中，则自动成为该子复形顶点；这把帽边上的新奇异点送入整边界正规性端点。主端点 `exists_triangle_cap_with_singular_comparison` 对一张保留盘与凸三角帽的共同细分同时使用三部分信息：紧支集局部化控制帽外旧顶点及层圆周数，帽内部定理把奇异点限制到共同边界或 `H p`，整边界正规性排除前者。由环境同胚固定所有其他旧顶点，进一步证明帽外对应点不可能等于原指定点 `p`。因此新奇异点去掉 `H p` 后包含于原奇异点去掉 `p`，且每个其他旧顶点的奇异成员关系按所属保留盘精确保持、层圆周数不增。

模块聚焦检查 exit=0（13.2 秒）、零 warning；`AuditF191.lean` 两个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步用相反高度侧的两个方向分别实例化 A、B，统一选择一个同时适合两张有限复形且严格分离 `H p` 与三角帽的高度，并为每张球面构造显式 `heightSingularPoints` 嵌入到原球面。F-M1 仍为 partial，严格指标下降、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF192.lean`。

### 19.44 F-M1：高度取负给出上侧三角帽的对称正规性

`TriangleCapSideSymmetry.lean` 已提交并推送为 `3019d3743`。`levelPolygons_neg` 与 `heightSingularPoints_neg` 分别证明高度函数取负时层圆周族和奇异点集在对应负高度上精确不变。主端点 `exists_triangulation_triangle_cap_with_nonsingular_boundary_of_ge` 将局部位于旧高度高侧的保留盘改看作负高度的低侧盘，调用低侧参数化共同细分定理，再沿连续自同构 `f ↦ -f` 把充分小邻域搬回原高度；顶点单射和奇异点排除同时保持。因此相反侧的两张保留盘现在具有完全对称的整边界正规性，不需要预先选定哪一张在低侧。

模块聚焦检查 exit=0（12.0 秒）、零 warning；`AuditF192.lean` 三个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步让单帽奇异点比较接受统一低侧或统一高侧两种输入，随后从 `exists_parameterized_triangle_cut_with_opposite_height_sides` 的两个分支同时构造 A、B 两张新球面及其奇异点嵌入。F-M1 仍为 partial，严格指标下降、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF193.lean`。

### 19.45 F-M1：单帽奇异点比较统一覆盖两个高度侧

`TriangleCapSingularComparison.lean` 的主端点已加强并提交为 `16202494b`。`exists_triangle_cap_with_singular_comparison` 现在接受保留盘在共同水平边界附近统一位于低侧或统一位于高侧的析取输入；低侧直接调用参数化三角帽共同细分，高侧调用取负高度得到的对称版本。两条分支返回完全相同的有限球面、帽边正规性和局部化数据，后续奇异点包含、逐旧顶点成员关系及层圆周数不增的证明无需分叉。

加强后的模块聚焦检查 exit=0（12.1 秒）、零 warning；`AuditF193.lean` 两个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步从参数化三角切割的相反侧芽构造 A、B 各自的半空间析取和边界等高集合芽，同时实例化两张封帽球面，并统一选择满足两边一般位置与帽内严格分离的高度。F-M1 仍为 partial，严格指标下降、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF194.lean`。

### 19.46 F-M1：相反半空间芽同时识别共同边界的两侧

`ParameterizedTriangleCap.lean` 已加强并提交为 `521027c3d`。新端点 `eventually_mem_inter_iff_right_and_eq_of_opposite_halfSpaces` 与原左侧版本对称：两闭片在某点附近分别位于同一函数的相反闭半空间、且交集等于共同边界时，共同边界的集合芽也精确等于右片内的等高集合芽。证明直接使用两个成员等价和反对称性，不交换参数化盘或环境同胚。

模块聚焦检查 exit=0（12.8 秒）、零 warning；`AuditF194.lean` 左侧、右侧及共同细分三个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步按参数化三角切割返回的两种相反侧分支，分别构造 A、B 的半空间析取与各自边界等高芽，并调用统一单帽比较得到两张有限 PL 球面。F-M1 仍为 partial，严格指标下降、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF195.lean`。

### 19.47 F-M1：两张三角封帽球面的同时奇异点比较

`TriangleCapPair.lean` 已提交并推送为 `b906f6e2d`。主端点 `exists_triangle_cap_pair_with_singular_comparison` 从一个旧奇异点一次性构造 A、B 两张保留盘的三角封帽有限复形。证明对参数化切割返回的两种相反侧分支逐一提取 A、B 的低侧或高侧析取和各自边界等高芽，再两次调用统一单帽比较。输出保留共同的保高度环境 PL 同胚、水平 PL 盘像、严格分离方向与旧临界层圆周计数，并把两个充分小邻域取交；因此同一个新高度只要在两张复形顶点及有限三角顶点并上单射、且严格抬高帽面，就同时得到两张球面去掉 `H p` 后的奇异点包含和所有其他旧顶点处的层圆周数不增。

模块聚焦检查 exit=0（14.7 秒）、零 warning；`AuditF195.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步用 `HeightPerturbation` 在该共同邻域内选取一个高度：在两张新复形及三角顶点的有限并上单射、保持旧顶点严格次序，并在整个帽盘像去掉 `H p` 后严格大于 `f(H p)`。随后构造两张新奇异点集到旧奇异点集的显式嵌入。F-M1 仍为 partial，严格指标下降、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF196.lean`。

### 19.48 F-M1：为两张封帽球面选择共同的一般位置高度

`TriangleCapPerturbation.lean` 已提交并推送为 `48eb01988`。主端点 `exists_small_triangle_cap_pair_with_singular_comparison` 对任意正误差，把上一层两张球面的共同有效邻域与误差球取交，再调用有限集合一般位置和半空间扰动生产者。所得同一个连续线性高度在两张新复形的顶点上分别单射，保持所有旧顶点之间由原高度给出的严格次序，在整个三角帽像去掉 `H p` 后严格高于 `f(H p)`，并同时满足两张球面的奇异点包含、逐旧顶点成员关系和层圆周数不增。

模块聚焦检查 exit=0（12.6 秒）、零 warning；`AuditF196.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步将每张新奇异点集中的 `H p` 映到旧点 `p`，其余点用比较包含恒等映入旧奇异点集；去掉 `H p` 后目标自动避开 `p`，从而证明这是显式嵌入，并在所有非例外点搬运层圆周数不增。F-M1 仍为 partial，严格指标下降、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF197.lean`。

### 19.49 F-M1：带指定例外点的奇异点集显式嵌入

`SingularPointEmbedding.lean` 已提交并推送为 `908b74641`。主端点 `exists_embedding_heightSingularPoints_of_sdiff_subset` 是后续指标比较的集合论核心：若源奇异点集去掉 `a` 后包含于目标奇异点集去掉 `b`，且 `b` 确为目标奇异点，则构造源到目标的显式嵌入；源中的 `a` 若出现便映到 `b`，所有其他点保持原值。单射性来自非例外像自动避开 `b`，不要求 `a` 本身属于源集。

模块聚焦检查 exit=0（10.8 秒）、零 warning；`AuditF197.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步把该端点用于两张封帽球面的去单点包含，并由旧奇异点必为旧复形顶点及逐顶点层圆周数比较，证明每个不映到 `p` 的新奇异点指标贡献不增。剩余核心将只是在两张候选球面中证明至少一张的例外项严格下降。F-M1 仍为 partial，严格指标下降、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF198.lean`。

### 19.50 F-M1：奇异点嵌入上的非例外层圆周数比较

`SingularPointComparison.lean` 已提交并推送为 `65fb525c2`。主端点 `exists_embedding_heightSingularPoints_with_levelPolygons_le` 把去指定点的奇异点包含升级为带指标数据的嵌入：例外源点若出现映到指定旧奇异点，其他源点保持原值；对每个非例外源奇异点，先由包含得到其为旧奇异点，再用一般位置下旧奇异点属于旧复形顶点，因而可调用单帽比较的逐旧顶点结论，得到新层圆周数不超过嵌入像处的旧层圆周数。

模块聚焦检查 exit=0（10.4 秒）、零 warning；`AuditF198.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步分析唯一未覆盖的 `H p` 项：把三角帽在严格分离高度层中的截面压到单点或空集，并把保留盘贡献与旧 A/B 临界层圆周数比较；结合两盘计数和等于旧计数加一，选出至少一张封帽球面的例外贡献严格下降。F-M1 仍为 partial，Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF199.lean`。

### 19.51 F-M1：单点纤维交下的层圆周精确分割

`CapLevelPolygons.lean` 已提交并推送为 `65e6f87f0`。`levelPolygons_union_of_fiber_inter_subset_singleton` 与 `disjoint_levelPolygons_of_fiber_inter_subset_singleton` 证明：两闭片在目标高度纤维中的交若至多为指定单点，则并集的层圆周族恰为两片层圆周族的不交并；`encard_levelPolygons_union_of_fiber_inter_subset_singleton` 给出相应的精确基数加法。`levelPolygons_union_cap_of_fiber_subset_singleton` 进一步证明：若封帽在目标纤维至多含帽尖，则封帽与保留片的并不会新增层圆周。证明使用 PL 圆周删去一点仍连通且稠密，没有把圆周分割或计数关系写入输入。

模块聚焦检查 exit=0（11.5 秒）、零 warning；`AuditF199.lean` 四个端点均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步把帽面严格分离直接转成单点纤维条件，并在变形后原球面上应用两片精确分割；剩余核心缩成证明小高度扰动保持该球面在原临界值附近的层圆周总数。F-M1 仍为 partial，Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF200.lean`。

### 19.52 F-M1：两张封帽的例外层合并为原球面一层

`TriangleCapLevelCount.lean` 已提交并推送为 `607f4a6d2`。主端点 `encard_levelPolygons_triangle_cap_pair_add_eq` 对任意两闭片 A、B、共同封帽 D 与环境同胚 H 证明：只要 `A ∩ B ⊆ D` 且新高度在 `H '' D` 上除 `H p` 外严格较高，两张封帽球面在 `f(H p)` 层的圆周数之和就精确等于变形后原并集 `H '' (A ∪ B)` 在同层的圆周数。证明先用单点帽纤维去除两个帽盘，再证明两保留片在该纤维至多交于 `H p`，故其圆周族为不交并；没有加入旧新计数比较作为输入。

模块聚焦检查 exit=0（11.7 秒）、零 warning；`AuditF200.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。因此两张候选球面的例外贡献已经归约为一个单一义务：证明充分小的一般位置高度 f 下，`H '' K.space` 在 `f(H p)` 层的圆周数不超过 K 在旧临界层 `ℓ p` 的圆周数。下一步建立保高度环境 PL 同胚后的临界层稳定性，再把该不等式接回奇异点嵌入。F-M1 仍为 partial，Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF201.lean`。

### 19.53 F-M1：向下三角帽的对称奇异点比较

`TriangleCapSingularComparisonSymmetry.lean` 已提交并推送为 `3327abc5b`。主端点 `exists_triangle_cap_with_singular_comparison_of_cap_below` 把单帽比较完整搬到帽面严格低于帽尖的情形：对旧高度和扰动高度同时取负，调用已经验证的向上帽端点，再用 `heightSingularPoints_neg` 与 `levelPolygons_neg` 把结论搬回。局部半空间析取的两个分支在取负时互换；顶点单射、紧支集纤维分离、边界等高芽、非例外奇异点包含及逐点层圆周数不增均保持。因此可以按照 Moise 17.12 的原始路线，对两张保留盘分别选择方向相反的小倾斜，无需再要求一个共同高度控制变形后原球面的整个临界层。

模块聚焦检查 exit=0（12.2 秒）、零 warning；`AuditF201.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步从参数化切割给出的相反半空间芽，为 A、B 两张封帽球面分别选择充分小的一般位置高度：与保留盘位于旧水平面的同一侧倾斜帽面，使选定的最内层圆周 J 在帽尖新高度层消失，同时保留所有非例外奇异点比较。F-M1 仍为 partial，严格指标下降、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF202.lean`。

### 19.54 F-M1：保持旧次序的向下半空间一般位置扰动

`HeightPerturbationSymmetry.lean` 已提交并推送为 `026576e48`。主端点 `exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace_below_of_isPolyhedron` 对有限一般位置集合、有限旧顶点集以及位于旧等高面的紧多面体片构造任意小的新高度，使其在一般位置集合上单射、保持旧顶点的全部严格高度次序，并把多面体片除指定点外严格压到该点下方。证明对旧高度取负后调用向上半空间扰动，再把所得高度取负；距离、非零性、单射性和旧次序均逐项搬回。

模块聚焦检查 exit=0（10.7 秒）、零 warning；`AuditF202.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步在参数化三角切割的两个相反侧分支中，分别用向上与向下生产者选择独立高度，并接入相应的单帽奇异点比较端点，输出两张封帽球面及方向相反的严格帽面分离。F-M1 仍为 partial，严格指标下降、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF203.lean`。

### 19.55 F-M1：两张封帽球面的独立相反方向扰动

`OppositeTriangleCapPerturbation.lean` 已提交并推送为 `feeae6c5a`。主端点 `exists_small_opposite_triangle_cap_pair_with_singular_comparison` 从一个旧奇异点同时保留所选最内层圆周 J、两盘分割和临界层计数恒等式，但为 A、B 两张封帽球面分别选择独立的新高度。若 A 在旧水平面局部高侧，则 A 的帽面严格高于帽尖而 B 的帽面严格低于帽尖；另一侧别分支完全互换。两个高度都可任意逼近旧高度、在各自新复形顶点上单射、保持全部旧顶点严格次序，并分别满足去帽尖后的奇异点包含和每个非例外旧顶点处的层圆周数不增。

模块聚焦检查 exit=0（16.1 秒）、零 warning；`AuditF203.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步证明匹配方向的局部层圆周消失引理：保留盘在 J 去掉 p 后位于旧水平面的同一闭半空间，而新高度把整个变形后三角盘去掉 H p 严格推到该侧时，新帽尖层的圆周可注入保留盘的旧临界层圆周族，且像避开指定 J。F-M1 仍为 partial，严格指标下降、Lemma 1、Lemma 2–6 和 I1 尚未交付；下一审计文件 `AuditF204.lean`。
