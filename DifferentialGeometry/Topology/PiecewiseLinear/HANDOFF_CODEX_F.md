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

### 19.56 F-M1 停点：相对层圆周删除的确切义务

Moise 17.12 的两个相反转轴现已分别构造，且每张封帽球面的全部非例外奇异点与层圆周贡献均已控制。剩余义务不再是变形后整张原球面的临界层稳定性，而是以下相对带边版本：对 `Q = A` 或 `B`，在 `Q` 沿共同边界圆周 `J` 的穿孔集合芽位于旧水平面一侧、`H '' D \ {H p}` 被新高度严格推到同侧、并保持旧顶点严格次序时，构造单射

`levelPolygons (H '' (Q ∪ D)) f (f (H p)) ↪ levelPolygons Q ℓ (ℓ p) \ {J}`。

等价的计数结论是新帽尖层圆周数加一不超过旧保留盘临界层圆周数。现有 `HeightRotation` 只处理无边界 PL 球面且基剖分在旧高度上一般位置；`HeightLocalization` 只处理扰动支集避开的其他旧顶点；`TriangleCapSingularComparison` 排除了帽尖以外的新奇异点，但不构造跨越边界临界值时的层圆周对应。把整球稳定性用于 `H '' K.space` 也要求一个旧高度一般位置的直线剖分，而凸化同胚在 `H '' J` 上必产生多个同高折点。故当前库缺少的是真实的相对 PL 高度稳定性/一次边界临界圆周删除定理，不能由集合包含或现有 `encard` 引理补出，也不能把所需单射加入最终结论的假设。

按 `NIGHT_PLAN.md` §0.4，F-M1 在此保持 partial 并转入下一里程碑；已完成的相反方向生产者保留为后续证明的精确前置。F-M2 下一审计文件仍使用 `AuditF204.lean`。

### 19.57 F-M2：正规奇异 2-胞腔接口与坐标搬运

`SingularNormalForm.lean` 已提交并推送为 `63077045e`。`IsNormalSingularCell` 同时记录局部单射、至多二重纤维、边界像约束、精确奇点图的一维带边组合三角剖分，以及每个双点的坐标 crossing。边界双点由 `HasPLNormalDoubleCrossingAt` 的第一分支表达：点位于坐标边界像，并显式给出实际局部半空间集合和 `HasPLBoundaryDoubleCrossingAt`；内部点由第二分支给出 `HasPLDoubleCrossingAt`。局部半空间没有误写成二维边界集合，也没有作为图册自动提供的无根据数据。

基本 API 包含 `HasPLNormalDoubleCrossingAt.postcomp_openPartialHomeomorph` 的坐标后复合搬运、`IsNormalSingularCell.locallyInjective_restrict`、`fiber_le_two_restrict`、`doublePointSet_mono` 的源子集限制，以及 `exists_crossing_chart`。聚焦检查 exit=0（12.1 秒）、零 warning；`AuditF204.lean` 七项均只依赖 `propext`、`Classical.choice`、`Quot.sound`。F-M2 done；F-M1 的相对层圆周删除缺口仍保持 §19.56 的精确形式。下一里程碑 F-M3 写 `TwoFoldCrossing.lean`；下一审计文件 `AuditF205.lean`。

### 19.58 F-M3：两张折叠曲面的共同拉直与 crossing

`TwoFoldCrossing.lean` 已提交并推送为 `10fd6827e`。`exists_common_direction_of_eq_apply` 在两条一维折线方向张成的共同折叠平面两侧，显式解出两张半片平面的共同横向方向。`exists_isPLHomeomorphOn_straighten_two_folds` 将正、负方向分别归一到高度 1 和 −1，再用固定整个折叠平面的分片线性剪切把负方向送到正方向；同一个全局 PL 同胚因而同时把两张折叠曲面拉直为 `S ⊔ span {w}` 与 `T ⊔ span {w}`。

主端点 `hasPLCrossingAt_of_two_folds` 证明三维空间中，若两个一维折线方向共同张成折叠平面的高度核，且每张曲面的两个半片分别严格位于该平面两侧，则两张局部折叠曲面在交点满足 `HasPLCrossingAt`。一维条件、三维维数和核的张成等式已经排除两条折线重合；四个严格高度符号给出各半片的横截性，没有另加 crossing 假设。聚焦检查 exit=0（12.2 秒）、零 warning；`AuditF205.lean` 七项均只依赖标准三公理。F-M3 done；下一里程碑 F-M4 写 `ArrangementGeneralPosition.lean`，下一审计文件 `AuditF206.lean`。

### 19.59 F-M4：有限仿射平面族的分层相对通用位置

`ArrangementGeneralPosition.lean` 已提交并推送为 `f1efe8e04`。`arrangementDirection` 与 `arrangementLayer` 把一点所在层定义为所有经过该点的安排超平面的方向交与相应仿射平移；`openCell_mem_nhdsWithin_arrangementLayer` 证明原符号胞腔是该层中的相对邻域。`exists_mem_openCell_notMem_affineSubspaces` 在任意小相对球中同时避开有限个不包含整层的坏仿射子空间，`exists_small_update_affineIndependent_in_arrangement` 给出单顶点插入。

有限同步生产者 `exists_small_affineIndependent_constraints_in_arrangement` 接受固定顶点集、有序可动顶点表和有限约束族。每次插入只要求该约束中已确定点数不超过当前层维数；`arrangementLayer_not_le_affineSpan_of_affineIndependent` 从这个计数实际推出坏仿射包在当前层中为真子空间。所得映射固定全部非可动顶点、任意小、并让每个可动顶点留在原开胞腔的相对内部，同时使全部指定约束仿射无关。

主端点 `exists_small_vertexMap_transverse_in_arrangement` 再以 `arrangementEnvelope` 表示一组顶点各层的最小共同仿射包。只要约束族覆盖每对待比较面之并内、基数不超过包络维数加一的子集，相交的不交面扰动后满足方向空间之和精确等于该安排包络的方向。单平面边界情形的核平面/全空间二分由此成为包络方向的特例；固定部分只输入自身的仿射无关性，没有输入最终横截结论。

聚焦检查 exit=0（12.2 秒）、零 warning；`AuditF206.lean` 十九项全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`。F-M4 done，无剩余缺口；下一里程碑 F-M5 重写 `RelativeNormalForm.lean`，下一审计文件 `AuditF207.lean`。

### 19.60 F-M5：安排分层下的欧氏相对正规形式核心

`RelativeNormalForm.lean` 已重写并提交为 `1c1074eea`。`eventually_mem_space_iff_mem_coface_pair_foldedPlane` 把二维组合流形一条内折边的两个余面精确识别为 `foldedPlane` 集合芽；`hasPLCrossingAt_of_two_fold_faces` 将该识别接到 F-M3 的双折叠定理。`IsArrangementGeneralFoldPair` 用安排超平面、两条折边的方向张成等式、以及两片分别位于超平面两侧来陈述固定折边的一般位置；`foldDirections_ne` 在三维中从这些数据实际推出两折线方向不相同，因而明确排除了 §16.2 的重合固定折边，而没有假设 crossing。

`hasPLCrossingAt_of_transverse_or_arrangement_fold` 统一处理普通横截的平/平、折/平情形与同一安排平面内的折/折情形。`IsBoundaryArrangementGeneralPair.hasPLBoundaryCrossingAt` 给出零平面边界版。`IsVertexMapGeneralInArrangement` 记录顶点留在原安排开胞腔、约束族仿射无关、相交面方向张成安排包络方向；`exists_small_vertexMap_generalInArrangement` 从 F-M4 的生产者给出任意小相对位移并保持这一完整不变量。

F-M5 状态为 partial。唯一未闭合的生产步骤是：给定 F-M6 的公共仿射细分 `K*`，从 `IsVertexMapGeneralInArrangement` 对每个实际双点识别两张像面星的最小载体，证明其集合芽要么方向张成全空间，要么恰形成 `IsArrangementGeneralFoldPair`；边界点则形成 `IsBoundaryArrangementGeneralPair`。F-M4 已生产方向等式，但尚无现成 API 把目标 `K*` 的共面相邻三胞腔及图卡变换的两侧性搬成两个余面顶点的严格异号条件。不能把这项局部分类作为结论型假设塞入最终正规形式端点；它必须由 `K*` 的组合流形结构和图卡同胚性证明。

聚焦检查 exit=0（13.8 秒）、零 warning；`AuditF207.lean` 十六项全部只依赖 `propext`、`Classical.choice`、`Quot.sound`。下一里程碑 F-M6 在 `SingularNormalForm.lean` 构造紧致片、公共细分与图卡归纳，并尝试生产上述局部分类；下一审计文件 `AuditF208.lean`。

### 19.61 F-M6：紧致载体、星图卡族与公共仿射细分

`PiecewiseAffineSimplicial.lean` 与 `SingularNormalForm.lean` 已提交并推送为 `5d5a89f9f`，星图卡接口加强提交为 `04b71666c`。`exists_isSubdivision_affineOn_faces_finset` 与 `_finite` 对有限族逐片仿射映射构造同一个有限细分；后续细分上的仿射性由载体面包含保持。`IsPiecewiseAffineOn.exists_isSubdivision_affineOn_subcomplex`、`exists_isSubdivision_affineOn_subcomplexes_finset` 与 `_finite` 把该构造推广到有限子复形族：逐个把子复形的仿射细分相对延拓到全复形，随后用限制细分保持已经处理的各子复形。

`SingularTwoCell.exists_compact_piece_neighborhood` 用 F6.2 将整幅紧致像装入一个紧致多面体三维带边流形片。`PLPieceIn.exists_isSubdivision_affineOn_chart_stars` 先细分至每个旧顶点的整个闭星落入一张 PL 图卡，再对全部有限闭星作上述共同相对细分；输出保留旧复形、公共细分、每个旧顶点的实际图卡、闭星包含以及该图卡坐标在公共细分限制中的每个单形上的仿射公式。`PLPieceIn.exists_isSubdivision_affineOn_chart_faces` 给出逐面消费版本。`SingularTwoCell.exists_compact_piece_affine_chart_refinement` 将紧致载体、公共细分、三维带边组合流形性、原像包含于载体内部和逐面仿射图卡一次性打包。这已经完成 F-M6 的 `K_T`、有限星图卡族与 `K*` 生产，不把全域图卡映射的逐片仿射性作为错误假设。

F-M6 状态为 partial。剩余的首个数学义务是一个真实的余面异侧定理：在上述同一星图卡内，若 `q` 是 `K*` 的内部二维面且恰有两个三维余面，则两个余面的对顶点在 `affineSpan ℝ (e(T(q)))` 的严格相反两侧；边界二维面唯一余面的对顶点须位于所选内部严格一侧。现有组合流形 API 给出余面个数，公共细分给出图卡内的仿射性与单射性，但库中尚无把这两项合成为严格符号的定理。缺少该结论时，不能从 `IsVertexMapGeneralInArrangement` 生产 `IsArrangementGeneralFoldPair` 或 `IsBoundaryArrangementGeneralPair`，因此不能证明每个实际双点的 crossing，也不能启动保持该不变量的有限图卡归纳。该严格异侧性必须从 `K*` 的实际相邻三胞腔、图卡同胚性和单形内部不交推出，不能作为 `exists_small_isNormalSingularCell` 的假设。`Ξ = K*` 的二维骨架、图卡归纳和最终端点均留在此义务之后；本次未声明 `exists_small_isNormalSingularCell`。

聚焦检查：`PiecewiseAffineSimplicial` exit=0（9.5 秒）、`SingularNormalForm` exit=0（12.2 秒），均零 warning。`AuditF208.lean` 十八项全部只依赖 `propext`、`Classical.choice`、`Quot.sound`。F-M6 partial；下一审计文件 `AuditF209.lean`。

### 19.62 F-M1：小 Lipschitz 扰动下的三角形截面为 PL 弧

`TriangleFiber.lean` 从三角域的水平切片严格递增、左边严格递增、右边严格递减，实际构造每条非极值等高纤维到一个非退化闭区间的第二坐标双射。`exists_isPLHomeomorphOn_snd_triangle_fiber` 用纤维的紧致多面体性将该双射升级为 PL 同胚，`isPLBall_triangle_fiber_of_monotone` 给出 PL 一维球。证明允许函数在原三角形内部任意有限分段，不要求凸化后的函数在整个旧三角形上仿射。

定量端点 `exists_isPLHomeomorphOn_snd_triangle_fiber_of_lipschitz` 与 `isPLBall_triangle_fiber_of_lipschitz` 从实际误差控制生产上述三方向单调性：若 `b(x,y) - (a*x+c*y+d)` 的 Lipschitz 常数 `k` 同时小于 `c` 和 `a-c`，则任意严格介于两个底角值之间的纤维都是 PL 弧。不存在把弧性、纤维对应或层圆周计数加入假设的做法。

聚焦检查 exit=0（10.8 秒），零 warning；`AuditF211.lean` 七个公开端点全都只依赖 `propext`、`Classical.choice`、`Quot.sound`。此前已推送的 `59c52ce24`、`bce61a695` 提供 `RelativeLevelCircleDeletion.lean` 的精确纤维删除消费者及固定子复形外的逐面符号控制，后者由 `AuditF210.lean` 审计；这些仍不是相对删除的生产者。

F-M1 仍为 partial。下一步把凸化映射在紧致旧三角形上的 PL Lipschitz 延拓与新高度的算子范数小量接入本定量端点，然后构造沿旧三角形公共边相容的纤维同胚，并证明它在保留盘上删去指定圆周 `J`。§19.56 的单射、严格降指标、S.4 M2/M3 及 I1 尚未交付。下一审计文件 `AuditF212.lean`。

### 19.63 F-M1：保高度凸化后的旧三角形小转轴截面

`HeightTriangleStability.lean` 已把 §19.62 的定量判据接到实际 PL 映射。`eventually_exists_isPLHomeomorphOn_triangle_fiber_of_affine_height` 对在紧致三角形上具有仿射旧高度的逐片仿射映射，先构造全域 PL Lipschitz 延拓，再把扰动写成旧仿射高度加 `(f-ℓ) ∘ G`；算子范数邻域统一控制全部中间层。输出每条这样的实际纤维到非退化区间的 PL 同胚。`eventually_isPLBall_image_triangle_fiber_of_affine_height` 在映射单射时把弧性送到像截面。

主端点 `eventually_isPLBall_affine_triangle_image_fiber` 已直接用于环境同胚：只要求 `H` 是保 `ℓ` 的全域 PL 同胚，仿射三角形的三个旧顶点高度严格排序，就证明充分小的每个新高度 `f` 在 `H` 的三角形像内、严格介于两底角值之间的截面是 PL 一维球。没有要求 `H` 在旧三角形上仿射，也没有假设凸化后旧高度在新顶点上单射。故同高折点已经不再阻挡单个旧面的纤维稳定性。

聚焦检查 exit=0（13.3 秒）、零 warning；`AuditF212.lean` 三个公开端点全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`。F-M1 仍为 partial；下一步补弧端点与旧边的精确对应、极值层的单点/空集分类，然后沿公共边拼接各旧面的纤维映射，接入 `Q` 的侧芽以得到 §19.56 的相对删除。S.4 M2/M3、I1 尚未交付。下一审计文件 `AuditF213.lean`。

### 19.64 F-M1：逐边保持的三角形纤维 PL 对应

`TriangleFiberBoundary.lean` 证明中间层截面恰在区间参数的两个端点碰三角形边界，并精确识别退出边：左边当且仅当参数为上端点且目标层不高于上角值，右边当且仅当参数为上端点且目标层不低于上角值。最低、最高纤维分别精确等于对应单点；高度范围外的纤维为空。端点分类由实际单调性和介值性推出。

`TriangleFiberEquivalence.lean` 的 `exists_isPLHomeomorphOn_triangle_fibers_preserving_edges` 以两个纤维的区间参数和正比例缩放构造 PL 同胚。只要两个目标高度相对中间角点的大小/相等情形一致，所得对应逐点保持三条旧边的成员关系，包含经过上角的情形；边兼容不是输入。该结论是随后沿旧三角形公共边拼接的局部数据。

聚焦检查：`TriangleFiberBoundary` exit=0（11.7 秒），`TriangleFiberEquivalence` exit=0（11.7 秒），均零 warning；`AuditF213.lean` 七项全都仅依赖 `propext`、`Classical.choice`、`Quot.sound`。F-M1 仍为 partial。下一步从 §19.63 的 Lipschitz 误差生产三方向单调性和顶点符号稳定性，实际得到每个小转轴的逐边保持对应；再进行有限复形拼接和保留盘侧芽分析。§19.56 的相对层圆周删除、S.4 M2/M3 与 I1 尚未交付。下一审计文件 `AuditF214.lean`。

### 19.65 F-M1：小转轴实际生产逐边保持的全部三角形纤维对应

`TriangleFiber.lean` 将既有定量证明抽出为 `strictMonoOn_triangle_slices_of_lipschitz_sub_affine`，旧端点签名保持。`HeightTriangleStability.lean` 的 `eventually_strictMonoOn_triangle_height` 通过 PL Lipschitz 延拓实际生产小转轴后高度的三个单调方向，旧区间参数化和像截面弧性端点现在直接消费该结果。

新端点 `eventually_exists_isPLHomeomorphOn_triangle_fiber_preserving_edges` 对任意指定点高度同时处理全部情形：介于底角值之间时，用有限顶点严格次序稳定性确定退出边，再构造逐边保持的 PL 同胚；最低/最高值层用同高角点等于指定点这一真实唯一性条件固定相应单点；高度范围外两纤维均为空。因此结论从实际小高度邻域生产新旧层对应，不要求调用者输入单调性、边对应或层圆周计数，也不需要排除经过旧顶点的临界层。

聚焦检查：`TriangleFiber` exit=0（15 秒），`HeightTriangleStability` exit=0（12.9 秒），均零 warning；`AuditF214.lean` 八项全部只依赖 `propext`、`Classical.choice`、`Quot.sound`。在本工作树没有 Lean 进程时运行 `fresh.py`，5 个改动模块的 olean 均新鲜、禁用模式 0；脚本同时提示系统另有一个 Lean 进程，故最终验收依上述聚焦检查与审计。

F-M1 仍为 partial。单个旧三角形的全部纤维及逐边对应已闭合；下一步把有限原面族的局部映射按公共边唯一交点拼成整体 PL 对应，并从保留盘的相反半空间芽证明指定 `J` 的相对删除。§19.56 的全局单射、严格降指标、S.4 M2/M3 与 I1 尚未交付。下一审计文件 `AuditF215.lean`。

### 19.66 F-M1：有限 PL 拼接与二维复形的层纤维拼接

`FiniteGluing.lean` 构造有限多面体闭覆盖上的实际全局映射：局部 PL 同胚在交上相容且交像精确时，拼接为并集之间的 PL 同胚，并逐片保持给定函数。`exists_isPLHomeomorphOn_iUnion_of_subsingleton_inter` 进一步从目标两片交至多一点、局部映射保持其他片成员关系，推导相容性及交像等式。

`HeightFiberGluing.lean` 的纯代数引理证明至多两顶点凸包的一般高度纤维至多一点，并由复形面交性质与顶点高度单射，证明不同二维面在目标层的交至多一点。`exists_isPLHomeomorphOn_height_fiber_of_face_maps` 因而把二维有限复形逐面的 PL 纤维映射实际拼成整个 `K.space` 层截面的 PL 同胚。输入的源片多面体性不再单独假设，而是从到旧面线性纤维的局部 PL 同胚反推出。公共交上的相容和全局单射均在证明中推出。

聚焦检查：`FiniteGluing` exit=0（9.2 秒），`HeightFiberGluing` exit=0（11.6 秒），均零 warning；`AuditF215.lean` 五项全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`。F-M1 仍为 partial。下一步用实际仿射三角形坐标把 §19.65 的逐边对应搬为这里所需的逐原面成员关系，并统一有限个小高度邻域；保留盘侧芽到指定圆周删除仍在其后。尚未交付 §19.56 的相对单射、S.4 M2/M3 或 I1。下一审计文件 `AuditF216.lean`。

### 19.67 F-M1：三角形坐标与任意子面的精确搬运

`TriangleCoordinates.lean` 定义按最低、中间、最高角点排列的仿射三角形坐标及三个重心系数，证明坐标像恰为三个顶点的凸包，并由仿射无关性证明坐标映射单射。`triangleAffineMap_mem_convexHull_image_iff` 把属于任意顶点子集凸包精确刻画为其余重心系数为零；`triangleAffineMap_mem_convexHull_image_iff_of_preserving_edges` 因而从三条边的成员关系保持推出每个子面的成员关系保持。全部证明只用实模的代数结构，没有加入范数或有限维假设。

聚焦检查 exit=0（10.6 秒）、零 warning；`AuditF216.lean` 十个定义和公开定理全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`。F-M1 仍为 partial。下一步按原高度排列各旧三角形顶点，把 §19.65 的局部对应搬到实际面并统一有限个小高度邻域，再证明保留盘的相对层圆周删除。§19.56、S.4 M2/M3 与 I1 尚未交付。下一审计文件 `AuditF217.lean`。

### 19.68 F-M1：保高度 PL 变换后的整体层纤维稳定性

`HeightFaceStability.lean` 从旧高度在三顶点上的单射性实际构造有序仿射坐标，调用 §19.65 的小转轴生产者，再经 §19.67 的重心系数判据搬回原面。`eventually_exists_isPLHomeomorphOn_face_fiber_preserving_subfaces` 对该面的每个子面同时保持成员关系，包含临界层、单点和空层。

`HeightComplexStability.lean` 的 `eventually_exists_isPLHomeomorphOn_height_fiber_preserving_faces` 在有限纯二维复形上统一全部三角形的小高度邻域，由复形的精确面交把逐子面保持升级为任意其他原面的成员关系保持，然后实际拼出整个新旧层的 PL 同胚。源层是 `K.space ∩ {x | f (H x) = f (H p)}`，目标是原直线复形的 `K.space ∩ {x | ℓ x = ℓ p}`；`H` 只要求全域 PL 且保持旧高度，不要求它在旧面上仿射。带边组合二维流形版本直接从已经证明的纯维性得到该生产者，没有把纤维对应作为假设。

聚焦检查：`HeightTriangleStability` exit=0（12.7 秒）、`HeightFaceStability` exit=0（12.9 秒）、`HeightComplexStability` exit=0（12.5 秒），均零 warning。前一模块仅公开现有标准三角域多面体引理供复用；`AuditF217.lean` 四个端点全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`。F-M1 仍为 partial；§19.56 的首个剩余义务现为保留盘相对性：从沿 `J` 的半空间芽及转轴将 `J \ {p}` 推至同侧，证明整体对应把保留盘新层的圆周送到旧保留盘圆周且避开 `J`。不能把本整体纤维稳定性误报为相对删除或 I1。下一审计文件 `AuditF218.lean`。

### 19.69 F-M1 检查点：§19.56 相对层圆周删除已闭合

`FaceLevelPolygons.lean` 证明保持全部原面成员关系的映射也保持最小开面；同一开面内的旧水平截面一旦碰到某条旧圆周，就全部属于该圆周。后者使用截面的凸连通性及非例外点处的真实层圆周集合芽，不要求圆周预先是旧复形的子复形。

`HeightFiberWitness.lean` 在任意小的原开面邻域内，通过保高度连续映射的射线介值构造实际新层点；单侧版本在指定旧层点被推到上侧时，实际给出旧高度严格在下侧的新层点。正高度方向由原顶点的唯一层条件生产。

`RelativeHeightDeletion.lean` 的 `eventually_exists_isPLHomeomorphOn_fiber_deleting_levelPolygon_of_upper_side` 已构造整体层 PL 同胚，其圆周像把保留盘的新层圆周送入旧保留盘圆周族且避开 `J`。证明对每条不属于保留盘的旧圆周选取盘外开面见证，再用旧圆周族有限性统一邻域；对指定 `J` 则用同侧推离和旧半空间芽选取反侧新层见证。映射在实际新层上单射，因此确实给出圆周族单射，而非把单射或计数作为输入。

封帽端点 `eventually_encard_levelPolygons_cap_add_one_le_of_upper_side` 与 `_of_lower_side` 直接证明 `(levelPolygons (H '' (Q ∪ D)) f (f (H p))).encard + 1 ≤ (levelPolygons Q ℓ (ℓ p)).encard`。只需要 `Q` 闭且包含于原球面、`J` 是旧保留盘层圆周、`J ⊆ D`、沿 `J` 的相应半空间芽，以及 `H` 保旧高度和新高度把 `H '' D` 除帽尖外严格推至同侧；允许 `p ∉ J`。§19.56 的数学缺口至此关闭，没有增加 `SchoenfliesInput` 字段。

聚焦检查：`FaceLevelPolygons` exit=0（10.8 秒）、`HeightFiberWitness` exit=0（11.3 秒）、`RelativeHeightDeletion` exit=0（13.1 秒），均零 warning。`AuditF218.lean` 九项全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`；fresh 自检 13/13 新鲜、禁用模式 0。下一步将相对删除邻域并入两方向三角封帽生产者，构造两个严格降指标球面，再做 Lemma 1 归约和 S.4 M2/M3。F-M1 整体与 I1 仍未交付。下一审计文件 `AuditF219.lean`。

### 19.70 F-M1：两封帽球面严格降指标

`OppositeTriangleCapPerturbation.lean` 的新端点 `exists_small_opposite_triangle_cap_pair_with_level_comparison` 已把相对删除的小高度邻域并入两方向通用转轴生产者；它实际返回两张封帽球面在帽尖层的圆周数加一不超过各自旧保留盘圆周数，并保留其他奇异点比较、环境同胚在指定凸开邻域外恒同、公共帽盘和恢复原球面的精确等式。旧的 singular comparison 接口保持不变。

`HeightIndexReduction.lean` 的 `heightIndex_lt_of_singular_comparison` 将实际奇异点嵌入和逐层比较合成为严格指标不等式：帽尖仍是奇异点时该项严格下降，否则正贡献的原点从嵌入像中消失。`exists_cap_pair_heightIndex_lt_of_pos` 从正的原指标实际选出正贡献点，生产两个指标均严格较小的有限 PL 球面、各自一般位置高度，以及可供 17.11 消费的平面公共盘与精确恢复式；同时环境同胚保持原球面的像位于给定凸开邻域内。没有增加结论型假设。

聚焦检查：`OppositeTriangleCapPerturbation` exit=0（19.7 秒）、`HeightIndexReduction` exit=0（14 秒），均零 warning。`AuditF219.lean` 四端点全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`。§19.56 与严格降指标已闭合，下一步做 Lemma 1 的良基归纳，把 S.4 归约到零指标球面，再闭合 M2 的零指标情形。F-M1 整体和 I1 尚未交付；下一审计文件 `AuditF220.lean`。

### 19.71 S.4 M1 检查点：Lemma 1 的零指标归约闭合

`SchoenfliesReduction.lean` 的 `isSimplyEmbedded_of_heightIndex_zero_case` 已对有限自然数指标作强归纳。正指标分支使用 §19.70 的实际两封帽生产者，分别由归纳假设得到两球面单嵌入，再由 `SchoenfliesInput` 的 17.11 字段拼合；最后复合指定凸开邻域外恒同的环境同胚，恢复原球面的单嵌入，完整保留 `IsSimplyEmbedded` 对每个凸开邻域的量词。任意 PL 球面的有限剖分和非零一般位置高度均由现有生产者选出。

这里的零指标情形是 Lemma 1 要归约到的明确子问题，尚未作为新的 `SchoenfliesInput` 字段，也不是最终 17.12 端点。主定理实际完成从零指标子类到任意球面的归纳论证；S.4 的旧 M1 至此闭合。聚焦检查 exit=0（11.9 秒）、零 warning；`AuditF220.lean` 主端点仅依赖 `propext`、`Classical.choice`、`Quot.sound`。

下一步进入 M2：先证明零指标时不存在高度奇异点，再证明中间水平截面为一条 PL 圆周及相邻层薄片边界单嵌入。M2/M3 与 I1 尚未交付，S.4 和夜间 F-M1 整体仍为 partial；下一审计文件 `AuditF221.lean`。

### 19.72 S.4 M2：零指标恰为无高度奇异点

`HeightLevelLink.lean` 先证明半空间适配复形的水平限制确实覆盖整个水平纤维，再由水平 PL 圆周的顶点链环为零维球，结合保高度符号的径向细分对应，证明原链环水平截面恰有两个点。`notMem_heightSingularPoints_of_isPLSphere_one_fiber` 因而由已经核验的 crossing 判据排除该层上的候选奇异点。

`HeightRegularity.lean` 的 `one_lt_encard_levelPolygons_of_mem_heightSingularPoints` 证明每个高度奇异点所在层至少有两个 PL 圆周：若至多一个，已有临界层覆盖与奇异点属于圆周并的定理迫使整层为一条圆周，违反前述局部判据。`heightIndex_eq_zero_iff_heightSingularPoints_eq_empty` 随后由有限非负指标和闭合零指标与无奇异点的精确等价。这排除了定义中出现贡献为零的实际奇异点，并未将局部正规性加作假设。

聚焦检查：`HeightLevelLink` exit=0（11.4 秒）、`HeightRegularity` exit=0（11.6 秒），均零 warning。`AuditF221.lean` 六项全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步从 crossing 的实际局部模型控制水平图的分支，并证明零指标下中间水平层连通；Lemma 4–6 的薄片及 I1 仍在其后，M2/M3 尚未完成。下一审计文件 `AuditF222.lean`。

### 19.73 S.4 M2：crossing 的实际分支上界与两侧链环连通性

`RadialEmbedding.lean` 证明径向单射点族若各初始径向线段可连续单射映入实直线，则点族至多有两个元素。证明用介值性排除同号的两条不同径向分支，再将方向注入二元类型；无需有限性假设。`CrossingFiber.lean` 从真实 `HasPLCrossingAt` 图卡投影到一维交子空间，实际构造交集的连续实坐标单射，因此任何包含于该交集芽的复形链环至多二点。孤立水平点的链环水平截面则由小径向线段直接证明为空。

`HeightLevelLink.lean` 将既有适配细分构造提取为 `exists_isPLHomeomorphOn_geometricLink_fiber`：实际给出水平纤维剖分，并将其顶点链环 PL 同胚到原链环的水平截面；原圆周纤维端点签名保留。`CrossingFiber.encard_geometricLink_fiber_le_two_of_notMem_heightSingularPoints`（实际全名不含文件前缀）由 crossing/孤立分类证明每个非奇异顶点的该截面至多二点。

`LinkHeightConnected.lean` 使用 PL 圆周的二点截弧参数化，证明避开链环顶点且至多二点的水平截面，其严格上下两部分各自连通（允许空集）。`isPreconnected_geometricLink_halfSpaces_of_heightIndex_eq_zero` 直接从零指标、原顶点一般位置和球面性生产每个顶点的这两项连通性；没有假设分支上界或两侧连通性。

聚焦检查：`RadialEmbedding` exit=0（9.9 秒）、`HeightLevelLink` exit=0（11.3 秒）、`CrossingFiber` exit=0（11.3 秒）、依赖模块 `HeightRegularity` exit=0（10.4 秒）、`LinkHeightConnected` exit=0（10.6 秒），全部零 warning。`AuditF222.lean` 十四项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步将连续严格半空间截面的连通性送到低顶点子复形，再按有限顶点高度排序排除下层分量的合并，从而证明中间层连通。M2/M3、薄片边界及 I1 尚未完成；下一审计文件 `AuditF223.lean`。

### 19.74 S.4 M2：零指标球面的严格上下半空间整体连通

`HeightSubcomplex.lean` 实际构造严格子水平集到低顶点子复形的重心投影：证明低顶点权重和严格为正、投影连续且像恰为该子复形，并保留子复形上的恒同。`SimplicialComplex/EdgeConnectivity.lean` 由有限个闭的图分量复形证明空间连通与边图连通等价；此对应不要求环境有限维。

`Combinatorics/HeightConnectivity.lean` 先逐路径证明：新顶点的原有邻点若可在原图内互达，删去该顶点保连通；再按有限顶点高度最大值归纳，证明所有严格子水平诱导图连通。一般图论端点只用有限顶点、线序高度的单射性以及每个顶点较低邻点在较低部分互达，不预设任何整体子水平连通性。

`HeightSublevelConnected.lean` 用 §19.73 的真实下链环连通性、上述重心收缩和边图对应生产图论前提，再用低顶点闭星与严格半空间的交集拼回原空间。`isPreconnected_halfSpaces_of_heightIndex_eq_zero` 因而直接从有限 PL 二维球面、三维环境、非零一般位置高度及零指标，证明任意高度的严格上下两部分各自连通（允许空集）；没有新增结论型假设。

聚焦检查：`HeightSubcomplex` exit=0（9.7 秒）、`EdgeConnectivity` exit=0（10.4 秒）、`HeightConnectivity` exit=0（5.9 秒）、`HeightSublevelConnected` exit=0（11.1 秒），均零 warning。`AuditF223.lean` 十五项均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步结合球面上 PL 圆周的两侧分离，证明中间水平层恰是一条 PL 圆周；随后推进 Lemma 4–6 的薄片边界。S.4 M2/M3、夜间 F-M1 整体和 I1 尚未完成；下一审计文件 `AuditF224.lean`。

### 19.75 S.4 M2：Lemma 3 的全部中间水平层为 PL 圆周

`Connected/CompactIntersection.lean` 证明 Hausdorff 空间中向下有向的紧致连通集族之交连通，并把严格子水平集的连通性传到闭子水平集。`HeightFiberClosure.lean` 证明一般位置高度的每个非顶点点可由同一面的低高度线段逼近；结合有限顶点删除的稠密性，得到零指标球面在每个严格中间高度的闭上下半空间恰为严格两侧的闭包。这一步覆盖孤立候选顶点，不只处理避开顶点的水平面。

`SimplicialComplex/PuncturedConnected.lean` 从既有流形图卡定理证明维数至少二的连通有限组合流形去掉一点仍连通。`HeightFiberCircle.lean` 的 `exists_levelPolygon_of_between_heights` 因而在经过唯一顶点的层也实际生产一个层圆周；非顶点层使用已有圆周分解。`fiber_eq_levelPolygon_of_heightIndex_eq_zero` 再由球面上的两盘分解、严格两侧连通性及上述闭包公式，证明该圆周等于整个层。最终端点 `isPLSphere_one_fiber_of_heightIndex_eq_zero` 对所有严格位于最高与最低高度之间的 r 成立，没有避开顶点的附加条件。

聚焦检查：`CompactIntersection` exit=0（7.4 秒）、`HeightFiberClosure` exit=0（11 秒）、`PuncturedConnected` exit=0（8.8 秒）、`HeightFiberCircle` exit=0（11.1 秒），均零 warning。`AuditF224.lean` 十项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。Lemma 3 已闭合；下一步提取水平两侧盘及有界填充的层结构，进入 Lemma 4–6 的薄片边界单嵌入。S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成；下一审计文件 `AuditF225.lean`。

### 19.76 S.4 M2：中间水平圆周两侧的精确曲面盘

`Connected/LevelSet.lean` 对任意具闭序拓扑的线序值连续函数证明：连通的严格子水平集（或上水平集）恰是删去该水平纤维后包含其任一点的连通分支，不需要欧氏、紧致或流形假设。`SphericalComponents.lean` 新 API 从球面切圆周的两分支分解中实际选择任意指定分支闭包的 PL 盘参数化，并保留精确的参数边界像。

`HeightHalfDisk.lean` 的 `exists_isPLHomeomorphOn_halfSpaces_of_heightIndex_eq_zero` 结合 §19.74–19.75 的连通性、闭包公式和整层圆周性，实际生产闭上、下半空间截面的两个 PL 盘参数化，两者参数边界均恰为整个水平纤维。`isPLBall_halfSpaces_of_heightIndex_eq_zero` 给出球性 API。仍覆盖顶点高度；没有引入结论型假设，也没有扩充 `SchoenfliesInput`。

聚焦检查：`LevelSet` exit=0（6.3 秒）、`SphericalComponents` exit=0（10.5 秒）、`HeightHalfDisk` exit=0（10.8 秒），均零 warning。`AuditF225.lean` 五项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步构造水平平面张成盘与封帽/薄片，继续 Lemma 4–6；S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF226.lean`。

### 19.77 S.4 M2：水平张成盘及上下封帽球面的精确拼接

`PlanarSpanningDisk.lean` 的 `IsPLSphere.exists_isPLHomeomorphOn_disk_of_subset_fiber` 将任意三维实范数空间中的平面 PL 圆周送入实际二维仿射坐标，使用已经证明的平面 Schoenflies 生产张成 PL 盘并搬回；盘位于原水平面，且位于包含该圆周的任意指定凸开邻域。参数边界像严格等于原圆周。

`HeightCaps.lean` 的 `exists_isPLSphere_pair_of_heightIndex_eq_zero` 使用 §19.76 的两侧曲面盘，实际生产共同平面盘 D，并证明下、上半球各与 D 的并都是 PL 二维球面、两封帽球面的交恰为 D、删去公共盘参数内部后恰好恢复原球面。没有把封帽球性或拼接等式作为输入。此处只交付 PL 球性；封帽边界的单嵌入性仍需后续锥形首尾薄片及中间薄片论证。

聚焦检查：`PlanarSpanningDisk` exit=0（10.1 秒）、`HeightCaps` exit=0（10.8 秒），均零 warning。`AuditF226.lean` 两项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步证明最低/最高顶点附近的截半球确实是水平圆周的几何锥，以 17.10 处理首尾薄片；S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF227.lean`。

### 19.78 S.4 M2：首尾封帽的锥表示与单嵌入生产者

`HeightCone.lean` 对任意实范数空间、任意单纯复形和仿射实值高度证明：若 p 低于 r、其余全部顶点严格高于 r，则每个高度不超过 r 的点所在的面都含 p；沿该面的射线实际构造高度 r 的点，得到闭下截面恰等于 p 与水平纤维的几何锥。这里不需要有限复形、三维环境、零指标或球面性。

`HeightCapCone.lean` 取水平张成盘的实际有限剖分，以其边界复形和上述锥等式证明封帽球面恰为该盘锥的 frontier。`isSimplyEmbedded_lower_cap_of_lt_other_vertices` / `isSimplyEmbedded_upper_cap_of_other_vertices_lt` 因而直接使用固定的 17.10 字段证明首尾封帽单嵌入，没有新增接口字段。

`ExtremeHeightCaps.lean` 的 `exists_height_between_lowest_vertices` 在任意正维有限 PL 球面上实际选出最低两顶点之间的高度；`exists_isSimplyEmbedded_lower_cap_of_heightIndex_eq_zero` / `exists_isSimplyEmbedded_upper_cap_of_heightIndex_eq_zero` 从零指标球面和给定凸开邻域实际生产首尾高度、平面张成盘及单嵌入封帽。两高度都严格位于球面的极端高度之间，且参数边界等于整层圆周。这闭合 Lemma 4/5 的首尾锥形封帽几何论证；未把中间薄片当作已证明。

聚焦检查：`HeightCone` exit=0（8.9 秒）、`HeightCapCone` exit=0（10.6 秒）、`ExtremeHeightCaps` exit=0（10.8 秒），均零 warning。`AuditF227.lean` 九项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步为中间两层的封口薄片球性、实际三维薄片胞腔分解及 Lemma 6 的自由胞腔删除；S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF228.lean`。

### 19.79 S.4 M2：任意两中间高度的双封口薄片是 PL 球面

`HeightSlab.lean` 的 `isPLSphere_slab_of_heightIndex_eq_zero` 从两个实际水平张成盘证明 `(S ∩ {a ≤ ℓ ≤ b}) ∪ D₀ ∪ D₁` 为 PL 二维球面。证明先以 D₀ 替换下半球，再以 D₁ 替换上半球；每次替换的公共圆周、并集和盘参数化均由既有两侧盘定理和高度不等式验证。`exists_isPLSphere_slab_of_heightIndex_eq_zero` 同时在给定凸开邻域内实际生产两张水平盘。端点允许中间高度经过顶点，不附加避顶点条件。

聚焦检查 `HeightSlab` exit=0（10.2 秒）、零 warning；`AuditF228.lean` 两项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。此结果是薄片边界的 PL 球性，尚非单嵌入性。下一步提取只依赖球面与凸胞腔相交盘的实际推移，避免调用要求整体及删除后整体已为 PL 三维球的 `TetrahedronDeletion` 形成循环；随后生产薄片胞腔分解与自由盘相交条件。S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF229.lean`。

### 19.80 S.4 M2：不预设整体三维球性的相对凸胞腔推移

`SphereCellPush.lean` 的 `HasPushProperty.exists_isPLHomeomorphOn_sphere_surgery` 从实际 PL 二维球面 S、具有推移性质的胞腔 C、盘 S∩C 及其位于 frontier C 的条件，构造全空间 PL 自同胚，将 S 送到 `closure (S \ C) ∪ closure (frontier C \ S)`，同时固定 `closure (S \ C)` 和给定开邻域外部。`exists_isPLHomeomorphOn_sphere_surgery_of_convex` 用固定的 17.9 字段生产凸 PL 三维胞腔的推移性质。没有假设薄片整体或删除后的整体已是三维球。

`HasPushProperty.isSimplyEmbedded_of_sphere_surgery` 在 C 位于 S 的凸包内时，将手术后球面的单嵌入传回 S；证明对定义中的每个凸开邻域构造上述相对推移并复合，保留邻域外逐点固定。此处是删除归纳的传递引理，尚未生产薄片胞腔及可删相交盘，未将这些条件当作 I1 的结论。

聚焦检查 `SphereCellPush` exit=0（9.8 秒）、零 warning；`AuditF229.lean` 三项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步为实际薄片胞腔分解、自由盘相交条件与 Lemma 6；S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF230.lean`。

### 19.81 S.4 M2：凸多胞体的实际 PL 球性

`PolytopeBoundary.lean` 的 `IsHPolytope.isPolyhedron_frontier` 从有限线性不等式表示证明边界是非零约束等号截面的有限并，从而是多面体；允许空集、低维退化集和零约束，没有附加内部非空条件。

`ConvexPolytope.lean` 的 `isPLSphere_frontier_and_isPLBall_of_convex` 对任意有限维实范数空间，假设紧凸集有非空内部且边界为多面体，以内部点为顶点将边界剖分作锥；锥空间恰为原凸集，其顶点链环由欧氏邻域定理是 PL 球面，链环又恰为原边界剖分。由此同时生产边界 PL 球面和整体 PL 球。`IsHPolytope.isPLSphere_frontier` 与 `IsHPolytope.isPLBall` 应用于紧凸多胞体；后者维数为环境 finrank，并包含零维情形。证明没有使用三维 Schoenflies，也没有假设胞体已是 PL 球。

聚焦检查：`PolytopeBoundary` exit=0（11.9 秒）、`ConvexPolytope` exit=0（9.6 秒），均零 warning。`AuditF230.lean` 四项均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步将球性生产者应用到水平截面和薄片胞腔，再完成自由胞腔的球面相交盘与删除归纳；S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF231.lean`。

### 19.82 S.4 M2：水平截面和薄片胞腔的非退化球性生产者

`Topology/ConvexLevelSet.lean` 的 `exists_mem_interior_fiber_of_convex` 对任意实范数空间中的凸集、非空内部及连续实值函数，从集合上严格位于 r 两侧的两个点，实际生产内部的 r 层点。证明用凸集内部稠密性及介值性；不要求有限维、紧致或函数仿射。

`PolytopeSection.lean` 先证明紧凸多胞体在有限维定义域的单射仿射映射下的原像仍为紧凸多胞体。`IsHPolytope.isPLBall_inter_fiber` 通过真实仿射纤维坐标和 §19.81 的球性定理，生产横截于内部的余维一 PL 球；`isPLBall_inter_slab` 生产实际穿过内部的闭薄片 PL 球。随后以顶点/点的高度不等式生产内部条件，得到 `isPLBall_convexHull_inter_fiber` 和 `isPLBall_convexHull_inter_slab`。在三维环境中，前者覆盖四面体的三角形与四边形截面，后者覆盖截断四面体；不把截面/胞腔球性藏入假设。

聚焦检查：`ConvexLevelSet` exit=0（7.9 秒）、`PolytopeSection` exit=0（13.9 秒），均零 warning。`AuditF231.lean` 八项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步保留所有原面上的截面控制并构造有限胞腔分解，再生产自由胞腔与薄片球面的相交盘。S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF232.lean`。

### 19.83 S.4 M2：有界补分支与实际三维流形填充

已通过合并整合分支取得 `2abc555f9`（合并提交 `df3228eaa`），使用 S 车道已证明且不带 Schoenflies 假设的闭曲面补集两分支定理。整合版 `Topology/Connected/BallComplement.lean` 提供更强的道路连通性，保留其原源码与接口；此前本地同名草稿已撤除，并恢复对应共享产物。

`BoundedSurfaceComponent.lean` 从补集两分支与大球外连通性实际选出有界分支，证明其闭包是多面体、内部恰为该分支、闭包边界恰为原曲面且外部连通。`SurfaceFilling.lean` 的 `isCombinatorialManifoldWithBoundary_of_space_eq_closure_connectedComponentIn_compl` 将 S 的局部两侧 PL 球与补分支闭包配对，证明任意有限剖分的顶点链环均满足三维流形条件。端点 `IsCombinatorialManifold.exists_isCombinatorialManifoldWithBoundary_boundaryComplex` 从有限连通闭组合二维流形实际生产有限三维带边界流形 R，组合边界及拓扑边界均恰为原曲面；R 是内部的闭包，内部与外部都连通。适用于任意三维实范数空间，不预设原曲面为球面，也未把填充宣称为 PL 三维球。

聚焦检查：`BoundedSurfaceComponent` exit=0（10.3 秒）、`SurfaceFilling` exit=0（10.0 秒），均零 warning；整合版 `BallComplement` 产物恢复检查 exit=0（7.8 秒）。`AuditF232.lean` 六项（含两项整合输入）仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步在实际填充顶点上选择保零指标的一般位置高度，确定水平填充盘和薄片胞腔分解，再做 Lemma 6 自由胞腔删除。S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF233.lean`。

### 19.84 S.4 M2：保零指标的填充高度与每个中间层的实际 PL 盘

`PlanarJordan/RegionRecognition.lean` 在不预设开集连通的条件下证明：非空有界开集避开 Jordan 曲线且边界包含于该曲线时，它恰为曲线内部。`FiberFilling.lean` 的 `exists_isPLHomeomorphOn_closure_inter_fiber` 将三维有界开集的水平截面搬到真实仿射平面坐标，以此识别截面并生产闭截面的 PL 盘参数化，参数边界恰为原边界的水平圆周。只需截面非空和边界截面为 PL 圆周；无需假设截面连通、截面是盘或其闭包交换公式。

`exists_isPLHomeomorphOn_filling_fiber_of_heightIndex_eq_zero` 从零指标与实际填充内部的连通性，通过介值性生产非空条件，覆盖全部严格中间高度，包含顶点高度。`HeightFilling.lean` 的 `exists_continuousLinearMap_injOn_heightIndex_eq` 在任意给定有限点集上选择任意小的一般位置高度，保持原球面指标。端点 `exists_filling_injOn_vertices_of_heightIndex_eq_zero` 实际生产有限三维填充 R、全部 R 顶点上单射的非零高度 f、零指标，以及每个严格中间高度的填充 PL 盘和精确参数边界。边界使用 R 自带的边界复形，原球面与边界复形的空间相等，未假设两份剖分的顶点一致。

聚焦检查：`RegionRecognition` exit=0（8.1 秒）、`FiberFilling` exit=0（10.5 秒）、`HeightFilling` exit=0（10.2 秒），均零 warning。`AuditF233.lean` 五项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步从填充的单形水平截面实际构造有限盘胞腔分解，包含截面公共面与自由盘相交条件，再完成 Lemma 6 的有限删除及 M3 拼装。S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF234.lean`。

### 19.85 S.4 M2：实际四面体截面的有限盘胞腔分解

`SimplexSection.lean` 将截面球性推广到单形自身的维数：仿射独立的 n+2 个顶点跨越给定仿射高度时，截面为 PL n-球，不要求单形满维于环境。一般位置下，任何非空截面要么恰为一个极值顶点，要么跨越高度两侧。因此两个不同至多四顶点的单形的非空截面交，实际为 PL 零维球或 PL 一维球，包含经过顶点的高度层。

`DiskCover.lean` 从有限 PL 二维盘覆盖及点/弧公共部分，实际构造共同剖分并证明 `IsPLDiskDecomposition`。公共部分位于胞腔边界并未作为假设：先用低维 PL 球的稠密补集，再用子流形边界定理导出。

`HeightSectionDecomposition.lean` 定义 `heightSectionCells` 为实际四面体的非退化水平截面。`biUnion_heightSectionCells_eq_fiber` 用填充的正规闭性与盘删去有限顶点后的稠密性，证明这些二维胞腔覆盖整个水平盘，故经过顶点时的单点截面也已覆盖。`exists_isPLDiskDecomposition_fiber_of_heightIndex_eq_zero` 从 §19.84 所生产的零指标填充数据实际构造每个中间层的有限盘胞腔分解及参数化边界；无需另加截面球性、共同剖分或胞腔边界相交假设。

聚焦检查：`SimplexSection` exit=0（10.6 秒）、`DiskCover` exit=0（10.3 秒）、`HeightSectionDecomposition` exit=0（10.3 秒），均零 warning。`AuditF234.lean` 十五项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步证明指定层顶点的闭星截面 d0 是上述胞腔中的子盘，再将相对自由盘提升为三维薄片中与边界相交为盘的凸胞腔，执行有限删除及 M3 拼装。S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF235.lean`。

### 19.86 S.4 M2：闭星截面子盘及其外部自由胞腔的实际选择

`ConeFiber.lean` 证明过锥顶的线性水平截面仍是锥，并实际构造有限底复形。`ClosedStarFiber.lean` 的 `isPLBall_closedStar_inter_fiber` 从整层为正维 PL 球推出顶点闭星的同层截面为同维 PL 球：先将原链环的水平截面与整层剖分的顶点链环作 PL 对应，再分别对球面链环和球链环作锥。结论适用于任意有限维实范数空间，不需要三维、顶点高度单射或预设闭星截面球性。

`HeightStarDecomposition.lean` 从正规闭填充的纯三维性及盘删去有限顶点后的稠密性，证明 d0 恰为实际截面胞腔中包含于闭星者的并。`exists_free_heightSectionCell_outside_closedStar` 因而从整层盘、一般位置高度及 d0 不等于整层，实际生产共同剖分和 d0 外的一块自由截面盘；没有把 d0 球性、子胞腔覆盖或自由胞腔作为额外输入。

聚焦检查：`ConeFiber` exit=0（8.9 秒）、`ClosedStarFiber` exit=0（10.4 秒）、`HeightStarDecomposition` exit=0（10.4 秒），均零 warning。`AuditF235.lean` 七项（含链环搬运输入）仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步将所选自由盘提升为三维薄片凸胞腔，证明其与当前边界的交为盘并闭合有限删除，再做 M3。S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF236.lean`。

### 19.87 S.4 M2：无顶点单形薄片的逐子面 PL 棱柱模型

`CellEquivalence.lean` 对两个有限仿射超平面配置，从出现的符号向量族相同构造导出剖分的同构及 PL 同胚，并证明每一点的全部定义符号保持。`SimplexHeightInterpolation.lean` 从高度闭区间避开全部顶点，实际生产各层上具有相同零坐标集合的标准单形点；不假设层的面对应。

`SimplexSlabPrism.lean` 因而实际生产标准单形闭薄片到其下端截面乘闭区间的 PL 同胚，保留全部零坐标及上下端面。`SimplexCoordinates.lean` 提取标准线性组合的 PL 坐标、任意子面由坐标零集确定的纯代数 API。`SimplexSlab.lean` 的 `exists_isPLHomeomorphOn_convexHull_slab_prism` 将模型搬回任意有限维实范数空间中的仿射独立单形，保留每个原子面的成员关系及两端截面；不要求单形满维、不要求恰四个顶点，也不假设一个棱柱参数化。该结果用于 d0 外非关联顶点胞腔的侧面带与可删边界盘。

聚焦检查：`CellEquivalence` exit=0（8.2 秒）、`SimplexHeightInterpolation` exit=0（8.1 秒）、`SimplexSlabPrism` exit=0（9.3 秒）、`SimplexCoordinates` exit=0（8.4 秒）、`SimplexSlab` exit=0（9.2 秒），均零 warning。`AuditF236.lean` 十项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步生产自由截面盘对应的三维侧面带，证明其与当前薄片边界的交为 PL 盘，随后有限删除及 M3。S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF237.lean`。

### 19.88 S.4 M2：自由截面胞腔的实际侧面带与两端相交盘

`SimplexSlabPrism.lean` 与 `SimplexSlab.lean` 将既有棱柱模型推广到闭区间内任意参考高度 r，仍保持所有原子面和上下端截面；参考截面可取层内唯一顶点的高度。`SlabFaceTransport.lean` 从单形交为公共面的性质，将逐子面控制提升为对原复形每个子复形的成员关系保持，不假设各侧面带已经存在。

`PrismArcPatch.lean` 的 `isPLBall_prism_ends_union_arc` 用实际棱柱边界上的两次沿弧粘盘，证明两端盘与一条边界弧上方的侧面带之并是 PL 二维盘。`FreeCellSlab.lean` 的 `isPLBall_slab_patch_of_isFreeDiskCell` 从实际截面盘分解中的自由胞腔及精确截面边界等式，生产原薄片中对应的相交盘。自由弧等于胞腔与整层边界之交由子流形边界单调性导出，棱柱模型沿原边界子复形保持此交；没有增添相交盘球性或侧面带参数化假设。

聚焦检查：`SimplexSlabPrism` exit=0（8.8 秒）、`SimplexSlab` exit=0（9.3 秒）、`SlabFaceTransport` exit=0（8.4 秒）、`PrismArcPatch` exit=0（11.3 秒）、`FreeCellSlab` exit=0（9.8 秒），均零 warning。`AuditF237.lean` 六项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。下一步把此相交盘生产者接入 d0 外自由胞腔的实际选择，证明凸胞腔及可推移条件并执行有限删除，再做 M3。S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF238.lean`。

### 19.89 S.4 M2：闭星外实际凸胞腔的选择与单步相对环境删除

`Topology/SlabBoundary.lean` 证明闭集交的精确边界公式，以及任意实范数空间中非零连续线性高度的闭薄片边界公式。`HeightFreeSlab.lean` 的 `exists_convex_slab_cell_of_ne_closedStar` 从实际填充、精确参数边界的水平盘和层内唯一顶点 p，在 d0 不等于整层时实际选出不含 p 的四面体 T。其闭薄片胞腔 C 是凸 PL 三维球，与整体薄片边界的交是 PL 二维盘，且此交包含于 frontier C；未把自由胞腔、三维球性或可删相交盘作为额外输入。

`HeightSlabSurgery.lean` 先从零指标生产整体填充薄片边界的 PL 二维球性。`exists_isPLHomeomorphOn_delete_slab_cell` 随后消费上述实际胞腔与固定 17.9 输入，构造环境 PL 自同胚，将 S 送到 `closure (S \ C) ∪ closure (frontier C \ S)`，固定 `closure (S \ C)` 及给定凸开邻域 W 外。C 位于 W 的条件由薄片紧致性和 `Topology/ConvexFrontier.lean` 的边界包含定理证明，不要求 W 预先包含三维填充，也不假设整体薄片为 PL 三维球。

聚焦检查：`SlabBoundary` exit=0（7.9 秒）、`HeightFreeSlab` exit=0（10.2 秒）、`HeightSlabSurgery` exit=0（10.8 秒），均零 warning。`AuditF238.lean` 五项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。已闭合实际单步删除；下一步证明删除后的区域与截面分解保留归纳条件，有限迭代到残余闭星锥，再做 M3。S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF239.lean`。

### 19.90 S.4 M2：截面上保留 d0 的实际有限自由胞腔删除序列

`DiskCellDeletion.lean` 证明删除一块原胞腔 C 后的闭包恰为其余原胞腔之并；证明使用两两点/弧交的低维稠密补集，没有将覆盖余项的等式作为假设。自由胞腔与整层边界的交是弧，由此证明删除后仍是 PL 盘，并在原共同剖分的限制上保留全部剩余胞腔，得到新的 `IsPLDiskDecomposition`。

`IsFreeDiskCellDeletion D` 精确记录一轮删除：源盘分解、所选自由胞腔 C、C 不包含于固定子盘 D，以及目标复形和胞腔族恰为闭差限制与 erase。`IsPLDiskDecomposition.exists_free_disk_cell_deletion_sequence` 以胞腔族的严格子集归纳，实际构造有限轮删除到 D，保留组成 D 的所有原胞腔。`HeightStarDeletion.lean` 的 `exists_free_disk_cell_deletion_sequence_to_closedStar` 将此序列接到实际四面体水平截面；终点恰为闭星截面 d0，剩余胞腔恰为最初包含于闭星者。

聚焦检查：`DiskCellDeletion` exit=0（9.7 秒）、`HeightStarDeletion` exit=0（9.9 秒），均零 warning。`AuditF239.lean` 六项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。二维有限删除及准确终点已闭合；下一步把序列的每一步提升到三维剩余薄片，证明更新后的相交盘与区域边界公式，拼接环境推移并识别残余闭星锥。现有 §19.89 环境删除定理直接适用于初始零指标填充，尚未把它宣称为整个三维迭代。S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF240.lean`。

### 19.91 S.4 M2：任意剩余子复形的截面边界与自由胞腔相交盘

`FaceProjection.lean` 证明：在原单形的相对内部，沿该面方向的小投影保持任意有限子复形的成员关系；由此将环境内部点与水平截面的相对内部点精确对应。`FiberBoundary.lean` 用真实仿射平面坐标把 PL 盘的相对内部与参数边界互补对应，得到任意剩余子复形在非顶点处的环境边界与其水平盘组合边界的等价，不要求剩余子复形预先为三维流形。

`FaceInterior.lean` 证明任意有限子复形的内部/边界成员关系在每个原开单形上恒定，因此其拓扑边界实际为原复形的限制子复形。`FreeCellSlab.lean` 将既有相交盘生产者的边界等式减弱为所选胞腔上的局部交等式，唯一旧消费者已同步。`SubcomplexSlab.lean` 的 `isPLBall_frontier_slab_inter_cell_of_isFreeDiskCell` 因而直接从当前水平盘分解及其自由胞腔，生产对应三维薄片胞腔与当前薄片边界的 PL 二维相交盘。避开胞腔全部顶点的高度区间排除了该胞腔截面上的原顶点，局部边界等价遂覆盖整块自由胞腔；没有新增整体边界等式或相交盘假设。

聚焦检查：`FaceProjection` exit=0（9.5 秒）、`FiberBoundary` exit=0（9.8 秒）、`FaceInterior` exit=0（9.3 秒）、`FreeCellSlab` exit=0（9.7 秒）、`SubcomplexSlab` exit=0（9.8 秒）；旧消费者 `HeightFreeSlab` exit=0（10.4 秒）、`HeightSlabSurgery` exit=0（10.8 秒），全部零 warning。`AuditF240.lean` 十三项仅依赖 `propext`、`Classical.choice`、`Quot.sound`；无 Lean 进程时 `fresh.py` 为 71/71 fresh、零 stale/missing、零禁用项。下一步连接现有三维流形补集定理，识别每轮剩余薄片与原胞腔删除，迭代环境推移到闭星锥并做 M3。S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF241.lean`。

### 19.92 S.4 M2：真实闭差区域的边界、原胞腔和水平盘同步删除

`Topology/Connected/CompactRegion.lean` 证明非紧 Hausdorff 空间中紧致正规闭区域的边界唯一性，参照区域的内部与外部连通。`SurfaceRegion.lean` 将它接到已证的有界补分支生产者，从实际正规闭区域及连通闭组合曲面边界证明该区域是三维带边界组合流形；球面特例不消费 Schoenflies。`RegionCellPush.lean` 因而先用已有三维流形补集定理证明 `frontier (closure (P \ C))` 的精确换盘公式，再构造环境 PL 同胚，将旧边界实际送到这个闭差区域的边界，固定未删部分和给定凸开邻域外。

`Topology/RegularClosed.lean` 证明正规闭集删去闭集后的闭包仍正规闭，并给出在正规闭条件下闭差与闭集裁剪的交换公式。`ConvexLevelSet.lean` 新 API 由凸集的两端严格不等式生产其内部落在开区间的点；`SimplexSlabInterior.lean` 从端面避开原顶点生产满维单形薄片的非空内部，并证明任意有限正规闭复形的这种薄片仍正规闭。`SimplexSlabDeletion.lean` 的 `closure_sdiff_slab_eq_subcomplexGeneratedBy_inter` 将薄片中删去一块原满维单形的闭差，准确识别为 `subcomplexGeneratedBy K {s | ¬s ⊆ T}` 的薄片。

`HeightCellDeletion.lean` 的 `fiber_subcomplexGeneratedBy_eq_closure_sdiff` 证明同一生成子复形的水平截面恰为旧水平截面删去该胞腔后的闭包。证明在被删单形上排除原顶点，在剩余满维原面上利用点/弧相交的低维稠密补集；不预设余截面为盘。`heightSectionCells_erase_subset_subcomplexGeneratedBy` 同时保证其余每一块原截面胞腔仍由剩余原面生产，且此结果无需有限维假设。下一步把 §19.91 的自由相交盘与这些等式组合为完整删除步骤，对 §19.90 的有限序列归纳，直到闭星锥后做 M3。

聚焦检查：`CompactRegion` exit=0（5.5 秒）、`SurfaceRegion` exit=0（9.5 秒）、`RegularClosed` exit=0（5.2 秒）、`RegionCellPush` exit=0（9.6 秒）、`ConvexLevelSet` exit=0（7.4 秒）、`SimplexSlabInterior` exit=0（9.1 秒）、`SimplexSlabDeletion` exit=0（9.5 秒）、`HeightCellDeletion` exit=0（10.2 秒），均零 warning。`AuditF241.lean` 十七项仅依赖 `propext`、`Classical.choice`、`Quot.sound`；无 Lean 进程时 `fresh.py` 为 78/78 fresh、零 stale/missing、零禁用项。三维有限迭代和残余锥识别尚未拼装；S.4 M2/M3、夜间 F-M1 整体及 I1 尚未完成。下一审计文件 `AuditF242.lean`。

### 19.93 S.4 M2：完整三维有限环境删除及闭星薄片精确终点

`SlabCellDeletion.lean` 的 `exists_isPLHomeomorphOn_slab_of_free_disk_cell_deletion` 消费一轮实际二维自由胞腔删除，从当前原子复形中选择对应四面体，证明其不含固定顶点 p，并实际构造下一原子复形。输出同时保留正规闭性、所有含 p 的原面、二维删除后的精确水平盘和其余原截面胞腔，且构造环境 PL 同胚把当前薄片边界送到真实下一薄片边界。未追加余截面盘性、相交盘球性、余区域流形性或额外环境推移输入。

`SlabDeletionSequence.lean` 的 `exists_isPLHomeomorphOn_slab_of_free_disk_cell_deletion_sequence` 对 §19.90 的有限序列作头部归纳，实际复合全部环境同胚。每轮新边界的球性由前一轮环境像传递；给定凸开邻域 W 外始终固定，故新边界仍在 W 内。`ClosedStarSlab.lean` 通过保持全部原子复形的单形棱柱模型，将最终水平盘包含于 d0 的条件提升为整个剩余薄片恰等于闭星薄片，无需额外纯维性或胞腔计数。端点 `exists_isPLHomeomorphOn_frontier_slab_closedStar` 从原零指标填充实际生产环境 PL 同胚，将整个薄片边界送到 `frontier (closedStar K p ∩ ℓ ⁻¹' Icc a b)`，固定 W 外。

当前完整删除端点使用 `a < ℓ p < b`，这是 §19.91–19.92 的端面避开全部顶点版本。书页 124–125 的最终锥论证把 p 放在一端平面，故下一步应将正规闭裁剪和删除步骤推广到 `a = ℓ p` 或 `b = ℓ p`（保持 p 层为真实 PL 盘，删除胞腔仍避开 p），再识别单侧残余闭星为盘与点的 join，消费 17.10，最后按 17.11 做 M3。不能把当前双侧闭星薄片直接冒充 17.10 的盘锥。

聚焦检查：`SlabCellDeletion` exit=0（10.6 秒）、`ClosedStarSlab` exit=0（8.2 秒）、`SlabDeletionSequence` exit=0（9.9 秒），全部零 warning。`AuditF242.lean` 四项仅依赖 `propext`、`Classical.choice`、`Quot.sound`；无 Lean 进程时 `fresh.py` 为 81/81 fresh、零 stale/missing、零禁用项。三维有限删除及闭星精确终点已闭合，单侧锥识别和 M3 尚未完成；S.4 M2/M3、夜间 F-M1 整体及 I1 仍为 partial。下一审计文件 `AuditF243.lean`。

### 19.94 S.4 M2：参考顶点可在端面的完整薄片删除

`SlabFiberInterior.lean` 从凸包中分别严格低于上端和高于下端的点生产满维单形薄片的非空内部，不再要求端面避开全部顶点。`closure_interior_space_inter_slab_of_isPLBall_fiber` 从有限正规闭复形、顶点高度一般位置、闭区间内至多一个顶点 p 及 p 层的正维 PL 球性，证明整个闭薄片正规闭；p 可在任一端面。证明对非顶点使用跨越高度的满维面，对 p 使用水平 PL 球删去有限顶点后的稠密性；适用于任意有限维实范数空间，不要求三维。

`SlabCellDeletion.lean` 与 `SlabDeletionSequence.lean` 的三项删除端点已同步采用 `a < b`、`ℓ p ∈ Icc a b`。被删四面体仍不含 p，故其自身端面继续避开全部顶点；剩余区域的正规闭裁剪由新定理实际生产，闭差交换公式随之成立。书中一端经过 p 的薄片现已纳入完整有限环境删除，未增添剩余区域正规闭性或相交盘假设。

聚焦检查：`SlabFiberInterior` exit=0（9.6 秒）、`SlabCellDeletion` exit=0（10.7 秒）、`SlabDeletionSequence` exit=0（10.1 秒），全部零 warning。`AuditF243.lean` 五项仅依赖 `propext`、`Classical.choice`、`Quot.sound`；无 Lean 进程时 `fresh.py` 为 82/82 fresh、零 stale/missing、零禁用项。下一步构造单侧闭星薄片的实际锥底并证明其 PL 二维盘性，消费 17.10，再按 17.11 做 M3。S.4 M2/M3、夜间 F-M1 整体及 I1 仍为 partial。下一审计文件 `AuditF244.lean`。

### 19.95 S.4 M2：单侧裁剪锥的实际有限底复形

`RadialIndependence.lean` 证明：仿射独立单形的凸包不含 p，且每条以 p 为起点的正射线至多交它一点，则插入 p 后仍仿射独立。若存在将 p 表为该面顶点仿射组合的系数，就从重心沿此仿射组合取足够小的位移，得到同一射线上的两个不同凸包点，矛盾。`isConeBase_of_isRadiallyInjective` 因而从不含锥顶及径向单射实际生产任意给定复形的 `IsConeBase`；两项结果均不要求有限维或复形有限。

`ConeSlab.lean` 的 `IsConeBase.exists_coneComplex_inter_slab` 对任意有限锥、任意仿射高度 ℓ 和 `ℓ p < b`，实际构造有限底复形 L 及 `IsConeBase p L`。其空间恰为旧底中高度落在 `[ℓ p, b]` 的部分与原锥的上端截面之并；新锥空间恰为原锥的整个闭薄片。径向唯一性、插顶独立性、底面多面体性和空间双向等式均已证明，不预设新的锥表示，也不要求三维、顶点高度一般位置或原底为球。应用于原顶点链环即可得到单侧闭星薄片的真实锥表示；该底的二维盘性尚待接入实际边界球性和锥顶链环分类。

聚焦检查：`RadialIndependence` exit=0（66.2 秒）、`ConeSlab` exit=0（14.0 秒），全部零 warning。`AuditF244.lean` 六项仅依赖 `propext`、`Classical.choice`、`Quot.sound`；无 Lean 进程时 `fresh.py` 为 84/84 fresh、零 stale/missing、零禁用项。按用户要求在当前文件闭环后返回，未继续后续证明。下一步从实际残余球面边界与正规闭区域生产三维流形，用位于边界的锥顶识别锥底为 PL 二维盘并消费 17.10，再做 M3。`ConeManifold` 的未验证草稿保存于本工作树 `.lake/scratch/ConeManifold.pending.lean`，未放入源码或提交，不能当作已证输入。S.4 M2/M3、夜间 F-M1 整体及 I1 仍为 partial。下一审计文件 `AuditF245.lean`。

### 19.96 S.4 M2 done：中间薄片的实际盘锥与单嵌入

已合并整合分支 `a8f07c475` 并读取本目录 `AGENTS.md`；本结果的源码、交接及计划记录一起暂存提交。`BallRegularClosed.lean` 将满维 PL 球的正规闭性搬到任意同维有限维实范数空间。`ConeManifold.lean` 由锥顶位于实际拓扑边界及组合流形的链环分类识别锥底为 PL 球；三维特例先从正规闭区域及实际球面边界生产三维带边界流形，再识别锥底为 PL 二维盘，不消费 Schoenflies。

`ClosedStarCone.lean` 证明带边界组合流形的顶点闭星为同维 PL 球，并将 §19.95 的真实裁剪锥接到 §19.94 的端面正规闭性。`exists_isPLBall_coneComplex_eq_closedStar_slab` 实际构造单侧闭星薄片的有限盘锥：底面盘性来自锥顶边界的链环，锥顶在边界由端面边界公式证明。该辅助结果所用残余边界球性，在最终消费者中由完整有限环境删除的实际像生产。

`SlabEmbedding.lean` 的 `isSimplyEmbedded_frontier_slab_of_heightIndex_eq_zero_of_vertex_lower` 与 `isSimplyEmbedded_frontier_slab_of_heightIndex_eq_zero_of_vertex_upper` 从原零指标填充、一般位置高度和区间内唯一端点顶点，实际证明薄片边界单嵌入。先按 §19.93–19.94 的有限删除送到闭星薄片，再消费原 `SchoenfliesInput` 的 17.10，将其送到单形边界；完整复合仍固定任意给定凸开邻域外。上端版本通过高度反射，逐一对应全部奇异点及层圆周数。未增加锥底盘性、删除后边界球性、区域流形性或额外推移接口等最终假设。

状态：M2（Lemma 2–6）done；M3、I1 与夜间 F-M1 整体仍为 partial。四模块聚焦检查依次为 `ConeManifold` exit=0（11.9 秒）、`BallRegularClosed` exit=0（11.6 秒）、`ClosedStarCone` exit=0（12.1 秒）、`SlabEmbedding` exit=0（14.2 秒），全部零 warning。`AuditF245.lean` 七项仅依赖 `propext`、`Classical.choice`、`Quot.sound`；无 Lean 进程时 `fresh.py` 为 88/88 fresh、零 stale/missing、零禁用项。下一步 M3：证明相邻薄片与下截区域的精确平面公共盘和删盘恢复式，按有限顶点高度归纳消费 17.11，接回零指标归约及 I1 两端点。下一审计文件 `AuditF246.lean`。

### 19.97 S.4 M3 done：有限水平盘拼装与 I1 两端点

`Topology/SlabBoundary.lean` 给出闭区域与上下半空间相交的边界公式，以及相邻薄片/下截区域的平面公共盘和删盘恢复式；纯拓扑结果适用于任意实范数空间。`Topology/HeightRange.lean` 证明非平凡实范数空间中紧致区域的严格高度见证可在其边界找到，无需高度非零或有限维。`SublevelGluing.lean` 据此精确消费原 17.11，沿实际参数化水平盘拼接相邻边界。

`SublevelEmbedding.lean` 的 `isSimplyEmbedded_frontier_sublevel_of_heightIndex_eq_zero` 按不高于截面高度的原顶点数作强归纳。最底部由真实盘锥及 17.10 生产；归纳步在最高已越过顶点之前选择新高度，使用 M2 的上端、下端顶点薄片，再沿各层实际水平盘连续消费 17.11。归纳计数的严格下降由有限顶点集合的真包含给出；没有把有限薄片序列、公共盘或各步单嵌入作为最终假设。

`Schoenflies.lean` 在最大顶点之前选取最后一层，与顶端盘锥拼合，得到 `isSimplyEmbedded_frontier_of_heightIndex_eq_zero`。`HeightFilling` 实际生产所需带边界三维流形填充及顶点一般高度，得到 `isSimplyEmbedded_of_heightIndex_eq_zero`，再接回已证的降指标归约。I1 已交付：`isSimplyEmbedded_of_isPLSphere_two (I : SchoenfliesInput) (hS : IsPLSphere 2 S) : IsSimplyEmbedded S` 与 `exists_isPLBall_of_isPLSphere_two (I : SchoenfliesInput) (hS : IsPLSphere 2 S) : ∃ B, IsPLBall 3 B ∧ frontier B = S ∧ Bornology.IsBounded B`，其中 `S : Set (EuclideanSpace ℝ (Fin 3))`。接口仍是原四字段，未增加结论型假设；S 车道可用已整合的 `schoenflies_input` 实例化，解除其消费者参数。

状态：S.4 的 M1、M2、M3 及夜间 F-M1 done；I1 已交付，无剩余数学义务。最终五模块检查为 `SlabBoundary` exit=0（12.5 秒）、`HeightRange` exit=0（10.0 秒）、`SublevelGluing` exit=0（12.1 秒）、`SublevelEmbedding` exit=0（13.0 秒）、`Schoenflies` exit=0（11.0 秒），全部零 warning。`AuditF246.lean` 对十七项新声明及原 `schoenflies_input` 共十八项审计，全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`。无 Lean 进程时 `fresh.py` 为 92/92 fresh、零 stale/missing、零禁用项；`git diff --check` 通过。源码、交接与两个计划记录同次提交。恢复后下一步按 NIGHT_PLAN §6.2 做 F-M5 的实际双点分类，并生产 F-M6 的余面严格异侧性；这两项及最终 `exists_small_isNormalSingularCell` 仍为 partial。下一审计文件 `AuditF247.lean`。

按用户要求，本结果整理、同次提交并推送后暂停。未开始新的 F-M5/F-M6 证明；本车道无运行中的 Lean 进程。

### 19.98 2026-09-17 F5.2：目标区域保持与实际紧致片扰动半径

按新任务恢复，已合并整合基线 `b069cd003`（合并提交 `3f69fe924`）。本轮 F-M1 指 F5.2，旧夜间 F-M1 = S.4 已在 §19.97 done。重新核对了 `GeneralPosition.lean`：相对子复形横截生产者原来没有像包含结论；`exists_small_simplicialMap_preimage_manifold_relative` 的 G 是固定目标复形的逆像，不是双点集，不可直接填 `doublePointSet_triangulated`。

`GeneralPositionWithin.lean` 的 `exists_small_simplicialMap_transverse_on_subcomplex_mapsTo` 在原相对横截端点上增加开目标 U 的真实 MapsTo 结论，同时保留精确固定子复形、逐面单射、横截、任意小距离和有限细分。证明从原紧致像到 U 的闭加厚余量选择更小扰动半径；取 U = 给定复形载体的环境内部即得到对应保像版本。`exists_small_simplicialMap_doublePointSet_manifold_mapsTo` 则消费真正的自横截生产者，保留全源局部单射、纤维至多二重、精确双点集的一维带边组合流形和所有 crossing，同时保证全像仍在 U 内。

对抽象流形中的目标片，不能把上段的环境内部用于高维欧氏嵌入。`SingularTwoCell.exists_compact_piece_with_perturbation_radius` 已在 M 自身的度量中实际构造紧致带边界三维片 P、PLPiece T 和 δ > 0；原盘全像落在 interior P，任何 M 值映射 g 只要在原域逐点满足 dist(g x, D x) < δ，全像仍落在 interior P。这里的内部和距离均属于 M，不属于 T 的高维线性环境。

`Topology/Pasting.lean` 的 `mapsTo_of_preimage_singleton_eq_off` 从修改区外完整纤维相等推出区域保持。`exists_isOpen_forall_exists_small_isPLOn_crossing_in_chart_mapsTo` 将它实际接到已有流形图卡正规化：若原像在 P 内且当前双点在 interior P，先把修改邻域收进 interior P；所得任意小局部正规化保留 MapsTo g K.space P、局部单射、二重纤维和真实局部双点 crossing，且选定开覆盖邻域仍独立于误差量。后续采用三维图卡中的内在修改；未宣称在高维载体之外自由挪顶点的旧端点可保持载体，也未宣称该局部结果已经保持所有旧区域的 crossing。给定原有物理边界的点仍需半空间局部构造，不能套用内部双点版本。

本闭合层为目标区域保持，F5.2 / 新 F-M1 整体仍 partial。`Topology.Pasting` 检查 exit=0（7.3 秒），`GeneralPositionWithin` exit=0（12.7 秒），零 warning。`AuditF247.lean` 五项均仅标准三公理；`git diff --check` 通过。下一步接相对分层通用位置和余面异侧性以保持有限图卡归纳中的既有 crossing，随后拼装精确双点三角剖分与 `IsNormalSingularCell`；边界情形须保留半空间约束。F-M2 的非紧多面体概念尚未开始。下一审计文件 `AuditF248.lean`。

### 19.99 F5.2：半空间相对邻域内的完整保像正规形式

`GeneralPositionWithin.lean` 新增 `exists_small_simplicialMap_doublePointSet_with_boundary_in_halfSpace_mapsTo`。输入是原有限二维带边组合流形、局部单射且至多二重的 PL 映射、原像位于非负半空间、原边界落在零平面，以及目标 U 在每个原像点处是半空间内的相对邻域。U 无需为环境开集，因而覆盖真实边界附近的半空间目标约束。

证明将相对邻域转为 `interior (U ∪ halfSpaceᶜ)`，用紧致像生产统一正余量，再调用原半空间自横截生产者。其非负性排除补半空间分支，从而实际证明整个新像落在 U 中。输出仍含原完整有限细分、局部单射、纤维至多二重、星上 PL 同胚、精确双点集 G、一维带边流形、零层恰对应原边界、两种 crossing、度数 1/2 和 `(boundaryComplex 1 G).space = G.space ∩ {ℓ = 0}`。未加入扰动后保像、crossing 或图流形性等结论型假设。

检查 `GeneralPositionWithin` exit=0（11.0 秒）、零 warning；`AuditF248.lean` 一项仅标准三公理。半空间标准模型的保像层 done；完整 F5.2 / 新 F-M1 仍 partial，尚需在实际带边图卡内使用该模型并完成保持旧区域 crossing 的有限拼接。下一步从单形内部不交证明相邻满维余面的严格异侧性，再做安排分层下的实际双点分类。下一审计文件 `AuditF249.lean`。

### 19.100 F5.2：指定超平面上的余面严格异侧性

`CofaceSeparation.lean` 复用整合分支 `AffineOrientation.lean` 中 `exists_linearMap_separating_cofaces` 的实际分离生产者，证明 `linearMap_mul_neg_of_distinct_cofaces` 与 `affineMap_mul_neg_of_distinct_cofaces`：公共面的方向恰为指定线性泛函的核时，两个不同余面的对顶点在指定平面两侧取严格相反的符号。证明从分离泛函消去公共面方向，得到两个指定高度的商严格为负；不把异侧性作为假设。

`affineMap_mul_neg_of_distinct_cofaces_of_card_eq_finrank` 从公共面顶点数等于环境维数、仿射函数非零线性部分及面上为零，实际推出所需核等式。`IsCombinatorialManifoldWithBoundary.exists_cofaces_pos_neg` 再为满维带边组合流形的内部余维一面选出正、负两侧的全部两个对顶点。基础版本不需要有限维或有限面族，只有维数和流形推论增加对应条件。

检查 `CofaceSeparation` exit=0（10.0 秒）、零 warning；`AuditF249.lean` 五项（四个新端点及分离输入）仅标准三公理。本层 done；F5.2 / 新 F-M1 仍 partial。尚需将该满维余面结论经公共仿射细分和图卡搬到奇异曲面的折叠支上，生产实际双点的横截/双折分类，再完成保持旧区域 crossing 的有限图卡拼接；不能将满维条件直接套在三维中的二维曲面上。下一审计文件 `AuditF250.lean`。

### 19.101 F5.2：公共仿射细分的余面异侧性实际搬入图卡

`CofaceTransport.lean` 的 `affineMap_mul_neg_of_distinct_cofaces_of_affineOn_faces` 从每面仿射且在载体上单射的映射实际构造像复形，证明仿射无关、公共面顶点数与余面对顶点均被保留，再应用 §19.100 的指定超平面分离。源复形不要求有限面族或有限维环境；只有目标坐标需要有限维。

`PLPieceIn.affineMap_mul_neg_of_distinct_cofaces_in_chart` 用片映射的单射性与图卡的单射性提供实际输入，恰可用于 §19.61 公共细分在一个星图卡中的限制。已闭合先前明确列出的“同一星图卡内相邻满维余面对指定公共面平面的严格异侧性”，未假设曲面折叠支已经异侧。

检查 `CofaceTransport` exit=0（10.3 秒）、零 warning；`AuditF250.lean` 两个新端点仅标准三公理。本层 done；完整 F5.2 仍 partial。接下来的义务是分层生产者的实例化与实际曲面支分类：公共目标余面的异侧性本身不保证一张奇异曲面的两个支分属这些余面。当前完整仿射无关约束在两个共配置平面折边的场景还需单独核对维数相容性。下一审计文件 `AuditF251.lean`。

### 19.102 F5.2：完整安排约束在共面双折情形的确切维数障碍

`ArrangementConstraints.lean` 证明 `IsVertexMapGeneralInArrangement.card_le_finrank_of_zero`：在 B 上固定、在 V 上保持原安排开胞腔的通用位移中，若某个仿射无关约束的全部原顶点落在非零配置泛函的零超平面内，则该约束至多含环境维数个顶点。证明先由符号保持得到新点仍在零平面内，再用方向空间包含于核与仿射无关的维数界。

`card_le_finrank_of_complete_zero` 将此计数接到现有生产者的原样 `hcomplete`。端点 `not_isVertexMapGeneralInArrangement_of_complete_hyperplane` 精确证明：若一对面 s q、t q 的安排包络方向为全空间，而其并中含有环境维数加一的顶点 u 全部落在某个非零配置零超平面，覆盖与完整约束假设成立，则任何在 B 上固定的 φ 都不可能满足当前通用位置谓词。

三维中的具体义务：两个折边各有两个不同源顶点，四个顶点都留在同一配置平面；取含这两条折边且有离平面顶点的两张三角形，其安排包络可为三维。现有 `hcomplete` 要求这四个共面顶点组成一个仿射无关约束，因为 `4 ≤ 3 + 1`。保层后四点仍共面，而新端点推出 `4 ≤ 3`。这不仅是旧的重合固定折边反例：两条不同方向的折边也触发该阻碍，且顶点可全是可动的。

检查 `ArrangementConstraints` exit=0（9.6 秒）、零 warning；`AuditF251.lean` 三项仅标准三公理。此前已证欧氏/半空间保像、实际双点图、两折线 crossing、满维余面严格异侧和图卡搬运均保留有效；完整 F5.2 / 新 F-M1 为 partial，当前的“全约束安排生产者直接实例化”路线 blocked，不声明最终正规形式。

可选路线：用尊重每个受迫子层秩的分层通用位置条件替换当前 `hcomplete`，重新证明存在及双点分类；或先在图卡中使曲面对目标骨架横截，再对骨架截出的折边采用相容的相对移动与双点分类。两条路线都还需要实际证明曲面各支跨越目标公共面；不能仅删除约束、增加 `IsArrangementGeneralFoldPair` 假设或把 C0 小扰动当 crossing 保持。按常驻规则 §5 转做已授权的新 F-M2 非紧多面体接口；不改变既有公共定义的语义。下一审计文件 `AuditF252.lean`。

### 19.103 新 F-M2：非紧局部多面体定义、紧致等价与集合运算

`LocallyPolyhedral.lean` 定义 `IsLocallyPolyhedral S`：S 的每个点都有一个包含于 S 的紧致有限多面体 P，且 P 是该点相对于 S 的邻域。它允许非紧、非闭及非流形的集合，不改变旧 `IsPolyhedron` 的有限紧致含义。§32 的要求现在可写成 `IsLocallyPolyhedral (U \ P)`，不再因 U 是开胞腔而强迫该部分紧致。

`isPolyhedron_iff_isLocallyPolyhedral_and_isCompact` 证明与旧紧致情形完全相容。`exists_isPolyhedron_neighborhood_of_isCompact` 实际用有限子覆盖把 S 内任意紧集放入 S 内的有限多面体相对邻域。`isLocallyPolyhedral_iff_isPiecewiseAffineOn_id` 与现有逐片仿射 API 对接；一般 `IsPiecewiseAffineOn` 的源域也满足此局部多面体性。

集合运算包含无附加条件的相交、开集及相对开子集、删去闭集，以及各片在并中相对闭时的有限并（附环境闭集推论）。闭子集接口 `iff_forall_isPolyhedron_inter_of_isClosed`：S 内相对闭的 T 为局部多面体，当且仅当它与 S 内每个有限多面体的交都是有限多面体。没有声称任意闭子集仍为多面体（Cantor 集反例），也没有声称任意两局部多面体之并仍局部多面体（离散集合 `{1/n : n ≥ 1}` 加上 `{0}` 的积聚反例）。这些条件是数学必需的。

`of_locallyFinite_cover` 与 `isLocallyPolyhedral_space_of_locallyFinite` 接收集合自身拓扑中的局部有限有限多面体覆盖／单形覆盖，推出新谓词；局部有限性不强加在整个环境空间，因而允许开胞腔。新定义不捆绑一个全局无限复形，本次未声明从局部条件反向构造一个全局相容无限三角剖分。

新 F-M2 的定义及所需基本接口 done：`LocallyPolyhedral` 最终检查 exit=0（8.7 秒）、零 warning；`AuditF252.lean` 全部 22 个公开定义与端点仅标准三公理。F5.2 仍按 §19.102 保持 partial，当前完整安排约束路线 blocked。下一审计文件 `AuditF253.lean`。

### 19.104 新 F-M2：局部多面体性经 PL 同胚的实际搬运

`LocallyPolyhedralImage.lean` 的 `IsLocallyPolyhedral.image_of_isPLHomeomorphOn`：若 `S` 局部多面体、
`S ⊆ U` 且 `f` 在 `U` 上是到 `V` 的 PL 同胚，则 `f '' S` 局部多面体。证明在每点取 `S` 内的紧致多面体相对邻域 `P`，
用 `IsPolyhedron.image_of_isPiecewiseAffineOn`（f 在 P 上逐片仿射且单射）得到 `f '' P` 是有限多面体，
再用逆映射在 `V` 上的逐片仿射性（故连续）经 `continuousOn_iff'` 把 `P` 的相对邻域性搬成 `f '' P` 在 `f '' S` 中的
相对邻域性。没有假设 `f '' S` 或 `V` 是开集，也没有假设 `S` 紧致。
`IsLocallyPolyhedral.image_invFunOn_of_isPLHomeomorphOn` 用既有的 `IsPLHomeomorphOn.symm` 给出反方向。
§32 需要的是把 `IsLocallyPolyhedral (U \ P)` 在 PL 图卡之间搬运，这一条正是那一步。

检查 `LocallyPolyhedralImage` exit=0（7.9 秒）、零 warning；`AuditF253.lean` 两项仅
`propext`、`Classical.choice`、`Quot.sound`。注意：`IsPLHomeomorphOn.symm` 早已存在于 `PLHomeomorph.lean`
（在 `namespace IsPLHomeomorphOn` 内写作 `theorem symm`），按名字 grep 找不到；本轮一度重证，被编译器的
"已声明" 报错挡下。下一审计文件 `AuditF254.lean`。

### 19.105 E3 交来的分离生产者：沿圆分支时需要双侧性（数学分析，未形式化）

E3 §44 把 `exists_supported_separation_along_compact_crossing_arc` 交给 F。逐点局部模型缺的两项里，
第一项（哪张平面对应固定源片 `A`）其实不是选择：两张片只沿 `S` 相交，故"含 `D(A)` 的那张平面"在每个图卡里
唯一确定，可以直接把它作为定义，不需要沿分支作相容选择。

第二项（横向商线的正向）是真的障碍，而且它不是技术性的：把 `A` 推离 `Q` 需要 `Q` 沿 `S` 的法线丛有不消失的截面，
即 `Q` 沿 `S` 双侧。若 `S` 是圆且该法线丛不可定向（Möbius 情形），任何支撑在 `S` 邻域内的环境同胚都不能使
`h(A) ∩ Q = ∅`：`A` 与 `Q` 沿 `S` 的模二相交数是该芽的同痕不变量。因此按 E3 现在的措辞，该生产者对一般紧致 PL
1-球面 `S` 为假，必须加上"`Q` 沿 `S` 双侧"或等价的相容框架假设。

对 §25.1 实际需要的情形这不是限制：Case 3/4 里的 `A_j` 是**触边分支**，即端点落在 `Bd |D|` 上的弧。
区间上的 ±1 丛平凡，故相容正向自动存在；端点处的半空间模型只额外要求推移方向与 `Bd M` 相切。
建议把生产者重述为两条：(i) 弧情形无条件（先沿弧的有限图卡链按次序传播正向，再插值）；
(ii) 圆情形以双侧性为显式假设。E3 §44 列出的输出条款其余部分不变。本条只是分析，没有 Lean 端点。

### 19.106 分离生产者的链骨架：紧致 PL 弧的从属链覆盖

`ArcChainCover.lean` 的 `exists_subordinate_chain_of_isPLBall_one`：设 `S` 是紧致 PL 1-球（弧），
`U : ι → Set E` 是开集族且覆盖 `S`，则存在 `n` 与 PL 同胚 `γ : Icc 0 1 → S`，使得均匀分划的每一小段
`γ '' Icc (j/(n+1)) ((j+1)/(n+1))`（`j ≤ n`）整体落在某个 `U i` 内，且这些小段的并恰好是 `S`。
证明用 `exists_isPLHomeomorphOn_Icc_of_isPLBall_one` 取参数化，用 `continuousOn_iff'` 把图卡拉回成
`[0,1]` 的环境开覆盖，再用 `lebesgue_number_lemma_of_metric` 与 `exists_nat_one_div_lt` 选网距小于 Lebesgue 数的
均匀分划；`mem_Icc_uniform_partition` 用 `Nat.floor` 给出覆盖性（`x = 1` 落在最后一段）。

这条与 E3 §45 的 `exists_sideChoice_of_chain` 合起来就是 §44 缺口的骨架：小段按 `j` 天然沿弧排序，
相邻小段只交于一个端点，侧选择 `ε` 在该端点两侧一致，因此横向方向场在整条弧上连续；
余下的义务是在单张 crossing 图卡内写出线性推移，并用该方向场把它们拼成全局单射 PL 自映射
（幅度取 `S` 邻域上的一个正函数即可，不需要小段重叠）。

检查 `ArcChainCover` exit=0（10.5 秒）、零 warning；`AuditF254.lean` 两项仅
`propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF255.lean`。

### 19.107 更正 §19.105：横向推移证明失败，弧情形靠沿分支滑出而不是双侧性

§19.105 把缺口归结为"`Q` 沿 `S` 的双侧性"。这个框架是错的，现更正如下。

局部模型里两张条带是 `A = {z = 0, |y| ≤ 1}` 与 `Q = {y = 0, |z| ≤ 1}`，沿 x 轴横截相交。
把 `A` 沿 `Q` 的法向平移 `ε`（`0 < ε ≤ 1`）后，`h(A)` 仍含点 `(x, 0, ε)`，而该点满足 `|z| ≤ 1`，
故仍在 `Q` 内：**任何横向推移都不能把两张相交的条带分开**，与 `Q` 是否双侧无关。
沿 `A` 自身的带方向平移同理无效。所以 §19.105 里"弧情形无条件、圆情形加双侧性假设"的建议作废。

实际可行的机制是**沿分支方向滑出**：若 `S` 是端点到达自由边界（`Bd |D|` 或 `Q` 条带的端边）的弧，
把 `A` 沿 `S` 的方向推过 `Q` 条带的端点，即可使 `h(A) ∩ Q = ∅`；支撑是 `S` 的邻域并上滑动路径的邻域，
仍落在给定的 `W` 内（只要 `W` 含该端点的邻域）。这对圆分支不可用：圆没有端点可滑出。

这与 Moise 的分情形恰好吻合：§25.1 的 Case 1/2 是盘内部的 PL 圆，书中不做分离，而是**换掉内盘**
（环带邻域加柱形图，Case 2 的内盘替换用 S 车道的 I2）；Case 3/4 才是触边分支，用切开重贴加沿分支滑出。
因此 E3 §44 交来的 `exists_supported_separation_along_compact_crossing_arc` 应当只对**触边弧**提，
并且输出条款里要允许支撑包含滑动路径；圆分支不应走这条生产者。

尚未在此证明"圆分支的交点不能由支撑在其邻域内的环境同胚消去"这一否定命题；上面只证了横向平移这一族构造失败。
E3 §45 的 `ZMod 2` 循环障碍仍然成立并且有用（它是沿分支相容定向的障碍），但它不是这里的分离障碍，
两者的联系应按本条更正理解。

### 19.108 沿分支滑出的标准模型：显式 PL 自同构与实际分离

`ModelSlide.lean` 按 §19.107 的更正给出标准模型里的滑动，全部是显式公式：

- `slideAmount p = max 0 (min (1 - |y| - |z|) ((3 - |x|)/2))`，`slideMap p = (x - slideAmount p, y, z)`；
  沿 x 方向按到 x 轴的距离滑动，横向宽度 1，纵向锥度 3。
- `isPiecewiseAffineOn_slideMap`：`slideMap` 在整个 `ℝ × ℝ × ℝ` 上逐片仿射。证明只用既有的
  `IsPiecewiseAffineOn` 代数（`abs`、`max`、`min`、`add`、`prod_mk`、`affine_comp`）与
  `IsLocallyPolyhedral.of_isOpen isOpen_univ` 给出的 `id` 的逐片仿射性；锥度里的 `/2` 用
  `halfMap`（`(2:ℝ)⁻¹ • LinearMap.id` 的仿射化）搬进来。
- `bijective_slideMap`：单射由"锥度斜率 1/2 ⟹ `x ↦ x - slideAmount` 严格增"给出
  （`slideAmount_le_add`：固定 `(y,z)` 时 `slideAmount` 对 `x` 是 (1/2)-Lipschitz）；满射由
  `|x| ≥ 3` 处是恒等加中值定理给出。
- `slideMap_eq_self_of_width`（`1 ≤ |y| + |z|`）与 `slideMap_eq_self_of_taper`（`3 ≤ |x|`）：
  支撑落在盒 `{|y| + |z| ≤ 1, |x| ≤ 3}` 内，故可以在图卡里用恒等延拓。
- `modelBandA = {z = 0, |y| ≤ 1, x ∈ [0,1]}`，`modelBandQ = {y = 0, |z| ≤ 1, x ∈ [1/2,2]}`：
  `inter_modelBandA_modelBandQ` 说明滑动前两条带沿 `x ∈ [1/2,1]` 的弧横截相交（非平凡），
  `disjoint_slideMap_image_modelBandA` 说明滑动后 `slideMap '' modelBandA` 与 `modelBandQ` 不相交
  （在 `y = z = 0` 处滑动量恰为 1，把 A 的 x 区间移到 `[-1,0]`）。

这就是 §19.107 里"沿分支滑出"的局部实现，并且证明了横向推移做不到的事它能做到。
检查 `ModelSlide` exit=0（9.7 秒）、零 warning；`AuditF255.lean` 六项无 `sorryAx`。
剩下的义务：把这个模型经 crossing 图卡搬到流形里（图卡是 PL 同胚，`slideMap` 的支撑在盒内，
可用 `Topology/Pasting.lean` 的支撑外恒等接口拼接），并按 `ArcChainCover` 的链与 E3 §45 的侧选择
沿整条触边弧串起来；端点处要把模型换成半空间版本使滑动与 `Bd M` 相切。下一审计文件 `AuditF256.lean`。

### 19.109 滑动经图卡共轭成环境自映射

`ChartSlide.lean` 把 §19.108 的模型滑动搬进图卡：

- `slideSupport = {|y| + |z| ≤ 1, |x| ≤ 3}`，`isCompact_slideSupport`（闭且含于 `closedBall 0 3`）、
  `eqOn_slideMap_id_compl`（支撑外恒等）、`mapsTo_slideMap_slideSupport` 与
  `mapsTo_slideMap_of_subset`（任何含支撑的集合被 `slideMap` 映回自身）。
- `isPiecewiseAffineOn_chartSlide`：对任意 PL 图卡 `e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)`
  （两向逐片仿射）与 `slideSupport ⊆ e.target`，共轭映射 `e.conjugateMap slideMap` 在整个 `M` 上逐片仿射。
  直接消费既有的 `isPiecewiseAffineOn_conjugateMap`，`slideMap` 在开集 `e.target` 上的逐片仿射性由
  `IsPiecewiseAffineOn.mono` 从 univ 版本取得。
- `injective_chartSlide`：共轭映射整体单射（图卡内用 `slideMap` 的单射性与 `right_inv`/`left_inv`，
  图卡外恒等；混合情形用"像落在 `e.source` 内"排除）。
- `disjoint_chartSlide_image`：若两条模型带都落在 `e.target` 内，则
  `e.conjugateMap slideMap '' (e.symm '' modelBandA)` 与 `e.symm '' modelBandQ` 不相交。

于是"单张 crossing 图卡内的支撑滑动"这一层 done：它给出 E3 §44 输出条款里的 `IsPL`（逐片仿射）、
`Function.Injective`、`EqOn h id Uᶜ` 与一张带的分离。剩下的义务是沿 `ArcChainCover` 的链把逐张图卡的滑动
串成一个整体自映射（用 E3 §45 的侧选择定向，相邻段在公共端点处方向一致），并在触边端点换成半空间模型
使滑动与 `Bd M` 相切；另外需要把这里的欧氏环境 `M` 换成流形图卡下的版本（`Manifold.lean` 的 `IsPLOn` 接口）。

检查 `ChartSlide` exit=0（9.6 秒）、零 warning；`AuditF256.lean` 五项无 `sorryAx`。下一审计文件 `AuditF257.lean`。

### 19.110 任意长度的滑动：锥度必须是滑距的两倍

`ModelSlideLong.lean` 把 §19.108 的模型按滑距 `d` 与锥度半径 `R` 参数化，因为 §19.108 的固定滑距 1
只能清掉长度 1 以内的 crossing 区段，而一条触边分支的长度事先不受控。

- `slideWidthScaled d p = d * (1 - |y| - |z|)`、`slideTaperRad R p = (R - |x|) / 2`、
  `slideAmountLong d R = max 0 (min · ·)`、`slideMapLong d R p = (x - slideAmountLong d R p, y, z)`。
- 单射性的机制不变且与 `d` 无关：宽度因子不含 `x`，锥度对 `x` 是 (1/2)-Lipschitz，故
  `slideAmountLong_le_add` 给出 `a(q) ≤ a(p) + (q.1 - p.1)/2`，代入 `x - a(x)` 相等即得 `p.1 = q.1`。
  锥度斜率 1/2 < 1 是这里唯一用到的定量事实，所以滑距可以任意大，**代价全在锥度半径**。
- 分离的定量条件写成 `disjoint_slideMapLong_image_slideBandA`：对
  `slideBandA c = {z = 0, |y| ≤ 1, x ∈ [0, c]}` 与 `slideBandQ a b = {y = 0, |z| ≤ 1, x ∈ [a, b]}`，
  只要 `0 ≤ d`、`c + 2 * d ≤ R`、`c - d < a`，就有
  `Disjoint (slideMapLong d R '' slideBandA c) (slideBandQ a b)`。
  第二个条件就是本条的几何内容：**要滑动 `d`，锥度半径必须至少是 `c + 2d`**；否则锥度在带 `A` 的远端
  把滑距压到不足 `d`。证明只需注意 `slideBandQ` 要求 `y = 0`，而 `slideMapLong` 不动 `y`，
  所以只有 `y = 0` 的点参与，那里宽度恰好取满 `d`。
- `surjective_slideMapLong`（`0 ≤ R` 时用 `[-R, R]` 上的介值定理）、`bijective_slideMapLong`、
  `isPiecewiseAffineOn_slideMapLong`（新增 `scaleMap` 把常数倍写成仿射映射）、
  `isCompact_slideSupportLong`、`eqOn_slideMapLong_id_compl`、`mapsTo_slideMapLong_of_subset`。
- 端点的半空间版本不必另造模型：`slideMapLong` 只改第一坐标，故
  `slideMapLong_snd`、`mapsTo_slideMapLong_prod` 与 `bijOn_slideMapLong_prod` 给出
  对任意 `T ⊆ ℝ × ℝ`，`{p | p.2 ∈ T}` 被双射地保持。取 `T = {q | q.2 = 0}` 或 `{q | 0 ≤ q.2}`
  即得滑动与模型边界相切、并保持半空间——§19.109 里列为待办的"端点换半空间模型"由此消解。

检查 `ModelSlideLong` exit=0（10.0 秒）、零 warning。

### 19.111 长滑动的图卡版本

`ChartSlideLong.lean` 把 §19.110 的模型经 PL 图卡共轭，结论与 §19.109 同形但带定量条件：
`isPiecewiseAffineOn_chartSlideLong`（`e.conjugateMap (slideMapLong d R)` 在整个 `M` 上逐片仿射）、
`injective_chartSlideLong`（整体单射）、`disjoint_chartSlideLong_image`（在 `0 ≤ d`、`c + 2d ≤ R`、
`c - d < a` 下分离两条带的像）。证明与 §19.109 逐行对应，只是把模型引理换成带参数的版本。

于是 E3 §44 输出条款中"单张图卡内、滑距任意"的一层 done。仍未闭合的是把有限多张图卡沿分支排成链并合成
一个整体自映射：注意 §19.110 说明滑距可以任意大，所以**如果分支有单张乘积邻域（沿弧的相容平凡化），
就不需要串接，一次滑动即可**；因此下一步的正确目标是沿弧的乘积邻域，而不是逐张图卡的插值。

检查 `ChartSlideLong` exit=0（8.9 秒）、零 warning；`AuditF257.lean` 九项无 `sorryAx`。下一审计文件 `AuditF258.lean`。

### 19.112 沿整条分支的滑动图卡：谓词层

`BranchSlideSeparation.lean` 按 §19.111 的结论把"单张乘积图卡即可"写成谓词。E3 §44 要的生产者从此分成
两段：谓词的**生产**（几何，尚未闭合，见 §19.115）与谓词的**消费**（分离数据，已闭合，见 §19.113/19.114）。

- `IsBranchSlideChart R c a b P Q e`：`e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)` 两向逐片仿射，
  `slideSupportLong R`、`slideBandA c`、`slideBandQ a b` 三者都落在 `e.target` 内，且两张片正好是
  `P = e.symm '' slideBandA c`、`Q = e.symm '' slideBandQ a b`。
  常数分工：`c` 是分支（A 片与 Q 片的交线）在图卡里的长度上界，`[a,b]` 是 Q 片沿分支方向的区间，
  `R` 是锥度半径。§19.110 的定量条件 `c + 2 * d ≤ R` 因此是对 `R` 的要求而非对滑距 `d` 的要求——
  谓词本身不含 `d`，滑距在消费定理里取。
- `HasBranchSlideChart R c a b P Q` 是它的存在版本，也就是 §19.115 里生产者的确切目标。
- 附带 `symm_image_subset_source`、`isCompact_symm_image_slideSupportLong` 与四条访问器
  （`sheet_subset_source`、`crossing_subset_source`、`support_subset_source`、`isCompact_support`）。
  支撑 `e.symm '' slideSupportLong R` 紧致这一条给出 E3 §44 输出条款里"支撑外恒等"所需的闭集。

检查 `BranchSlideSeparation` exit=0（9.0 秒）、零 warning；`AuditF258.lean` 八项仅
`propext`、`Classical.choice`、`Quot.sound`。

### 19.113 谓词直接给出 E3 §44 的分离数据

`exists_supported_separation_of_isBranchSlideChart`：设 `IsBranchSlideChart R c a b P Q e`，
`0 ≤ d`、`c + 2 * d ≤ R`、`c - d < a`，则存在 `h : M → M` 同时满足

- `IsPiecewiseAffineOn h univ`（§19.111 的 `isPiecewiseAffineOn_chartSlideLong`）；
- `Function.Injective h`（`injective_chartSlideLong`）；
- `EqOn h id (e.symm '' slideSupportLong R)ᶜ`；
- `Disjoint (h '' P) Q`（`disjoint_chartSlideLong_image`）。

见证就是 `e.conjugateMap (slideMapLong d R)`，没有选择也没有黏合。第三条是新的一块：
`eqOn_chartSlideLong_id_compl` 由 `OpenPartialHomeomorph.conjugateMap_eqOn_compl` 与
`eqOn_slideMapLong_id_compl` 直接合成，支撑集取图卡里紧致 `slideSupportLong R` 的原像。
三个数值条件之间没有冲突：给定 `c` 与 `a`（`c < a` 时取 `d` 小、`a ≤ c` 时取 `d > c - a`），
再把 `R` 取到至少 `c + 2 * d` 即可，这正是 §19.110 说的"代价全在锥度半径"。

检查 `BranchSlideSeparation` exit=0（9.6 秒）、零 warning；`AuditF258.lean` 十项无 `sorryAx`。

### 19.114 滑动保持流形边界：E3 §44 的端点条款

`slideMapLong` 只改第一坐标（`slideMapLong_snd`），所以 `bijOn_slideMapLong_prod` 说任何
`{p | p.2 ∈ T}` 被双射保持。把它经图卡共轭就得到本条：

- `mapsTo_chartSlideLong_of_forall_mem_iff`：设 `slideSupportLong R ⊆ e.target`、`0 ≤ d`，
  并设 `B : Set M` 在图卡内由横向条件刻画，即 `∀ x ∈ e.source, x ∈ B ↔ (e x).2 ∈ T`，
  则 `MapsTo (e.conjugateMap (slideMapLong d R)) B B`。图卡外共轭是恒等，图卡内用
  `mapsTo_slideMapLong_prod`（即 `bijOn_slideMapLong_prod` 的 `MapsTo` 分量，
  不需要 `0 ≤ R`，故按最少假设取这一半）。双向 `↔` 是必需的：正向把 `x ∈ B` 搬进模型，
  反向把滑动后的点搬回 `B`。
- `mapsTo_chartSlideLong_boundary`（`T = {q | q.2 = 0}`，即模型边界平面）与
  `mapsTo_chartSlideLong_halfSpace`（`T = {q | 0 ≤ q.2}`，即模型半空间）是两个特例。
  于是 §19.109 遗留的"端点处要把模型换成半空间版本使滑动与 `Bd M` 相切"彻底消解：
  不需要第二个模型，滑动方向本来就与所有横向水平集相切。
- `exists_supported_separation_of_isBranchSlideChart_boundary` 是把 §19.113 的四条与边界条款
  `h '' (e.symm '' slideSupportLong R ∩ B) ⊆ B` 合并后的完整包，对应 E3 §44 的
  `h (U ∩ BdM) ⊆ BdM`。这里的 `B` 是显式参数而不是 `Bd M` 的内置概念：生产者交付图卡时
  必须同时交付"该图卡把流形边界拉直成 `{p.2.2 = 0}`"这一条，形式就是上面的 `hB`。

检查 `BranchSlideSeparation` exit=0（9.3 秒）、零 warning；`AuditF258.lean` 十四项无 `sorryAx`。

### 19.115 生产者的代数核心已闭合，几何核心的确切缺口

`HasBranchSlideChart`（§19.112）的生产者分成代数与几何两半。代数一半现在闭合：

- `TransversePlaneCoordinates.lean` 的 `exists_linearEquiv_of_transverse_planes`：设
  `P Q : Submodule ℝ E`，`finrank P = finrank Q = 2`、`finrank (P ⊓ Q) = 1`、`P ⊔ Q = ⊤`
  （这正是 `HasPLCrossingAt`/`HasPLBoundaryCrossingAt` 里携带的数据），则存在线性同构
  `L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ`，使 `y ∈ P ↔ (L y).2.2 = 0` 且 `y ∈ Q ↔ (L y).2.1 = 0`。
  推论 `mem_inf_iff_of_linearEquiv_of_transverse_planes` 给 `y ∈ P ⊓ Q ↔ (L y).2 = 0`，
  即分支线被送到第一坐标轴——`slideMapLong` 正是沿这条轴滑动的方向。
  构造不用基：由 `Submodule.exists_dual_map_eq_bot_of_lt_top` 取 `ker β = P`、`ker γ = Q`
  （核相等由 `P ≤ ker β`、`finrank P = 2` 与 `finrank (ker β) < 3` 夹出），由
  `Module.Projective.exists_dual_ne_zero` 取在 `P ⊓ Q` 的生成元上非零的 `α`，
  取 `α.prod (γ.prod β)`；单射性用 `P ⊓ Q = span {u}`，满射性用
  `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` 与 `finrank E = 3`
  （后者由 `finrank_sup_add_finrank_inf_eq` 得：`3 + 1 = 2 + 2`）。
  辅助 `exists_ker_eq_of_finrank_succ_eq` 对任意余维一子空间都成立，可复用。

几何一半**未闭合**，且不能由本次指定的两个输入得到，理由要记清楚：

- `exists_subordinate_chain_of_isPLBall_one` 只说"每小段整体落在某个开集里"。它不给相邻图卡之间
  的任何关系，因此无法把两张局部平凡化对接。
- `exists_sideChoice_of_chain` 只在 `ZMod 2` 层面给相容的侧选择。它解决的是"横向正向"的组合障碍，
  不产生任何 PL 同胚；即使 `ε` 已定，两张图卡在重叠上仍相差一个未受控的 PL 自同胚。
- `HasPLCrossingAt` 是逐点的，并且只在 `∀ᶠ y in 𝓝 x` 的意义下把两片认同成半平面。把相邻两张平凡化
  拼成一张，需要"两个球对（ball pair）的平凡化沿公共横截盘对相等时相差一个可锥化的 PL 同胚"，
  即 **PL 球对的正则邻域唯一性 / 相对 Alexander 技巧**。本树有 `ConeExtension.lean` 的
  `exists_isPLHomeomorphOn_coneComplex` 与 `ConeAmbientExtension.lean` 的两条延拓，都是单个复形的锥化，
  没有球对版本，也没有沿链归纳所需的相对（在一张面上固定）版本。因此缺口不是"再拼一下"，
  而是缺一条定理。

确切的缺失输入（下一个里程碑的目标）：设 `S` 是紧致 PL 弧，`A B` 是沿 `S` 横截相交的两张 PL 2-片，
`W ∈ 𝓝ˢ S`；求开集 `U` 与 `e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)`，使 `S ⊆ e.source ⊆ W`、
`e` 两向逐片仿射，且 `e '' (A ∩ e.source) ⊆ {p | p.2.2 = 0}`、`e '' (B ∩ e.source) ⊆ {p | p.2.1 = 0}`，
并且 `e.source` 只碰这两张片（不含第三张片的点）。有了它，取 `c` 为 `S` 在图卡里的长度上界、
`[a,b]` 为 `B` 的区间、`R ≥ c + 2 * d`，再按需缩放坐标即得 `HasBranchSlideChart`，
于是 §19.113/19.114 立刻给出 E3 §44 的全部输出条款。
"`e.source` 只碰这两张片"这一条对应 E3 §44 里
`doublePointSet g D.domain = doublePointSet D D.domain \ S` 的"不产生邻近的新交线"，
它属于生产者的义务，不属于滑动层：滑动本身支撑在 `e.symm '' slideSupportLong R` 内，
不会把任何点移出 `e.source`。

检查 `TransversePlaneCoordinates` exit=0（7.5 秒）、零 warning；`AuditF259.lean` 三项仅
`propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF260.lean`。

### 19.116 环境类型的转写义务（§19.112–19.115 的适用范围）

§19.112–19.114 与 §19.108–19.111 一样，环境 `M` 是有限维实赋范空间，图卡取
`OpenPartialHomeomorph M (ℝ × ℝ × ℝ)`，结论里的 PL 性是 `IsPiecewiseAffineOn h univ`。
E3 §44 的 `M` 是带 `ChartedSpace (EuclideanSpace ℝ (Fin 3))` 的拓扑 3-流形，结论要求 `IsPL 3 3 h`。
两者之间还差一次转写，且这不是记号问题：

- `ChartConjugate.lean` 已有流形版的 `isPL_conjugateHomeomorph`，但它要求 `h` 是
  `EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)` 的同胚，模型空间是 `EuclideanSpace`
  而不是 `ℝ × ℝ × ℝ`，并且要 `Homeomorph` 而不是裸函数。
- 因此还需要：把 `slideMapLong d R` 经 `ℝ × ℝ × ℝ ≃ EuclideanSpace ℝ (Fin 3)` 的线性同胚搬过去
  （逐片仿射性经仿射同构保持，见 `AffineImageTransport.lean`），并用
  `bijective_slideMapLong`（`0 ≤ R`）把它升级成 `Homeomorph`（连续性由
  `continuous_slideMapLong` 给出，逆的连续性由紧支撑加双射得到）。
  然后 `isPL_conjugateHomeomorph` 直接给 `IsPL 3 3`，`disjoint`/边界两条不受影响。
- 这一步不难但不是零工作量，交付给下一次；在它完成前，§19.113/19.114 的端点只对赋范空间环境成立。

### 19.117 触边端点的前向滑动模型：半空间保持，边界平面不保持

E3 §48 指出 §19.114 的边界条款只覆盖**平行于分支**的 `Bd M`。在 `HasPLBoundaryCrossingAt` 的触边端点，
双点线与 `Bd M` 横截：把 `Bd M = {x = 0}`、`M = {x ≥ 0}` 代进模型，`slideMapLong` 把 `(0, y, 0)` 推到
`x = -slideAmountLong < 0`，直接出 `M`。`ModelSlideFwd.lean` 按"向前滑（越过第二条带的远端）而不是
向后滑（退出它的近端）"给出端点模型，全部是符号翻转，机制与 §19.110 相同：

- `slideMapFwd d R p = (p.1 + slideAmountLong d R p, p.2.1, p.2.2)`；锥度与宽度函数原封不动复用
  `slideWidthScaled`、`slideTaperRad`、`slideAmountLong`，所以支撑仍是 `slideSupportLong R`。
- 单射性的机制不变，但需要**反向**的 Lipschitz 界：`slideAmountLong_le_add'`
  （`p.2 = q.2`、`p.1 ≤ q.1` 时 `a p ≤ a q + (q.1 - p.1)/2`）。§19.110 的 `slideAmountLong_le_add`
  只给 `a q ≤ a p + (q.1 - p.1)/2`，对 `x + a(x)` 严格增没有用。两条合起来就是
  `|a p - a q| ≤ |p.1 - q.1|/2`，锥度斜率 1/2 < 1 仍是唯一的定量事实。
- `isPiecewiseAffineOn_slideAmountLong` 把 §19.110 证明内部的 `hamount` 提成独立引理，
  于是 `isPiecewiseAffineOn_slideMapFwd` 只有一行 `(hx.add ·).prod_mk (hy.prod_mk hz)`。
- `surjective_slideMapFwd`（`0 ≤ R`）、`bijective_slideMapFwd`、`eqOn_slideMapFwd_id_compl`、
  `mapsTo_slideMapFwd_slideSupportLong`、`mapsTo_slideMapFwd_of_subset`、
  `mapsTo_slideMapFwd_prod`、`bijOn_slideMapFwd_prod` 与 §19.110 逐条对应。

**半空间与边界平面的确切事实**（`slideEndpointHalfSpace = {p | 0 ≤ p.1}`、
`slideEndpointPlane = {p | p.1 = 0}`）：

- `mapsTo_slideMapFwd_slideEndpointHalfSpace`：闭半空间被保持，**无任何假设**（`a ≥ 0` 即可）。
  这是端点模型相对 `slideMapLong` 唯一真正的改进：滑动不再把 `M` 的点推出 `M`。
- 边界平面**不被保持**，这是定理而不是遗漏：`not_mapsTo_slideMapFwd_slideEndpointPlane`
  （`0 < d`、`0 < R` 时 `¬ MapsTo (slideMapFwd d R) slideEndpointPlane slideEndpointPlane`），
  见证点是 `(0,0,0)`，像的第一坐标是 `min d (R/2) > 0`。
- 被固定的边界点刻画完全：`slideAmountLong_eq_zero_iff_of_fst_eq_zero` 与
  `slideMapFwd_eq_self_iff_of_fst_eq_zero` 说，`0 < d`、`0 < R`、`p.1 = 0` 时
  `slideMapFwd d R p = p ↔ 1 ≤ |p.2.1| + |p.2.2|`，即**恰好是宽度带之外的那部分边界**不动。
- 反过来一条是好的：`slideMapFwd_mem_slideEndpointPlane_iff` 说在半空间内
  `slideMapFwd d R p ∈ slideEndpointPlane ↔ p ∈ slideEndpointPlane ∧ slideMapFwd d R p = p`，
  即滑动**不会把内点推到边界上**，留在边界上的恰是不动的那些点。
- `not_surjOn_slideMapFwd_slideEndpointHalfSpace`（`0 < d`、`0 < R`）：半空间被真包含地映进自己，
  由 `le_slideMapFwd_fst_of_mem_axis`（轴上 `0 ≤ p.1` 时 `min d (R/2) ≤ (slideMapFwd d R p).1`）给出。
  所以 `slideMapFwd` 限制在 `M` 上是单射自映射而**不是** `M` 的自同胚；`MapsTo`、`Injective`、
  支撑外恒等这三条仍然成立，E3 §47 的消费者只用到这三条与 `MapsTo h U U`。

**分离的定量条件**（`disjoint_slideMapFwd_image_slideBandA`）：`0 ≤ d`、`c + 2 * d ≤ R`、`b < d` 时
`Disjoint (slideMapFwd d R '' slideBandA c) (slideBandQ a b)`。两条带只在 `y = z = 0` 处可能相交，
那里宽度取满，滑动量恰是 `d`（用到 `c + 2 * d ≤ R` 让锥度在 `[0, c]` 上不压制滑距），
于是 A 的 x 区间由 `[0, c]` 变成 `[d, c + d]`，`b < d` 就把它整体推过 Q 的远端。
注意与 §19.110 的区别：向后滑的条件是 `c - d < a`（越过 Q 的**近**端），向前滑是 `b < d`（越过**远**端）。
`exists_slideMapFwd_parameters` 给出三条件非空（取 `d = max (b+1) 1`、`R = c + 2d`），防止端点被空假设架空。

检查 `ModelSlideFwd` exit=0（9.9 秒）、零 warning；`AuditF260.lean` 二十项仅
`propext`、`Classical.choice`、`Quot.sound`。

### 19.118 端点滑动的图卡版本与打包端点；`MapsTo` 型共轭转写（E3 §48 的回应）

`BranchSlideEndpoint.lean` 把 §19.117 的模型经 PL 图卡共轭，结论与 §19.111/19.113 同形，
但边界条款按 §19.117 的真实情况重写。

- `OpenPartialHomeomorph.mapsTo_conjugateMap`（抽象层，任意拓扑空间、任意 `k`）：设
  `MapsTo k e.target e.target`、`∀ x ∈ e.source, x ∈ A ↔ e x ∈ B`、`MapsTo k (e.target ∩ B) B`，
  则 `MapsTo (e.conjugateMap k) A A`。这条是**真缺的一块**：`Homeomorph/Conjugate.lean` 的
  `conjugateMap_mem_iff` 要求双向的 `∀ y ∈ e.target, k y ∈ B ↔ y ∈ B`，而半空间只有单向
  （`slideMapFwd d R p ∈ {0 ≤ x}` 推不出 `p ∈ {0 ≤ x}`，把 `p.1` 取成小负数即是反例），
  所以两层共轭时半空间条款不能走 iff 版本。写在本模块的 `OpenPartialHomeomorph` 命名空间里，
  与 E3 `BranchSlideConjugation.lean` 的 `injective_conjugateMap`、`disjoint_conjugateMap_image`
  同层、不同名、不重叠。
- `isPiecewiseAffineOn_chartSlideFwd`、`injective_chartSlideFwd`、`eqOn_chartSlideFwd_id_compl`、
  `disjoint_chartSlideFwd_image`（定量条件 `0 ≤ d`、`c + 2 * d ≤ R`、`b < d`）、
  `mapsTo_chartSlideFwd_of_forall_mem_iff`（横向水平集，用于**平行于分支**的那部分 `Bd M`）、
  `mapsTo_chartSlideFwd_halfSpace`（`N` 在图卡里是 `0 ≤ (e x).1`）。后两条都由上面的抽象引理给出。
  除 `isPiecewiseAffineOn_chartSlideFwd` 外都只要 `[TopologicalSpace X]`，所以外层可以直接用
  流形图卡作共轭，不必再放宽一次。
- `exists_supported_separation_of_isBranchSlideChart_endpoint`：复用 §19.112 的 `IsBranchSlideChart`
  （不另立谓词），在 `0 ≤ d`、`c + 2 * d ≤ R`、`b < d` 与 `hN : ∀ x ∈ e.source, x ∈ N ↔ 0 ≤ (e x).1`
  下给出 `h`，满足 `IsPiecewiseAffineOn h univ`、`Function.Injective h`、
  `EqOn h id (e.symm '' slideSupportLong R)ᶜ`、`Disjoint (h '' P) Q`、`MapsTo h N N`。
  与 §19.113/19.114 的差别只有两处：分离条件由 `c - d < a` 换成 `b < d`，
  边界条款由 `h '' (支撑 ∩ B) ⊆ B` 换成 `MapsTo h N N`（保流形而不是保边界）。
- `not_mapsTo_chartSlideFwd_boundaryPlane` 与
  `not_mapsTo_boundary_of_isBranchSlideChart_endpoint`：`0 < d`、`0 < R` 时，
  对图卡内由 `(e x).1 = 0` 刻画的 `B`，`¬ MapsTo (e.conjugateMap (slideMapFwd d R)) B B`。
  见证点是 `e.symm (0,0,0)`。**这是定理，不是未做的部分**：横截于分支的流形边界在这个模型里
  确实保不住，写成否定命题以免下游误以为还能补出来。

**环境类型转写（§19.116 的结论）**：E3 的 `BranchSlideConjugation.lean` 已经把转写做完了，
本车道不重复。逐条核对：`isPL_conjugateMap` 对**任意** `k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)`
成立（只要 `IsPiecewiseAffineOn k univ`、`MapsTo k e.target e.target`、紧 `C ⊆ e.target`、`EqOn k id Cᶜ`），
`OpenPartialHomeomorph.injective_conjugateMap` 与 `disjoint_conjugateMap_image` 对任意拓扑空间成立，
三条都与滑动方向无关，所以对 `slideMapFwd` 逐字适用。§19.116 里设想的
「经 `ℝ × ℝ × ℝ ≃ EuclideanSpace ℝ (Fin 3)` 的线性桥 + `Homeomorph` 升级」**不需要**：
E3 的两层共轭（外层流形图卡 `E`、内层模型拉直 `e`）绕开了线性桥，且 `isPL_conjugateMap` 收裸函数，
不需要逆的连续性。本模块给出的
`isPiecewiseAffineOn_chartSlideFwd` / `injective_chartSlideFwd` / `eqOn_chartSlideFwd_id_compl` /
`disjoint_chartSlideFwd_image` 正好是 `isPL_conjugateMap` 那四个前提的前向版本，
另加 `OpenPartialHomeomorph.mapsTo_conjugateMap` 供半空间条款两层串用。
**未做**：`exists_separated_slide` 的前向版本（把这些拼成 `IsPL 3 3` 层的打包定理）。它属于 E3 的消费者模块，
且需要 `import ...BranchSlideConjugation`；该模块的共享 olean 当前不新鲜（源 06:29:15、olean 06:18:09），
按 `AGENTS.md` §3 不由本车道重编，故本轮不接线。

**归 F 的确切剩余义务（更新 §19.115、替换 E3 §48 的问号）**：
1. 生产者仍缺几何一半：紧致触边分支的单张 PL 乘积图卡（§19.115 末尾那段陈述不变）。
   端点情形还要多一条：该图卡把 `Bd M` 拉直成 `{p | p.1 = 0}`、把 `M` 拉直成 `{p | 0 ≤ p.1}`，
   并且分支从 `x = 0` 伸向 `x > 0`。代数上这一条**可达**：`TransversePlaneCoordinates` 的
   `exists_linearEquiv_of_transverse_planes` 之后还剩的自由度恰是
   `(x,y,z) ↦ (αx + βy + γz, δy, εz)`（保住两张片的坐标平面描述），而横截于 x 轴的任何平面都是
   `{ax + by + cz = 0}` 且 `a ≠ 0`，故可正规化成 `{x = 0}`；这一步尚未形式化。
2. 若下游确实需要「`h` 是 `M` 的自同胚、保 `∂M`」，前向滑动给不出来，
   `not_surjOn_slideMapFwd_slideEndpointHalfSpace`（§19.117）说它把半空间真包含地映进自己。
   E3 §47 的消费者只用 `MapsTo`、`Injective`、支撑外恒等与 `MapsTo h U U`，这四条都有；
   真正被放弃的只有 `∀ x, h x ∈ BdM ↔ x ∈ BdM` 那一条，且 §48 已经把它改成带数据的蕴含。
   要恢复它只能换模型：把端点处的锥度改成在 `Bd M` 处归零，但那样 `(0,0,0)` 不动、
   而它正是一个双点，分支端点清不掉——所以**保边界与清端点在单个支撑滑动里不可兼得**，
   真正的出路是两步构造（先把端点沿 `Bd M` 的一个双领作用挪进内部，再用 §19.113 的内部滑动），
   或由消费者接受「`h` 只保 `M`、不保 `∂M`」。本条是对 E3 §48 那句「要么…要么…」的判决：
   第一条路（与 `Bd M` 相切的收尾模型）走不通，剩下的是第二条路或放宽消费者条款。

检查 `BranchSlideEndpoint` exit=0（9.3 秒）、零 warning；`AuditF261.lean` 十项仅
`propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF262.lean`。

### 19.119 E3 §48 第一条出路的判决：与 `Bd M` 相切的收尾模型不可能

`not_disjoint_image_slideBandA_of_origin_fixed`（`ModelSlideFwd.lean`）：对**任意**
`h : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ`，只要 `0 ≤ c`、`a ≤ 0 ≤ b` 且 `h (0,0,0) = (0,0,0)`，就有
`¬ Disjoint (h '' slideBandA c) (slideBandQ a b)`。原点同时落在两条带里，被固定的原点就仍是双点。

E3 §48 给了两条出路：(1) 给端点一个锥度在 `Bd M` 处归零、与 `Bd M` 相切的收尾模型；
(2) 先把端点挪开的两步构造。本条把 (1) **排除**：在端点模型里 `Bd M = {x = 0}`，
分支端点就是原点，而"锥度在 `Bd M` 处归零"正是 `h (0,0,0) = (0,0,0)`；
于是分离在原点处直接失效。这与滑动方向、滑距、锥度的具体形状都无关，
所以任何逐点固定 `Bd M` 的支撑滑动都不行。

结论：触边端点只剩两种走法——(2) 两步构造（先用别的机制把端点移进 `int M`，再用 §19.113 的内部滑动），
或者消费者接受 `h` 只保 `M`（`MapsTo h N N`，§19.118）而不保 `∂M`。后者已经可用，
且 E3 §47 的双点集等式只需要 `MapsTo`、`Injective`、支撑外恒等与 `MapsTo h U U` 四条。

检查 `ModelSlideFwd` exit=0（9.7 秒）、`BranchSlideEndpoint` exit=0（9.4 秒），均零 warning；
`AuditF260.lean` 二十一项、`AuditF261.lean` 十项仅 `propext`、`Classical.choice`、`Quot.sound`。

### 19.120 端点图卡的最后一条代数条款：横截于分支线的边界平面可正规化成 `{p.1 = 0}`

§19.115 末尾留下的那步（"`exists_linearEquiv_of_transverse_planes` 之后剩下的自由度恰是
`(x,y,z) ↦ (αx+βy+γz, δy, εz)`，横截于 x 轴的平面可正规化成 `{x = 0}`"）已形式化，
`TransversePlaneCoordinates.lean` 新增十六条，`TransversePlaneNormalForm.lean` 新增一条。

**三角群就是正确的群**（不是随手选的子群）：`mapsTo_planes_iff_exists_coeff` 给出等价
`(MapsTo T {p.2.2 = 0} {p.2.2 = 0} ∧ MapsTo T {p.2.1 = 0} {p.2.1 = 0}) ↔
∃ a b c d e, ∀ p, T p = (a p.1 + b p.2.1 + c p.2.2, d p.2.1, e p.2.2)`，对任意
`T : (ℝ×ℝ×ℝ) →ₗ[ℝ] ℝ×ℝ×ℝ`。正向由 `T e₁` 落在两张片上、`T e₂` 落在第一张、`T e₃` 落在第二张
读出五个系数（`exists_coeff_of_mapsTo_planes`）。`ne_zero_of_surjective_triangular`：三角映射满射
⟹ `a ≠ 0 ∧ d ≠ 0 ∧ e ≠ 0`（先用 `(0,1,0)`、`(0,0,1)` 取出 `d`、`e` 非零，再用 `(1,0,0)` 取 `a`）。
`noncomputable def triangularEquiv α β γ δ ε hα hδ hε` 是显式的线性自同构（逆映射手写，
`inv_mul_cancel_left₀` / `mul_inv_cancel_left₀` 验证两侧），`exists_coeff_triangularEquiv_symm`
给出逆仍是三角的系数 `(α⁻¹, -α⁻¹βδ⁻¹, -α⁻¹γε⁻¹, δ⁻¹, ε⁻¹)`，
`image_triangularEquiv_setOf_snd_snd_eq_zero` / `..._snd_fst_...` 是两张片平面被**逐集固定**。

**`a ≠ 0` 需要的横截性假设就是 `HasPLBoundaryCrossingAt` 已经带着的那一条**：定义里的
`(∃ u ∈ P ⊓ Q, ℓ u = 1)`。不需要任何新假设。`exists_mem_apply_eq_one_iff_not_le_ker` 把它等价改写成
`¬ (P ⊓ Q ≤ LinearMap.ker ℓ)`，即**分支线不落在边界平面里**。用 `u` 时 `(L u).2 = 0`，于是
`1 = ℓ u = a (L u).1`，立刻得 `a ≠ 0`。反之若分支线落在 `ker ℓ` 内则 `a = 0`，正规化确实失效——
这不是可以省掉的技术条件。

端点定理（均在 `TransversePlaneCoordinates.lean`）：
- `exists_triangularEquiv_normalizing`：给定已满足两张片条款的 `L`，存在 `α β γ`、`α ≠ 0`，使
  `T = triangularEquiv α β γ 1 1` 满足 `ℓ y = (T (L y)).1` 且 `(T (L y)).2 = (L y).2`
  （`δ = ε = 1`，所以两张片的坐标**原封不动**，只有第一坐标被换成 `ℓ`）。系数取
  `α = ℓ (L.symm (1,0,0))`、`β = ℓ (L.symm (0,1,0))`、`γ = ℓ (L.symm (0,0,1))`。
- `exists_linearEquiv_of_transverse_planes_of_transverse_functional`：打包版，产出 `L` 同时满足
  `y ∈ P ↔ (L y).2.2 = 0`、`y ∈ Q ↔ (L y).2.1 = 0`、`y ∈ P ⊓ Q ↔ (L y).2 = 0`、`ℓ y = (L y).1`。
- `exists_linearEquiv_boundaryCrossing_normalForm`：集合像形式的五条款，
  `{0 ≤ ℓ} ↦ {0 ≤ p.1}`、`{ℓ = 0} ↦ {p.1 = 0}`、
  `P ∩ {0 ≤ ℓ} ↦ {p.2.2 = 0 ∧ 0 ≤ p.1}`、`Q ∩ {0 ≤ ℓ} ↦ {p.2.1 = 0 ∧ 0 ≤ p.1}`、
  `(P ⊓ Q) ∩ {0 ≤ ℓ} ↦ {p.2 = 0 ∧ 0 ≤ p.1}`。最后一条就是"分支从 `x = 0` 伸向 `x > 0`"。

**直接消费 `HasPLBoundaryCrossingAt` 的桥**（新模块 `TransversePlaneNormalForm.lean`，
import `SingularGeneralPosition` 与 `TransversePlaneCoordinates`）：
`HasPLBoundaryCrossingAt.exists_linearEquiv_normalForm`，由 `HasPLBoundaryCrossingAt M A B x`
产出 `U V h L`，`IsPLHomeomorphOn h U V`、`h x = 0`，且 `∀ᶠ y in 𝓝 x` 四条款
`y ∈ M ↔ 0 ≤ (L (h y)).1`、`y ∈ A ↔ (L (h y)).2.2 = 0 ∧ 0 ≤ (L (h y)).1`、
`y ∈ B ↔ (L (h y)).2.1 = 0 ∧ 0 ≤ (L (h y)).1`、
`y ∈ A ∩ B ↔ (L (h y)).2 = 0 ∧ 0 ≤ (L (h y)).1`。
`h` 仍是 `E → E`，只有读坐标那一层后接 `L`，所以 `IsPLHomeomorphOn` 不需要异型版本，
§19.116 判断的"不需要线性桥"在这里同样成立。

**§19.115 生产者的剩余义务因此只剩几何一半**：紧致触边分支的单张 PL 乘积图卡（正则邻域唯一性），
由 H 车道负责。代数一半（把两张片拉直成坐标平面、把边界平面拉直成 `{p.1 = 0}`、
把闭半空间拉直成 `{0 ≤ p.1}`、分支落在非负 x 轴上）现在**全部闭合**。

检查 `TransversePlaneCoordinates` exit=0（7.9 秒）、`TransversePlaneNormalForm` exit=0（8.8 秒），
均零 warning；`AuditF262.lean` 十九项、`AuditF263.lean` 一项，仅 `propext`、`Classical.choice`、
`Quot.sound`。下一审计文件 `AuditF264.lean`。

### 19.121 单顶点的图卡条款：germ 形式已闭合，且它不需要 H 的锥对机器

**结论先说**：分支上**单个顶点**处的图卡陈述现在是定理，
`HasPLCrossingAt.exists_linearEquiv_normalForm` 与
`HasPLBoundaryCrossingAt.exists_linearEquiv_normalForm`（均在 `TransversePlaneNormalForm.lean`）。
但它**不是**由 H 的 `ConePairExtension` / `ConePairCrossing` 得到的——那两个模块与单顶点情形无关，
它们解决的是弧情形的归纳步。核对如下。

`HasPLCrossingAt`（`GeneralPosition.lean:2342`）与 `HasPLBoundaryCrossingAt`
（`SingularGeneralPosition.lean:1717`）的定义**本身就携带**一张单点图卡：`U V h`、`IsOpen U`、
`x ∈ U`、`IsPLHomeomorphOn h U V`、`h x = 0`，外加 `∀ᶠ y in 𝓝 x` 把两片认同成 `P`、`Q` 的锥模型。
所以单顶点处缺的从来不是"存在图卡"，而是"把那个锥模型放进标准坐标"。这一步就是 §19.120 的线性正规化，
于是：

- `HasPLCrossingAt.exists_linearEquiv_normalForm`：产出 `U V h L`，并按定义里
  `α = 0 ∨ β = 0` 那一条给出三分支——两片都是整平面
  （`y ∈ A ↔ (L (h y)).2.2 = 0`、`y ∈ B ↔ (L (h y)).2.1 = 0`），
  或 `A` 整片而 `B` 是半平面（多一条 `0 ≤ (L (h y)).1`），或对称的另一支。
  `α`、`β` 的横截性条款在定义里写成 `∃ u ∈ P ⊓ Q, α u ≠ 0`，由
  `exists_mem_apply_eq_one_of_exists_mem_apply_ne_zero` 归一成 §19.120 需要的 `α u = 1`。
- `HasPLBoundaryCrossingAt.exists_linearEquiv_normalForm`（§19.120）：四条款，多出
  `y ∈ A ∩ B ↔ (L (h y)).2 = 0 ∧ 0 ≤ (L (h y)).1`，即分支落在非负 x 轴上。

**H 的两条新定理是什么**（逐条读过）：
- `exists_isPLHomeomorphOn_closedStar_of_geometricLink_subcomplex`
  （`ConePairExtension.lean:142`）把**已经给定**的连接同胚
  `hf : IsPLHomeomorphOn f (geometricLink K {p}).space (geometricLink K' {p'}).space`
  （`:148-149`）与 `hfJ : f '' (geometricLink J {p}).space = (geometricLink J' {p'}).space`
  （`:150-151`）锥化成闭星同胚，并保 `closedStar J p ↦ closedStar J' p'`。
  它是**延拓**，不产生 `f`。
- `HasPLCrossingAt.of_geometricLink_pair`（`ConePairCrossing.lean:10`）把**模型点处已知的**
  `hcross : HasPLCrossingAt M'.space B' q`（`:24`）沿同一个 `f` 搬回 `p`，
  还要求两侧的集合确实是自己连接迹的锥（`hB`、`hB'`，`:20-21`）。它是**搬运**，同样不产生 crossing。

所以两条都是"连接层已匹配 ⟹ 星层已匹配"，正是弧情形归纳步需要的方向；
对单顶点没有增量，因为单顶点的模型已经在 `HasPLCrossingAt` 的假设里。

**真正的连接层生产者已经在树里，但配置不够**：`exists_isPLHomeomorphOn_geometricLink_pair`
（`LinkPair.lean:53`）确实**产出** `f`，并同时给出 `f '' J = J'` 与
`f '' (link ∩ {ℓ = 0}) = link' ∩ {ℓ' = 0}`——即一对圆（PL 1-球面 `J` 与 ℓ-赤道）在连接 2-球面里的匹配，
这正是 H 的两条定理缺的输入。它要求：`finrank = 3`、`K.space ∈ 𝓝 p`、`ℓ ≠ 0`、`ℓ p = 0`、
`J` 是 PL 1-球面且 `J ∩ {ℓ = 0}` 恰好是两点 `{a, b}`、`J` 两侧都非空，
以及 `hside : ∀ s ∈ K.faces, conv s ⊆ {ℓ ≤ 0} ∨ conv s ⊆ {0 ≤ ℓ}`。

**因此把单顶点从 germ 形式升级到星（subcomplex）形式的确切义务只剩两条**：
1. 把 `p` 附近的两张片实现成子复形，使 `link(A, p)`、`link(B, p)` 是 `link(K, p)` 里的 PL 1-球面，
   且恰交于分支的两个方向 `{a, b}`；
2. 供上 `hside` 那条相容细分：其中一张片要被某个线性泛函的零集承载
   （`LinkPair` 只处理"一个圆 + 一条赤道"，不是任意两个圆）。
满足这两条后，`LinkPair.lean:53` → `ConePairExtension.lean:142` 就把单顶点的星对闭合，
`ConePairCrossing.lean:10` 再把 crossing 搬过去。**弧情形**（§19.115 真正的缺口）还要在此之上
沿分支做归纳，并要求相邻星在公共连接上已匹配；那仍是 H 的正则邻域唯一性工作。

检查 `TransversePlaneCoordinates` exit=0（7.7 秒）、`TransversePlaneNormalForm` exit=0（9.1 秒），
均零 warning；`AuditF264.lean` 三项仅 `propext`、`Classical.choice`、`Quot.sound`。
下一审计文件 `AuditF265.lean`。

### 19.122 单顶点星形图卡：链条早已在树里，H 的 `ConePairExtension` 与 `StarPair` 撞名

**必须先报的缺陷（属于 H，本车道不改）**：`ConePairExtension.lean:125` 声明的
`exists_isPLHomeomorphOn_closedStar_pair` 与 `StarPair.lean:78` **同名同命名空间**。
`ConePairExtension` 只 import `ConeExtension`（`:1`），够不到 `StarPair`，所以 H 自己的聚焦检查看不见冲突；
但**任何同时 import 两者的模块都无法 elaborate**。本车道实测到这条硬错误：

```
import ...StarPair failed, environment already contains
'...exists_isPLHomeomorphOn_closedStar_pair' from ...ConePairExtension
```

而且 `StarPair.lean:78` 的版本**严格更强**：除了
`IsPLHomeomorphOn g (closedStar K p) (closedStar K' q)`、`g p = q`、
`g '' closedStar M p = closedStar M' q`（这三条 H 的版本也有）之外，还多一条
`g '' (closedStar K p ∩ {x | ℓ x = 0}) = closedStar K' q ∩ {x | ℓ' x = 0}`，
即赤道（第二张片）的星也被带过去——那正是分支情形真正要用的一条。
所以 H 的 `exists_isPLHomeomorphOn_closedStar_pair` 是**冗余且更弱**的重复声明，
建议 H 删掉它并改 import `StarPair`；`ConePairCrossing` 因 import 了 `ConePairExtension` 也带着这个毒性。
本车道绕开：不 import `ConePairExtension`，`geometricLink` 的空间单调性按
`VertexCrossing.lean:103-114` 的既有写法在证明内部用 `have` 就地做掉，不新增公共名字。

**协调者要求的链条 `LinkPair → ConePairExtension → ConePairCrossing` 其实早已存在**，
形式是 `LinkPair.lean:53 → StarPair.lean:78 → HasPLCrossingAt.of_closedStar_pair`，
整条写在 `hasPLCrossingAt_fiber_of_geometricLink_section`（`VertexCrossing.lean:12`，
串联在 `:115-121`）里，早于 H 的工作。`VertexCrossingLevel.lean:57` 的 `_at` 版本更通用
（不要求 `ℓ p = 0`，在水平面 `ℓ p` 上工作）。

**关于 `hside`：正规形式并不能消掉它，两者不在一个层次。** `hside` 是**单纯复形 K 的性质**
（每个面整个落在超平面一侧），而 `TransversePlaneNormalForm` 给的是 PL 同胚加线性同构的 germ 条款，
不谈任何复形，所以无法蕴含 `hside`。但 `hside` **也不是新工作**：
`exists_triangulation_union_with_halfSpace_faces`（`HeightSubdivision.lean:10`）
对任意 `K`、任意仿射映射 `a` 与水平 `r` 产出 `R`，满足 `R.space = K.space ∪ D`、
`IsSubdivision (restrict R K.space) K`，以及正是 `hside` 那一条；
`VertexCrossing.lean:72-73` 就是这样给模型造出 `hRside` 的。所以 `hside` 由相容细分供给。

**本轮闭合的两条**（新模块 `VertexBranchChart.lean`）：
- `exists_isPLHomeomorphOn_closedStar_pair_of_geometricLink_section`：把 `LinkPair.lean:53`
  与 `StarPair.lean:78` 显式串成一条可复用的定理。输入是两侧的连接数据
  （`IsPLSphere 1 (link M {p}).space`、`(link M {p}).space ∩ {ℓ = 0} = {a, b}`、`a ≠ b`、两侧非空、
  `hside`），输出是**星对**：`IsPLHomeomorphOn g (closedStar K p) (closedStar K' p')`、`g p = p'`、
  `g '' closedStar M p = closedStar M' p'`、
  `g '' (closedStar K p ∩ {ℓ = 0}) = closedStar K' p' ∩ {ℓ' = 0}`。
  这就是单顶点的星形（subcomplex）图卡，且第四条给出第二张片。
- `exists_linearEquiv_normalForm_of_geometricLink_section`：把
  `hasPLCrossingAt_fiber_of_geometricLink_section_at`（`VertexCrossingLevel.lean:57`）
  与 §19.121 的 `HasPLCrossingAt.exists_linearEquiv_normalForm` 复合，
  **从纯组合输入无条件**产出 `U V h L`，`IsPLHomeomorphOn h U V`、`h p = 0`，且
  `∀ᶠ y in 𝓝 p, (y ∈ M.space → (L (h y)).2.2 = 0) ∧ (ℓ y = ℓ p → (L (h y)).2.1 = 0)`。
  这正是 §19.115 图卡条款（那里本来就写成 `⊆`）在单顶点的形式，且 `HasPLCrossingAt`
  不再是假设。三分支（两片皆整平面／其一为半平面）取 `→` 方向后合并，所以结论对三种情形一致。

**剩余义务（item 1 的真正内容，未闭合）**：上面两条的输入里，
`hlink : IsPLSphere 1 (link M {p}).space` 已有生产者——`IsCombinatorialManifold.isPLSphere_link`
（`VertexChart.lean:247`），即 `M` 是组合 2-流形时每个顶点的连接是 PL 1-球面。
真正缺的是 `hzero`/`hab`/`hpos`/`hneg`：**第二张片把第一张片的连接圆恰好截成两点**。
树里只有平坦情形的生产者 `exists_pair_geometricLink_fiber_of_eventually_plane`
（`VertexCrossing.lean:90-92` 使用），它要求 `hlocal : ∀ᶠ x in 𝓝 0, x ∈ N.space ↔ x - 0 ∈ P`，
即该片在 `p` 附近**就是**一张平面——只覆盖模型侧，覆盖不了一般的 PL 曲面片。
缺的是一条一般位置定理：两张横截相交的 PL 2-片在分支点处，一张的连接圆与另一张的
零集恰交于两点。**估计 150–400 行**（需要连接圆与超平面的一般位置 + 计数，
可能要先做一次相容细分把交点变成顶点）；**此估计未经验证**，只是按树里同类定理的规模推断。
两张片都非平坦的对称情形还要额外一步：`LinkPair` 只处理"一个圆 + 一条赤道"，
所以必须先用本轮第一条把其中一张片拉直成 `{ℓ = 0}`，再对第二张片重复。

检查 `VertexBranchChart` exit=0（10.2 秒）、零 warning；`AuditF265.lean` 两项仅
`propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF266.lean`。

### 19.123 `hzero`/`hab` 已闭合；`hpos`/`hneg` 归约到星上——以及对 §19.122 估计的更正

**先更正自己**：§19.122 里把"连接圆与超平面恰交于两点"估成缺失定理、150–400 行，**估错了**。
按协调者要求先做侦察 grep，结果它**早就在树里**：
`encard_geometricLink_fiber_of_isPLSphere_one`（`HeightLevelLink.lean:75`）——
若 `K.space ∩ {x | ℓ x = ℓ p}` 是 PL 1-球面，则
`((geometricLink K {p}).space ∩ {x | ℓ x = ℓ p}).encard = 2`。
实际代价：该条 1 行（配 `Set.encard_eq_two`），加上星→连接的归约约 45 行。
教训与 `important_lesson` 里那条一致：**先 grep 陈述形状，再估成本**。

**关于 `hside`（协调者第 1 点，确认）**：`encard_geometricLink_fiber_of_isPLSphere_one`
**不把 `hside` 当假设**，它在证明内部用
`exists_triangulation_union_with_halfSpace_faces`（`HeightSubdivision.lean:10`）
自己造出来（`HeightLevelLink.lean:37-38`，再经 `restrict` 传到 `L`、`F`）。

**本轮闭合（新模块 `VertexBranchSection.lean`，六条）**：
- `closedStar_eq_coneSet_geometricLink`：`closedStar K p = coneSet p (geometricLink K {p}).space`。
  重建 H 原先在 `ConePairExtension` 里、这次整理时删掉的那条，由
  `closedStar_eq_coneComplex_space` 与 `coneComplex_space_eq_coneSet` 拼成。
- `exists_mem_geometricLink_smul_of_mem_closedStar`：星上任一非顶点都写成 `p + s • (z - p)`，
  `z` 在连接上、`0 < s`。
- `exists_mem_geometricLink_apply_lt_of_mem_closedStar` /
  `exists_mem_geometricLink_lt_apply_of_mem_closedStar`：**把 `hneg`/`hpos` 从连接归约到闭星**。
  关键是 `ℓ` 仿射：`ℓ (p + s • (z - p)) = ℓ p + s * (ℓ z - ℓ p)`，`s > 0` 时同号。
  于是消费者只需在**片上**给出 `p` 附近上下各一点，不必直接谈连接圆。
- `exists_pair_geometricLink_fiber_of_isPLSphere_one`：`encard = 2` 经 `Set.encard_eq_two`
  变成 `∃ a b, a ≠ b ∧ (geometricLink M {p}).space ∩ {x | ℓ x = ℓ p} = {a, b}`，
  即 **`hzero` 与 `hab` 完全消掉**。
- `exists_linearEquiv_normalForm_of_isPLSphere_one_fiber`：打包版。假设改成几何自然形式后，
  产出与 §19.122 同样的单顶点图卡
  `∀ᶠ y in 𝓝 p, (y ∈ M.space → (L (h y)).2.2 = 0) ∧ (ℓ y = ℓ p → (L (h y)).2.1 = 0)`。

**必须明说：还假设了什么**
1. `hfiber : IsPLSphere 1 (M.space ∩ {x | ℓ x = ℓ p})`——"两张片在 `p` 附近交成一个圆"。
   这是横截相交的 PL 写法，是**真输入**，不是可省的技术条件。
2. `hpos`/`hneg` 仍需消费者给（现在以星上两点的形式给）。它**不能**由 `encard = 2` 推出：
   连接是 PL 圆，`ℓ` 在其上的水平集恰两点时，两条开弧上 `ℓ - ℓ p` 各自定号，
   但两条弧**可以同号**（同一水平上的两个孤立极小）。所以"两侧都有点"是独立的横截性输入。
3. `hside`（对外层 `K`）仍是假设：它喂给 `hasPLCrossingAt_fiber_of_geometricLink_section_at`。
   由 `HeightSubdivision.lean:10` 可造，但要连带把 `M` 相容细分并沿 PL 同胚搬运
   `hlevel`/`hpos`/`hneg`——`VertexSectionSubdivision.lean:73-105` 正是这套搬运的现成写法。
   本轮未接，属于纯 bookkeeping。
4. `hlink` 仍是假设，生产者已知：`IsCombinatorialManifold.isPLSphere_link`（`VertexChart.lean:247`），
   即 `IsCombinatorialManifold 2 M` 时每个顶点的连接是 PL 1-球面。

**确切剩余义务（两张片都不平坦的对称情形，如 §19.122 预告）**：
上面一切仍要求第二张片**就是** `{ℓ = ℓ p}`（`LinkPair` 只处理"一个圆 + 一条赤道"）。
两张真 PL 曲面相交时，得先用本轮的图卡把其中一张拉直成超平面，再对第二张重复。
缺的是**把图卡搬成复形层的转写**：图卡是 `IsPLHomeomorphOn h U V`，
要把 `K`、`M` 沿 `h` 变成新的单纯复形并保持 `Finite`、`faces ⊆`、`{p} ∈ faces`，
才能第二次喂给 `hasPLCrossingAt_fiber_of_geometricLink_section_at`。
树里 `affineImage`（`VertexCrossingLevel.lean:10-55`）只做仿射搬运，PL 搬运没有对应物。
**估计 200–500 行，未验证**；鉴于本轮估计已错过一次，先 grep
`IsPLHomeomorphOn` 与 `SimplicialComplex` 的像/三角剖分转写再动手。

检查 `VertexBranchSection` exit=0（10.4 秒）、零 warning；`AuditF266.lean` 六项仅
`propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF267.lean`。

### 19.124 PL 转写已在树里；单顶点图卡的假设现在全是几何输入

**grep 先行的结果（协调者三条都问到了点上，答案是"已有"）**：
- 沿 PL 同胚搬运复形：`exists_simplicialComplex_image_of_affineOn_faces`（`PLImage.lean:113`）。
  它不只给 `L.space = f '' K.space` 和 `IsPLHomeomorphOn f K.space L.space`，**还给面的刻画**
  `∀ t, t ∈ L.faces ↔ ∃ s ∈ K.faces, t = s.image f`——这一条正是保住 `M.faces ⊆ K.faces`
  与 `{p} ∈ M.faces` 的关键。`exists_isPLHomeomorphOn_image`（`:140`）是 PL 版但**丢掉了面的刻画**
  （`:150` 处用 `-` 吃掉），所以对本任务不够，要用 `_of_affineOn_faces` 版并自己走细分那一步。
- 细分到 `h` 在每个面上仿射：`IsPiecewiseAffineOn.exists_isSubdivision_affineOn_faces`（`PLImage.lean:147` 使用）。
- 把子复形一起细分：`IsSubdivision.restrict`（`Subcomplex.lean:108`）——
  `IsSubdivision R K → L.faces ⊆ K.faces → IsSubdivision (restrict R L.space) L`。
- `simplicialMap` 层：`simplicialImage`（`SimplicialImage.lean:89`）是上面那条的底层构造，不必重做。

**本轮闭合一：PL 转写**（新模块 `SimplicialPairImage.lean`）
`exists_simplicialComplex_pair_image_of_isPiecewiseAffineOn`：给 `IsPiecewiseAffineOn h K.space`、
`InjOn h K.space`、`M.faces ⊆ K.faces`、`{p} ∈ M.faces`，产出 `K₁ M₁ : SimplicialComplex ℝ F`，
满足 `K₁.faces.Finite`、`M₁.faces.Finite`、`M₁.faces ⊆ K₁.faces`、`{h p} ∈ M₁.faces`、
`K₁.space = h '' K.space`、`M₁.space = h '' M.space`、
`IsPLHomeomorphOn h K.space K₁.space`、`IsPLHomeomorphOn h M.space M₁.space`。
做法：先 `exists_isSubdivision_affineOn_faces` 得 `K'`，再 `M' := restrict K' M.space`
（`IsSubdivision.restrict` 保证 `M'.space = M.space`），然后对 `K'` 与 `M'` **用同一个 `h`**
各做一次 `exists_simplicialComplex_image_of_affineOn_faces`；
`M₁.faces ⊆ K₁.faces` 直接由两边的面刻画加 `M'.faces ⊆ K'.faces` 得到，不需要额外几何。
这正是 §19.123 末尾估的 200–500 行那一条，**实际 40 行**——估计又偏高，原因同上：没先 grep 就估。

**本轮闭合二：两条 bookkeeping 债**（新模块 `VertexBranchInput.lean`）
`exists_linearEquiv_normalForm_of_isCombinatorialManifold` 同时消掉 `hside` 与 `hlink`：
- `hlink` ← `IsCombinatorialManifold 2 M`，直接按定义 `hMan p hp`
  （`Polyhedron.lean:60` 的定义就是 `∀ v, {v} ∈ K.faces → IsPLSphere n (link K {v}).space`，
  不必 import `VertexChart`）。**坑**：该定义带 `open Classical in`，用的是 `Classical.propDecidable`，
  与 section 里的 `[DecidableEq E]` 不是同一个实例，报 type mismatch。
  解法是**去掉 `[DecidableEq E]` 绑定、证明里用 `classical`**，两边实例就字面相同；
  linter 本来也提示该绑定在类型里没用到。
- `hside` ← `exists_triangulation_union_with_halfSpace_faces K (isPolyhedron_space K)
  ℓ.toLinearMap.toAffineMap (ℓ p)` 取 `D := K.space`，得 `K₂ := restrict R K.space`；
  `M₂ := restrict K₂ M.space` 由 `IsSubdivision.restrict` 得 `M₂.space = M.space`。
  细分后连接变了，用
  `exists_isPLHomeomorphOn_geometricLink_of_isSubdivision_preserving_height_sign`
  （`LinkHeightSubdivision.lean:126`）把 `link M₂ {p}` 与 `link M {p}` 对上：
  它同时给 `= ℓ p`、`< ℓ p`、`ℓ p <` 三条像等式，于是
  `hlink₂ = hlinkM.of_isPLHomeomorphOn hf.symm`（`IsPLHomeomorphOn.symm` 在 `PLHomeomorph.lean:65`），
  `hpos₂`/`hneg₂` 按 `VertexSectionSubdivision.lean:94-105` 的写法沿严格号像等式拉回。
消费者现在只需给：`IsCombinatorialManifold 2 M`、
`IsPLSphere 1 (M.space ∩ {x | ℓ x = ℓ p})`（两张片交成圆）、
以及 `closedStar M p` 里上下各一点。**全部是真几何输入，没有 bookkeeping 债。**

**确切剩余义务（对称情形本身，仍未闭合）**：转写砖有了，但把它接成"两张都不平坦"的论证还缺一步：
要把第一次拉直得到的 germ 图卡 `IsPLHomeomorphOn h U V` 变成能喂给转写的形式，
需要 `IsPiecewiseAffineOn h K.space` 与 `InjOn h K.space`，而
`exists_linearEquiv_normalForm_of_*` 交付的是**开集 `U` 上**的图卡，
`K.space ⊆ U` 并不自动成立——`U` 只保证含 `p`。所以还要一步
"把复形收缩到图卡定义域内"（取 `closedStar` 或在 `U` 内取一个含 `p` 的子复形）。
`IsPLHomeomorphOn.restrict`（`PLImage.lean:168`）要求限制到**多面体**，闭星正是多面体，
所以路线是：先换成 `closedStar K p ⊆ U`，再转写。**估计 60–150 行，未验证**；
这一次的估计基于已经核对过的三个接口（`restrict`、`closedStar` 是多面体、转写砖），
但仍未写，按前两次的记录应当当作上界不可靠。

检查 `SimplicialPairImage` exit=0（8.9 秒）、`VertexBranchInput` exit=0（10.2 秒），均零 warning；
`AuditF267.lean` 两项仅 `propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF268.lean`。

### 19.125 图卡定义域内的收缩已闭合；对称情形卡在"面刻画与 glue-iso 只能二选一"

**grep 先行（协调者两问，都已有）**：
- **有没有"空间恰是闭星"的复形**：有，`starComplex`（`StarComplex.lean:15`）。
  `starComplex_space`（`:32`）给 `(starComplex K v).space = closedStar K v`，
  `starComplex_faces_subset`（`:27`）、`starComplex_faces_finite`（`:29`）、
  `singleton_mem_starComplex`（`:52`）齐全。**意外之喜**：
  `geometricLink_starComplex`（`:45`）给出 `link (starComplex K v) {v} = link K {v}`——
  取星**完全不改连接**，所以 `hlink` 这一条过收缩是免费的。
- **`closedStar K p ⊆ U` 是否要细分**：要，且现成：
  `exists_isSubdivision_closedStar_subset_of_mem_nhds`（`ClosedStarNeighborhood.lean:10`），
  由 `U ∈ 𝓝 p` 给出细分 `R`、`{p} ∈ R.faces` 与 `closedStar R p ⊆ U`。
- 另外两条为后面准备的：`exists_isPLHomeomorphOn_geometricLink_of_isSubdivision`
  （`LinkSubdivision.lean:45`，细分下连接的 PL 同胚，不需要 `hside`），
  `IsGlueIso.geometricLink`（`StarComplex.lean:79`）与 `IsGlueIso.isPLHomeomorphOn`（`:64`）。

**本轮闭合（新模块 `VertexChartTransport.lean`）**
`exists_simplicialComplex_pair_image_closedStar_of_isPiecewiseAffineOn`：给 `M.faces ⊆ K.faces`、
`{p} ∈ M.faces`、`U ∈ 𝓝 p`、`IsPiecewiseAffineOn h U`、`InjOn h U`，产出细分 `R` 与
`K₁ M₁ : SimplicialComplex ℝ F`，满足 `IsSubdivision R K`、`{p} ∈ R.faces`、
`closedStar R p ⊆ U`、`K₁.faces.Finite`、`M₁.faces.Finite`、`M₁.faces ⊆ K₁.faces`、
`{h p} ∈ M₁.faces`、`K₁.space = h '' closedStar R p`、
`M₁.space = h '' closedStar (restrict R M.space) p`。
做法：`ClosedStarNeighborhood` 把星缩进 `U`，`starComplex` 把闭星变成复形，
闭星是多面体所以 `IsPiecewiseAffineOn.mono_of_isPolyhedron`（`PLHomeomorph.lean:39`）
把 `h` 的分片仿射性限制过去，再喂 §19.124 的转写砖。
`(starComplex M' p).faces ⊆ (starComplex R p).faces` 由 `mem_starComplex_faces_iff` 一行得到。

**卡点（确切，属于本轮的真实发现）**：把对称情形拼完还差一条
`IsPLSphere 1 (link M₁ {h p}).space`（第二次喂图卡机器要它）。三段链条里两段是免费的：
`link M {p} → link M' {p}` 用 `LinkSubdivision.lean:45` 加 `IsPLHomeomorphOn.symm`；
`link (starComplex M' p) {p} = link M' {p}` 由 `geometricLink_starComplex` 直接相等。
**第三段过不去**：要把连接搬过像复形，得有 `IsGlueIso`，然后用
`IsGlueIso.geometricLink` + `IsGlueIso.isPLHomeomorphOn`。但树里两个接口**互补而不重叠**：
- `exists_simplicialComplex_image_of_affineOn_faces`（`PLImage.lean:113`）给**面刻画**，不给 glue-iso；
- `exists_isGlueIso_of_affineOn_faces`（`AffineImageTransport.lean:13`）给 **glue-iso**，
  但在 `:20-28` 处把 `hfaces` 吃掉了，不往外给。

而 §19.124 的转写**必须**用面刻画（那是 `M₁.faces ⊆ K₁.faces` 的唯一来源），
所以一次调用拿不到 glue-iso。形状与上一轮 `exists_isPLHomeomorphOn_image` 丢掉面刻画
（`PLImage.lean:150`）是同一类：同一构造的两个包装各丢一半。
**最小修法**：在 `AffineImageTransport` 的输出里把 `hfaces` 一并带出（该模块不属 H/E3，可改），
或在本车道写一个同时返回两者的版本。改完之后对称情形只剩装配：
第一次拉直把片 A 送进 `{q.2.2 = 0}`（要用 `HasPLCrossingAt` 的 **iff** 形而非
`exists_linearEquiv_normalForm_of_geometricLink_section` 的 `→` 形，后者为了三分支统一弱化过），
转写到 `ℝ × ℝ × ℝ`，再对片 B 以 `ℓ' := (· .2.2)` 走第二遍。
**不再给行数估计**：前两轮的估计各错一次（偏高 5–10 倍），本条的规模取决于上面那个包装改得多干净。

检查 `VertexChartTransport` exit=0（9.4 秒）、零 warning；`AuditF268.lean` 一项仅
`propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF269.lean`。

### 19.126 常驻提醒：包装缺一半时先找兄弟包装；连接球面已能过转写

**常驻提醒（今天第三次踩同一形状，写成规则）**：**某个包装的结论看起来"少一半"时，
先去找同一构造上的兄弟包装，再下"树里没有"的结论。** 今天三例：
`exists_isPLHomeomorphOn_image`（`PLImage.lean:140`）在 `:150` 丢掉面刻画；
`exists_simplicialComplex_image_of_affineOn_faces`（`:113`）保面刻画但不给 glue-iso；
`exists_isGlueIso_of_affineOn_faces`（`AffineImageTransport.lean:13`）给 glue-iso 但在 `:20-28` 丢面刻画。
三者是同一个 `simplicialImage` 构造的三个包装。

**本轮改动一：加强 `exists_isGlueIso_of_affineOn_faces`**（`AffineImageTransport.lean`，无车道归属）
结论末尾加上 `∀ t, t ∈ L.faces ↔ ∃ s ∈ K.faces, t = s.image f`，证明里 `hfaces` 本来就在手，
只需写进 `refine`。**注意：协调者说"加合取项不会破坏消费者"这一条不成立**——
`obtain ⟨…⟩` 的匿名构造子模式是定长右嵌套的，多一个合取项会让最后一个绑定变成
`(第n项 ∧ 新项)`。两个消费者都要补一个 `-`：
`PlanarChartDeletion.lean:36`（第 7 位 `hsm` 当 `EqOn` 用，**会真报错**）与
`SimplexDiskStraightening.lean:154`（第 7 位本就是 `-`，会静默吸收两项，不报错但应补齐）。
两处都不属 H/E3。重编结果：`AffineImageTransport` exit=0（9.1 秒）、
`PlanarChartDeletion` exit=0（11.9 秒）、`SimplexDiskStraightening` exit=0（11.1 秒），均零 warning。

**本轮改动二：连接球面现在能过转写**
`exists_simplicialComplex_pair_image_of_isPiecewiseAffineOn`（`SimplicialPairImage.lean`）
新增末条 `∀ n, IsPLSphere n (link M {p}).space → IsPLSphere n (link M₁ {h p}).space`。
证明把 `M₁` 那一次调用换成加强后的 glue-iso 版（同时拿到面刻画与 glue-iso），
再走 `exists_isPLHomeomorphOn_geometricLink_of_isSubdivision`（`LinkSubdivision.lean:45`）
加 `IsPLHomeomorphOn.symm` 下到细分，最后
`IsGlueIso.geometricLink`（`StarComplex.lean:79`）+ `IsGlueIso.isPLHomeomorphOn`（`:64`）过像。
`exists_simplicialComplex_pair_image_closedStar_of_isPiecewiseAffineOn`
（`VertexChartTransport.lean`）把同一条propagate 出来：中间那步
`link (starComplex M' p) {p} = link M' {p}` 由 `geometricLink_starComplex` 直接相等。
两条都因为类型里出现 `geometricLink` 而必须带回 `[DecidableEq E] [DecidableEq F]`。

**对称情形：装配还差两条，都已定位**
`IsPiecewiseAffineOn.affine_comp`（`BranchCollarPrism.lean:57` 在用）给出 `L ∘ h` 仍分片仿射，
所以"复合线性同构"不是障碍。剩下：
1. `K₁.space ∈ 𝓝 (h p)`（第二次喂图卡机器要）。现有 `K₁.space = h '' closedStar R p`，
   要它是 `h p` 的邻域，得用 `IsPLHomeomorphOn h U V` 诱导的同胚 `U ≃ₜ V`
   （`PLBallSphere.lean:14`）加上 `IsOpen U`、`IsOpen V`。图卡本来就给这两个开性，
   所以是可做的一步，但要把 `≃ₜ` 的开映射性质接出来。
2. 第二次的 `hfiber`：`IsPLSphere 1 (M₁.space ∩ {q | q.2.2 = c})`，即**第二张片被已拉直的第一张片
   截成圆**。这和 §19.123 里第一次的 `hfiber` 同性质，是**真几何输入**，不是 bookkeeping。
另外第一次拉直要取 `HasPLCrossingAt.exists_linearEquiv_normalForm` 的 **iff** 形
（`exists_linearEquiv_normalForm_of_geometricLink_section` 为统一三分支弱化成了 `→`），
这一步在源头取即可，不必反推。

检查 `SimplicialPairImage` exit=0（9.1 秒）、`VertexChartTransport` exit=0（10.9 秒）、
`VertexBranchInput` exit=0（11.1 秒），均零 warning；`AuditF269.lean` 三项仅
`propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF270.lean`。

### 19.127 邻域条款已闭合；自查发现 `hfiber` 的可满足域被限死，装配路线要改

**本轮闭合两条**
- `image_closedStar_mem_nhds_of_isPLHomeomorphOn`（`VertexChartTransport.lean`）：
  `K.space ∈ 𝓝 p`、`IsOpen W`、`IsPLHomeomorphOn h U W`、`p ∈ U` ⟹ `h '' closedStar K p ∈ 𝓝 (h p)`。
  不走 `≃ₜ` 的子类型：直接用 `IsPiecewiseAffineOn.continuousOn`（`PiecewiseAffine.lean:218`）
  给 `Function.invFunOn h U` 在 `W` 上的 `ContinuousAt`，再用
  `ContinuousAt.preimage_mem_nhds`，最后
  `W ∩ invFunOn h U ⁻¹' closedStar K p ⊆ h '' closedStar K p`。
  **写完发现 `closedStar K p ⊆ U` 这条假设用不到**（对 `y ∈ W`，`invFunOn h U y` 自动落在 `U` 里），
  已删除；linter 的 unused-variable 警告是这么被发现的。
- `exists_linearEquiv_normalForm_of_isPLSphere_link`（`VertexBranchInput.lean`）：
  把 §19.124 的 `IsCombinatorialManifold 2 M` 换成直接的
  `IsPLSphere 1 (link M {p}).space`，`_of_isCombinatorialManifold` 退化成一行推论。
  这样转写之后拿到的连接球面（§19.126 的新条款）可以直接喂进去。
  **注意实例坑的另一面**：泛化版的类型里出现 `geometricLink`，所以必须带 `[DecidableEq E]`
  并去掉 `classical`；推论版反过来不带绑定、用 `classical`，两边才对得上
  `IsCombinatorialManifold` 的 `Classical.propDecidable`。

**自查发现（按协调者要求逐条检查假设，确实查出一条）**
`exists_linearEquiv_normalForm_of_isPLSphere_link` 的假设逐条判定：
1. `hn : finrank ℝ E = 3` —— 几何输入（环境是 3 维）。
2. `[Finite K.faces] [Finite M.faces]` —— 构造性副产品（机器需要有限性）。
3. `hM : M.faces ⊆ K.faces` —— 几何输入（片是子复形）。
4. `hp : {p} ∈ M.faces` —— 几何输入（`p` 是片的顶点）。
5. `hK : K.space ∈ 𝓝 p` —— 几何输入（`p` 是 3-流形内点）。
6. `ℓ ≠ 0` —— 几何输入，**并且是平坦性限制**：第二张片必须就是超平面。
7. `hlinkM : IsPLSphere 1 (link M {p}).space` —— 几何输入（`M` 在 `p` 处是曲面）。不涉及 `ℓ`，不夹带结论。
8. `hfiber : IsPLSphere 1 (M.space ∩ {x | ℓ x = ℓ p})` —— 几何输入，但**可满足域被限死**。
9. `hu hv hult hvlt` —— 几何输入（片在平面两侧都有点），§19.123 已证不能由计数推出。
没有一条夹带结论。但**第 8 条有实质问题**：它要求"片被平面截出的截线是**闭曲线**"。
`encard_geometricLink_fiber_of_isPLSphere_one`（`HeightLevelLink.lean:75`）内部先把
`K.space ∩ {ℓ = ℓ p}` 做成复形 `F`，再用 `isPLSphere_geometricLink_of_isPLSphere`
（`BallSphereLink.lean:20`）取 `p` 处连接，所以确实需要 1-球面而不是 1-球体。
于是：**若 `M` 取成 `p` 的闭星（圆盘），截线是弧不是圆，第 8 条为假**，定理在那种取法下空转。
它只在片是闭曲面（截线成圆）时可用。

**这条直接改掉了装配路线。** 原计划第二次应用是对 `N₁`——而 `N₁` 是**闭星的像**，即圆盘，
其平面截线必然是弧，所以 `hfiber` 对 `N₁` 恒假，**不能**用 `_of_isPLSphere_link` 那层包装做第二次。
第二次必须直接用 `exists_linearEquiv_normalForm_of_geometricLink_section`
（它收 `hab`/`hlevel`/`hpos`/`hneg`，没有 `hfiber` 那条全局限制），把这四条**随转写一起搬过去**：
`hlevel` 与 `hab` 要沿 §19.126 的 glue-iso 连接同胚搬（连接是有限点集，像仍是两点），
`hpos`/`hneg` 用 §19.123 的星→连接归约在像一侧重新给。
可能的替代是给 `encard_geometricLink_fiber_of_*` 补一个 **1-球体 + `p` 为内点**的版本；
树里有 `isPLSphere_or_isPLBall_geometricLink_of_isPLBall`（`BallSphereLink.lean:151`），
但它给的是析取，要另外排除边界点情形。**不估行数**。

检查 `VertexChartTransport` exit=0（9.7 秒）、`VertexBranchInput` exit=0（11 秒），均零 warning；
`AuditF270.lean` 三项仅 `propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF271.lean`。

### 19.128 第二次应用的入口已建好（假设可满足）；装配还缺连接同胚本身

**本轮闭合：`exists_linearEquiv_normalForm_of_geometricLink_pair`**（`VertexBranchInput.lean`）
它就是 §19.127 说的"正确入口"：收 `hlinkM`、`hab`、`hlevel`、`hpos`、`hneg` 四条连接层数据，
**内部照旧用 `HeightSubdivision.lean:10` 消掉 `hside`**，结论与 §19.124 相同。
关键技术点：细分后要把 `hab`/`hlevel` 从 `M` 搬到 `M₂`，用
`exists_isPLHomeomorphOn_geometricLink_of_isSubdivision_preserving_height_sign` 的
**第二个返回值 `hfeq`**（`= ℓ p` 的像等式，§19.124 里被我用 `-` 丢掉了），再走计数：
`hf.bijOn.injOn.mono inter_subset_left` 给单射，`Set.InjOn.encard_image` 把
`encard` 搬过去，`hlevel`、`Set.encard_pair hab` 化成 2，最后 `Set.encard_eq_two` 取回一对。
`ℓ : E →L[ℝ] ℝ` 与 `ℓ.toLinearMap` 的形状差异统一用
`simp only [ContinuousLinearMap.coe_coe] at hfeq hflt hfgt` 抹平。
`_of_isPLSphere_link` 现在退化成它的推论（用 `hfiber` 造 `hab`/`hlevel`，用星→连接造 `hpos`/`hneg`），
`_of_isCombinatorialManifold` 再退化成那个的推论。三层，无重复证明。

**新入口的假设逐条判定（含可满足性，按 §19.127 的教训两种失效模式都查）**
1. `hn : finrank ℝ E = 3` —— 几何输入；可满足。
2. `[Finite K.faces] [Finite M.faces]` —— 构造性副产品；可满足。
3. `hM : M.faces ⊆ K.faces` —— 几何输入（片是子复形）；可满足。
4. `hp : {p} ∈ M.faces` —— 几何输入；可满足。
5. `hK : K.space ∈ 𝓝 p` —— 几何输入（`p` 是 3-流形内点）；可满足。
6. `hℓ : ℓ ≠ 0` —— 几何输入，**仍是平坦性限制**（第二张片必须是超平面）；可满足。
7. `hlinkM : IsPLSphere 1 (link M {p}).space` —— 几何输入（`M` 在 `p` 处是曲面）；
   **对圆盘状的片可满足**（闭星的连接就是圆）。
8. `hab` + `hlevel : (link M {p}).space ∩ {x | ℓ x = ℓ p} = {a, b}` —— 几何输入
   （连接圆与平面恰交于两点）。**这一条正是 §19.127 的修复**：
   旧的 `hfiber` 要求**整片**的截线是闭曲线，对圆盘恒假；
   新的只要求**连接圆**与平面交两点，圆盘状的片完全满足。可满足性已恢复。
9. `hpos`/`hneg` —— 几何输入（片在平面两侧都有点）；§19.123 已证不能由计数推出；可满足。
没有一条夹带结论（结论是 PL 图卡，假设都只谈连接与截面）。

**装配的确切剩余义务（比 §19.127 更具体）**
第二次应用要在像一侧给 `hab`/`hlevel`/`hpos`/`hneg`。源侧对应的几何陈述是
`(link N {p}).space ∩ M.space = {a, b}`（分支的两个方向）与"`link N {p}` 在 `M` 两侧都有点"，
两条都可满足。**但搬不过去**：§19.126 给转写加的那一条只输出
`IsPLSphere n (link M {p}).space → IsPLSphere n (link M₁ {h p}).space`，
即只交付**球面性质**，不交付**连接同胚本身**，而 `hab`/`hlevel` 是集合等式，必须有映射才能搬。
所以下一块砖是把 §19.126 那条再加强一次：除球面性质外，把
`IsGlueIso.geometricLink` 得到的连接同胚（以及它在 `link M' {p}` 上等于 `h` 这一点——
`exists_isGlueIso_of_affineOn_faces` 的 `hsm` 分量，我在 `SimplicialPairImage` 里用 `-` 丢掉了）
一并输出。**又是"包装丢掉自己内部已有的东西"那个形状**，和 §19.126 的常驻提醒同类，
只不过这次丢的是我自己写的包装。**不估行数。**

检查 `VertexBranchInput` exit=0（11.1 秒）、零 warning；`AuditF271.lean` 三项仅
`propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF272.lean`。

### 19.129 转写现在交付连接同胚；但"它等于 h"不成立，装配还差两块

**常驻提醒补一条（接 §19.126）**：**解构模式里的 `-` 是信息死掉的地方，每写一个都值得回头看一眼。**
本车道今天自己踩了两次：§19.124 用 `-` 丢掉 `hfeq`，§19.128 为了搬 `hab`/`hlevel` 又回去捡；
§19.126 用 `-` 丢掉 `hsm`，本轮又回去看。两次都不是别人的包装，是自己刚写的。

**本轮闭合：两个转写包装改为交付连接同胚**
`exists_simplicialComplex_pair_image_of_isPiecewiseAffineOn`（`SimplicialPairImage.lean`）与
`exists_simplicialComplex_pair_image_closedStar_of_isPiecewiseAffineOn`（`VertexChartTransport.lean`）
的末条由
`∀ n, IsPLSphere n (link M {p}).space → IsPLSphere n (link M₁ {h p}).space`
换成
`∃ g : E → F, IsPLHomeomorphOn g (link M {p}).space (link M₁ {h p}).space`。
球面性质现在是它的一行推论（`.of_isPLHomeomorphOn`），不必单列。
证明用 `IsPLHomeomorphOn.trans`（`PLHomeomorph.lean:78`）把两跳接起来。
消费者重编：`SimplicialPairImage` exit=0（9 秒）、`VertexChartTransport` exit=0（9.7 秒）、
`VertexBranchInput` exit=0（11.7 秒），均零 warning。两个包装各只有一个消费者，
`-` 的位置检查过，没有需要补的。

**必须更正任务前提："g 在连接上等于 h"不成立。**
转写到 `M₁` 是**两跳**，不是一跳：
`link M {p}` --(细分)--> `link M' {p}` --(glue-iso)--> `link M₁ {h p}`。
第二跳的映射确实是 `h`（那正是我丢掉的 `hsm` 分量）。
但第一跳是 `exists_isPLHomeomorphOn_geometricLink_of_isSubdivision`，其内部是
`exists_isPLHomeomorphOn_of_radial`（`LinkSubdivision.lean:50`），即
`simplicialMap L' (radialProj p L.space)`——**沿 `p` 出发的射线做径向投影**，不是恒等，更不是 `h`。
细分是把 `h` 变成逐面仿射所必需的，这一跳去不掉。所以复合 `g = h ∘ (径向)⁻¹`，
只能说"第二跳等于 `h`"，不能说"`g` 等于 `h`"。

**装配的确切剩余义务（两块，都已定位）**
1. **三元转写**。要搬 `(link N {p}).space ∩ M.space = {a, b}`，得同时知道 `N` 和 `M` 各自搬到哪里，
   而且必须用**同一个细分 `K'`**——现有包装一次只带一个子复形，分两次调用得到的 `K'` 不保证相同。
   所以需要 `(K, M, N)` 的三元版本。证明与现有二元版逐字同构（对第三个子复形再做一次像构造，
   面刻画同样给出 `N₁.faces ⊆ K₁.faces`），不是新数学。
2. **径向跳与锥的相容性**。复合 `g` 要把 `M.space` 那一侧对上，需要第一跳的径向投影保持
   `closedStar M p`。它确实是 `p` 处的锥（§19.125 的 `closedStar_eq_coneSet_geometricLink`），
   而径向投影沿射线走，所以保锥是对的；树里 `image_coneSet_of_radial`
   （`ConePairExtension.lean:38`，H 的模块，只读）是同一形状的引理。
   要把它接上，得让 `exists_isPLHomeomorphOn_geometricLink_of_isSubdivision` 交出"该映射是径向的"
   这一事实——**又是包装不交付内部已有信息**，和本节开头那条提醒同一形状，这次在别人的包装里。
**不估行数。**

检查见上；`AuditF272.lean` 两项仅 `propext`、`Classical.choice`、`Quot.sound`。
下一审计文件 `AuditF273.lean`。

### 19.130 三元转写已闭合；第二件事不用改（已有显式版）；并更正 §19.129 自己的"径向保锥"论证

**闭合：三元转写**（`SimplicialPairImage.lean`）
`exists_simplicialComplex_triple_image_of_isPiecewiseAffineOn`：对 `(K, M, N)`，
`M.faces ⊆ K.faces`、`N.faces ⊆ K.faces`、`{p} ∈ M.faces ∩ N.faces`，
用**同一个细分 `K'`** 产出 `K₁ M₁ N₁`，交付 `Finite` 三条、
`M₁.faces ⊆ K₁.faces`、`N₁.faces ⊆ K₁.faces`、`{h p}` 在两者的面里、三条空间等式、
三条 `IsPLHomeomorphOn`，以及 `M`、`N` 各自的连接同胚。
二元版 `exists_simplicialComplex_pair_image_of_isPiecewiseAffineOn` 现在是它的推论
（取 `N := M` 再丢掉 `N₁` 那一半），**证明不重复**。
消费者重编：`SimplicialPairImage` exit=0（9.7 秒）、`VertexChartTransport` exit=0（9.1 秒）、
`VertexBranchInput` exit=0（10.5 秒），均零 warning。

**第二件事不必做：显式径向版早已存在**
授权是去加强 `exists_isPLHomeomorphOn_geometricLink_of_isSubdivision`（9 个消费者，改了必炸）。
先 grep，结果树里**已经有**显式映射版：
`isPLHomeomorphOn_simplicialMap_radialProj_geometricLink_of_isSubdivision`
（`LinkHeightSubdivision.lean:83`），直接给出
`IsPLHomeomorphOn (simplicialMap (link K' {p}) (radialProj p (link K {p}).space))
 (link K' {p}).space (link K {p}).space`。
底层的 `exists_isPLHomeomorphOn_of_radial`（`RadialProjection.lean:315`）确实把映射藏在 `∃ f` 里
（`:323` 处 `refine ⟨simplicialMap L' (radialProj p L.space), ?_⟩`），
但 `LinkHeightSubdivision` 已经把它接出来了。**一个消费者都不用动。**

**更正 §19.129 自己的论证：径向并不逐点径向。**
§19.129 我写"第一跳是径向投影，沿 `p` 出发的射线走，所以保锥"。**读了构造之后，这是错的。**
实际映射是 `simplicialMap (link K' {p}) (radialProj p …)`，即 radialProj 在**顶点处**取值、
再在每个面上**仿射插值**。`radialProj p S w = p + radialRatio p S w • (w - p)`（`Cone.lean:77`）
对**顶点**确实沿射线，但面内一点的像是若干"已径向投影的顶点"的凸组合，
一般**不在**过原像的那条射线上。所以"射线保锥"这条对该映射不成立，
§19.129 里"第 2 块砖 = 接上 `image_coneSet_of_radial`"的路线**按原样走不通**。
锥不是凸集，仿射插值也救不回来。这一条与 §19.127 同类：不是夹带结论，是论证本身基于名字而非构造。

**因此装配的剩余义务要重写**：第二次应用所需的
`(link N₁ {0}).space ∩ {q | q.2.2 = 0} = {a₁, b₁}` 与两侧性，
既不能靠"径向保锥"从源侧搬（上面已否），也不能靠 `hfiber` 造（§19.127 已否）。
剩下的诚实选项有两条，都还没验证：
(a) 把第二次应用所需的四条**直接写成关于转写后对象的假设**，
    定理拆成 T1（产出 `K₁ M₁ N₁ φ₁` 与结构性质）与 T2（由配置加四条产出双片图卡）。
    代价是 T2 的假设谈的是构造出来的对象，可检查性差一些，但不夹带结论也不空转。
(b) 找一条"连接同胚把一个片的连接交线送到另一个片的连接交线"的定理，
    即 LinkPair 那一层的配对陈述——回到 §19.122 说过的"两个圆的连接配对"，树里没有。
**不估行数。**

检查见上；`AuditF273.lean` 三项仅 `propext`、`Classical.choice`、`Quot.sound`。
下一审计文件 `AuditF274.lean`。

### 19.131 T1 与 T2 都已闭合；并附 T2 四条假设的生产者义务

**先补一条自查**：本轮差点发出一条**错误的更正**。我用
`grep -rn "affine_comp" … | head -4` 看到四条全是 Ricci flow 的 `rfs_width_affine_comparison`
（子串匹配），就准备宣布"`affine_comp` 在 PL 树里不存在、§19.126 的说法有误"。
去掉 `head` 重查：**57 条命中**，`IsPiecewiseAffineOn.affine_comp` 就在
`GeneralPosition.lean:25`，§19.126 的说法是对的。
**教训：截断过的搜索结果不是搜索结果。** 与协调者"非零退出当作没信息"同一条，
再加一句：`| head -n` 也会把信息截没，先数命中数再看内容。

**T1（`VertexChartTransport.lean`）**
`exists_simplicialComplex_triple_image_closedStar_of_isPiecewiseAffineOn`：
由 `U ∈ 𝓝 p` 的图卡把 `(K, M, N)` 缩进图卡定义域再一起搬过去，产出
`R`（`K` 的细分，`closedStar R p ⊆ U`）与 `K₁ M₁ N₁`，交付三条 `Finite`、
`M₁.faces ⊆ K₁.faces`、`N₁.faces ⊆ K₁.faces`、`{h p}` 在两者面里、三条空间等式、
以及 `M`、`N` 各自的连接同胚。二元版现在是它的推论，证明不重复。

**T2（`VertexBranchInput.lean`）**
`exists_linearEquiv_normalForm_two_sheets`：在 `ℝ × ℝ × ℝ` 里，取第三坐标泛函
`(ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))`，
由转写后的 `(K₁, N₁, q)` 加四条连接层数据产出图卡，结论两条：
`y ∈ N₁.space → (L (h y)).2.2 = 0` 与 `y.2.2 = q.2.2 → (L (h y)).2.1 = 0`，
即**第二张片与第一张片被拉直后所在的平面同时被送到两张坐标平面**。
`{x | ℓ x = ℓ q}` 与 `{x | x.2.2 = q.2.2}` 定义相等，`exact` 直接过。

**T2 的假设逐条判定（标注 + 可满足性 + 是否夹带结论）**
1. `[Finite K₁.faces] [Finite N₁.faces]` —— 构造性副产品；T1 交付；可满足。
2. `hN : N₁.faces ⊆ K₁.faces` —— 构造性副产品；T1 交付；可满足。
3. `hq : {q} ∈ N₁.faces` —— 构造性副产品；T1 交付（`q = φ₁ p`）；可满足。
4. `hK : K₁.space ∈ 𝓝 q` —— 构造性副产品；§19.127 的
   `image_closedStar_mem_nhds_of_isPLHomeomorphOn` 加 T1 的 `K₁.space = φ₁ '' closedStar R p`
   即可；可满足。
5. `hlinkN : IsPLSphere 1 (link N₁ {q}).space` —— 几何输入，但**可由源侧搬**：
   T1 给出连接同胚，配 `IsPLSphere.of_isPLHomeomorphOn`；对圆盘状的片可满足。
6. `hab` + `hlevel : (link N₁ {q}).space ∩ {x | x.2.2 = q.2.2} = {a, b}` —— **几何输入**。
   对真横截的分支可满足：两张片沿一条过 `p` 的弧相交，该弧在 `p` 处的连接正是两点。
7. `hpos`/`hneg` —— **几何输入**（第二张片的连接在第一张片的平面两侧都有点）；
   §19.123 已证与第 6 条独立；对真横截的分支可满足。
没有一条夹带结论：结论是 PL 图卡，假设只谈连接、截面与有限性。
第 1–4 条是构造性的，第 5 条可搬，**真正要由几何生产的只有第 6、7 两条**。

**生产者义务（每条一行，供后续车道直接执行）**
- 第 5 条：给出源侧 `IsPLSphere 1 (link N {p}).space`，沿 T1 的连接同胚用
  `IsPLSphere.of_isPLHomeomorphOn` 推过去。
- 第 6 条：给出 `link N₁ {q}` 上第三坐标等于 `q.2.2` 的两个不同点，并证明再无其它；
  等价地证 `encard = 2`，为此只需给出源侧集合 `(link N {p}).space ∩ M.space`
  （分支的两个方向）到它的一个双射。
- 第 7 条：给出 `link N₁ {q}` 上第三坐标分别大于、小于 `q.2.2` 的各一点；
  由 §19.123 的星→连接归约，只需给出 `closedStar N₁ q` 在平面两侧的各一点。
- 第 4 条：把 §19.127 的 `image_closedStar_mem_nhds_of_isPLHomeomorphOn` 用在第一张图卡上
  （`U` 取其定义域），再用 T1 的 `K₁.space = φ₁ '' closedStar R p` 改写。

**尚未接线的一步**：T1 与 T2 之间要把第一张图卡 `φ₁ = L₁ ∘ h₁` 交给 T1，
需要 `IsPiecewiseAffineOn φ₁ U`（`IsPiecewiseAffineOn.affine_comp`，`GeneralPosition.lean:25`）
与 `InjOn φ₁ U`（`h₁` 单射加 `L₁` 单射）；两条都有现成工具，**但本轮未写**。
把 T2 的结论沿 `φ₁` 拉回 `E` 还要一次复合（`IsPLHomeomorphOn.trans`、
`IsPiecewiseAffineOn.mono` 对开集，`PiecewiseAffine.lean:208`）。**不估行数。**

检查 `VertexChartTransport` exit=0（10 秒）、`VertexBranchInput` exit=0（10.7 秒），均零 warning；
`AuditF274.lean` 三项仅 `propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF275.lean`。

### 19.132 接线的两块砖已闭合；并判定假设 6、7 无法由 germ 数据推出（会循环）

**本轮闭合两条**（`VertexChartTransport.lean`）
- `IsPLHomeomorphOn.restrict_isOpen`：把 PL 同胚限制到**开**子集。
  树里原有的 `IsPLHomeomorphOn.restrict`（`PLImage.lean:168`）要求限制到**多面体**，
  图卡定义域是开集不是多面体，所以那条用不上。新写的三条分量各自成立：
  `BijOn` 用 `InjOn.bijOn_image`，正向 PL 用 `IsPiecewiseAffineOn.mono`（`PiecewiseAffine.lean:208`，
  它收的正是 `IsOpen`），逆向 PL 用同一个 `mono` 再 `congr`——
  因为 `Function.invFunOn f P₀` 与 `Function.invFunOn f P` 在 `f '' P₀` 上逐点相等
  （两边都由 `InjOn.leftInvOn_invFunOn` 送回同一个原像）。
- `isPiecewiseAffineOn_injOn_linearEquiv_comp`：由 `IsPLHomeomorphOn h U V` 与线性同构 `L`
  给出 `IsPiecewiseAffineOn (fun y => L (h y)) U` 与 `InjOn (fun y => L (h y)) U`，
  即**第一张图卡 `φ₁ = L₁ ∘ h₁` 可以喂给 T1** 了。

**坑（第三次同一形状）**：本来想用 `IsPiecewiseAffineOn.affine_comp`（`GeneralPosition.lean:25`），
报错 `The environment does not contain 'Function.affine_comp'`——
`IsPiecewiseAffineOn` 是 `def`，展开成 `∀ x ∈ u, …`，**名字找不到时点记号就去展开后的类型上找**。
根因是 `VertexChartTransport` 没 import `GeneralPosition`（很重，不值得为一条引理引进来）。
改用底层的 `IsPiecewiseAffineOn.comp`（`PiecewiseAffine.lean:226`）配
`isPiecewiseAffineOn_of_affine`（`:173`）与 `rw [preimage_univ, inter_univ]` 即可。
**与 §19.124 的 `IsSubdivision.singleton_mem` 是同一个诊断：点记号失败先查 import，不是先查名字。**

**判定：假设 6、7 不能由 germ 数据消掉，会循环。**
协调者要求试试从 `HasPLCrossingAt` 直接推出 6、7。**推不出，且理由是结构性的。**
6、7 的源侧版本是"`link N {p}` 与 `M.space` 恰交于两点"和"`link N {p}` 在 `M` 两侧都有点"，
即**第二张片相对第一张片的横截性**。手上可用的 germ 数据只有第一张图卡，
而它来自 `HasPLCrossingAt M.space {x | ℓ x = ℓ p} p`——**整条陈述里没有 `N`**。
能给出 6、7 的 germ 陈述是 `HasPLCrossingAt N.space M.space p`，
但那正是本条链要构造的结论，拿它当假设就是循环。
所以 6、7 是**真正的新几何输入**，必须由消费者（弧链）在每个顶点供给。这与 §19.123
证过的"`hpos`/`hneg` 不能由计数推出"是同一类独立性，只是换到了两片之间。

**弧链在每个顶点要供给的，确切就是两条**（第一张片的数据由弧链自己的 `ℓ` 给）：
- `(SimplicialComplex.geometricLink N {p}).space ∩ M.space = {a, b}` 且 `a ≠ b`；
- `link N {p}` 在 `M` 的两侧各有一点。
其余（`Finite`、面包含、`{q} ∈ N₁.faces`、`K₁.space ∈ 𝓝 q`、`hlinkN`）全部由 T1 与
§19.127 的邻域引理交付，**不是几何债**。

**最后一步（未写）**：把 T2 的结论沿 `φ₁` 拉回 `E`，还差一条
`isPLHomeomorphOn_linearEquiv`（`L` 在开集上本身是 PL 同胚），
再用 `IsPLHomeomorphOn.trans` 与本轮的 `restrict_isOpen` 把
`Φ = L₂ ∘ h₂ ∘ φ₁` 装成开集上的 PL 同胚；germ 条款用
`Filter.Tendsto.eventually` 沿 `φ₁` 拉回，`y ∈ N.space → φ₁ y ∈ N₁.space` 用
`closedStar_mem_nhdsWithin`（`Star.lean:15`）加 T1 的空间等式。
`L` 的开映射性质要走 `LinearEquiv.toContinuousLinearEquiv`（有限维），**本轮未验证该名字是否存在**。

检查 `VertexChartTransport` exit=0（9.6 秒）、`VertexBranchInput` exit=0（10.3 秒），均零 warning；
`AuditF275.lean` 两项仅 `propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF276.lean`。

### 19.133 拉回已闭合；单顶点层的五条链条齐备，接口契约只剩两条

**验证了协调者给的名字**：`LinearEquiv.toContinuousLinearEquiv` 在本树可直接用
（`VertexChartTransport` 现有 import 就够，不必显式加），
`L.toContinuousLinearEquiv.toHomeomorph.isOpenMap` 给出线性同构的开映射性质。

**本轮闭合四条**（全在 `VertexChartTransport.lean`）
- `IsPLHomeomorphOn.isOpen_image_of_isOpen`：`Q` 开、`P₀ ⊆ P` 开 ⟹ `f '' P₀` 开。
  证法与 §19.127 同一招：`f '' P₀ = Q ∩ Function.invFunOn f P ⁻¹' P₀`，再用逆的
  `ContinuousOn` 与 `ContinuousOn.isOpen_inter_preimage`。
- `isPLHomeomorphOn_linearEquiv`：开集上线性同构本身是 PL 同胚。
  正向用 `isPiecewiseAffineOn_of_affine`，逆向用 `L.symm` 的仿射性加 `congr`
  （`Function.invFunOn (⇑L) V (L x) = L.symm (L x)`），像开用上面的
  `toContinuousLinearEquiv`。
- `exists_isPLHomeomorphOn_comp_two_sheets`：**本轮的正主**。取
  `U₀ = U ∩ φ ⁻¹' U₂`（开，用 `ContinuousOn.isOpen_inter_preimage`），
  用 `restrict_isOpen` 把 `φ`、`h₂` 各自限制到该开集及其像，
  `IsPLHomeomorphOn.trans` 两次接上 `L₂`，得到
  `IsPLHomeomorphOn (fun y => L₂ (h₂ (φ y))) U₀ V₀`；`Φ p = 0` 由 `hφp`、`hh₂0`、`map_zero`；
  germ 条款由 `Filter.Tendsto.eventually`（`htend : Tendsto φ (𝓝 p) (𝓝 0)`，来自
  `ContinuousOn.continuousAt` 加 `← hφp` 改写）沿 `φ` 拉回，再与 `hA`、`hB` 用
  `filter_upwards` 合并。结论两条：
  `y ∈ A → (Φ y).2.1 = 0` 与 `y ∈ B → (Φ y).2.2 = 0`——**两张片同时落在两张坐标平面上**。
- `eventually_mem_image_closedStar_of_mem_space`：`∀ᶠ y in 𝓝 p, y ∈ N.space → φ y ∈ φ '' closedStar N p`。
  由 `closedStar_mem_nhdsWithin`（`Star.lean:15`）加
  `mem_nhdsWithin_iff_exists_mem_nhds_inter`。这条正是上面 `hB` 的生产者，
  配 T1 的 `N₁.space = φ '' closedStar (restrict R N.space) p` 与
  `(restrict R N.space).space = N.space` 即可消掉。

**单顶点层的完整链条（五步，全部已证）**
1. `exists_linearEquiv_normalForm_of_geometricLink_pair`（§19.128）：拉直第一张片 `M`，
   给出 `h₁`、`L₁`、`U`、`V` 与 `y ∈ M.space → (L₁ (h₁ y)).2.2 = 0`。
2. `isPLHomeomorphOn_linearEquiv` + `IsPLHomeomorphOn.trans`：`φ₁ = L₁ ∘ h₁` 是开集上的 PL 同胚；
   若只要 T1 所需的 `IsPiecewiseAffineOn` 与 `InjOn`，用 §19.132 的
   `isPiecewiseAffineOn_injOn_linearEquiv_comp`。
3. `exists_simplicialComplex_triple_image_closedStar_of_isPiecewiseAffineOn`（§19.131 T1）：
   把 `(K, M, N)` 缩进 `U` 再一起搬到 `ℝ × ℝ × ℝ`。
4. `exists_linearEquiv_normalForm_two_sheets`（§19.131 T2）：在像一侧拉直第二张片与第一张片所在平面。
5. `exists_isPLHomeomorphOn_comp_two_sheets`（本轮）：把 4 的结论沿 `φ₁` 拉回 `E`。

**接口契约（弧链在每个顶点必须供给的，只有两条，其余全由链条内部交付）**
- `(SimplicialComplex.geometricLink N {p}).space ∩ M.space = {a, b}` 且 `a ≠ b`；
- `link N {p}` 在 `M` 的两侧各有一点。
§19.132 已判定这两条**不能**由 germ 数据推出（会循环），它们是第二张片相对第一张片的横截性。

检查 `VertexChartTransport` exit=0（10.5 秒）、`VertexBranchInput` exit=0（11.6 秒），均零 warning；
`AuditF276.lean` 四项仅 `propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF277.lean`。

### 19.134 单顶点定理已打包；**更正 §19.133 的契约位置**；链层需要 ZMod 2 相容选择

**必须先更正一条我自己发给协调者、并已转给 H 的说法。**
§19.133 写"契约是源侧两条：`(link N {p}).space ∩ M.space = {a, b}` 与 `link N {p}` 在 `M` 两侧有点"。
**这条没有被证实。** 打包定理里契约实际落在**像侧**：
`(link N₁ {φ p}).space ∩ {x | x.2.2 = (φ p).2.2} = {a₁, b₁}` 与像侧的两侧性。
源侧 ⟹ 像侧的转换需要两步：
(i) 用第一张图卡的 **iff** 形把 `{x.2.2 = 0}` 与 `M₁.space` 在小邻域上认同——这一步可做；
(ii) 用 T1 的连接同胚把 `link N {p} ∩ M.space` 送到 `link N₁ {φ p} ∩ M₁.space`——
**这一步是 §19.130 留下的未决问题**：转写的第一跳是
`simplicialMap (link N' {p}) (radialProj p …)`，只在顶点处径向，面内是插值，
所以"径向保锥"的论证不成立；我**没有**证明它为假，只是没有证明它为真。
可能的修法是绕开那个单纯映射、直接用 `radialProj` 本身在两个交集上建双射
（`M.space` 收缩成闭星之后是 `p` 处的锥），**未验证**。
在此之前，**H 应按像侧契约准备**，即在 T1 交付的 `N₁` 上给两条；
若 (ii) 后来落地，源侧形式再作为推论提供。抱歉给出过早的接口形状。

**闭合：单顶点定理已打包成一条**（新模块 `VertexBranchChartPair.lean`）
`exists_chart_two_sheets_of_transverse_vertex`：输入第一张片的几何数据
（`hn`、`hM`、`hN`、`hpM`、`hpN`、`hK`、`ℓ`、`hℓ`、`hlinkM`、`hlinkN`、`hab`、`hlevel`、
`hposM`、`hnegM`），产出转写后的配置 `(K₁, N₁, φ)` 与全部结构性条款
（`Finite` 两条、`N₁.faces ⊆ K₁.faces`、`φ p = 0`、`{φ p} ∈ N₁.faces`、
`K₁.space ∈ 𝓝 (φ p)`、`IsPLSphere 1 (link N₁ {φ p}).space`），
再加一条蕴含：给了像侧两条契约就产出
`IsPLHomeomorphOn Ψ U₀ V₀`、`Ψ p = 0` 与
`∀ᶠ y in 𝓝 p, (y ∈ M.space → (Ψ y).2.1 = 0) ∧ (y ∈ N.space → (Ψ y).2.2 = 0)`。
**H 现在只需实例化这一条**，不必再走五步。
（顺带给 T1 的结论补上 `R.faces.Finite`，`image_closedStar_mem_nhds_of_isPLHomeomorphOn` 要它。）

**链层的判定：仅有"相邻在公共连接上一致"不够，ZMod 2 侧选择会回来。**
设相邻顶点 `p_i`、`p_{i+1}` 的图卡为 `Φ_i`、`Φ_{i+1}`。重叠上过渡映射
`Φ_{i+1} ∘ Φ_i⁻¹` 是把 `{z = 0}` 与 `{y = 0}` 各自保住的 PL 同胚；
在线性层，§19.120 的 `mapsTo_planes_iff_exists_coeff` 已经算清楚：这样的映射恰是三角形
`(αx + βy + γz, δy, εz)`，而 **`δ`、`ε` 的正负是自由的**——
`δ < 0` 翻转第一张片的两半，`ε < 0` 翻转第二张片的两半。
于是每条重叠带一个 `ZMod 2 × ZMod 2` 的符号，沿分支弧走一圈的乘积就是一个单值性类；
它非零时**不存在**统一的单张图卡。所以链层假设必须包含**相容的侧选择**，
不能只要求连接一致。树里已有对应机器：`exists_sideChoice_of_chain`（`BranchSignChain.lean:13`），
消费点在 `CocycleMonodromy.lean:197`。
**结论：§45 的 ZMod 2 侧选择确实回来了，而且落在"图卡黏合"这一层，不只是 E3 最初放的位置。**

**链层陈述所需的假设（供 H 的链归纳对照，尚未写成 Lean）**
1. 有限顶点族 `p_i`，每个带一张本节的顶点图卡；
2. 相邻图卡在公共连接上一致；
3. **相容的侧选择**（第 2 条不蕴含它，见上）；
4. **覆盖级条款**：每张 `Φ_i.source` 不碰第三张片——这是**族**的性质不是单张图卡的性质，
   §19.115 里写成 `doublePointSet g D.domain = doublePointSet D D.domain \ S`，
   必须作为族假设给出；
5. `S ⊆ ⋃ Φ_i.source ⊆ W`。
产出 `OpenPartialHomeomorph M (ℝ × ℝ × ℝ)`，两向 PL，两片分别进
`{p.2.2 = 0}` 与 `{p.2.1 = 0}`。**不估行数。**

检查 `VertexChartTransport` exit=0（10.1 秒）、`VertexBranchChartPair` exit=0（11.6 秒），均零 warning；
`AuditF277.lean` 两项仅 `propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF278.lean`。

### 19.135 (ii) 的旁路失败，原因比预期更靠前：源侧契约的**形状**就不对

**结论**：`radialProj` 旁路不能闭合 (ii)，而且失败点**不在映射的形式**上
（§19.130 与本轮任务都假定问题是"单纯映射插值、不逐点径向"）。真正的问题是
**源侧契约本身是"半径相关"的陈述**，换半径就不成立，任何双射都救不了。

**诊断**
- 源侧 `(link N {p}).space ∩ M.space = {a, b}`：`M.space` 缩成闭星之后是 `p` 处的
  **有界**锥（`closedStar M p = coneSet p (link M {p})`，§19.125）。
  一个 `link N {p}` 上的点落不落在 `M.space` 里，取决于 `M` 沿那条射线伸多远——
  即方向 `d` 上要 `r_N(d) ≤ r_M(d)`。细分把连接挪到**另一个半径**，
  这个条件就可能翻转，两边的交集**基数都可能不同**。所以不是"找不到双射"，
  而是**两个集合本来就未必等势**。
- 像侧 `(link N₁ {q}).space ∩ {x | x.2.2 = q.2.2} = {a₁, b₁}`：
  `{x.2.2 = 0}` 是线性平面，即 `0` 处的**无界**锥。
  连接上的点落不落在里面**只取决于方向**，与半径无关，径向重参数化下保持。

于是：**像侧形式不只是"我能证的那个"，它是内在正确的形状；
§19.133 的源侧形式是形状错了，不只是未证。** 这比 §19.134 的更正更强一层。

**核对过的工具，确认都不适用**（无需向 H 索要变体）
- `radialProj_mem`（`Cone.lean:86`）只保证"射线与 `S` 相交则投影落在 `S` 内"，
  对"是否仍在另一个有界锥 `M.space` 内"一无所知。
- `IsRadiallyInjective.radialProj_eq_self`（`:114`）只在点已在 `S` 内时为恒等。
- H 的 `image_coneSet_of_radial`（`ConePairExtension.lean:38`）的前提 `hrad` 要求
  `g (p + s • (z - p)) = q + s • (f z - q)` 对 `s ∈ [0,1]`，
  说的是**锥映到锥**，不是"换半径后仍在同一个有界锥内"。**不需要 H 提供变体。**

**因此接口定论**
- **像侧契约是首要接口**，即 §19.134 打包定理里那两条，H 按它准备。
- 源侧若要有一个形式，正确的写法是**半径无关的 germ 条件**：
  `∀ᶠ y in 𝓝 p, y ∈ M.space ∩ N.space ↔ y ∈ A`，`A` 是过 `p` 的弧，
  即"两张片在 `p` 附近交成一条弧"。germ 条件沿 `φ`（`p` 附近的同胚）**可以搬**，
  而像侧第一张片已是真平面，链接条件在那边是半径无关的，可以从 germ 条件推出。
  这条路线**未验证**，但它是唯一形状正确的候选；**不估行数**。

**未做**：链层的五条假设尚未写成 Lean。它依赖上面接口形状的最终决定
（若改用 germ 形式的源侧契约，顶点定理的假设列表要跟着改），
所以本轮不写，等接口定下来再一次成型，避免写两遍。

本轮无 Lean 改动，按 `AGENTS.md` §1 作纯文档提交。下一审计文件 `AuditF278.lean`。

### 19.136 链层陈述已闭合（§19.115 的图卡条款）；germ 入口的确切缺口

**本轮闭合两条**（新模块 `BranchChainChart.lean`）
- `isPLHomeomorphOn_iUnion_of_forall`：若 `Φ` 在每个开集 `U i` 上是到 `V i` 的 PL 同胚，
  且 `Φ` 在 `⋃ U i` 上单射，则 `IsPLHomeomorphOn Φ (⋃ i, U i) (⋃ i, V i)`。
  正、逆两向都用 `isPiecewiseAffineOn_of_locally`（`PiecewiseAffine.lean:197`）局部化：
  正向取 `v := U i`，逆向取 `v := V i`（关键是目标写成 `⋃ V i` 而不是像集，
  这样 `(⋃ V) ∩ V i = V i` 是开的，`mono` 才能用）；
  逆向还要证 `Function.invFunOn Φ (⋃ U) = Function.invFunOn Φ (U i)` 在 `V i` 上逐点相等，
  由两边都是 `w` 在 `⋃ U` 中的原像加 `hinj` 得到。
- `exists_chart_branch_chain`：**§19.115 的图卡条款**。产出开集 `O = ⋃ U i` 与
  `IsPLHomeomorphOn Φ O (⋃ i, V i)`，满足 `S ⊆ O ⊆ W`、`O ∩ T = ∅`（无第三张片）、
  `∀ y ∈ O, y ∈ A → (Φ y).2.2 = 0`、`∀ y ∈ O, y ∈ B → (Φ y).2.1 = 0`。

**五条假设如何落在这条定理里（供 H 对照）**
1. 顶点族 → `U : ι → Set E` 与每个 `hPL i`。
2. 相邻在公共连接上一致 → **抽象成"存在单一的 `Φ`"**。连接一致是生产者拼出同一个 `Φ` 的手段；
   在本层正确的写法就是一个函数在每片上都是 PL 同胚，不必把拼接过程写进假设。
3. 相容侧选择 → 落在 `hA`、`hB` 上：**每个 `i` 都把 `A` 送进同一张平面**。
   若侧选择不相容，就无法对所有 `i` 同时给出这两条，正是 §19.134 算出的
   `ZMod 2 × ZMod 2` 自由度被固定下来的地方。
4. 覆盖级无第三片 → `hthird : ∀ i, U i ∩ T = ∅`，结论里 `O ∩ T = ∅` 由 `iUnion_inter` 得到。
5. `S ⊆ ⋃ U i ⊆ W` → `hSU`、`hUW` 直接进出。
**外加一条必须明说的假设**：`hinj : InjOn Φ (⋃ i, U i)`。
逐片单射**不蕴含**整体单射（两个相距很远的片可以撞在一起），
所以这是生产者要另外交付的一条，不是 bookkeeping。它正是"这一族图卡真的拼成一张图卡"的实质内容。

**输出形式**：交付的是 `IsPLHomeomorphOn`，不是 `OpenPartialHomeomorph`。
本树的下游（§19.113/19.114 的滑动层）收的就是 `IsPLHomeomorphOn` 与 germ 条款，
所以这是可直接消费的形式；要 `OpenPartialHomeomorph` 需另加一层打包（两向连续 + 源/靶开），
**本轮未做**，按需再说。

**第 2 项（germ 入口）未做，确切缺口如下**
候选 `∀ᶠ y in 𝓝 p, y ∈ M.space ∩ N.space ↔ y ∈ A`（`A` 是过 `p` 的弧）形状正确：
germ 沿 `φ` 可搬，像侧第一张片是真平面、半径无关。搬过去得到
`∀ᶠ z in 𝓝 0, z ∈ M₁.space ∩ N₁.space ↔ z ∈ φ '' A`。
**剩下的一步**是从"`M₁ ∩ N₁` 在 `q` 附近是一条弧"推出
`(link N₁ {q}).space ∩ {x | x.2.2 = 0}` 恰两点：
先用第一张图卡的 iff 把平面换成 `M₁.space`，于是该集合落在弧上；
再需要"PL 1-球体内点处的连接是 0-球面（两点）"。
树里最接近的是 `isPLSphere_or_isPLBall_geometricLink_of_isPLBall`（`BallSphereLink.lean:151`），
**但它给的是析取**，要额外排除"`q` 是弧的端点"那一支——
而 `q` 是分支内点，这一支应当可排除，只是要写。**不估行数。**

检查 `BranchChainChart` exit=0（10.9 秒）、零 warning；`AuditF278.lean` 两项仅
`propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF279.lean`。

### 19.137 1-球体版链接截面已闭合；"排除端点"这一步是**免费的**，不需要内点论证

**grep 先行的收获**（协调者要求查"树里有没有区分 1-球体的内点与端点"）
不需要那种区分。真正有用的是两条把低维球/球面**完全刻画**的引理：
`isPLBall_zero_iff`（`GeneralPosition.lean:655`）：`IsPLBall 0 P ↔ ∃ p, P = {p}`；
`isPLSphere_zero_iff`（`:710`）：`IsPLSphere 0 P ↔ ∃ a b, a ≠ b ∧ P = {a, b}`。
于是 `isPLSphere_or_isPLBall_geometricLink_of_isPLBall`（`BallSphereLink.lean:151`）的析取
两支都给出**具体的集合**：两点或一点。

**因此"排除球体那一支"根本不必做。** 两支的 `encard` 分别是 2 与 1，都 `≤ 2`；
而一旦另外知道该集合含有两个**不同**的点，单点那一支自动矛盾。
所以协调者设想的"`q` 是弧的内点 ⟹ 排除端点情形"这条论证**不需要写**——
是否内点这件事根本不用谈。

**本轮闭合两条**（`VertexBranchSection.lean`）
- `encard_geometricLink_fiber_le_two_of_isPLBall_one`：若 `K.space ∩ {x | ℓ x = ℓ p}`
  是 PL **1-球体**（弧），则 `((link K {p}).space ∩ {x | ℓ x = ℓ p}).encard ≤ 2`。
  证法与 `encard_geometricLink_fiber_of_isPLSphere_one`（`HeightLevelLink.lean:75`）同构，
  只是把结尾的 `isPLSphere_geometricLink_of_isPLSphere` 换成上面的析取，两支分别算 encard。
- `geometricLink_fiber_eq_pair_of_isPLBall_one`：再给两个不同的成员 `a`、`b`，
  得 `(link K {p}).space ∩ {x | ℓ x = ℓ p} = {a, b}`。
  用 `Set.Finite.eq_of_subset_of_encard_le`（树里的写法见 `BoundaryLinkGerm.lean:77`）。

**这补上了 §19.127 的那个洞。** §19.127 发现 `hfiber : IsPLSphere 1 (…)` 对圆盘状的片恒假；
现在有了 1-**球体**版，弧状截面（正是闭星被平面截出来的形状）可以直接用。
消费者要给的从"整片截线是闭曲线"降成"整片截线是一条弧 + 两个不同的交点"，后者真实可满足。

**germ 入口的剩余部分（未做）**
`∀ᶠ y in 𝓝 p, y ∈ M.space ∩ N.space ↔ y ∈ A` 现在离像侧契约只差把
`link N₁ {q} ∩ {x.2.2 = 0}` 的两个成员找出来：由上面的定理，只要
`M₁.space ∩ N₁.space ∩ {x.2.2 = 0}` 是弧（即 germ 条件搬过去）并给出弧与连接的两个交点即可。
"两个交点"就是弧在 `q` 两侧各穿出连接一次，属于**第二条 germ 条件**（`N` 在 `M` 两侧都有点）
的内容，与 §19.123 判定的独立性一致——**germ 入口需要两条 germ 条件，不是一条**。
这一点值得记下：单靠"两片交成一条弧"给不出两侧性。**不估行数。**

**`OpenPartialHomeomorph` 包装：不短，未做。**
要造结构体需要两向连续（可由 `IsPiecewiseAffineOn.continuousOn` 给）、
`source`/`target` 开、`toFun`/`invFun` 互逆并且 `map_source`/`map_target` 齐全，
还要把 `Function.invFunOn` 换成结构体要求的 `invFun` 形式。不是一两行。
下游滑动层（§19.113/19.114）收 `IsPLHomeomorphOn` 加 germ 条款，不需要它，故按协调者的话略过。

检查 `VertexBranchSection` exit=0（11.3 秒）、`VertexBranchInput` exit=0（11.1 秒）、
`VertexBranchChartPair` exit=0（11.3 秒）、`BranchChainChart` exit=0（10.9 秒），均零 warning；
`AuditF279.lean` 两项仅 `propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF280.lean`。

### 19.138 成对 germ 入口与 `OpenPartialHomeomorph` 包装；并记一次**我自己违反 grep 规则**

**先记自己的错。** 写 `OpenPartialHomeomorph` 包装时我**没有先 grep 新名字**就直接定义了
`IsPLHomeomorphOn.toOpenPartialHomeomorph`，编译报"已声明"。
树里早有一条，在 `PLHomeomorphOpen.lean:10`，**逐字段与我写的一模一样，而且更一般**
（异型 `E → F`，我写的是 `E → ℝ × ℝ × ℝ`）。已删掉重复、改为 import 那个模块。
这正是本车道从 §19.126 起一直在提醒别人的那条规则，今天自己破了一次；
教训是**规则对新写的 `def` 同样适用，不只是对"以为缺失的定理"**。

**本轮闭合两条**
- `exists_linearEquiv_normalForm_two_sheets_of_arc_section`（`VertexBranchInput.lean`）：
  **成对 germ 入口**。把像侧契约里的集合等式 `link ∩ 平面 = {a, b}` 换成
  **一条弧条件 + 两个不同的交点**：
  `harc : IsPLBall 1 (N₁.space ∩ {x | x.2.2 = q.2.2})`（第二张片被第一张片截成一条弧）、
  `hab`、`ha`、`hb`（连接与平面的两个不同交点），再加原有的 `hpos`/`hneg`。
  由 §19.137 的 `geometricLink_fiber_eq_pair_of_isPLBall_one` 造出 `hlevel`，
  再喂 `exists_linearEquiv_normalForm_two_sheets`。
- `exists_openPartialHomeomorph_branch_chain`（`BranchChainChart.lean`）：
  把 §19.136 链层定理的输出包装成 `OpenPartialHomeomorph E (ℝ × ℝ × ℝ)`，
  交付 `S ⊆ e.source`、`e.source ⊆ W`、`e.source ∩ T = ∅`、
  `IsPiecewiseAffineOn e e.source`、`IsPiecewiseAffineOn e.symm e.target`、
  两条片条款。**这就是 §19.115 结论的原始形状**，与 §44 的输出条款对齐。
  用现成的 `IsPLHomeomorphOn.toOpenPartialHomeomorph`，一行；
  唯一要注意的是 `e.source ∩ T = ∅` 那条要先 `change (⋃ i, U i) ∩ T = ∅`
  才能 `rw [iUnion_inter]`（`.source` 是定义相等但不是语法相等）。

**必须显式记下的独立性（协调者要求，防止以后被默认掉）**
"两张片交成一条弧"**不蕴含**"第二张片在第一张片两侧都有点"。
前者只说交集的形状，后者说 `N` 真的穿过 `M`；`N` 完全落在 `M` 一侧、
只沿一条弧贴着它，同样满足弧条件。所以 germ 入口**必须是两条**：
`harc`（弧）与 `hpos`/`hneg`（两侧）。
这与 §19.123 判定的"`hpos`/`hneg` 不能由计数推出"是同一条独立性，只是升了一层：
那里是单片相对平面，这里是两片相对彼此。
同理，`ha`/`hb`（连接与平面的两个交点）也**不能**由 `hpos`/`hneg` 直接得到——
从"两侧各有一点"到"中间穿过平面两次"需要连接上的连通性论证（IVT 型），
本轮未做，故 `ha`/`hb` 仍是入口的显式输入。

检查 `VertexBranchInput` exit=0（11.4 秒）、`BranchChainChart` exit=0（11.2 秒），均零 warning；
`AuditF280.lean` 两项仅 `propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF281.lean`。

### 19.139 第二条独立性闭合：两侧性现在**蕴含**两个交点；germ 入口由四条降到两条

**grep 先行：两个圈层各出一半**
- `CircleHeightSection.lean` 的 `isPLSphere_one_height_section_ne_singleton`（`:41`）
  已经把"圆与水平面不只交一点"的论证写好了，用的是
  `IsPLSphere.isConnected_sdiff_singleton_one`（`CircleIntersection.lean:12`）加
  `IsPreconnected.intermediate_value`。**但它带一条 `havoid`（没有顶点恰好落在水平面上）**，
  因为它要先从一个截点反推出两侧的点。
- 我的情形反过来：**两侧的点是已知的**，所以 `havoid` 那一步整个不需要。
- 缺的另一半是"PL 1-球面的空间连通"，在 `IsPLSphere.isConnected_one`
  （`CurveInclusion.lean:129`）。

**本轮闭合两条**（`VertexBranchInput.lean`）
- `exists_pair_height_section_of_isPLSphere_one`：`S` 是 PL 1-球面、`ℓ` 连续、
  `S` 上有 `ℓ < r` 与 `ℓ > r` 的点 ⟹ `S ∩ {ℓ = r}` 含**两个不同的点**。
  两次 IVT：第一次在 `S` 上（`isConnected_one`）得一点 `z`；
  第二次在 `S \ {z}` 上（`isConnected_sdiff_singleton_one`）得第二点 `w ≠ z`，
  两次都用同一对两侧点。**不需要 `havoid`。**
- `exists_linearEquiv_normalForm_two_sheets_of_arc_section` 重写：
  假设由 §19.138 的 `harc, hab, ha, hb, hpos, hneg` **六条降为 `harc, hpos, hneg` 三条**
  （`hab`/`ha`/`hb` 由上面的引理造出）。
  加上结构性的 `hlinkN`，**真正的几何输入只剩两条**：
  `harc`（两片交成一条弧）与 `hpos`/`hneg`（第二片在第一片两侧都有点）。

**两条独立性的最终状态（更新 §19.138）**
1. 弧条件 **不蕴含** 两侧性——仍然独立，仍是两条输入。§19.138 的判定不变。
2. 两侧性 **蕴含** 两个交点——**本轮闭合**，不再是独立输入。
   §19.138 里说"需要连通性/IVT 论证，未做"的那一条现在做完了。
所以 germ 入口的最终形状是**两条几何条件**，正是消费者能直接交付的粒度。

检查 `VertexBranchInput` exit=0（11.8 秒）、`VertexBranchChartPair` exit=0（11.3 秒）、
`BranchChainChart` exit=0（10.8 秒），均零 warning；`AuditF281.lean` 两项仅
`propext`、`Classical.choice`、`Quot.sound`。下一审计文件 `AuditF282.lean`。

### 19.140 §19.115 图卡生产者的完整状态（单节；读这一节即可，不必回溯 §19.112–19.139）

#### A. 顶层交付物
`exists_openPartialHomeomorph_branch_chain`（`BranchChainChart.lean`）产出
`e : OpenPartialHomeomorph E (ℝ × ℝ × ℝ)`，交付 §44 的输出条款：
`S ⊆ e.source`、`e.source ⊆ W`、`e.source ∩ T = ∅`、
`IsPiecewiseAffineOn e e.source`、`IsPiecewiseAffineOn e.symm e.target`、
`∀ y ∈ e.source, y ∈ A → (e y).2.2 = 0`、`∀ y ∈ e.source, y ∈ B → (e y).2.1 = 0`。
其内核 `exists_chart_branch_chain` 交付同样条款但用 `IsPLHomeomorphOn`，
下游滑动层（§19.113/19.114）直接收这一形式。

#### B. 链层要求（`exists_openPartialHomeomorph_branch_chain` 的假设）
1. `U : ι → Set E` 开、`V : ι → Set (ℝ × ℝ × ℝ)` 开；
2. **单一函数** `Φ`，对每个 `i` 有 `IsPLHomeomorphOn Φ (U i) (V i)`。
   "相邻图卡在公共连接上一致"是生产者拼出这个 `Φ` 的手段，不是本层的假设形式。
3. `hinj : InjOn Φ (⋃ i, U i)`。**逐片单射不蕴含整体单射**（远处两片可以撞上），
   这是生产者要另外交付的实质条款。
4. `hA`/`hB` 对**每个 `i` 同时成立**。这就是相容侧选择：
   §19.134 算出重叠上的过渡是三角形 `(αx+βy+γz, δy, εz)`、`δ` `ε` 符号自由，
   一族 `ZMod 2 × ZMod 2`；能对所有 `i` 同时写出这两条，等价于侧选择已相容。
   弧上总可解（`exists_sideChoice_of_chain`，`BranchSignChain.lean:13`）。
5. `hthird : ∀ i, U i ∩ T = ∅`（覆盖级，非单张图卡的性质）；
6. `hSU : S ⊆ ⋃ U i`、`hUW : ⋃ U i ⊆ W`。

#### C. 每个顶点要什么（`VertexBranchChartPair.lean`，**2026-09-18 按 §19.143 改成两条**）
- `exists_transcription_of_transverse_vertex`（生产者）：输入第一张片的数据
  `finrank ℝ E = 3`、`M.faces ⊆ K.faces`、`N.faces ⊆ K.faces`、`{p} ∈ M.faces`、`{p} ∈ N.faces`、
  `K.space ∈ 𝓝 p`、`ℓ ≠ 0`、`IsPLSphere 1 (link M {p}).space`、`IsPLSphere 1 (link N {p}).space`、
  `M` 的连接截面对 `{ℓ = ℓ p}` 的两点与两侧性。产出 `∃ K₁ N₁ φ U W`，带全部结构条款
  （有限、`N₁ ⊆ K₁`、`φ p = 0`、`{φ p} ∈ N₁.faces`、`K₁.space ∈ 𝓝 (φ p)`、`link N₁` 是 1-球面）
  以及图卡半边实际要吃的三条：`IsOpen U ∧ p ∈ U ∧ IsOpen W ∧ IsPLHomeomorphOn φ U W`、
  `∀ᶠ y in 𝓝 p, y ∈ M.space → (φ y).2.2 = 0`、`∀ᶠ y in 𝓝 p, y ∈ N.space → φ y ∈ N₁.space`。
- `exists_chart_two_sheets_of_transverse_vertex`（图卡）：`K₁ N₁ φ U W` 是**参数**，上面每一条与
  像侧契约 D 都是**顶层假设**，结论只有图卡
  `∃ U₀ V₀ Ψ, IsOpen U₀ ∧ p ∈ U₀ ∧ IsPLHomeomorphOn Ψ U₀ V₀ ∧ Ψ p = 0 ∧ ∀ᶠ …`。
  两张片只以集合 `A B : Set E` 出现，不要 `DecidableEq`、不要源侧复形。
消费者的用法：先 `obtain` 生产者，再对**拿到手的那个** `N₁` 证 D，最后调图卡定理。

#### D. 像侧契约（**最终接口**，两种等价给法）
- 原始：`(link N₁ {q}).space ∩ {x | x.2.2 = q.2.2} = {a₁, b₁}`、`a₁ ≠ b₁`、两侧性。
- 推荐（`exists_linearEquiv_normalForm_two_sheets_of_arc_section`，`VertexBranchInput.lean`）：
  **两条几何条件**
  1. `harc : IsPLBall 1 (N₁.space ∩ {x | x.2.2 = q.2.2})`——两片交成一条**弧**；
  2. `hpos`/`hneg`——第二片在第一片两侧都有点。
  两个交点由 §19.139 的 `exists_pair_height_section_of_isPLSphere_one` 自动给出。

**为什么契约在像侧而不是源侧**（§19.135，数学结论非工程结论）：
源侧要问"`link N {p}` 上的点是否落在 `closedStar M p`"，那是**有界**锥，
答案依赖 `r_N(d) ≤ r_M(d)`，细分换半径可能翻转，两个交集**未必等势**；
像侧问的是对 `{x.2.2 = 0}`，**无界**线性锥，只依赖方向，径向重参数化下不变。

#### E. 两条独立性（终态）
- 弧条件 **⇏** 两侧性：贴着 `M` 一侧沿弧相切也满足弧条件。仍是两条独立输入。
- 两侧性 **⇒** 两个交点：§19.139 闭合（PL 1-球面连通 + 去一点仍连通，两次 IVT）。

#### F. 还欠谁
**只剩 H 的链构造**：造出满足 B 全部六条的 `(U, V, Φ)`，其中 3.（整体单射）与
4.（相容侧选择）是实质的。顶点层无几何债：C 的生产者输入是标准分支点数据，
D 的两条是真横截性，须由消费者对生产者交出的 `N₁` 证明（H 的星形链已按这个形状消费）；
其余结构条款现在直接写在生产者的结论里，由 T1
（`exists_simplicialComplex_triple_image_closedStar_of_isPiecewiseAffineOn`）与
`image_closedStar_mem_nhds_of_isPLHomeomorphOn` 交付。

### 19.141 本车道其余条目的状态（逐条附证据，非凭记忆）

- **`IsPL 3 3` 环境转写：closed，由 E3 完成。**
  `isPL_conjugateMap` 在 `BranchSlideConjugation.lean:57`（E3 模块）。§19.116 的判断成立，
  本车道不欠。
- **前向滑动的打包（§19.118 记为"未做"）：closed，由 E3 完成。**
  `exists_separated_slide_fwd` 在 `BranchSeparationBoundary.lean:29`（E3 模块）。
- **F5.2：仍 blocked，且障碍是已证定理而非缺口。**
  `not_isVertexMapGeneralInArrangement_of_complete_hyperplane`
  （`ArrangementConstraints.lean:58`）证明：在当前 `hcomplete` 下，
  共面双折情形任何在 B 上固定的 `φ` 都不可能满足通用位置谓词。
  §19.102 列的两条备选路线**都没试过**：
  (a) 用尊重每个受迫子层秩的**分层**通用位置条件替换 `hcomplete`，重证存在性与双点分类；
  (b) 先在图卡中让曲面对目标骨架横截，再对骨架截出的折边用相容的相对移动。
  两条都要先证"曲面各支跨越目标公共面"，**都不是小任务**，属于开放式设计工作而非有界引理。
- **新 F-M2（非紧局部多面体）：done。** `LocallyPolyhedral.lean` 与
  `LocallyPolyhedralImage.lean`（§19.103/19.104），审计干净。
- **§19.115 图卡生产者：顶点层与链层 done，等 H 的链构造**（见 §19.140 F）。

**结论：本车道当前没有既未阻塞又属于有界引理的条目。**
可做的只有 F5.2 的两条备选路线，那是开放式设计，不是本轮该起头的东西。

### 19.142 F5.2 共享前置已闭合：“曲面各支跨越目标公共面”的确切陈述与生产者

#### A. 陈述定案（先定陈述，再证）

§19.102 / §19.141 说两条备选路线都先要“曲面各支跨越目标公共面”。把它写成 Lean 命题时，
**“目标公共面”= 目标里那张公共面所在的仿射超平面**，即一个在该面上取零的仿射泛函 `ℓ : E →ᵃ[ℝ] ℝ`
的零集；**“支”= 曲面沿折边 `s` 的那张片**，也就是 `s` 的两张余面（`s.card = 2` 时是两个三角形）之并；
**“跨越”= 在双点 `x` 附近该支在 `{ℓ > 0}` 与 `{ℓ < 0}` 两侧都有点**，写成本树已有的写法
（`HeightFiberClosure.lean:14` 的 `x ∈ closure (K.space ∩ {y | ℓ y < ℓ x})`）：

```
hpos : x ∈ closure (K.space ∩ {y | 0 < ℓ y})
hneg : x ∈ closure (K.space ∩ {y | ℓ y < 0})
```

要产出的正是 `IsArrangementGeneralFoldPair`（`RelativeNormalForm.lean:180`）里的四条符号条款
`0 < l k aPos`、`l k aNeg < 0`、`0 < l k bPos`、`l k bNeg < 0`，因为
`hasPLCrossingAt_of_two_fold_faces`（`RelativeNormalForm.lean:140`）只吃这个形状。
所以本前置的确切内容是：**“支的两侧性”⟺“该支两个对顶点在 `ℓ` 下异号”**，即
`ℓ a * ℓ b < 0`，并把它打包成 `IsArrangementGeneralFoldPair` 与 `HasPLCrossingAt`。

**为什么不能沿用 §19.100/19.101 的满维结论。** `linearMap_mul_neg_of_distinct_cofaces`
（`CofaceSeparation.lean:10`）要 `vectorSpan ℝ (s : Set E) = LinearMap.ker ℓ`（等号）。
三维中二维曲面的折边 `s.card = 2`，`vectorSpan s` 是直线而 `ker ℓ.linear` 是平面，等号不可能成立；
`exists_linearMap_separating_cofaces`（`AffineOrientation.lean:184`）只给“存在某张含 `s` 的超平面分开两余面”，
与指定的 `ℓ` 不成比例，推不出符号。这正是 §19.100 末句“不能把满维条件直接套在三维中的二维曲面上”。

**陈述不能再弱。** 去掉两侧性假设后结论为假：§16.2 的坐标反例（`z = |x|` 与 `z = 2|x|` 沿 y 轴折叠）
中取 `ℓ = z`，两个对顶点都有 `ℓ > 0`，`ℓ a * ℓ b > 0`，而该支确实不跨越 `{z = 0}`。
本层同时证了反方向，所以两侧性正好是充要条件，两条路线都不可能需要比它更弱或更强的输入。

#### B. 已闭合的声明（`FoldPlaneCrossing.lean`，新文件）

- `exists_nonneg_apply_eq_of_mem_linearHalfSpace`、`pos_or_pos_of_mem_foldedPlane`、
  `neg_or_neg_of_mem_foldedPlane`、`mul_neg_of_mem_foldedPlane_of_pos_of_neg`：
  `ℓ` 在 `linearHalfSpace S u` 上的值恰为 `r * ℓ u`（`r ≥ 0`），故 `foldedPlane S u v` 上同时出现正负值
  当且仅当 `ℓ u * ℓ v < 0`。只要 `S ≤ ker ℓ`，不要有限维、不要复形。
- `apply_eq_linear_sub_of_eqOn_zero`、`mem_affineSpan_of_mem_openSimplex`：`ℓ` 在 `A` 上为零且
  `x ∈ affineSpan ℝ A` 时 `ℓ.linear (z - x) = ℓ z`。按 `omit` 纪律已把 `openSimplex`、`Finset` 弱化掉。
- `mem_closure_inter_pos_of_coface_pos` / `..._neg_of_coface_neg`：**反方向**。只要 `insert a s ∈ K.faces`、
  `x ∈ openSimplex s`、`ℓ` 在 `s` 上为零、`0 < ℓ a`（resp. `ℓ a < 0`），从 `openSegment ℝ x a` 得两侧性。
  不需要有限维、`Finite K.faces`、流形条件，也不需要 `s ∈ K.faces`。
- `mul_neg_of_mem_closure_inter_pos_of_mem_closure_inter_neg`：**主方向**。
  输入 `hs`、`hbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1`、`hx : x ∈ openSimplex s`、
  `hpair : {w | w ∉ s ∧ insert w s ∈ K.faces} = {a, b}`、`ℓ` 在 `s` 上为零与上面的 `hpos`/`hneg`，
  输出 `ℓ a * ℓ b < 0`。证明用 `eventually_mem_space_iff_mem_coface_pair_foldedPlane`
  （`RelativeNormalForm.lean:107`）把 `K.space` 的局部换成 `foldedPlane`，再用 A 的符号引理。
  `a = b`（只有一张余面）时假设自相矛盾，结论自动成立，无需另加 `a ≠ b`。
- `exists_coface_pair_pos_neg_of_mem_closure_inter`：定序版，给出 `0 < ℓ aPos ∧ ℓ aNeg < 0`。
- `IsCombinatorialManifoldWithBoundary.exists_cofaces_pos_neg_of_mem_closure_inter`：
  `(n+1)` 维组合带边流形的非边界余维一面版本，`hbound` 与余面对由
  `codimension_one_cofaces_of_notMem_boundary` 自动交付。
- `isArrangementGeneralFoldPair_of_mem_closure_inter`：两张 `IsCombinatorialManifoldWithBoundary 2` 的
  曲面在 `x` 处各沿 `s`、`t` 折叠，给定 `l k` 在 `s`、`t` 上为零、
  `vectorSpan s ⊔ vectorSpan t = ker (l k).linear` 与两张支各自的两侧性，产出
  `IsArrangementGeneralFoldPair l K L s t x`。`l k x = 0` 由假设推出，不另作参数。
- `hasPLCrossingAt_of_mem_closure_inter_two_folds`：加 `finrank ℝ E = 3` 后直接得
  `HasPLCrossingAt K.space L.space x`。这是共面双折情形现在缺的唯一几何输入被隔离出来的形式。

#### C. §19.141 的“共享”判断成立，但要点明边界

本层的陈述里没有 `hcomplete`、没有 `IsVertexMapGeneralInArrangement`、没有目标骨架横截性，
所以对 (a)、(b) 中立，两条路线都消费同一个生产者。**共享的是这条翻译**：
“支的两侧性 ⟺ 对顶点异号 ⟹ crossing”。**不共享的是怎么生产两侧性**，两条路线各自负责：

- 路线 (a)（分层通用位置）之后要做：用尊重受迫子层秩的条件替换 `hcomplete` 并重证存在性
  （`exists_small_vertexMap_generalInArrangement`，`RelativeNormalForm.lean:299` 的分层版），
  再由开胞腔保持得到 `sign (l k (φ v)) = sign (l k (φ₀ v))`，把 `φ₀` 的两侧性搬到 `φ`；
  两侧性本身在 (a) 里是**被保持**而不是**被造出**的，所以 (a) 还欠一条“原构型即已跨越”的输入，
  以及在不跨越时对该双点的处理（§16.2 的排布说明这时确实不是 crossing）。
- 路线 (b)（先对目标骨架横截）之后要做：由横截性给出折边所在片与目标 2-面的实际相交，
  从而产出同一对 `hpos`/`hneg`；`not_isVertexMapGeneralInArrangement_of_complete_hyperplane`
  的受迫共面前提在 (b) 下不再出现，但要重做 §19.61 的公共细分与图卡搬运。

两条都仍是开放式设计；本轮没有起头，也没有对它们作任何代价估计。

#### D. 验证

`FoldPlaneCrossing` check exit=0（10.6 秒）、零 warning；`AuditF282.lean` 全部 13 个声明仅
`propext`、`Classical.choice`、`Quot.sound`。零注释、无 `sorry` / `axiom` / `nolint` /
`maxHeartbeats` / `set_option`；`fresh.py` forbidden hits 0、无 stale/missing olean；
未登记根聚合，未跑 `lake build`。下一个审计文件 `AuditF283.lean`。

### 19.143 顶点定理的量词形状缺陷（H 查出）已按 (β) 修：契约提到顶层，`(K₁, N₁, φ)` 变成参数

**缺陷。** 旧的 `exists_chart_two_sheets_of_transverse_vertex` 结论是
`∃ K₁ N₁ φ, 结构条款 ∧ (∀ a₁ b₁, 契约 → … → ∃ 图卡)`。像侧契约位于存在量词内部的蕴含前件，
消费者要用它就得对定理藏起来的那个 `N₁` 证契约，而外部写得出的任何契约假设要么与该 `N₁` 无关、
要么对所有 `N₁` 全称而为假（H 的反例：`link N₁ {0}` 取平面 `{x.2.2 = 0}` 内的三角形边界，
满足全部结构条款，但与该平面的交是整条圆周）。H 据此弃掉了自己的链定理（HANDOFF_CODEX_H
"给 F 的接口缺陷报告"）。这与 `hgen`、`hfiber` 同类：编译与审计都干净、但按预期实例化不了。
我 §19.140 的假设审计只查了每条假设可否满足，没查结论的量词结构，故漏过。

**修法 (β)。** 拆成两条（`VertexBranchChartPair.lean`，新形状见 §19.140 C）：
- `exists_transcription_of_transverse_vertex`：旧定理的存在部分，另外把图卡半边实际消费的三条
  （`IsPLHomeomorphOn φ U W` 连同 `U`、`W` 开与 `p ∈ U`；`M` 送进 `{x.2.2 = 0}` 的 `∀ᶠ`；
  `N` 送进 `N₁.space` 的 `∀ᶠ`）写进结论。这三条原先只活在证明内部，不暴露就没人能重建图卡。
- `exists_chart_two_sheets_of_transverse_vertex`：`K₁ N₁ φ U W` 为参数，结构条款与
  `a₁ ≠ b₁`、`link N₁ ∩ {x.2.2 = (φ p).2.2} = {a₁, b₁}`、两侧性两条为顶层假设，结论只留图卡。
  按 `omit` 纪律：不需要 `DecidableEq E`，源侧只留 `A B : Set E`（消费者传 `M.space`、`N.space`），
  有限性写成显式 `Set.Finite` 假设以便直接接生产者的 `obtain` 输出。
H 的 `exists_arcChartChain_of_imageContract` 不受影响（它按 `hvertex` 打包形状消费）；
它换到顶层形状时的调用顺序是：`obtain` 生产者 → 对该 `N₁` 证 D → 调图卡定理。

**标准审计追加第三项**（已写进 `MOISE_CHAIN.md` 可行性复盘段）：结论形如
`∃ x, … ∧ (hyp x → …)` 时，检查消费者能否对被藏住的 `x` 实际供给 `hyp x`；供不了就提到顶层。

**验证。** 消费者计数：定理名在树中只有定义处 1 处命中；导入 `VertexBranchChartPair` 的模块 2 个
（`BranchChainChart`（本车道，未用该名）、`ArcChartChain`（H，只读）），无二级导入者。
`VertexBranchChartPair` exit=0（10.3 秒）、`BranchChainChart` exit=0（10.7 秒）、
`ArcChartChain` exit=0（10.6 秒），均零 warning；`AuditF283.lean` 五项（两条新定理、
`exists_chart_branch_chain`、`exists_openPartialHomeomorph_branch_chain`、
`exists_arcChartChain_of_imageContract`）仅 `propext`、`Classical.choice`、`Quot.sound`。
下一个审计文件 `AuditF284.lean`。

### 19.144 26.4 的"相对子复形细分"：定案为限制形、把记录里的固定形反证掉、指出 `Moise264` 结论缺一条

#### A. 陈述定案（先定后证）

"相对子复形的细分"有两种不同的定理：
- **(i) 限制形**：`∃ K', IsSubdivision K' K ∧ K'.faces.Finite ∧ (∀ s ∈ K'.faces, diam < ε) ∧
  IsSubdivision (restrict K' L.space) L`——`L` 被相容地一起细分，`K'` 落在 `|L|` 内的每个面都在 `L` 的某个面里
  （`IsSubdivision.exists_face_subset`）。
- **(ii) 固定形**（MOISE_CHAIN 第 327 行的出路 (a)）：`L.faces ⊆ K'.faces ∧ ∀ s ∉ L.faces, diam < ε`。

**26.4 需要的是 (i)，而且它已经在树上**（`IsSubdivision.restrict`，`Subcomplex.lean:109`，
配 `exists_isSubdivision_diam_lt`，`Mesh.lean:184`）。理由：26.4 全程只在一处用逼近——把所选环路的连续零伦
`f : Δ → |K|` 换成边界落在 `|L|` 里的 PL 奇异盘。`Moise264` 的假设是基本群元 `g`，不是固定的环路，
所以边界环路由我们选，只须留在 `|L|` 内且在 `|L|` 中自由同伦于 `g` 的代表；记录里之所以要"逐点相等"
（从而要 (ii)），是照抄书上 "Let D … with Bd D = L" 的字面，而 MOISE_CHAIN 第 397 行已经指出
`IsNullHomotopic` 换成 PL 环路后不变——同一个观察。按记录推荐的环带路线 (b)：在边界复形 `K₀` 上把环路
取成单纯映射（`exists_isPiecewiseAffineOn_freeLoop_homotopic`），对 `Δ` 的三角剖分 `K ⊇ K₀` 取细网格细分
`K'` 并做绝对单纯逼近 `g`（`exists_isSubdivision_simplicialApproximation`，`SimplicialApproximation.lean:20`），
再在棱柱 `∂Δ × [0,1]` 上以粗环路为顶、`g|∂Δ` 为底插值。棱柱每个格子的四个顶点值都落在同一个闭单形
`σ_e ∈ L` 里：粗边 `e` 上 `f` 仿射且 `f(e) = σ_e`（单纯），细顶点 `m ∈ e` 有
`g m ∈ conv (carrierFace L (f m)) ⊆ σ_e`（逼近定理的载体条款），而"细边落在某条粗边里"正是 (i)。
没有混合格问题，于是不需要 (ii)。

**(ii) 是假的**，只要 `L` 有一个面 `τ` 在 `K` 里有真余面 `σ`，且 `ε ≤ diam τ`：
`not_exists_isSubdivision_faces_subset_forall_diam_lt`。证明：`K' ⊇ L` 含 `τ`，`conv σ` 被 `K'` 的面覆盖，
`τ` 的重心在 `openSimplex σ` 的闭包里，有限并的闭包给出一个面 `s` 同时含重心且与 `openSimplex σ` 相交；
前者经 `face_subset_of_mem_openSimplex_of_mem_convexHull` 得 `τ ⊆ s`，后者经
`notMem_space_of_notMem_faces` 得 `s ∉ L`，于是 `diam τ ≤ diam s`。这把记录里"迭代 `relDerived` 不会变小"
从"这个构造不行"升级为"任何构造都不行"。(ii) 的最弱真形式是 `RelativeMesh.lean:9`（远离 `L` 在 `K` 中的闭星才小），
最强真形式是 join/扇形（`L` 固定、无 `L`-顶点的面全小、星内面 = `L` 的面 ∪ 一个小的 link 面），
后者才是 Zeeman 式逐点相等相对逼近要的东西；26.4 不需要它，本轮没做，也不给代价范围。

#### B. 模块 `SubcomplexMesh.lean`（新，三条）

- `exists_isSubdivision_diam_lt_restrict_isSubdivision`：(i)。按 `omit` 纪律不要面基数上界 `N`（由有限性内部导出）。
- `exists_face_notMem_diam_ge_of_isSubdivision_of_faces_subset`：上面证明的可复用中间件，
  给出 `s ∈ K'`, `s ∉ L`, `τ ⊆ s`, `diam τ ≤ diam s`。只要 `[Finite K'.faces]`、`L ⊆ K`、`L ⊆ K'`；不要有限维。
- `not_exists_isSubdivision_faces_subset_forall_diam_lt`：¬(ii)，逐字否定记录里的写法（含 `K'.faces.Finite`）。

检查 `SubcomplexMesh` exit=0（9.1 秒）、零 warning；`AuditF284.lean` 三项仅 `propext`、`Classical.choice`、
`Quot.sound`。零注释、无 `sorry`/`axiom`/`nolint`/`maxHeartbeats`/`set_option`。下一个审计文件 `AuditF285.lean`。

#### C. 26.4 在此之外还缺什么（未起头，不给代价范围）

1. 棱柱插值引理：`K₀' × [0,1]`（`K₀'` 是边界多边形的细分）上的 PA 映射，顶是粗单纯环路、底是细逼近的
   `simplicialMap`，格子四顶点值同在一个闭单形里故映进 `|L|`。`PrismProdCollar.lean` 的"乘积相对一端"
   是相近工具，是否能直接给两端插值要核对。
2. 把环带与缩小的盘沿圆周粘起来并重参数化成 PL 盘（`Gluing.lean` / `PlanarDiskUnion.lean`）。
3. 盘相对 `Bd W` 的一般位置且保持边界与像落在 `|K|` 内：`exists_small_simplicialMap_transverse_on_subcomplex`
   与 `GeneralPositionWithin.lean` 的 `_mapsTo` 版。
4. 双领域 `ρ` 的消费、沿最内多边形把盘推过双领域（Case 1/2）、Case 3 = 25.2 用于 `Cl(M³ − W)` 再补环带。
5. **`Moise264` 的结论缺一条**（`MoiseChain.lean:43`）：书上 26.4 的结论含 "Bd Δ 在 M² 中不可缩"，
   Lean 陈述只有 `Δ ∩ S = r '' stdSimplexBoundary 2`。按现状它可由一张推离 `S` 的小盘平凡满足
   （取 `L` 的一个 2-单形 `σ`，在双领域里取在 `∂σ` 上恰为零的 PL 高度函数的图；26.3 已交付），
   于是 30.4 无法从它得到任何东西。缺的条款用链条词汇写是：`r` 限制到 `stdSimplexBoundary 2` 的环路在
   `S` 中不 `IsNullHomotopic`。`Moise264` 尚未被任何定理消费，可以直接改；我没有动共享的 `MoiseChain.lean`。

### 19.145 链图卡加上两端面（板状）边界条款，并先给出一个具体实例

E3（HANDOFF_CODEX_L §81.3）证明单平面边界模型对触边分支无实例：分支是两端点都在 `Bd M` 的多面体 1-球，
图卡假设把每个分支点放到轴上，`Bd M = {p.1 = 0}` 与轴只交一点，两端点被迫重合。修正接口是**板**：
`M ↔ {0 ≤ x.1 ≤ c}`，`Bd M ↔ {x.1 = 0} ∪ {x.1 = c}`（两个端面），两张片仍是坐标平面。本车道的链定理原本没有
边界条款（所以它本身不空），这是新增不是修补。`BranchChainChart.lean` 新增三条：
- `image_inter_source_eq_of_forall_mem_iff`：`OpenPartialHomeomorph` 的通用引理，
  `(∀ y ∈ e.source, y ∈ P ↔ e y ∈ Q) → e '' (P ∩ e.source) = e.target ∩ Q`。
- `exists_openPartialHomeomorph_branch_chain_slab`：在原链定理的六条假设之外加两条逐图卡的 iff
  `y ∈ M ↔ 0 ≤ (Φ y).1 ∧ (Φ y).1 ≤ c`、`y ∈ BdM ↔ (Φ y).1 = 0 ∨ (Φ y).1 = c`；结论在原七条之外给出
  同样两条 iff 以及像等式 `e '' (M ∩ e.source) = e.target ∩ 板`、`e '' (BdM ∩ e.source) = e.target ∩ 两端面`。
  用 iff 而不是单向包含，因为 E3 的楔推要把模型里"端面逐点固定、留在板内"拉回到 `M`，两个方向都要。
  生产者在两端各用一次 `exists_linearEquiv_boundaryCrossing_normalForm`（`TransversePlaneCoordinates.lean:357`，
  远端先平移到 `x.1 = c`），内部顶点图卡的像须落在开板 `{0 < x.1 < c}` 内。原 `exists_openPartialHomeomorph_branch_chain`
  保留（无边界分支仍用它）。
- `exists_slab_branch_chain_instance`：**先做的实例审计**（按 §19.143 之后的第二条审计）。在 `ℝ³` 里取
  `A = {x.2.2 = 0}`、`B = {x.2.1 = 0}`、`M = 板`、`BdM = 两端面`、`S = A ∩ B ∩ M`（轴上从 `(0,0,0)` 到 `(c,0,0)` 的线段），
  单张图卡 `Φ = id`；定理把 `p = (0,0,0) ≠ q = (c,0,0)`、两点都在 `BdM` 与 `S`、`S = A ∩ B ∩ M`，连同对该数据
  实际调用板状链定理得到的图卡与全部条款一起证出。这正是 E3 证明在单平面模型里不存在的构型：
  一条两端在不同端面上的分支。

检查 `BranchChainChart` exit=0（10.7 秒）、零 warning；`AuditF285.lean` 四项
（三条新定理与原链定理）仅 `propext`、`Classical.choice`、`Quot.sound`（通用引理不含 `Classical.choice`）。
`BranchChainChart` 无导入者，无需重编下游。下一个审计文件 `AuditF286.lean`。

### 中断时状态（2026-09-18，主人会话结束）

**已落地并推送**（`codex/moise-smoothing`）：
1. `57a2cd48b` §19.142 `FoldPlaneCrossing.lean`（F5.2 共享前置）。
2. `561a91b9e` §19.143 (β) 修：`VertexBranchChartPair.lean` 拆成生产者 `exists_transcription_of_transverse_vertex`
   与顶层假设形的 `exists_chart_two_sheets_of_transverse_vertex`。
3. `f2da69cc9` §19.144 `SubcomplexMesh.lean`：26.4 消费限制形细分（已打包），固定形反证为假，
   并指出 `Moise264` 结论缺 "Bd Δ 在 M² 中不可缩"。
4. `9454cf931` 合并整合分支（`MOISE_CHAIN.md` 冲突两边保留）。
5. 本提交 §19.145 板状链图卡 + 实例。

**无未编译改动、无 stash。** 所有审计文件在 `.lake/scratch/AuditF282–285.lean`。

**确切的下一步**（按优先级）：
- H：把 `ArcChartChain` 改为消费顶层形（`obtain` 生产者 → 对该 `N₁` 证像侧契约 → 调图卡定理），
  并在链构造里生产 §19.145 的两条 iff（两端各用一次单端法式，内部图卡落在开板）。
- E3：楔推消费 `exists_openPartialHomeomorph_branch_chain_slab` 的两条像等式。
- 链主人：给 `Moise264` 补结论条款（`MoiseChain.lean:43`，尚无消费者）。
- F（26.4）：棱柱插值引理（§19.144 C.1），然后环带与盘的粘接（C.2）。
- F5.2 两条路线仍开放，各自欠的东西见 §19.142 C。

### 19.146 边界 crossing 的局部板图卡生产者（2026-09-18）

本轮仅接双端板图卡生产链；不恢复 F5.2、Case 1/2 或 §31/32。
`ArcChartChain.lean` 的所有权由协调者转给 F，但本层尚未修改其旧的条件式。
整合基线 `8808a5c0f` 已合入，合并提交 `5572fbdcf`。

**done：`BoundaryCrossingChart.lean` 的局部生产层。** 四个端点：

- `HasPLBoundaryCrossingAt.exists_openPartialHomeomorph_halfSpace`：从已有的边界 crossing
  在任意指定邻域内生产开部分同胚，正逆皆逐片仿射，中心送到零；`M`、`frontier M` 和
  两片分别具有半空间、边界平面、两个坐标半平面的双向像契约；`A ∩ B` 映为坐标半轴。
- `HasPLBoundaryCrossingAt.exists_openPartialHomeomorph_slab_left`：任意 `c > 0`，
  缩开源域至第一坐标小于 `c`，中心送到 `(0,0,0)`；实际生产
  `M ↔ 0 ≤ x₁ ≤ c`、`frontier M ↔ x₁ = 0 ∨ x₁ = c`，两片仍为相应坐标平面与板的交。
- `HasPLBoundaryCrossingAt.exists_openPartialHomeomorph_slab_right`：再作
  `(x₁,x₂,x₃) ↦ (c-x₁,x₂,x₃)`，中心送到 `(c,0,0)`，源域第一坐标严格为正；
  板、端面、两片以及分支 `A ∩ B` 的双向像契约全部保留。
- `HasPLCrossingAt.exists_openPartialHomeomorph_slab_interior`：在 `x ∈ interior M`、
  `0 < r < c` 下，生产中心为 `(r,0,0)`、全像落在开板内的局部图卡，并生产同样的
  `M` 与 `frontier M` 双向契约。**这里对两片只输出单向平面包含**：原 crossing
  定义允许其中一片为半平面；本结果没有把该包含提升成完整两片像等式。

这些 `OpenPartialHomeomorph.IsImage` 条款按定义是源域上的逐点 iff，可用 `.image_eq`
得到 `e '' (e.source ∩ M) = e.target ∩ slab` 等等式。边界不是额外假设：先缩小开域使
半空间 iff 处处成立，然后用 Mathlib 的 `OpenPartialHomeomorph.IsImage.frontier` 与
`frontier_Ici` 推出。若消费者使用 `BdM`，沿 `BdM = frontier M` 改写；有限组合三维
流形的该等式来自 `frontier_space_eq_boundaryComplex_space_of_finrank`。

**完整链仍 partial，确切缺口如下。**

1. `exists_transcription_of_transverse_vertex` 的输入没有 `M` 与 `N` 的相交/异侧条件，
   允许 `M = N`。例如令两者均为同一个平面凸圆盘的含中心锥剖分，`ℓ` 在该平面上的限制非零：
   两个 link 均为圆周，`M` 的 link 截面是两点且有正负两侧，全部源侧类型相容。
   将 `M` 压到平面后，同一个 `N` 不会变成横穿该平面的另一片。因而不能仅从该转写
   的现有输入推出其具体 `N₁` 的两点截面与正负两侧。这里是对实际输入的退化检查，
   不是本层新增的 Lean 反例定理。
2. 当前 `ArcChartChain.exists_arcChartChain_of_imageContract` 仍直接假设各顶点所需的
   像侧契约和最终局部图卡。未生产实际弧链到具体 `N₁` 契约的层，也未把逐点图卡
   拼成同一个单射 `Φ`；侧选择的 `ZMod 2` 递推并不等于过渡映射相容。
3. H 的未标记 `IsPLBallPair 2 1` 仅标记环境球与弧，不标记两张片；不能用它直接
   声称已保持两片并闭合板图卡。还需实际两片交弧、跨片异侧与片保持的过渡数据。

验证：在协调者 `F-BoundaryCrossing-20260918` 窗口内，用统一私有输出脚本检查本模块，
2026-09-18 21:50:01 UTC 的回执为 exit=0、diagnosticLines=0、sourceStable=true。
显式启用标准语法 linter 集、header 和 longLine；没有关闭 linter 或增加资源预算。
外部静默 `AuditF286.lean` 于 21:52:10 UTC 完成：四个公开端点与一个私有边界引理，
共五项非自动声明的传递公理全部属于 `propext`、`Classical.choice`、`Quot.sound`；
默认环境 linter 集仅排除 `docBlame`、`docBlameThm`，exit=0、零诊断。
源码 SHA256 为 `14A3391385E7714F837B2BE7FEC178F8F7D16FC020F2808277613310B4DC2DC5`。
回执、空日志和私有产物保存在
`C:\Users\liao9\AppData\Local\Temp\codex-f-boundary-private`；共享产物未改写。
本轮复用了导入模块的既有对象，不能据此宣称当前全部源码依赖已重编；独立根重编仍由协调者负责。
窗口已释放，无 F 编译进程。源码、本记录、`MOISE_CHAIN.md` 与根聚合登记随本数学提交一并交付。
下一审计编号为 `AuditF287.lean`。

### 19.147 边界双点集的双向半轴图卡与真实载体追踪（2026-09-18）

§19.146 的局部板图卡已在 `1fbdc358f` 推送。本层继续实际双点集的生产，
不从允许两片重合的 `exists_transcription_of_transverse_vertex` 输入推导横截性。

生产链核对：`SingularGeneralPosition.exists_small_simplicialMap_doublePointSet_with_boundary_in_halfSpace`
实际输出相对于指定 `{ℓ ≥ 0}` 的 `HasPLBoundaryDoubleCrossingAt`。
`SingularChart.exists_small_map_doublePointSet_normal_form_in_halfSpace_chart` 搬运后指定
`Mloc = e.symm '' (e.target ∩ {ℓ ≥ 0})`、`Bloc = e.symm '' (e.target ∩ {ℓ = 0})`。
其 `exists_small_map_doublePointSet_normal_form_in_boundary_chart` 在输入真实载体 `M`
和边界 `Bd` 的半空间图卡后，利用 `hMimage`、`hBdimage` 与 `congr_target`
实际产出 `HasPLBoundaryDoubleCrossingAt g K.space M y`；这里真实 `M` 没有丢失。
但是多图卡的 `IsNormalSingularCell` 总生产者尚未闭合，不能据此从任意 `NormalSingularCellData`
恢复真实载体。`HasPLNormalDoubleCrossingAt` 的边界分支仅有 `y ∈ Bd` 和一个存在量化的
`Mloc`，没有 `frontier Mloc` 与 `Bd` 的局部等式；此义务与两片/过渡相容性分开保留。

**局部生产层 done：`BoundaryDoubleCrossingChart.lean`。** 三个公开端点：

- `HasPLBoundaryCrossingAt.not_eventuallyEq`：真正的边界 crossing 排除两张片在交点附近的
  germ 相等。证明在开目标域内取 `(t,0,t)`、`t > 0` 的小点，再用双向像契约拉回，
  得到它属于第二片而不属于第一片；这正是弱 transcription 输入没有的实际排除条件。
- `HasPLBoundaryDoubleCrossingAt.exists_openPartialHomeomorph_doublePointSet`：从指定载体 `M`
  的实际 boundary-double-crossing，产出两个不交源片 `A, B ⊆ P`、它们各自的 PL 嵌入，
  以及任意指定邻域内的同一开部分同胚。`M`、`frontier M`、`f '' A`、`f '' B`
  分别与半空间、边界平面、两坐标半平面双向对应；**`doublePointSet f P` 双向对应坐标半轴**。
  同时保留该源域上的全纤维包含 `P ∩ f ⁻¹' {z} ⊆ A ∪ B`，没有第三张片被忽略。
  证明复用 `mem_doublePointSet_iff_mem_image_inter_of_injOn`，先按实际纤维覆盖缩小邻域，
  再调用 §19.146 的边界图卡；没有另造 crossing 或有限图卡覆盖。
- `HasPLBoundaryDoubleCrossingAt.exists_openPartialHomeomorph_doublePointSet_of_halfSpace_chart`：
  消费上述 `halfSpace_chart` 构造的明确 `Mloc`，从非零连续线性泛函和开部分同胚
  **证明** `frontier Mloc ↔ Bloc` 在原图卡源域成立，再把第二个像契约改成构造的 `Bloc`。
  没有假设最终半轴或板的像等式，也没有把未标记球对当成两片相容数据。

验证：统一私有检查脚本在 `F-BoundaryDouble-20260918` 窗口内于
2026-09-18 22:39:06 UTC 完成模块检查，exit=0、diagnosticLines=0、sourceStable=true。
显式启用标准语法 linter 集、header 与 longLine；没有关闭 linter 或增加资源预算。
外部静默 `AuditF287.lean` 于 22:40:01 UTC 完成：三个公开定理与一个私有边界引理，
共四项非自动声明的传递公理全部属于 `propext`、`Classical.choice`、`Quot.sound`；
默认环境 linter 集仅排除 `docBlame`、`docBlameThm`，exit=0、零诊断。
当前源码 SHA256 为 `B457B1D7A65503704498A2925A92B20FE14A0A989C5C23A25C826B4559655E6B`。
回执、空日志、importArts 映射和私有对象保存在
`C:\Users\liao9\AppData\Local\Temp\codex-f-boundary-private`；共享对象未改写。
检查复用已推送且源 hash 匹配的 `BoundaryCrossingChart` 私有对象与其它既有导入对象，
不据此宣称当前源码的完整传递依赖已重编；独立根重编仍由协调者负责。
F 检查进程已结束；源码、根登记、本记录与 `MOISE_CHAIN.md` 状态随同一数学提交交付。
完整弧链仍 partial：尚缺实际分支上两片的统一标记、相邻胞腔片迹匹配及单射全局图卡。
下一审计编号为 `AuditF288.lean`。

### 19.148 触边分支的一致标记多面体源片邻域（2026-09-18）

§19.147 已在 `7302186ab` 推送。本层从真实 `NormalSingularCellData` 的触边分支生产源侧邻域，
不消费弱 transcription 的横截结论，也不把最终环境图卡的相容性作为输入。

**源片邻域生产层 done：`BoundaryBranchSheets.lean`。** 公开端点
`NormalSingularCellData.exists_polyhedral_sheet_neighborhoods_of_boundaryBranch`。
它调用现有 `exists_two_isPLBalls_branchPreimage_of_boundaryBranch_with_coordinate`，取得
实际分支原像的两条不交 PL 弧 `A, C` 及其共同分支坐标。由该坐标的单射性推出 `D` 在各弧上
单射；用 Mathlib 的 `Set.InjOn.exists_isOpen_superset` 将紧弧上的单射性与真实
`locallyInjective` 字段扩到相对源域的邻域。分离这两条紧弧后，用现有多面体邻域定理取得
不交多面体 `S, T ⊆ D.domain`，分别是整条 `A, C` 的相对邻域，且 `D` 在每片上均为嵌入
并保留 `IsPLOn 2 3`。它们并未被声明为 PL 2-球。

再从源域子类型中两片相对内部的补集出发，用紧致源域映射的闭性构造开集 `W`，满足：

- 整条实际 `branchCarrier c` 落在 `W` 内；
- 对每个 `y ∈ W`，全部纤维 `D.domain ∩ D ⁻¹' {y}` 均落在固定的 `S ∪ T`；
- `y ∈ doublePointSet D D.domain ↔ y ∈ D '' S ∩ D '' T`。

这在源侧给出沿整条分支固定的两片标签及精确双点集；没有逐点重新选择可能互换的标签。
`CutAndPaste` 的源片 germ 搬运和 `ConePairExtension` 的标记锥延拓保持原样、未复制。
尚未生产相邻环境胞腔的边界片迹匹配、保持两片的过渡映射或单射全局板图卡；
真实 carrier/boundary 的兼容缺口也没有因此消除。

验证：统一私有检查脚本在 `F-BranchSheets-20260918` 窗口内于
2026-09-18 23:15:37 UTC 完成模块检查，exit=0、零诊断、sourceStable=true；
标准语法 linter 集、header 与 longLine 均启用。外部静默 `AuditF288` 于
23:18:12 UTC 完成最终审计：本模块一个公开定理、一个私有引理及三个复用关键端点，
共五项传递公理闭包仅含 `propext`、`Classical.choice`、`Quot.sound`。
复用项为上述分支两弧生产者、Mathlib 的开单射邻域定理与
`mem_doublePointSet_iff_mem_image_inter_of_injOn`；本模块全部非自动声明均纳入审计。
默认环境 linter 集仅排除 `docBlame`、`docBlameThm`，显式断言恰有 13 项且全部通过；
审计 exit=0、零诊断。源码 SHA256 为
`45AEA24E05FE32A4530A42D4B5A6295A058C6937209F538BC2722540D0C54245`。
回执、空日志、importArts 与私有产物位于
`C:\Users\liao9\AppData\Local\Temp\codex-f-boundary-private`，共享对象未改写。
本轮复用导入模块的既有对象；独立完整源码根重编仍由协调者负责，本结果未宣称该根检查完成。
源码、根登记、交接与计划同提交交付。完整板图卡仍 partial，下一步是固定源片与既有 crossing
片的局部 germ 对齐，再生产相邻胞腔片迹匹配；真实载体/边界兼容继续保持显式。
下一审计编号为 `AuditF289.lean`。
