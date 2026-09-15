# E.0 交接：不变域定理（计划 D6），与 F 车道并行

交接日期 2026-09-14。本文件是 E.0 接手者的唯一入口。E.0 独立于 F 车道，但与 F 车道的 Codex **共用主机与
共享 oleans 库**，所以工作树、分支和进程配额都与 F 车道分开，见 §1。

## 0. 任务

得到**无条件**的不变域定理（有限维实内积空间任意维数）及其流形形式，公理只含 `propext`、
`Classical.choice`、`Quot.sound`。分三步：(1) 原生移植外部文件里"以 Brouwer 不动点定理为条件"的解析证明；
(2) 用本树已证的球面同调把 Brouwer 不动点定理在任意维数证出来，消掉条件；(3) 给 M.3、S.1、E.3/E.4
需要的推论形式。消费者：`PHASE3_APPROXIMATION_PLAN.md` 行 S.1（17.1 `Bd M = Fr M`）、M.3（23.8）、
E.3/E.4（36.1 的过渡，"E.0 得 `h(U)` 与 `Int N'_i` 开"）。

## 1. 环境与硬规则

- 工作树 `D:\differential-geometry-moise-e0`，分支 `codex/moise-e0`（从 `codex/moise-smoothing` 分出，已创建）。
  **不要进入** `D:\differential-geometry-moise-plan`（F 车道的 Codex 正在那里工作），不要动共享检出
  `E:\differential-geometry-dev` 的源码或分支，不在任何地方运行 `lake build`，不把新模块登记进
  `DifferentialGeometry.lean`。
- 检查脚本在 `D:\differential-geometry-moise-e0\.lake\scratch\tools\`（`check-f.ps1` 已把 `$root` 指向本工作树），
  它把 olean 写进共享库 `E:\differential-geometry-dev\.lake\build\lib\lean`；本任务的模块名与 F 车道不重叠。
- 主机 Lean 进程配额：F 车道的 Codex 同时跑 1 个，你也**只跑 1 个**（一次一个聚焦检查或审计）。
- `AGENTS.md`（= `CLAUDE.md`）：非 vendored Lean 文件零注释、零 docstring；无 `sorry`/`axiom`/`nolint`/`maxHeartbeats`/`set_option`；
  Mathlib 标准 linter 集零警告；提交信息用英文描述数学结果；绝不 push main、绝不 force-push。
  计划 D6 决定这是**原生移植**（`Topology/InvarianceOfDomain.lean`，去注释），不是 `External/` vendoring；
  出处与许可按 §5 记录。
- 不弱化目标：最终端点不得残留 `BrouwerFixedPoint` 或任何未证类假设；中间文件可以保留该类作为过渡。
- 状态登记：在 `E:\differential-geometry-dev\WORKING_STATUS.md` 末尾加一条 "Moise smoothing E.0(Codex) 2026-09-14"
  （只编辑、不提交）。

## 2. 验证配方

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File D:\differential-geometry-moise-e0\.lake\scratch\tools\check-f.ps1 `
  -Module DifferentialGeometry.Topology.InvarianceOfDomain *> D:\differential-geometry-moise-e0\.lake\scratch\iod.log
$env:PYTHONIOENCODING='utf-8'; python D:\differential-geometry-moise-e0\.lake\scratch\tools\errblocks.py D:\differential-geometry-moise-e0\.lake\scratch\iod.log
powershell -NoProfile -ExecutionPolicy Bypass -File D:\differential-geometry-moise-e0\.lake\scratch\tools\audit-f.ps1 -File '.lake/scratch/AuditE0.lean'
```
要求 exit=0、输出无 `warning:`；审计每条输出 `depends on axioms: [propext, Classical.choice, Quot.sound]`。
被 import 的新模块必须先通过检查（olean 已生成）。模块名 = 路径去掉 `.lean`、`/` 换 `.`。

## 3. 源材料（已放在 `D:\differential-geometry-moise-e0\.lake\scratch\ext\classification-of-surfaces\`）

- `Topology/InvarianceOfDomain.lean`（813 行）：来自 mccorvie/classification-of-surfaces@e3c7230（Apache-2.0；
  Lean 4.32.0，Mathlib 81a5d25；本树 v4.33.1，Mathlib 0df444a，会有少量 API 漂移）。文件头说明它改编自
  Kai Lam 的 mathlib4 PR #36770（commit 230d75a）与 Steven Sivek 的 TopologicalManifolds（commit 05f8033）。
  结构：`class BrouwerFixedPoint (E)`（闭单位球上连续自映射有不动点，**假设**）→ `differentiable_approx_of_continuous`
  （Tietze + Stone–Weierstrass）→ `stability_of_zero` → `invariance_of_domain_interior`（闭球形式，Jacobian 测度论证）
  → `invariance_of_domain_open_map (f : E → E) (U) (hU : IsOpen U) (hf : ContinuousOn f U) (hinj : InjOn f U) : IsOpen (f '' U)`
  → `invariance_of_domain_partial_equiv` → `class HasInvarianceOfDomain (X)` 与实例 → 图卡无关性
  `independence_of_interior`、`isInteriorPoint_iff_any_chart`、`isBoundaryPoint_iff_any_chart`、
  `isOpen_range_of_isOpen_of_continuous_injective (I : ModelWithCorners 𝕜 E H) [HasInvarianceOfDomain E] {U : Set E} (hU : IsOpen U) (f : U → M) (hfcont : Continuous f) (hfinj : Injective f) : IsOpen (range f)`、
  `isOpen_range_of_isOpen_of_isEmbedding`、`mem_interior_range_of_eq_of_mem_interior_range_of_isInteriorPoint`。
- `Moise/Brouwer.lean`（239 行）：从"无收缩"推 Brouwer 的射线构造 `fixedPointRayScale`、`brouwer_fixed_point_planeClosedUnitBall`，
  只对 `Plane`（ℝ²）写出，但只用内积，逐字推广到任意有限维实内积空间。
- `Moise/NoRetraction.lean`：平面版无收缩（经圆周提升），**不移植**，用本树同调代替。
- `LICENSE`（Apache-2.0）、`PROVENANCE.txt`。

本树可直接使用的已证输入（2026-09-14 我逐条 `#print axioms`，只含标准三公理）：
```lean
-- DifferentialGeometry/Topology/Homology/Integral.lean（namespace DifferentialGeometry.Topology）
abbrev integralSingularHomology (n : ℕ) (X : Type u) [TopologicalSpace X] : ModuleCat.{u} ℤ
def integralSingularHomologyMap (n : ℕ) (f : C(X, Y)) : integralSingularHomology n X ⟶ integralSingularHomology n Y
theorem integralSingularHomologyMap_id / integralSingularHomologyMap_comp / integralSingularHomologyMap_homotopic
-- SphereTopHomology.lean（namespace DifferentialGeometry.Topology）
def integralSphereTopHomologyEquiv (n : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : finrank ℝ E = n + 2) :
    integralSingularHomology (n + 1) (sphere (0 : E) 1) ≃ₗ[ℤ] ℤ
-- SphereHomologyVanishing.lean：integralSphereHomology_subsingleton (n k) (E) (hd : finrank ℝ E = n + 1) (hk : k ≠ 0) (hkn : k ≠ n) :
--     Subsingleton (integralSingularHomology k (sphere (0 : E) 1))
-- Reduced.lean（namespace DifferentialGeometry.Homology）
theorem isZero_reducedSingularHomology_of_contractible [ContractibleSpace X] (n : ℕ) : …
def reducedSingularHomologySuccIso (n : ℕ) : …      -- 正维数下约化同调 ≅ 非约化同调
def reducedSingularHomologyIso (e : X ≃ₕ Y) (n : ℕ) : …
-- Homology/Local/ClosedBall.lean（namespace DifferentialGeometry.Homology）
def euclideanClosedBallFundamentalClass {d : ℕ} (a : EuclideanSpace ℝ (Fin (d + 1))) …
theorem euclideanClosedBallFundamentalClass_ne_zero …
-- Homology/Local/Neighborhood.lean：puncturedNeighborhoodHomologyIso [T1Space X] (hU : IsOpen U) (n)
-- Homology/OneDimensionalSphere.lean：oneDimUnitSphere_eq_or_antipode (hd : finrank ℝ E = 1) …、oneDimUnitSphere_finite
-- FixedPoint/PlanarDisk.lean（namespace DifferentialGeometry.Topology.FixedPoint，二维备用）
theorem exists_fixedPoint_closedBall (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (f : C(closedBall c r, closedBall c r)) : ∃ z, f z = z
-- Mathlib：Convex.contractibleSpace (hs : Convex ℝ s) (hne : s.Nonempty) : ContractibleSpace s；convex_closedBall
```
本树同调库的坐标系数是 `ULift ℤ`、空间在 `Type u`；`EuclideanSpace ℝ (Fin k)` 与其子类型都在 `Type 0`，直接取 `u := 0`。

## 4. 砖块（按顺序，每砖一个文件）

### 砖 E0.1 `DifferentialGeometry/Topology/InvarianceOfDomain.lean` —— 原生移植

命名空间 `DifferentialGeometry.Topology`。保留源文件的全部声明与名字（去掉 `LeanEval…` 前缀），去注释、去 docstring、
修 API 漂移与 linter；`class BrouwerFixedPoint (E)` 暂时保留为条件。检查通过后审计 `invariance_of_domain_open_map`
（此时会显示只含标准公理，因为类假设在陈述里，不在公理里——这不是终点）。

### 砖 E0.2 `DifferentialGeometry/Topology/FixedPoint/NoRetraction.lean` —— 任意维数无收缩（同调）

```lean
theorem not_exists_retraction_closedBall_sphere {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : 0 < Module.finrank ℝ E) :
    ¬ ∃ r : Metric.closedBall (0 : E) 1 → Metric.sphere (0 : E) 1,
      Continuous r ∧ ∀ x : Metric.sphere (0 : E) 1, r ⟨x.1, Metric.sphere_subset_closedBall x.2⟩ = x
```
证明：记 `finrank ℝ E = n + 1`。`n = 0`：`sphere` 是两点 `{v, -v}`（`oneDimUnitSphere_eq_or_antipode`），闭球凸故连通，
`r` 的像连通且含 `v, -v`，与两点集不连通矛盾（或直接用 `IsPreconnected.image` 与 `IsPreconnected` 的两点集刻画）。
`n ≥ 1`：`i : sphere → closedBall` 包含，`r ∘ i = id`；对 `integralSingularHomologyMap n` 用 `_comp`、`_id` 得
`H_n(i)` 有左逆故单射；`closedBall` 可缩（`(convex_closedBall 0 1).contractibleSpace ⟨0, by simp⟩`），
`isZero_reducedSingularHomology_of_contractible` 加 `reducedSingularHomologySuccIso` 给 `H_n(closedBall) = 0`；
于是 `H_n(sphere) = 0`，与 `integralSphereTopHomologyEquiv (n - 1) E _ : … ≃ₗ[ℤ] ℤ` 矛盾（`ℤ` 非平凡）。

### 砖 E0.3 `DifferentialGeometry/Topology/FixedPoint/Brouwer.lean` —— Brouwer 不动点，任意维数

```lean
theorem exists_fixedPoint_closedBall_of_continuous {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : Metric.closedBall (0 : E) 1 → Metric.closedBall (0 : E) 1) (hf : Continuous f) :
    ∃ x, f x = x
instance {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : BrouwerFixedPoint E
```
把 `Moise/Brouwer.lean` 的 `fixedPointRayScale`（射线 `f x → x` 与单位球面的交点参数，显式二次方程根）与其
连续性、`fixedPointRayEndpoint_mem_sphere`、`fixedPointRayScale_eq_one_of_mem_sphere` 从 `Plane` 改成一般 `E`，
无不动点时得到收缩，与砖 E0.2 矛盾。`finrank ℝ E = 0` 时球是单点，直接给不动点。

### 砖 E0.4 `DifferentialGeometry/Topology/InvarianceOfDomainManifold.lean` —— 无条件端点与流形形式

```lean
theorem invariance_of_domain_isOpen_image {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U) {f : E → E} (hf : ContinuousOn f U)
    (hinj : Set.InjOn f U) : IsOpen (f '' U)          -- 由砖 E0.1 + E0.3 实例，无类假设
theorem isOpen_image_of_continuousOn_injOn {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [TopologicalSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂] {U : Set M₁} (hU : IsOpen U) {f : M₁ → M₂}
    (hf : ContinuousOn f U) (hinj : Set.InjOn f U) : IsOpen (f '' U)
theorem isOpenMap_of_continuous_injective {n : ℕ} {M₁ M₂ : Type*} [..同上..] {f : M₁ → M₂}
    (hf : Continuous f) (hinj : Function.Injective f) : IsOpenMap f
```
流形版证明是局部的：`x ∈ U`，取 `e₁ := chartAt _ x`、`e₂ := chartAt _ (f x)`，由 `hf` 取 `x` 的开邻域
`V ⊆ U ∩ e₁.source` 使 `f '' V ⊆ e₂.source`；`e₂ ∘ f ∘ e₁.symm` 在开集 `e₁ '' V ⊆ ℝⁿ` 上连续单射，
由第一条其像开；`e₂.symm` 把 `e₂.target` 内的开集送到 `M₂` 的开集（`OpenPartialHomeomorph.isOpen_image_symm_of_subset_target`
或 `e₂.symm.isOpen_image_of_subset_source` 之类，搜索确认），故 `f '' V` 开；`f '' U = ⋃ f '' V_x`。
同时保留移植文件里的 `isOpen_range_of_isOpen_of_continuous_injective`（带 `ModelWithCorners`）的无条件实例化。
审计文件 `.lake/scratch/AuditE0.lean`：至少列出 `invariance_of_domain_isOpen_image`、`isOpen_image_of_continuousOn_injOn`、
`isOpenMap_of_continuous_injective`、`exists_fixedPoint_closedBall_of_continuous`、`not_exists_retraction_closedBall_sphere`、
`isInteriorPoint_iff_any_chart`。

## 5. 记录、出处与汇报

- 出处与许可（Apache-2.0 要求保留声明）：新增 `docs/third_party/InvarianceOfDomain.md`，写明来源仓库与 commit、
  上游作者（Kai Lam / mathlib4 PR #36770；Steven Sivek / TopologicalManifolds）、许可证 Apache-2.0、本地改动
  （去注释、命名空间、API 漂移修正、Brouwer 条件由本树同调消去），并把 `LICENSE` 全文复制为
  `docs/third_party/classification-of-surfaces-LICENSE`。Lean 源文件本身不写注释。
- 计划记录：完成后在 `PHASE3_APPROXIMATION_PLAN.md` 行 E.0 的状态列写明模块、端点、审计编号、出处；在
  `MOISE_PLAN.md` §6 加一条验证记录。这两个文件 F 车道的 Codex 也在改：先 `git fetch origin`、
  `git rebase origin/codex/moise-smoothing`，只在最后一次提交里改它们，冲突时保留双方内容。
- 提交到 `codex/moise-e0` 并推送；不要合并进 `codex/moise-smoothing`（合并由用户安排）。
- 汇报：各砖的检查退出码、审计结果、端点名、与源文件的差异清单、未完成项。

## 6. Lean 坑

- 本树 `IsCombinatorialManifold*` 之类的可判定性约定与本任务无关；但 `open Classical` 下 `not_imp` 有歧义，用 `Classical.not_imp`。
- linter `unusedSectionVars`/`unusedDecidableInType`：源文件的 `variable` 块要按本树习惯收紧，纯拓扑引理用 `omit … in`。
- `▸` 高阶合一易选错实例：写显式 `have … := by rw [heq]; exact h`。
- 源文件是 Lean 4.32 写的：`Set.image` 与 `Function.extend` 的引理名、`OpenPartialHomeomorph` 的字段名、
  `ContinuousOn`/`IsEmbedding` 的命名空间（`Topology.IsEmbedding`）在本树 Mathlib 里可能已变，逐个用 `exact?`/搜索修。
