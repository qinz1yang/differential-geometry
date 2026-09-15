# S 车道交接：移植 Moise §2–§10 平面 PL 链（vendored）并桥接到本车道词汇

交接日期 2026-09-14。本文件是接手者的唯一入口。目标是让 `PHASE3_APPROXIMATION_PLAN.md` §4.1 的
P.1–P.5 与 §4.2 的 S.1 尽快成为"已证生产者"，然后进入 S.2–S.4（§17 PL Schoenflies）。

## 0. 任务

1. 把外部仓库 mccorvie/classification-of-surfaces@e3c7230（Apache-2.0，sorry-free）里 Moise §2–§10 的
   平面 PL 链按 `AGENTS.md` 规则 4 **vendored** 到 `External/ClassificationOfSurfaces/…`，保留上游注释、
   docstring、命名空间与出处；只做 import 路径、Mathlib API 漂移等必要修改，逐条记入修改日志。
2. 写**原生**桥接模块（零注释），把上游结论翻译成本车道词汇（`IsPLSphere 1`、`IsPLBall 2`、
   `IsPLHomeomorphOn`、`IsTriangle`…），闭合计划行 P.1（3.6/5.3）、3.7 相对形式、P.2（5.4）、
   以及 P.3/P.4/P.5 中上游已覆盖的部分；把对照写进计划行。
3. 之后做 S.1（17.1 `Bd M = Fr M`，依赖 E.0 与 F4.1）、S.2（17.4–17.8 推移性质）；S.3/S.4 视进度。

## 1. 环境与硬规则

- 工作树 `D:\differential-geometry-moise-s`，分支 `codex/moise-s`（从 `codex/moise-e0` 的 c33ee6ff6 分出，
  含 F 车道至 b9f0cc102 与 E.0 全部成果）。只在此工作树工作、只提交到此分支并推送同名远程分支；
  不合并进其它分支（合并由用户安排）；绝不碰 main。
- 另两个 Codex 分别在 `D:\differential-geometry-moise-plan`（F 车道）和 `D:\differential-geometry-moise-e3`
  工作：不要进入它们的目录；不改共享检出 `E:\differential-geometry-dev` 的源码或分支；不运行 `lake build`；
  不把模块登记进根聚合 `DifferentialGeometry.lean`。
- 主机 Lean 进程配额 4 个，三条车道各 1 个：你**同时只跑 1 个** lean 进程。
- 验证只用 `D:\differential-geometry-moise-s\.lake\scratch\tools\` 的 `check-f.ps1`/`audit-f.ps1`
  （`$root` 已指向本工作树；olean 写进共享库 `E:\differential-geometry-dev\.lake\build\lib\lean`，
  模块名 = 路径去 `.lean`、`/` 换 `.`，对 vendored 文件即 `External.ClassificationOfSurfaces.Moise.X`）。
- 原生文件（桥接、S.1 起）遵守 `AGENTS.md`：零注释零 docstring；无 `sorry`/`axiom`/`nolint`/`maxHeartbeats`/
  `set_option`；Mathlib 标准 linter 集零警告；提交信息用英文描述数学结果。
- vendored 文件遵守 `AGENTS.md` 规则 4：保留上游头部版权声明、docstring、注释、命名空间
  `LeanEval.Topology.ClassificationOfSurfaces…`；不得引入 `sorry`/`axiom`；上游本身没有 `set_option`/`nolint`，
  也不要新增。上游 lakefile 用的 lean 选项与本树相同（`weak.linter.mathlibStandardSet=true`、
  `maxSynthPendingDepth=3`、`pp.unicode.fun`），所以漂移修好后警告应接近零；残余的纯风格警告可保留，
  但要在修改日志里逐条列出。
- 不弱化目标：桥接定理的陈述必须是消费者需要的形式（见 §4.2），上游如果证得更弱，报告差距而不是改陈述。
- 状态登记：`E:\differential-geometry-dev\WORKING_STATUS.md` 末尾加一条 "Moise smoothing S(Codex) 2026-09-14"
  （只编辑不提交）。

## 2. 验证配方

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File D:\differential-geometry-moise-s\.lake\scratch\tools\check-f.ps1 `
  -Module External.ClassificationOfSurfaces.Moise.PlaneComplex *> D:\differential-geometry-moise-s\.lake\scratch\pc.log
$env:PYTHONIOENCODING='utf-8'; python D:\differential-geometry-moise-s\.lake\scratch\tools\errblocks.py D:\differential-geometry-moise-s\.lake\scratch\pc.log
powershell -NoProfile -ExecutionPolicy Bypass -File D:\differential-geometry-moise-s\.lake\scratch\tools\audit-f.ps1 -File '.lake/scratch/AuditS1.lean'
```
要求 exit=0、零错误；原生文件零警告；被 import 的模块必须先通过检查（olean 已生成）。审计文件模板
`.lake/scratch/AuditTemplate.lean`；期望每条 `depends on axioms: [propext, Classical.choice, Quot.sound]`。
Moise 原书：`.lake/scratch/moise_gtm47.pdf`（书页 p = PDF 页 p+10；§2–§10 在书页 16–80，§17 在 117–126）。

## 3. 源材料

上游全仓库源码在 `D:\differential-geometry-moise-s\.lake\scratch\ext\classification-of-surfaces\`
（`ClassificationOfSurfaces/`、`LICENSE`、`README.md`、`docs/ARCHITECTURE.md`、`lakefile.toml`、`lake-manifest.json`、
`lean-toolchain`、`PROVENANCE.txt`）。上游 Lean 4.32.0 / Mathlib 81a5d25；本树 v4.33.1 / Mathlib 0df444a。

第一批（多边形 Jordan + 多边形 Schoenflies 闭包，16 个模块，25.5k 行，全在 `ClassificationOfSurfaces/Moise/`）：
`PlaneComplex`（`abbrev Plane := EuclideanSpace ℝ (Fin 2)`、`IsTriangle`、`PlaneComplex`、`IsPure2`、`support`）、
`FinitePLHomeomorph`（`structure FinitePLHomeomorphOn (h : Plane ≃ₜ Plane) (A : Set Plane)`：一个纯 2 维平面复形，
支撑为 `A`，`h` 在每个胞腔上仿射）、`AmbientHomeomorph`、`CommonSubdivision`、`ConeExtension`、`ElementaryMove`、
`FreeTriangle`、`FreeTriangleMove`、`GeometricTriangulation`、`LineSubdivision`（3984 行）、`PLMoves`、`PolygonalCrosscut`、
`PolygonalJordan`（4158 行：`PolygonalCircle`（`n ≥ 3`、`vertex : ZMod n → Plane`、相邻顶点不同、相邻边只交于公共顶点、
非相邻边不交）、`carrier`、`interiorRegion`、`exteriorRegion`、`closedRegion`、`frontier_interiorRegion : frontier J.interiorRegion = J.carrier`、
`isCompact_closedRegion`…）、`PolygonalPolyhedron`、`ThinKiteMove`、`PolygonalSchoenflies`（3023 行）。
上游关键定理（`PolygonalSchoenflies.lean`）：
```lean
theorem closedRegion_is_polyhedron : ∃ K : PlaneComplex, K.support = J.closedRegion ∧ K.IsPure2      -- Moise §2 Thm 2
theorem closedRegion_triangulable : Nonempty (GeometricTriangulation J.closedRegion)
theorem polygonal_schoenflies_rel (U : Set Plane) (hU : IsOpen U) (hregion : J.closedRegion ⊆ U) :  -- Moise 3.7
    ∃ h : Plane ≃ₜ Plane, ∃ _ : FinitePLHomeomorphOn h J.closedRegionMesh.toPlaneComplex.support,
      (∃ C : Set Plane, IsTriangle C ∧ h '' J.carrier = frontier C ∧ h '' J.closedRegion = C) ∧ Set.EqOn h id Uᶜ
theorem polygonal_schoenflies (J' : PolygonalCircle) : ∃ h : Plane ≃ₜ Plane, h '' J.carrier = J'.carrier   -- Moise 3.6
```
第二批（平面 PL 逼近闭包，在第一批之上再加 10 个模块，约 10.6k 行）：`PLApproximation`（`pl_approximation_one_skeleton`、
`pl_approximation_pure_two_complex`、`pl_approximation_two_manifold`）、`PlaneCycle`、`PolygonalArc`、`PolygonalArcModel`、
`PolygonalFamilyPolyhedron`、`OpenMidpointComplex`、`IntrinsicSubdivision` 等（用 import 闭包确定）。
第三批（可选）：`LocallyFinite*`、`GeometricTriangulation`、`moise_triangulation`（2-流形三角剖分定理，Moise §8）。

本车道词汇（`DifferentialGeometry/Topology/PiecewiseLinear/`）：`IsPLHomeomorphOn f P Q`（`Polyhedron.lean`）、
`IsPLBall n P`、`IsPLSphere n P`（模型 `stdSimplex`/`stdSimplexBoundary`）、`isPLBall_convexHull_of_affineIndependent`
（`SimplexBall.lean`）、`simplexBoundary`、`isPLSphere_biUnion_erase`（`SimplexBoundary.lean`）、
`exists_isGlueIso_of_isPLHomeomorphOn`（`IsomorphicSubdivision.lean`：PL 同胚的复形有同构细分）、`simplicialMap`、
`IsGlueIso`、`boundaryComplex`（`ManifoldWithBoundary.lean`）、`exists_isPLHomeomorphOn_of_boundaryComplex`
（`BoundaryExtension.lean`：PL 球边界同胚的锥延拓，可用于 5.4）、E.0 的 `invariance_of_domain_isOpen_image`
（`Topology/InvarianceOfDomainManifold.lean`）。F 车道交接文档 `HANDOFF_CODEX_F.md` §5 有更全的签名表。

## 4. 砖块

### 砖 S0.1 vendoring 第一批

- 目录 `External/ClassificationOfSurfaces/Moise/<同名>.lean`，模块名 `External.ClassificationOfSurfaces.Moise.<同名>`；
  内部 `import ClassificationOfSurfaces.Moise.X` 改成 `import External.ClassificationOfSurfaces.Moise.X`。
- 在 `lakefile.toml` 增加 `[[lean_lib]]`、`name = "External"`（本树目前只有 `DifferentialGeometry` 一个 lib；
  规则 4 规定 vendored 代码放 `External/`，将来 lake 构建需要这条；提交信息里说明）。
- `External/ClassificationOfSurfaces/LICENSE`（上游全文）、`External/ClassificationOfSurfaces/VENDOR.md`：来源仓库与
  commit、作者、许可证、导入日期、导入的模块清单与 Moise 编号对照、**逐文件修改日志**（每处 import 改名、
  每处 API 漂移修正、每处为通过检查而做的改动）。
- 按依赖顺序逐模块 `check-f`（先用一段脚本从 import 图算拓扑序），每个模块 exit=0、零错误；
  不得引入 `sorry`；风格警告按 §1 处理。第一批全部通过后，写 `.lake/scratch/AuditS1.lean` 审计
  `polygonal_schoenflies_rel`、`polygonal_schoenflies`、`closedRegion_is_polyhedron`、`frontier_interiorRegion`，
  应只含标准三公理。

### 砖 S0.2 原生桥接 `DifferentialGeometry/Topology/PiecewiseLinear/PlanarSchoenflies.lean`

```lean
-- 记 P2 := EuclideanSpace ℝ (Fin 2)（上游的 Plane 就是它，可直接互换）
theorem isPLSphere_one_carrier (J : PolygonalCircle) : IsPLSphere 1 J.carrier
theorem exists_polygonalCircle_of_isPLSphere_one {S : Set P2} (hS : IsPLSphere 1 S) :
    ∃ J : PolygonalCircle, J.carrier = S
theorem isPLBall_two_closedRegion (J : PolygonalCircle) : IsPLBall 2 J.closedRegion
theorem frontier_closedRegion (J : PolygonalCircle) : frontier J.closedRegion = J.carrier
theorem isPLBall_of_isPLSphere_one {S : Set P2} (hS : IsPLSphere 1 S) :          -- P.1（3.6 + 5.3）
    ∃ D : Set P2, IsPLBall 2 D ∧ frontier D = S ∧ Bornology.IsBounded D
theorem exists_isPLHomeomorphOn_straighten_of_isPLSphere_one {S : Set P2} (hS : IsPLSphere 1 S)   -- 3.7 相对形式
    {U : Set P2} (hU : IsOpen U) (hSU : closure (bounded component) ⊆ U) :
    ∃ h : P2 → P2, IsPLHomeomorphOn h univ univ ∧ Set.EqOn h id Uᶜ ∧
      ∃ C : Set P2, IsTriangle C ∧ h '' D = C ∧ h '' S = frontier C
```
证明要点：
- `carrier → IsPLSphere 1`：`carrier` 是 `n` 条线段的圈；用 `simplexBoundary` 模型上的 `n` 等分细分与逐段仿射的
  `simplicialMap`，或直接构造 `stdSimplexBoundary 2 → carrier` 的 PL 双射（`IsGlueIso` 给 PL 同胚）。
- `IsPLSphere 1 → PolygonalCircle`：`hS` 给 `f : ∂Δ² → S` PL 同胚；`exists_isGlueIso_of_isPLHomeomorphOn` 把它变成
  `∂Δ²` 的某个细分（一个 `n`-圈）到 `S` 的三角剖分的单纯同构，顶点按圈序读出即 `vertex : ZMod n → P2`；
  `adjacent_ne`/`consecutive_inter`/`nonadjacent_disjoint` 来自单射性与复形公理。
- `IsPLBall 2 J.closedRegion`：`polygonal_schoenflies_rel univ` 给 `h`，`h '' closedRegion = C` 三角形，`h` 在
  `closedRegionMesh` 支撑（= `closedRegion`）上逐胞腔仿射 ⟹ 本车道的 `IsPLHomeomorphOn h closedRegion C`
  （用 `isPiecewiseAffineOn_of_forall_isHPolytope` 或 `isPiecewiseAffineOn_space_of_forall_face`，逆映射同理），
  `C` 是 `IsPLBall 2`（`isPLBall_convexHull_of_affineIndependent`），`IsPLBall.of_isPLHomeomorphOn`。
- 相对形式的 `IsPLHomeomorphOn h univ univ`：核查上游 `FinitePLHomeomorphOn h A` 是否蕴含 `h` 在 `U \ A` 上也 PL
  （查 `AmbientHomeomorph.lean` 与 `polygonal_schoenflies_rel` 的构造）。若上游只给 `A` 上 PL、`Uᶜ` 上恒同，
  就先陈述并证明这个较弱版本（明确命名 `_on_closedRegion`），在报告与计划行里写出差距，不要伪装。
- 对照计划行 P.1–P.5 与 Moise 编号（3.3、3.6、5.3、5.4、10.8、2.7–2.8、4.4）写状态列；5.4 用 `BoundaryExtension` 的
  `n = 1` 实例加本砖；10.8 看第二批是否覆盖。

### 砖 S0.3（视 P.4/P.5 需要）vendoring 第二批并桥接 `pl_approximation_*`

先把第二批各定理对应到 Moise 编号（§5 Thm 3–4、§6、§10 Thm 6–8），只有在它覆盖 P.4（10.8）或 P.5 时才导入；
导入后同 S0.1 的规则，桥接到 `IsPLHomeomorphOn`/`IsPolyhedron`。

### 砖 S1 `DifferentialGeometry/Topology/PiecewiseLinear/FrontierBoundary.lean`（计划行 S.1 与 M.2 的 ℝ³ 形式）

```lean
theorem frontier_space_eq_boundaryComplex_space {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    frontier K.space = (boundaryComplex 3 K).space
```
路线：内部顶点（link 球面）的开星是 `K.space` 内的开集且经 `invariance_of_domain_isOpen_image`（E.0）在 ℝ³ 中开；
边界点 `x`（link 球）的闭星是 PL 3-球 `B = f(Δ)` 且 `x = f(y)`，`y ∈ ∂Δ`；若 `K.space ∈ 𝓝 x` 则 `f⁻¹` 在含 `x` 的开集上
连续单射，像是 `Δ` 内含 `y` 的开集，与 `y ∈ ∂Δ` 矛盾（E.0）。`boundaryComplex` 的点的 link 刻画见
`BoundaryFaces.lean`、`BoundaryOfBall.lean`（`boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex`）。
E3 车道会证"边界点集在 PL 同胚下不变"；若你先需要，可在本文件内证明并通知（避免重复：先看 `codex/moise-e3` 分支）。

### 之后：S.2（17.4–17.8 推移性质）、S.3、S.4（17.12 ℝ³ 的 PL Schoenflies，§17.10–17.12 用到 3.7 相对形式与 F5.1 的
水平平面族 `exists_generalPosition_height_fibers`）。开工前把 §17 的逐条陈述写进计划行 S.2–S.4 的"拟定 Lean"列。

## 5. 记录与汇报

- 每砖通过后更新 `PHASE3_APPROXIMATION_PLAN.md` 对应行（P.1–P.5、S.1…）与 `MOISE_PLAN.md` §6；这两个文件
  F 车道也在改：先 `git fetch origin`，把改动放在最后一次提交并在 `origin/codex/moise-smoothing` 上 rebase 后再推。
- 审计文件 `AuditS<k>.lean` 递增；报告：模块、端点、审计、检查退出码、上游差距、修改日志位置。

## 6. Lean 坑（本车道实测）

- `rw` 关闭目标后再 `rfl` 报 "No goals"；`rcases … with rfl` 会消去固定变量；`▸` 高阶合一易选错实例，改用 `have … := by rw [heq]; exact h`。
- linter `unusedSectionVars`/`unusedDecidableInType`：`[DecidableEq E]` 只放在需要的陈述上，证明里 `classical`；纯 Finset 引理 `omit … in`。
- `open Classical` 下 `not_imp` 有歧义，用 `Classical.not_imp`。
- Git Bash 里 `grep -P` 不可用（locale），用 `sed -n 's/…/\1/p'` 提取名字。
- 上游文件用 Lean 4.32 写：`Set.image`、`Function.extend`、`OpenPartialHomeomorph` 字段、`Topology.IsEmbedding` 等命名可能已变，逐个用 `exact?`/搜索修，并记入修改日志。

## 7. 2026-09-15 追加：P.1 的重复与分工

- F 车道按其旧计划也原生证明了 P.1（`PolygonalSchoenflies.lean`：`isPLBall_of_isPLSphere_one`、
  `exists_polyhedral_region_of_isPLSphere_one` 等，已在 `origin/codex/moise-smoothing`，你的分支合并 F 后已含）。
  这是我的排程失误。处理：F 的原生陈述作为 P.1 的规范陈述；你的 vendored 链继续提供 3.7 相对形式与 §5–§8 材料；
  不要再证 P.1，需要时写一条桥接引理把两边的陈述连起来；计划行 P.1 状态列注明"两条证明：F 原生（规范）、S vendored（3.7）"。
- S.5（两 3-球沿边界盘并为 3-球）、S.2–S.4、S.7 仍由本车道负责；F 车道已被告知不再进入 S.* 与 P.* 项。
- F 车道最新模块的 olean 目前写在它的私有目录（`D:\differential-geometry-moise-plan\.lake\scratch-lib`），共享库里
  可能没有：import F 的新模块若报 unknown module，报告，不要把 `f-lib` 加进搜索路径。

## 8. 2026-09-15：17.5 局部延拓引理的未验证交接

- 分工更正：07:35 发给 C 线程的 §7 消息原属 S 线程；S.2–S.5 继续由 S 线程负责，C 线程到此停止在本工作树中的编辑与 Lean 检查。
- 新文件 `DifferentialGeometry/Topology/PiecewiseLinear/RelativeThinKite.lean` 保留了 17.5 的局部延拓候选：
  `TriangleMesh.exists_eventually_transportedThinKitePatch_inter_edge_subset_baseEndpoints`、
  `TriangleMesh.exists_supported_triangle_push_fixing_boundaryCarrier_and_family`、
  `PolygonalCircle.exists_thinKite_fixing_outside_triangle_and_family`。其作用是对有限受保护边族统一选择薄风筝厚度，使局部推移既支撑于给定开集，又固定旧边界和受保护边族。
- `PlanarSchoenflies.lean` 已接入上述候选，并增加带 `_and_family` 后缀的一边自由、两边自由和一般几何自由三角形删除命题；原有端点保留为兼容包装。这些改动同样尚未完成最终复核。
- 最后一次实际运行 `check-f.ps1 -Module DifferentialGeometry.Topology.PiecewiseLinear.RelativeThinKite -Threads 2` 的退出码为 1。它报告四处问题：错误调用
  `M.mem_simplexes_of_mem_cells`；`M.toPlaneComplex.position` 与 `M.position` 阻止用 `hface` 改写；无法直接取得受保护边成员关系；以及 `simp` 参数 `hvw` 未使用。随后已分别改为
  `M.toPlaneComplex.mem_simplexes_of_mem_cells T.2`、先用 `change` 统一 `hface` 的位置/载体表示、改写后显式给出 `exact hp.2`、移除 `hvw`，但遵照停止指令没有重新检查。因此当前 `RelativeThinKite.lean` 不能记为已通过。
- `PlanarSchoenflies.lean` 在接入较早版本时曾以退出码 0 通过，但有一个 `hk` 未显式使用的警告；已把相应依赖函数的绑定形式改为匿名蕴含以消除该警告，之后因 `RelativeThinKite.lean` 又有改动而没有复核。当前文件不能记为零警告通过。
- S 线程接手后的最小复核顺序是先检查 `RelativeThinKite`，再检查 `PlanarSchoenflies`；本次没有运行审计，也没有修改计划文件。
- 完成 Moise 17.5 仍缺：把球面三角剖分/`FaceStarDeletion` 接到受保护边族；证明局部星之外每个保留三角形的边界被固定，并用平面紧区域识别推出该三角形集合保持；证明一次删除后的整盘精确像；在保留指定三角形的条件下归纳删除自由三角形；最后用单纯形顶点星的锥形图表作环境延拓。故 17.5、17.6、17.8 均未闭合，S.3/S.4 仍受 17.6/17.8 阻塞。

- S 线程恢复后的复核（2026-09-15）：从干净且与远端一致的 `5d7a83446` 接手；修正 `RelativeThinKite` 中三角形成员资格到 `toPlaneComplex.cells` 的转换。按依赖顺序重建 `RelativeThinKite`、`PlanarSchoenflies`、`FaceStarBoundary`、`PlanarFreeFace`、`FaceStarDeletion`，最终均 exit 0、零警告。`AuditS29.lean` 的 23 个不同声明均仅含标准三公理，exit 0。此前“未验证”记录是交接时状态；当前源码已复核，17.5/17.6/17.8 的数学缺口仍保留。


## 9. 2026-09-15：S.2 的 17.5、17.6、17.8 全部闭合

- 本轮从干净且与远端一致的 `5d7a83446` 接受 `e21341229` 及后续 C 线程提交；没有回退交错编辑。
  修正并重建 `RelativeThinKite`、`PlanarSchoenflies`，再复核 `FaceStarBoundary`、`PlanarFreeFace`、
  `FaceStarDeletion`。最终均 exit=0、零警告；AuditS29 的 23 个不同声明仅含标准三公理。
- 会话要求的 integration 合并已由 `bbf60272f` 完成（合入当时的 `74117a65b`）。
  最终计划更新前重新 `git fetch origin`，确认本地与 `origin/codex/moise-s` 一致。
- `9701b821a` 给一次完整球面盘删除：局部平面移动保护外部三角形，经四面体顶点图与内外锥扩张后，
  保持整个四面体，整个圆盘的像等于删去该自由三角形的复形，且固定指定邻域外。
- `2fe7240ef` 的 `SimplexDiskStraightening.lean` 完成有限三角形递降归纳和原始面比较。
  17.5 端点 `exists_isPLHomeomorphOn_straighten_disk_in_tetrahedron` 对任意四面体边界 PL 圆盘成立，
  保留实际 frontier 与指定开邻域的精确量词；没有剖分、平面模型、Brouwer 类或未证生产者输入。
- `16ade009b` 的 `TetrahedronPush.lean` 给 17.6 `hasPushProperty_convexHull_simplex`；
  `SimplyEmbedded.lean` 定义对每个凸开邻域均有支持控制的 `IsSimplyEmbedded`，并给 17.8
  `exists_hasPushProperty_of_isSimplyEmbedded`，输出有界 PL 3-球、准确 frontier 和推移性质。
- 本轮 18 个新增或修改的原生模块以及上述 3 个指定复核依赖，共 21 个模块的最终聚焦检查均 exit=0、
  零警告。`.lake/scratch/S2-VERIFICATION.json` 保存日志位置和源码 SHA-256。
  AuditS38 四项、AuditS39 的完整 17.4–17.8 十项均只有 `propext`、`Classical.choice`、`Quot.sound`。
  原生源码没有注释、docstring、诊断命令、资源覆盖或证明占位；没有新增 vendored Lean 修改。
  所有原生适配差异与分层验证记录在 `External/ClassificationOfSurfaces/VENDOR.md`。
- S.2 已完成。下一段工作是 S.3（17.9–17.11）与 S.4（17.12）；P.3 的一般胞腔分解及避开给定真盘
  子复形的形式仍未完成，P.4、P.5 的既有上游差距仍保留。不要把已证 17.8 升格为任意 PL 2-球面的
  Schoenflies 定理，也不要再把 17.6/17.8 记为阻塞项。
