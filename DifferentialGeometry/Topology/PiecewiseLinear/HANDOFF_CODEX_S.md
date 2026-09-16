# S 车道交接：移植 Moise §2–§10 平面 PL 链（vendored）并桥接到本车道词汇

交接日期 2026-09-14。本文件是接手者的唯一入口。目标是让 `PHASE3_APPROXIMATION_PLAN.md` §4.1 的
P.1–P.5 与 §4.2 的 S.1 尽快成为"已证生产者"，后续责任划分与最新交付见 §11。

## 0. 任务

1. 把外部仓库 mccorvie/classification-of-surfaces@e3c7230（Apache-2.0，sorry-free）里 Moise §2–§10 的
   平面 PL 链按 `AGENTS.md` 规则 4 **vendored** 到 `External/ClassificationOfSurfaces/…`，保留上游注释、
   docstring、命名空间与出处；只做 import 路径、Mathlib API 漂移等必要修改，逐条记入修改日志。
2. 写**原生**桥接模块（零注释），把上游结论翻译成本车道词汇（`IsPLSphere 1`、`IsPLBall 2`、
   `IsPLHomeomorphOn`、`IsTriangle`…），闭合计划行 P.1（3.6/5.3）、3.7 相对形式、P.2（5.4）、
   以及 P.3/P.4/P.5 中上游已覆盖的部分；把对照写进计划行。
3. S.1–S.3、P.3 的一般 17.2 与 S.5 已交付；**S.4（17.12）由 F 车道负责**。当前先交付一般 `hpush`，再做 §26.2，均只允许完整 `hSchoenflies` 为未交付的定理输入。局部构造的已证范围及整盘归纳缺口见 §11。

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

### 后续责任划分（以 2026-09-15 指令为准）

S.2、S.3 与一般 17.2 已完成；S.4 由 F 车道负责。S 车道的 S.5 当前交付强度与最后一个外部输入见 §10。

## 5. 记录与汇报

- 数学层逐砖提交并推送；`PHASE3_APPROXIMATION_PLAN.md`、`MOISE_PLAN.md` §6 与交接状态放在最后一次提交。
  按最新会话指令，在每个检查点先 `git fetch origin`，再 `git merge --no-ff origin/codex/moise-integration`；
  计划文件冲突保留双方内容。此规则取代初始 rebase 配方，不改写已发布历史，不合入其它分支。
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
- S.2 完成时的后续安排如下，现已由 §10 更新：S.3（17.9–17.11）与 S.4（17.12）；P.3 的一般胞腔分解及避开给定真盘
  子复形的形式仍未完成，P.4、P.5 的既有上游差距仍保留。不要把已证 17.8 升格为任意 PL 2-球面的
  Schoenflies 定理，也不要再把 17.6/17.8 记为阻塞项。

## 10. 2026-09-15：S.3、一般 17.2 与 S.5 当前交付

工作树与分支仍为 `D:/differential-geometry-moise-s`、`codex/moise-s`。数学检查点 `08ee37003`
已推送；各检查点按最新指令合并 integration，最终同步包含 `4a70576a0`，没有改写已发布历史。
S.4 已移交 F，本会话不实现 17.12。

| 项目 | 模块与端点 | 强度与提交 |
|---|---|---|
| 17.9 | `ConvexStraightening.lean`：`isSimplyEmbedded_frontier_of_convex` | 无条件；`97995c328` |
| 17.10 | `ConeStraightening.lean`：`isSimplyEmbedded_frontier_coneComplex` | 任意 PL 二维底盘、有限复形与 `IsConeBase`；无条件；`26d321906` |
| 17.11 | `PlanarDiskGluing.lean`：`isSimplyEmbedded_union_sdiff_diskInterior`、`_of_subset_fiber` | 仿射平面及 F 的精确线性层形式；删除盘的内在内部；无条件；`f1d104761`、`caa641003` |
| 17.2 | `FreeDiskCell.lean`：`IsPLDiskDecomposition.exists_two_free_disk_cells`、`.exists_free_disk_cell_ne` | 任意有限维实赋范空间、任意圆盘胞腔的共同有限三角剖分；无条件；`08ee37003` |
| F 的输入 | `SchoenfliesFoundations.lean`：`schoenflies_input : SchoenfliesInput` | 四字段全部已证；接口原样来自 F 的 `44806ee61`；`08ee37003` |
| 23.9 | `SchoenfliesManifold.lean`：`exists_isPolyhedralBall_of_isPolyhedralSphere_in_chart`、`_in_openStar` | 显式假设完整 17.12；填充位于原图卡/顶点开星；`434c3970b` |
| 23.10 | `PushManifold.lean`：`exists_isPL_homeomorph_push_disk_in_chart`、`exists_isPL_homeomorph_push_between_disks_in_chart`、`_in_openStar` | 显式假设完整 17.12；保留精确相对邻域与双向 PL；`30f9f6f6e` |
| 23.11 | `BallGluing.lean`、`BallGluingManifold.lean`：`isPLBall_union_of_inter_isPLBall_two`、`isPolyhedralBall_union_of_inter_isPolyhedralBall_two` | 无条件；共同有限维环境、PL piece 与任意有限组合三维流形；允许不同顶点星；`a5f38dd84`、`8e9d6309a` |

### 验证与来源

- 最终 9 个端点模块全部 exit=0、零警告；AuditS62 的 16 个声明全部只有标准三公理。
  AuditS61 另检查第四字段的精确三维类型和完整 `SchoenfliesInput` 值。
- `.lake/scratch/S3-P3-S5-VERIFICATION.json` 保存数学提交、源码 SHA-256、端点模块日志与审计日志。
  `.lake/scratch/audit-s3-p3-s5-final.log` 是最终公理输出。
- 一般 17.2 的证明层依次为 `DiskDecomposition`、`PolygonalArc`、`DiskCrosscut`、
  `PlanarDiskUnion`、`PlanarDiskSplit`、`PlanarDiskDecomposition`、`FreeDiskCell`。
  横切弧将不自由胞腔扩成两个严格较小的圆盘子族；有限交点与删有限点稠密性确保子盘自由胞腔传回原盘。
- 每层的检查、审计和数学差异均记录在 `External/ClassificationOfSurfaces/VENDOR.md`。
  本轮全部为原生证明，未改 vendored Lean 源码；未运行 lake build，未登记根聚合。

### 唯一待交付的 S.5 输入及余项

23.9/23.10 的显式参数为
`∀ S : Set (EuclideanSpace ℝ (Fin 3)), IsPLSphere 2 S → IsSimplyEmbedded S`。
F 交付 17.12 后，使用已证 `schoenflies_input` 实例化其接口，再解除这两类端点的显式参数并重检、审计。
三公理审计不表示这个命名参数已经被消掉。23.11 不依赖该参数。

一般 17.2 已闭合；17.3 的“避开指定真盘子复形”仍未证。不要把 `.exists_free_disk_cell_ne`
避开一个胞腔的推论当作 17.3。P.4/P.5 的既有余项仍保留，优先级低于解除 S.5 的 17.12 输入。

## 11. Boundary push-offs and the collar: current partial checkpoint

The current assignment is the general `hpush` producer for the sphere
case of the Loop theorem, followed by Theorem 26.2. Both global endpoints
may use only the explicit full `hSchoenflies` assumption specified by the
owner. S.4 remains owned by F. The later 17.3 and P.4/P.5 work follows the
collar. Other lanes' files must be acquired only by merging
`origin/codex/moise-integration`; copying, cherry-picking, and direct lane
merges are prohibited.

This continuation merged `fb4d53931` in `4511df016`, then integrated
`2b6c8a4a8` in `5967f629c`. No other lane branch was merged.

### Verified mathematics

- `fc3846d10`: `ConvexCone.lean` proves cone containment and exact frontier
  intersection. `FrontierBoundary.lean` exposes `C ⊆ K.space` through
  `exists_isPLBall_subset_inter_boundary`, preserving the earlier API.
- `BoundaryBall.lean`: `exists_isPLBall_subset_inter_frontier` cuts an
  arbitrary prescribed boundary disk out of a PL ball. The general
  finite-dimensional result returns a smaller PL ball with exactly the
  required frontier intersection. `exists_isPLBall_inter_frontier_eq_of_subset`
  applies this inside an ambient set M once a PL ball C contained in M
  and containing the disk is supplied.
- `LoopTheorem/BoundaryPush.lean`: the complement disk in the frontier of
  a boundary ball becomes a nonsingular `SingularTwoCell`, with its image
  in M and its exact boundary and boundary-intersection images. The
  theorem `exists_nonsingular_two_cell_in_boundary_ball` consumes an
  actual PL ball C contained in M and containing the disk. The ball-host
  case and a neighborhood version at each boundary point are proved.
- `565acc75c`: `BoundarySubdivision.lean` proves simultaneous ambient
  refinement subordinate to boundary-ball neighborhoods, then supplies
  an exact boundary ball for every face star of the boundary disk
  subcomplex. These are local balls; compatibility of their intersections
  is not asserted.
- `64da311fb`: `SphericalDiskExtension.lean` extends a disk
  self-homeomorphism fixed on its parameter boundary to its containing
  sphere and ball, fixing the closed complement disk. The union version
  extends by the identity across a polyhedron meeting only that fixed
  complement.
- `01d5fb185`: `SubcomplexComplement.lean` proves
  `IsPolyhedron.closure_sdiff`. `AmbientExtension.lean` extends a PL
  self-homeomorphism of C to M by the identity on `closure (M \ C)`:
  its hypotheses are `C ⊆ M`, an open U with `U ∩ M ⊆ C`, and fixing
  `frontier C \ U`. `BoundaryDiskExtension.lean` applies this to boundary
  disks. Its `exists_isPLHomeomorphOn_extension_boundary_patch` consumes
  precisely the ball and neighborhood conditions of the local
  construction, and derives the disk-rim compatibility itself.

All nine changed/new modules passed the prescribed focused checks,
with exit 0 and zero warnings. AuditS63 has 12 declarations, AuditS64
has two, AuditS65 has five, and AuditS66 has four. All 23 axiom closures
contain only `propext`, `Classical.choice`, and `Quot.sound`. The local
results need no Schoenflies hypothesis.
`External/ClassificationOfSurfaces/VENDOR.md` records scope and logs;
no vendored Lean source was changed. The new modules were not registered
in the root aggregate and no `lake build` was run. After `01d5fb185`,
`git fetch origin` and the requested integration merge reported
`Already up to date`.

### Exact remaining mathematical obligation

For a finite combinatorial 3-manifold with boundary K and a PL disk
`D ⊆ frontier K.space`, first prove the existence of a PL 3-ball C with
`C ⊆ K.space` and `D ⊆ C`. This is Problem 26.1, printed page 195.
`exists_isPLBall_inter_frontier_eq_of_subset` then gives the exact
boundary intersection, and `exists_nonsingular_two_cell_in_boundary_ball`
gives the requested push-off with image in K.space.

The local face-star balls from `BoundarySubdivision` do not yet solve
this obligation: their mutual intersections are uncontrolled. A finite
cover alone cannot be fed to 23.11. The new boundary-patch extensions
supply individual relative maps on M, with compatibility across the
actual complement proved. What remains is to construct the finite
sequence of disk moves (or compatible ball attachments) for the entire
disk using 23.9/23.10 and 23.11. The local extension theorem does not
supply that sequence. Do not add it as a new hypothesis to the
advertised global theorem or label general `hpush` complete. Full
Theorem 26.2, arbitrary neighborhood control, and the product collar
have not been proved in this continuation.

### Reproducible checks

- `.lake/scratch/check-convexcone-boundary.log`
- `.lake/scratch/check-frontierboundary-boundary.log`
- `.lake/scratch/check-boundaryball-boundary.log`
- `.lake/scratch/check-looptheorem-boundarypush-boundary.log`
- `.lake/scratch/check-boundary-subdivision.log`
- `.lake/scratch/AuditS63.lean` and `audit-boundary-push-local.log`
- `.lake/scratch/AuditS64.lean` and `audit-boundary-subdivision.log`
- `.lake/scratch/check-relative-disk-extension.log` and `AuditS65.lean`
- `.lake/scratch/audit-relative-disk-extension.log`
- `.lake/scratch/check-polyhedron-complement.log`
- `.lake/scratch/check-relative-polyhedron-extension.log`
- `.lake/scratch/check-boundary-disk-extension.log`
- `.lake/scratch/AuditS66.lean` and `audit-polyhedron-boundary-extension.log`

The shared `BallFrontier.olean` was observed to contain the differently
named `IsPLHomeomorphOn.image_stdSimplexBoundary`, whereas the current
integration source exports `image_stdSimplexBoundary_eq_frontier`.
Refreshing `BallFrontier` with the prescribed S script immediately before
checking `BoundaryPush` resolved the mismatch. Do not copy the other
lane's source or rename a consumer to an unmerged declaration merely to
match a shared artifact.

## 12. Regular-neighborhood piece checkpoint (2026-09-15)

Integration dependencies were obtained only by the requested merges:
`0b06c672f` merged b9a2cb2ca; after the mathematical checkpoints,
`f43dacc60` merged integration 8fb887bb9, adding `NIGHT_PLAN.md` only.
No other lane's checkout, branch, or source file was used for transfer.

### Completed: checkpoint 1)-2), or S-M1

- `249311c83`, `DerivedNeighborhoodCells.lean` and `BallFrontier.lean`:
  `derivedNeighborhoodCell` is the centroid closed star in the second
  derived subdivision. `derivedNeighborhoodCell_space` proves its exact
  equality with `closure (N(s) \ N(boundary s))`;
  `derivedNeighborhoodCell_singleton` identifies N(v).
  `isPLBall_derivedNeighborhoodCell` proves ballness for finite
  combinatorial manifolds with boundary in all indicated dimensions.
  `isPLBall_derivedNeighborhoodCell_inter_of_nonempty` proves the
  codimension-one ball intersection for distinct pieces, and
  `derivedNeighborhoodCell_inter_subset_frontier` puts the intersection
  in each frontier in the matching Euclidean dimension. The pieces
  cover the existing derived neighborhood and stay in K.space.
- Both focused checks exit 0, zero warnings. AuditS67 checks all 26
  new declarations, with only the three standard axioms.

This proof uses the existing PL link equivalence and cone theorems for
sphere links and ball links. No Schoenflies assumption is needed for
this layer; the regular-neighborhood definition has not changed.

### Partial: disk shelling, or S-M2

- `57a3f6a4e`, `DerivedNeighborhoodAttachments.lean`, `DiskUnion.lean`,
  and `BoundaryDerivedNeighborhood.lean`: intersections indexed by a
  face flag are the corresponding dual cell; a central piece and
  incomparable incident pieces glue to a 3-ball. Boundary-piece bases
  are PL 2-disks, all other intersections lie in the base, and triple
  face-flag intersections are PL arcs. The grouped attaching-disk
  theorem `isPLBall_derivedNeighborhoodCell_inter_union` handles a
  boundary piece meeting one central piece and incomparable arms.
  All three focused checks exit 0, zero warnings. AuditS68 has 14
  declarations, each with only the three standard axioms.
- `ee2a8a29d`, `SimplexDerivedNeighborhood.lean`:
  `IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_simplex`
  proves that the complete derived neighborhood of any boundary simplex
  of a finite combinatorial 3-manifold in Euclidean 3-space is a PL
  3-ball. The triangle case explicitly glues its triangle piece, three
  edge pieces, and three vertex pieces. The vertex and edge cases are
  included. The focused check exits 0, zero warnings; AuditS69 has two
  public declarations, each with only the three standard axioms.

These give the simplex base case and local grouped attachments. They
do not yet give the full disk induction. The precise next obligation
is to use `exists_isPLBall_eraseTriangleComplex_of_isGlueIso_planar`
(or the general 17.2 interface) to classify which proper faces of a
free triangle survive in the erased disk. The new triangle piece meets
old pieces along the subdivided attaching arc; each newly added edge
or vertex must then have its intersection with the whole accumulated
union identified with one of the checked grouped disks. Pairwise disk
intersections alone do not justify that induction.

Only after this step may Problem 26.1 and general hpush be marked done.
`exists_isPLBall_inter_frontier_eq_of_subset` and
`exists_nonsingular_two_cell_in_boundary_ball` remain the checked
Euclidean consumers. NIGHT_PLAN I2 additionally requires the intrinsic
version in K.space for general finite-dimensional E; the Euclidean
simplex endpoint does not by itself satisfy that interface. The full
26.2 product collar and neighborhood control remain open. No new
unproved hypothesis or axiom was added to any endpoint.

### Verification artifacts

Six changed/new mathematical modules have final focused-check exit 0
and zero warnings. AuditS67-S69 contain 42 declarations in total.
The logs and audit files are in this worktree's `.lake/scratch`:

- `check-ball-frontier.log`, `check-derived-neighborhood-cells.log`,
  `AuditS67.lean`, `audit-derived-neighborhood-cells.log`.
- `check-derived-neighborhood-attachments.log`, `check-disk-union.log`,
  `check-boundary-derived-neighborhood.log`, `AuditS68.lean`,
  `audit-derived-neighborhood-attachments.log`.
- `check-simplex-derived-neighborhood.log`, `AuditS69.lean`,
  `audit-simplex-derived-neighborhood.log`.

`External/ClassificationOfSurfaces/VENDOR.md` records the native proof
route, exact scope, and logs. No vendored Lean file or root aggregate
was modified. No lake build was run. The Euclidean simplex module uses
a local classical decidable-equality instance so that the fixed
Euclidean type and generic boundary-complex APIs use the same instance.

## 13. NIGHT_PLAN progress, 2026-09-15 evening

Integration was fetched and checked at `8fb887bb9`; the initial merge was already up to date.
The following checkpoints are pushed to `origin/codex/moise-s`.

### S-M1: done, now intrinsic in arbitrary finite-dimensional ambient spaces

`2375fc812` generalizes `IsCombinatorialManifoldWithBoundary.isPLBall_union_derivedNeighborhoodCells`,
`isPLBall_union_derivedNeighborhoodCells_of_card`, and `isPLBall_derivedNeighborhood_simplex`
from Euclidean three-space to arbitrary finite-dimensional real normed spaces.
`derivedNeighborhoodCell_inter_subset_boundaryComplex` places the intersection of distinct pieces
in their intrinsic combinatorial boundaries in all covered dimensions. Together with the
previous pair-intersection theorem, this gives both boundary incidences in the general ambient setting.
All three affected modules have focused-check exit 0 and zero warnings.
`AuditS71General.lean` / `AuditS71General.log`: five declarations, only the three standard axioms.
The source proof has no Schoenflies assumption.

### S-M2: partial; free-triangle face classification and intrinsic ball gluing checked

`32a3b37e8` adds `FreeTriangleFaces.lean` and `SubcomplexBallGluing.lean`.
The exact deletion formula is
`mem_eraseTriangleComplex_iff_of_free_triangle`: the remaining faces are precisely the old
faces that do not contain `t \ s`, where `s` is the boundary-trace parameter of the free triangle.
`IsCombinatorialManifoldWithBoundary.isPLBall_union_of_inter_isPLBall_two` proves that two
PL three-balls contained in the same finite combinatorial three-manifold with boundary,
whose intersection is a PL two-ball, have PL three-ball union. The proof first derives
intrinsic boundary incidence from the at-most-two codimension-one cofaces, then applies 23.11.
This theorem also holds in arbitrary finite-dimensional ambient spaces.
Both modules have focused-check exit 0 and zero warnings.
`AuditS70.lean` / `AuditS70.log`: six declarations, only the three standard axioms.
The remaining S-M2 obligation is the attachment disk for a whole existing disk neighborhood,
followed by the decreasing-triangle-count induction. Problem 26.1 is not yet marked delivered here.

### I2 signature issue found by source inspection

`LoopTheorem/SingularCell.lean` defines `SingularTwoCell M` with
`[ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]`.
`VertexChart.lean` defines `combinatorialChartedSpace K hK` only for
`hK : IsCombinatorialManifold (n + 1) K`, without boundary.
Consequently NIGHT_PLAN's proposed application to `K.space` with only
`IsCombinatorialManifoldWithBoundary 3 K` does not currently elaborate.
A boundary-compatible singular-cell/chart interface is needed from its owner; adding a
Euclidean charted-space assumption on a manifold with nonempty boundary would not repair the
mathematical interface. No such hypothesis has been added, and I2 is not marked delivered.
The intrinsic PL disk and boundary-ball geometry can be developed independently of that type.

### Concurrent write observed

During this session, the previously absent, untracked `FreeTriangleNeighborhood.lean` appeared
and continued changing; a separate Lean process was checking that file from this S worktree.
The user confirmed that another thread had intervened by mistake and that the interference is now corrected. This session is reviewing the retained source and will check and audit it before accepting it.
Only the explicitly listed files above were included in the checkpoints. Subsequent checks first
inspect active S-worktree Lean processes and defer when another one is running.

### S-M3: intrinsic geometry checked; containing-ball and singular-cell obligations remain

`SphereBallInclusion.lean`, `BoundaryMonotonicity.lean`, `BoundaryBallTransport.lean`, and
`BoundaryDiskPush.lean` have focused-check exit 0 and zero warnings.
`AuditS72Intrinsic.lean` / `AuditS72Intrinsic.log`: seven declarations, only the three standard axioms.
`exists_isPLBall_inter_boundaryComplex_eq_of_subset` shapes a given containing ball so that its
intersection with the ambient intrinsic boundary is exactly the prescribed disk.
`exists_isPLHomeomorphOn_disk_in_boundary_ball` constructs a parametrized PL disk inside the
ambient manifold with the same boundary image and no other intersection with the ambient boundary.
Both hold in arbitrary finite-dimensional real normed spaces, without a Schoenflies assumption.
The containing three-ball is still supplied as input until S-M2 closes Problem 26.1.
The singular-cell type issue above remains separate; this is not yet the exact bundled I2 endpoint.

### S-M2: done, Problem 26.1 in arbitrary finite-dimensional ambient spaces

`FreeTriangleNeighborhood.lean` proves
`IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_of_free_triangle`.
It identifies the exact old subfaces met by each new piece, proves the attaching two-disks,
and treats both free-triangle boundary traces. For one free edge, it adds the triangle and
edge pieces; for two free edges, it adds the triangle, both edges, and the new vertex.
`DiskDerivedNeighborhood.lean` uses strong induction on the number of triangles while retaining
a distinguished triangle. The base case is the full seven-piece simplex neighborhood.
A compatible ambient subdivision then gives
`IsCombinatorialManifoldWithBoundary.exists_isPLBall_containing_boundary_disk`:
for any PL two-disk D in the intrinsic boundary of finite combinatorial three-manifold K,
there is a PL three-ball C with D contained in C and C contained in K.space.
No containing-ball, shelling, Schoenflies, or Euclidean-chart hypothesis remains in this endpoint.
`SubcomplexBallGluing.lean` also supplies finite pairwise-disjoint ball attachments.
All three modules have focused-check exit 0 and zero warnings. `AuditS73Disk.lean` /
`AuditS73Disk.log` checks five public declarations; only the three standard axioms occur.
The previously retained source has now been reviewed, completed, checked, and audited.
Logs are `check-subcomplex-ball-gluing-finite.log`, `check-free-triangle-neighborhood.log`,
and `check-disk-derived-neighborhood.log` under `.lake/scratch`.

### S-M2 publication and S-M3 geometric delivery

S-M2 is committed and pushed as `d12dd514a`. The following fetch/merge found integration
already up to date. `BoundaryDiskPush.lean` now exports
`IsCombinatorialManifoldWithBoundary.exists_isPLBall_inter_boundaryComplex_eq` and
`IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_push_boundary_disk`.
Neither takes a containing-ball hypothesis: it is constructed by Problem 26.1.
`LoopTheorem/CombinatorialBoundaryPush.lean` proves
`exists_nonsingular_two_cell_in_combinatorial_manifold`, the Euclidean three-space singular-cell
endpoint with image inside K.space, prescribed boundary image, and no extra frontier contact.
Both modules have focused-check exit 0 and zero warnings. `AuditS74Push.lean` /
`AuditS74Push.log` audits these three endpoints with only the standard three axioms.
No Schoenflies assumption is needed. The general-ambient parametrized PL disk producer is complete.
S-M3 remains partial only at the exact `SingularTwoCell K.space` interface: the current type needs
a boundary-compatible target chart API from its owner. The phrase "I2 已交付" is deliberately not
used as a completion label while that obligation remains. S-M4 proceeds with the checked intrinsic
boundary-ball endpoint; it does not need the singular-cell type adaptation.

### S-M4: local boundary-disk product collar checked

S-M3's geometric producers are committed and pushed as `bd74dd7ca`; the next integration
merge was already up to date. The exact general-ambient singular-cell type issue remains as above.
`Product.lean` proves polyhedral products and products of PL homeomorphisms.
`Prism.lean` triangulates a triangular prism into three tetrahedra and proves
`isPLBall_three_prod`: a PL two-ball times a PL one-ball is a PL three-ball.
`PrismBoundary.lean` proves that the bottom of a disk prism lies in its intrinsic boundary.
The general boundary-incidence theorem added to `SubcomplexBallGluing.lean` supplies this step
in arbitrary finite-dimensional ambient spaces, without ambient frontier assumptions.
`DiskCollar.lean` exports
`IsCombinatorialManifoldWithBoundary.exists_collar_of_boundary_disk`:
for a boundary PL disk D, there are C contained in K.space and a PL homeomorphism
from D times [0,1] onto C which fixes (x,0), with C intersected with the intrinsic boundary
equal to D and every positive-height point lying off that boundary.
The proof uses Problem 26.1, the prism model, and the existing boundary-disk PL extension.
It needs no containing-ball or Schoenflies hypothesis.
All five affected modules have focused-check exit 0 and zero warnings.
`AuditS75Collar.lean` / `AuditS75Collar.log` audits thirteen public declarations with only
`propext`, `Classical.choice`, and `Quot.sound`. Check logs are `check-pl-product.log`,
`check-prism.log`, `check-subcomplex-ball-gluing-boundary.log`, `check-prism-boundary.log`,
and `check-disk-collar.log` under `.lake/scratch`.
This completes the requested subcomplex disk collar. The full 26.2 obligation is still the
compatible product on the entire compact boundary and the neighborhood property of its image.
A local disk collar alone is not claimed to be a neighborhood at the disk's boundary edges.

### S-M4 publication and whole-boundary collar frontier

The checked local product collar layer is pushed as `5f97aca9d` (thirteen audited declarations).
The integration merge was already up to date. Full 26.2 is partial. The exact remaining
induction invariant is a finite combinatorial triangulation of the closure of K.space minus
the accumulated collar image, together with the modified next disk in its intrinsic boundary.
One must prove that this closure is a manifold with boundary and extend the next product
map while preserving every previously fixed side face. The present 23.11 ball-union theorem
and independent disk collars do not establish either assertion. The final whole-boundary
image must also be shown to be a neighborhood. No compatibility or complement-manifold
assumption has been added to an endpoint. Under NIGHT_PLAN section 0.4, S-M5 proceeds.

### S-M5: 26.1 in PL charted ambient spaces checked; 26.3 remains open

`Connected/TwoSided.lean` defines `IsTwoSided` by separation of sufficiently small connected
neighborhoods of every connected component, as on Moise printed page 191.
For a regular closed set, an isolated boundary component separates each such neighborhood
into its nonempty interior and exterior parts. `Connected/FiniteCover.lean` proves that a finite
closed preconnected cover isolates its connected components.
`PolyhedralManifoldTopology.lean` proves `IsPolyhedralBall.closure_interior` and
`IsPolyhedralManifoldWithBoundary.closure_interior`, derives boundary-component isolation
from the finite simplicial cover, and exports
`IsPolyhedralManifoldWithBoundary.isTwoSided_of_union_boundary_components`.
This holds for full-dimensional polyhedral manifolds in an arbitrary Hausdorff PL charted
ambient space, in all positive dimensions. No regular-closed, local-connectedness, or
Schoenflies hypothesis remains in the PL endpoint. The ambient has Euclidean open charts;
applying it inside the interior of a general K with boundary still needs that interior chart
interface. This is recorded separately from the already valid PL ambient theorem.
All three modules have focused-check exit 0 and zero warnings. `AuditS76TwoSided.lean` /
`AuditS76TwoSided.log` audits eleven declarations with only the standard three axioms.
Check logs: `check-two-sided.log`, `check-finite-connected-cover.log`, and
`check-polyhedral-manifold-topology.log`.
For 26.3, the exact additional obligation is that a sufficiently small regular neighborhood
of a two-sided PL surface has exactly two complementary components, whose closures are
combinatorial three-manifolds with that surface as a boundary component. This is not a
consequence of disconnectedness alone; after it is proved, both sides still need full 26.2.
No bicollar endpoint is claimed. S-M6 proceeds under NIGHT_PLAN section 0.4.

### S-M6: relative free disk cell theorem checked

The S-M5 separation layer is committed and pushed as `ddf717a4b`; the next integration merge
was already up to date. `RelativeFreeDiskCell.lean` proves
`IsPLDiskDecomposition.exists_free_disk_cell_not_subset`, Moise 17.3 (printed page 118):
if a proper PL disk D is the union of a subfamily of the cells of a finite PL disk decomposition,
there is a free cell not contained in D. The statement holds in arbitrary finite-dimensional
real normed spaces. It does not replace the protected disk by a single protected cell.
The planar proof first finds an outside cell with nontrivial outer-boundary trace, splits at
that cell if necessary, and applies general 17.2 to the side opposite D. Planarization transports
the conclusion back to the original ambient space. `FreeDiskCell.lean` promotes and generalizes
its finite-union restriction identity for this reuse; its existing public endpoints are unchanged.
Both focused checks exit 0 with zero warnings. `AuditS77RelativeDisk.lean` /
`AuditS77RelativeDisk.log` audits four declarations with only the standard three axioms.
A missing declaration in the shared `DiskCrosscut.olean` was resolved by a focused refresh of
that module from this branch, also exit 0 with zero warnings. No source workaround was needed.
Logs: `check-free-disk-cell-relative.log`, `check-disk-crosscut-refresh.log`, and
`check-relative-free-disk-cell.log`. No Schoenflies assumption is used.
P.4 remains separate: polygonal graph redrawing alone does not produce a supported ambient
homeomorphism. Compatible sector extensions around vertices and edges, with the prescribed
neighborhood and pointwise displacement control, are the remaining geometric construction.

### S-M4 local refinement: prescribed relative neighborhoods

The relative 17.3 theorem is committed and pushed as `f0383a381`; the next integration merge
was already up to date. `BoundaryDiskNeighborhood.lean` strengthens Problem 26.1, the precise
boundary-ball theorem, the local disk collar, and the parametrized disk push-off: each output
can be chosen inside any prescribed member of the relative neighborhood filter of D in K.space.
The four endpoints are `exists_isPLBall_inter_boundaryComplex_eq_subset`,
`exists_isPLBall_containing_boundary_disk_subset`, `exists_collar_of_boundary_disk_subset`, and
`exists_isPLHomeomorphOn_push_boundary_disk_subset`, in the
`IsCombinatorialManifoldWithBoundary` namespace. All hold in arbitrary finite-dimensional
real normed spaces and need no Schoenflies or containing-ball assumption.
The proof first uses the existing controlled subdivision neighborhood, then intrinsic boundary
monotonicity transfers the smaller manifold's exact boundary incidence back to K.
This closes the arbitrary-neighborhood requirement for the boundary-disk part of B.2.
The focused check `check-boundary-disk-neighborhood.log` exits 0 with zero warnings.
`AuditS78BoundaryNeighborhood.lean` / `.log` audits the four endpoints using only the standard
three axioms. Full 26.2 still needs compatible collar gluing and the complement-manifold
induction invariant recorded above; neither is introduced as an extra assumption here.

### S-M6 P.4 input audit and milestone handoff

The controlled boundary-disk neighborhood layer is committed and pushed as `41b78491e`.
The final fetch and merge again found `origin/codex/moise-integration` already up to date.
`AuditS79P4Inputs.lean` / `.log` checks
`Schoenflies.jordan_schoenflies_homeomorph`, `Schoenflies.jordan_schoenflies_of_homeomorph`,
and `Graph.polygonal_redrawing`: three declarations, exit 0, only the standard three axioms.
The first two extend a homeomorphism of one Jordan curve; the third gives a polygonal drawing.
None supplies the supported, quantitatively controlled ambient graph homeomorphism of P.4.
The remaining argument must establish the disjoint covering sectors inside each vertex disk,
extend compatibly over those sectors while fixing the outer circle, straighten the trimmed
edge arcs inside disjoint edge frames, and derive the pointwise control from their diameters.
The second-batch approximation statements were also inspected and do not fill this gap;
no second-batch source or duplicate Jordan extension wrapper was introduced.

| Milestone | Status and proved layer | Checkpoint and audit | Exact remaining obligation |
|---|---|---|---|
| S-M1 | done: regular-neighborhood pieces, attaching disks, general ambient spaces | `2375fc812`; AuditS67--S69: 42; AuditS71General: 5 | None for the requested piece/intersection layer |
| S-M2 | done: complete boundary-disk derived neighborhood and Problem 26.1 | `d12dd514a`; AuditS70: 6; AuditS73Disk: 5 | None for the containing-ball theorem |
| S-M3 | partial: general parametrized PL push-off and Euclidean singular cell | `bd74dd7ca`; AuditS72Intrinsic: 7; AuditS74Push: 3 | `SingularTwoCell K.space` needs a boundary-compatible target type; its current Euclidean open-chart requirement is not available from a manifold-with-boundary hypothesis |
| S-M4 | done: whole-boundary collar with the relative-neighborhood property for finite combinatorial three-manifolds in arbitrary finite-dimensional real normed spaces | `691c7329d`, `e9feba0c2`, `f778f73ff`; AuditS88--S90: 12; earlier layers and audits below | None for the finite-complex endpoint in NIGHT_PLAN; abstract PL charted ambient transport is not asserted |
| S-M5 | partial: 26.1 in Hausdorff PL charted ambient spaces; the collar input for 26.3 is now proved | `ddf717a4b`; AuditS76TwoSided: 11; S-M4 collar: `f778f73ff` | Interior chart transport for arbitrary K; for 26.3, exactly two sides with manifold closures, followed by applying and gluing the proved collars |
| S-M6 | partial: general relative 17.3 done; P.4 inputs checked | `f0383a381`; AuditS77RelativeDisk: 4; AuditS79P4Inputs: 3 | Supported ambient graph extension with control, as detailed above |

All listed completed layers have focused-check exit 0 with zero warnings and transitive axiom
closures contained in `propext`, `Classical.choice`, and `Quot.sound`. No newly proved layer
requires Schoenflies. The previously delivered 23.9/23.10 consumers retain their authorized
explicit Schoenflies parameter until I1 arrives through integration.
The final plan-only checkpoint updates both preserved P.3 rows and the S-owned P.4/B.1--B.4
statuses. It does not mark the exact bundled I2 delivered, claim a whole-boundary collar,
claim a bicollar, modify another lane's source, or register modules in the root aggregate.

### S-M4 continuation: the complement-manifold invariant is proved

`PlanarDiskComplement.lean` proves that deleting a subdisk attached along a boundary arc
leaves a PL disk after closure, both in the plane and in arbitrary finite-dimensional ambient
spaces with intrinsic boundary. The full-boundary inclusion case forces equality of the disks.
`SubcomplexComplementLink.lean` identifies the links of the actual complementary subcomplex
with closures of differences of links, and identifies the boundary trace links.
`ManifoldComplement.lean` proves `IsCombinatorialManifoldWithBoundary.complement`:
for finite combinatorial three-manifolds A contained as a subcomplex of K, if their boundary
trace is a combinatorial two-manifold with boundary, the closure of K.space minus A.space
is a combinatorial three-manifold with boundary. This hypothesis concerns the boundary trace,
not the desired complement. The PL boundary-disk corollary discharges it automatically.
`exists_isCombinatorialManifoldWithBoundary_closure_sdiff` constructs a finite triangulation
of the exact closure after deleting any PL three-ball whose intersection with Bd K is a PL disk.
The proof separates sphere and ball links; the ball case uses the new planar complement theorem.
No Schoenflies assumption or complement-manifold assumption is introduced.

`DiskCollarComplement.lean` exports
`exists_collar_of_boundary_disk_subset_with_complement`: the already controlled local disk
collar now comes with this finite combinatorial triangulation of its actual closed complement.
The private disk-inclusion proof in `RelativeFreeDiskCell.lean` now reuses the canonical result;
its 17.3 statement is unchanged. All five affected modules have focused-check exit 0 and zero
warnings. `AuditS80Complement.lean` / `.log` audits sixteen new or affected declarations,
all with only `propext`, `Classical.choice`, and `Quot.sound`.
Logs: `check-planar-disk-complement.log`, `check-subcomplex-complement-link.log`,
`check-manifold-complement.log`, `check-disk-collar-complement.log`, and
`check-relative-free-disk-cell-complement.log` under `.lake/scratch`.
This discharges the complement-manifold part of the previously recorded 26.2 invariant.
The next obligations are the exact new boundary and modified next disk, product maps agreeing
on the previously fixed side faces, and the whole-boundary neighborhood property.

### S-M4 continuation: exact complementary boundary and boundary replacement

The preceding complement-manifold layer is committed and pushed as `51e4d8f21`.
`ManifoldFaces.lean` proves extension of every face to a top-dimensional face in a finite
combinatorial manifold, including dimension zero. `BoundaryComplement.lean` computes the
codimension-one cofaces in the actual complementary subcomplex. It proves, in every positive
dimension and for arbitrary finite triangulations of the same spaces,

`Bd R = closure (Bd K - A.space) union closure (Bd A - Bd K)`,

where `R.space = closure (K.space - A.space)` and the three complexes are manifolds with
boundary of the same dimension. In dimension three the previous complement theorem produces
R and its manifold proof from a boundary-attached PL ball, so this is not a new assumed
complement-manifold obligation.

`ManifoldSubcomplexBoundary.lean` proves that a submanifold meets the closure of its complement
only on its intrinsic boundary. In a manifold without boundary the intersection is exactly
that boundary. The parameterized disk version identifies the intersection with the image of
the standard simplex boundary. These results hold in all positive dimensions; the zero-sphere
link case uses equality of two-point subsets, not an additional dimension restriction.

`BoundaryBallReplacement.lean` constructs
`IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_boundary_complement`:
for a PL three-ball A in K meeting Bd K in a PL disk, it produces the actual finite manifold
complement R and a PL homeomorphism Bd K to Bd R that fixes the closure of Bd K minus A.
The proof replaces the attaching disk by the complementary disk in Bd A using P.2.
`DiskCollarComplement.lean` exports
`exists_collar_of_boundary_disk_subset_with_boundary_complement`, including the controlled
local disk collar, the same closed complement R, and this boundary homeomorphism, fixed on
the closure of Bd K minus the attaching disk. The homeomorphism transports subsequent boundary
disks to the new boundary. None of these results requires Schoenflies.

All five modules have focused-check exit 0 with zero warnings. `AuditS81BoundaryReplacement.lean`
and `.log` audit thirteen new or affected declarations, all with only `propext`,
`Classical.choice`, and `Quot.sound`. Logs under `.lake/scratch` are
`check-manifold-faces.log`, `check-boundary-complement.log`,
`check-manifold-subcomplex-boundary.log`, `check-boundary-ball-replacement.log`, and
`check-disk-collar-complement-boundary.log`.

The remaining 26.2 obligation is compatible product-coordinate gluing over the successive
boundary disks, followed by the whole-boundary neighborhood property. The boundary replacement
map and the local collar parametrization are both proved, but their independent existence
does not yet identify them on the side faces needed for that gluing. Full 26.2 remains partial.
The exact bundled I2 target-type issue and the recorded P.4 extension/control obligations
are unchanged. The source checkpoint hash is recorded with the final plan update below.

### S-M4 verified checkpoint and final plan update

The complement-manifold theorem is committed and pushed as `51e4d8f21`; the exact boundary
and PL boundary replacement layer is committed and pushed as `7f062e84c`.
The post-checkpoint fetch and merge found `origin/codex/moise-integration` already up to date
at `8fb887bb9`. The B.3 plan row now records both proved invariants and the actual remaining
product-gluing and neighborhood obligations. AuditS80/S81 contain 29 audit entries in total,
all with only the standard three axioms; the nine distinct Lean modules changed across these
two checkpoints passed their focused checks with zero warnings. The final bookkeeping commit
changes only this handoff and the B.3 plan row. No whole-boundary collar or bundled I2 delivery
is asserted.

### S-M4 continuation: prism attachment disks and prescribed side coordinates

`FrontierBoundary.lean` now identifies the topological frontier with the intrinsic boundary
in any finite-dimensional ambient space of the manifold's dimension.
`Prism.lean` exposes the existing coordinate triangle model and proves `isPLBall_unit_square`
and `isPLBall_two_prod`: two PL arcs have a PL disk as their product.
`PrismBoundary.lean` proves `boundaryComplex_space_prism`, identifying the complete boundary
of a disk prism with its two ends and its side wall, for arbitrary ambient spaces and finite
triangulations of the prism.

`PrismDisk.lean` proves that the bottom together with the whole side wall is a PL disk, and
that the same holds for any finite family of pairwise disjoint boundary-arc strips. The whole
wall result handles the final closed-boundary case, where the attaching set can be the entire
boundary circle; no proper-arc assumption is silently imposed on that case.
`CollarGluing.lean` constructs the PL map on a new bottom disk together with old collar side
strips. Its public relative extension theorems
`exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_boundary_arcs` and
`exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_boundary` extend this map across a new
three-ball while preserving both the prescribed bottom and every previously fixed side
coordinate. The input three-ball must have the modified attaching disk on its boundary.
These are relative extension results, not an assertion of the whole-boundary collar.

The five changed Lean modules have focused-check exit 0 with zero warnings. Logs are
`check-frontier-boundary-finrank.log`, `check-prism-products.log`, `check-prism-boundary.log`,
`check-prism-disk.log`, and `check-collar-gluing.log` under `.lake/scratch`.
`AuditS82PrismGluing.lean` / `.log` contain thirteen entries, all with only `propext`,
`Classical.choice`, and `Quot.sound`. No Schoenflies parameter or new unproved mathematical
input is used in the new geometric producers. No vendored source was changed.

Full 26.2 still requires the boundary cell ordering and complementary-boundary invariant to
produce each modified attaching disk in the actual complement, then the compatible union of
old and new product maps and the whole-boundary neighborhood property. The exact I2 target-type
issue and the recorded P.4 obligations remain unchanged. The source checkpoint hash is recorded
in the following checkpoint entry.

### S-M4 checkpoint: compatible collar enlargement

The prism and prescribed-side-coordinate layer is committed and pushed as `bc9b5bbcb`.
Its post-checkpoint integration merge was already up to date at `8fb887bb9`.

`CollarGluing.lean` now exposes the common relative extension core
`exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_isPLBall`; the boundary-arc and whole-circle
corollaries discharge its attaching-disk hypothesis with the proved prism disk constructions.
`CollarExtension.lean` proves `exists_collar_extension_of_boundary_arcs` and
`exists_collar_extension_of_boundary`. Given the current collar and its complementary-boundary
conditions, these theorems use Problem 26.1 to produce the new three-ball in any prescribed
relative neighborhood. They prove its intersection with the old collar is exactly the existing
side strip, glue the two product maps, preserve the entire old collar map, fix the enlarged
bottom, and prove that positive height avoids the original boundary. They also construct a
finite combinatorial three-manifold triangulation of the exact closed complement of the new
ball inside the current complement.

The public enlargement statements keep the inductive geometry explicit: the modified disk
lies on the current complementary boundary, and the intersections of that complement with
the old collar and the original boundary lie on its boundary. They do not assume the new ball,
the enlarged collar map, or the new complement manifold. Establishing and preserving these
geometric conditions through a finite boundary cell ordering is still required for full 26.2.
The whole-boundary neighborhood property is also still pending.

Focused checks for `CollarGluing.lean` and `CollarExtension.lean` exit 0 with zero warnings;
logs are `check-collar-gluing-extension.log` and `check-collar-extension.log`.
`AuditS83CollarExtension.lean` / `.log` audit five new or affected public declarations, all with
only `propext`, `Classical.choice`, and `Quot.sound`. The source checkpoint hash is recorded
with the next status update. No vendored source, other-lane source, or root aggregate changed.

### S-M4 continuation: the complementary-boundary conditions are preserved

The actual collar enlargement is committed and pushed as `7ec642daf`.
`GeneratedSubcomplex.lean` proves `subcomplexGeneratedBy_compl_compl` under the natural
cardinality bound and purity hypotheses. `SubcomplexComplement.lean` identifies the resulting
double closed difference with the original pure subcomplex.
`ManifoldSubcomplexBoundary.lean` transports this to arbitrary finite triangulations:
`IsCombinatorialManifoldWithBoundary.closure_sdiff_closure_sdiff_eq` holds in every dimension,
including zero. In positive dimensions, `inter_closure_sdiff_subset_boundaryComplex` and
`inter_space_complement_subset_boundaryComplex` put the common interface on the intrinsic
boundary of either manifold, including the actual complementary manifold.

`CollarExtension.lean` consumes these results and strengthens both public enlargement
endpoints. In addition to the already proved product map and exact complement R', they return
`(W union C) inter R'.space subset Bd R'` and `B inter R'.space subset Bd R'`.
Thus these two input boundary conditions are now preserved by the step itself. The unchanged
attaching-disk condition for each subsequent boundary cell still has to be proved from the
cell decomposition; it is not hidden in a new structure or claimed as discharged.

All four affected modules have focused-check exit 0 and zero warnings. Logs are
`check-generated-subcomplex-involution.log`, `check-subcomplex-complement-involution.log`,
`check-manifold-subcomplex-complement.log`, and `check-collar-extension-invariants.log`.
`AuditS84ComplementInvariants.lean` / `.log` audit seven new or affected declarations, all with
only the standard three axioms. No other lane's source or vendored source was modified.
The source hash is recorded in the final plan checkpoint below.

Next mathematical obligations for 26.2: construct a finite boundary cell ordering whose next
cell meets the previous union in finitely many disjoint boundary arcs or its whole boundary;
prove that each future disk together with the current vertical strips lies on the actual
complementary boundary; finish the finite induction and prove that the final image is a
neighborhood of the entire original boundary. The step already preserves old coordinates,
positive-height boundary avoidance, the complement's manifold property, and both interface
boundary conditions. Full 26.2 remains partial, and the exact I2 target-type issue is unchanged.

### S-M4 verified source checkpoints and plan update, 2026-09-16

The three source checkpoints are committed and pushed: `bc9b5bbcb` (prism attachment disks
and prescribed side coordinates), `7ec642daf` (actual compatible collar enlargement), and
`66d39dbdd` (preservation of the complementary-boundary conditions). All nine distinct Lean
modules changed across them have focused-check exit 0 and zero warnings. AuditS82/S83/S84
contain 25 entries in total, including repeated affected endpoints; every entry has only
`propext`, `Classical.choice`, and `Quot.sound`.

Each source checkpoint was followed by fetch and merge of the integration branch, still
already up to date at `8fb887bb9`. The final bookkeeping commit changes only this handoff and
the B.3 plan row. Full 26.2 remains partial for the precise obligations above; exact bundled
I2 is not marked delivered, and the P.4 obligations remain unchanged.

### S-M4 continuation: density and persistence on complementary boundaries

`BallDensity.lean` proves `IsPLBall.closure_sdiff_eq_of_isPLBall`,
`IsPLBall.closure_sdiff_iUnion_eq`, and
`IsPLBall.closure_sdiff_eq_of_inter_subset_iUnion`: deleting a finite union of
strictly lower-dimensional PL balls from a positive-dimensional PL ball leaves a dense subset.
`BoundaryDiskPersistence.lean` combines this with the exact complementary-boundary formula.
Its two public endpoints preserve disks from either the old boundary or the newly exposed
ball boundary when the removed intersection has such a finite lower-dimensional cover.
These results are in arbitrary finite-dimensional real normed ambient spaces.

Both modules have focused-check exit 0, zero warnings; logs are
`check-ball-density.log` and `check-boundary-disk-persistence.log`.
`AuditS85BoundaryDiskPersistence.lean` / `.log` contain five entries, all with only
`propext`, `Classical.choice`, and `Quot.sound`. No new assumptions on Schoenflies,
no vendored source changes, and no other-lane source changes are involved.
The source commit hash is recorded at the next checkpoint.

Full 26.2 remains partial. Next: produce the lower-dimensional intersection covers for
actual old collar patches and newly added vertical strips, then construct the finite
boundary cell ordering and finish the induction and whole-boundary neighborhood property.
The exact bundled I2 target-type issue is unchanged.

### S-M4 continuation: later collar disks remain on the new complementary boundary

The density checkpoint is committed and pushed as `ee372da29`; its integration merge was
already up to date. `BallDensity.lean` now also proves finite-point deletion density for
arbitrary positive-dimensional PL balls and transports the dense positive-height product
through a PL homeomorphism. The previous planar finite-point result in
`PlanarDiskUnion.lean` is a compatibility corollary of the general theorem.

`CollarBoundary.lean` proves `image_prism_side_subset_boundaryComplex`,
`image_strip_subset_boundaryComplex_complement`, and
`image_prism_side_subset_boundaryComplex_complement`. The first identifies actual prism sides
on the ball boundary. The other two preserve old and new strips using their finite base
intersections and the exact complementary-boundary formula. The combined endpoint
`collar_disk_subset_boundaryComplex_complement` preserves a later disk together with its
enlarged side strips. It handles both a shared PL arc and a disjoint new disk. Its hypotheses
are the previous collar geometry, a finite arc cover of the previous base intersection,
and finiteness of the triple intersection; these are still to be produced by the boundary
cell decomposition. The new complementary-boundary inclusion is proved, not assumed.

Both public endpoints in `CollarExtension.lean` now return the new prism parametrization,
the precise trace of the new ball on the old complementary boundary in those coordinates,
and the exact intersections with the original boundary and previous collar. These are
properties of the same ball and map constructed by the existing extension proof.

Focused checks for the four changed source modules and the directly affected `DiskUnion`
module have exit 0 and zero warnings. Logs are `check-ball-density-finite.log`,
`check-planar-disk-union-density.log`, `check-collar-boundary-persistence.log`,
`check-collar-extension-trace.log`, and `check-disk-union-density.log`.
`AuditS86CollarBoundary.lean` / `.log` audit nine new or affected public declarations;
every entry has only `propext`, `Classical.choice`, and `Quot.sound`.
No vendored or other-lane source changed. The source hash is recorded at the next checkpoint.

Full 26.2 remains partial: construct the finite dual boundary-cell decomposition and its
intersection data, discharge the attachment-arc or whole-boundary alternative, assemble the
finite collar induction, and prove the final neighborhood property. The exact bundled I2
target-type issue and P.4 obligations remain unchanged.

### S-M4 continuation: dual-cell coverage and intersection producers

The collar-boundary persistence layer is committed and pushed as `142653991`; its integration
merge was already up to date. `DualCellDecomposition.lean` now reuses the existing
`dualCell_space_inter_eq_dualCell` and proves that nonempty intersections force the union
face, nonfaces give disjoint dual cells, and maximal-dimensional dual cells reduce to their
barycenters. The vertex dual cells cover the full carrier. Adjacent vertex dual cells in an
(n+2)-manifold meet in an (n+1)-ball lying on each cell boundary.

For a two-dimensional manifold, three distinct vertex dual cells have finite intersection.
`IsCombinatorialManifoldWithBoundary.finite_inter_dualCell_singleton_iUnion` produces the
finite intersection with any already processed finite cell family.
`IsCombinatorialManifoldWithBoundary.exists_boundary_arcs_cover_inter_dualCell_iUnion`
produces an explicit finite family of shared boundary arcs covering the new cell's
intersection with that processed union. It does not assert that these arcs are pairwise
disjoint: adjacent arcs can share endpoints. Together these are the actual finite-intersection
and arc-cover inputs needed by `collar_disk_subset_boundaryComplex_complement`.

The new module has focused-check exit 0 and zero warnings (`check-dual-cell-decomposition.log`).
`AuditS87DualCellDecomposition.lean` / `.log` audit all ten public theorems, each with only
`propext`, `Classical.choice`, and `Quot.sound`. The existing other-lane `DualCells.lean` was
only imported and was not modified. The source hash is recorded in the final bookkeeping entry.

Remaining for full 26.2: turn the shared boundary-arc cover into pairwise disjoint arc
components or the whole boundary circle, connect these producers to the finite collar
induction, and prove the final image is a neighborhood of the entire original boundary.
The exact bundled I2 target-type issue and the other recorded milestones remain unchanged.

### S-M4 verified checkpoints and remaining global obligations, 2026-09-16

The three source checkpoints are committed and pushed: `ee372da29` (density and complementary
boundary persistence), `142653991` (actual future collar-disk persistence and precise extension
traces), and `fe71026b6` (dual-cell coverage and intersection producers). All six changed Lean
modules and the directly affected `DiskUnion` module have focused-check exit 0 and zero
warnings. AuditS85/S86/S87 contain 24 entries, all with only the standard three axioms.

Every source checkpoint was followed by fetch and merge of the integration branch, still
already up to date at `8fb887bb9`. This final bookkeeping change updates the S-M4 table and
B.3 plan row to the exact current proof frontier. No new consultation is required for the
next step: classify the finite boundary-arc cover into disjoint arc components or the whole
circle. Full 26.2 is still partial; exact bundled I2 is not marked delivered.

### S-M4 continuation: arbitrary finite boundary-arc covers

`Topology/Connected/FiniteComponents.lean` proves `exists_finite_isConnected_partition`:
a finite union of compact connected sets has a finite partition into compact connected
components, each containing an original member. No separation axiom is required.
`ArcSubset.lean` proves that a closed proper subset of a PL circle lies in a PL arc,
and that a compact connected nontrivial subset of a PL arc is again a PL arc.
`ArcDecomposition.lean` combines these facts in
`IsPLSphere.eq_or_exists_disjoint_arc_cover`: a finite union of boundary arcs is the
whole circle or a finite union of pairwise disjoint PL arcs. `IsPLBall.nontrivial`
is exposed in `BallDensity.lean` and reused by the existing density theorem.

`isPLBall_prism_bottom_union_strips` and the boundary-arc endpoints in `CollarGluing.lean`
and `CollarExtension.lean` now accept arbitrary finite boundary-arc covers; their former
pairwise-disjointness hypotheses are removed. In particular the actual shared arcs from
`DualCellDecomposition.lean`, which may meet at endpoints, supply their input directly.

All seven changed Lean modules have focused-check exit 0 and zero warnings. Logs are
`check-arc-subset.log`, `check-finite-connected-components.log`,
`check-ball-density-nontrivial.log`, `check-arc-decomposition.log`, and
`check-PrismDisk-arc-cover.log`, `check-CollarGluing-arc-cover.log`,
`check-CollarExtension-arc-cover.log`. `AuditS88ArcDecomposition.lean` / `.log`
contain nine new or affected public endpoints, all with only `propext`,
`Classical.choice`, and `Quot.sound`. The source hash is recorded at the next checkpoint.
No vendored or other-lane source changed.

Full 26.2 remains partial: assemble the finite collar induction using these actual dual-cell
inputs, then prove that the final image is a neighborhood of the entire original boundary.
The exact bundled I2 target-type issue and the other milestone obligations are unchanged.

### S-M4 continuation: finite surface-collar induction

The arc-cover layer is committed and pushed as `691c7329d`; the integration merge was
already up to date. `SurfaceCollar.lean` now proves
`IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_surface_prod_Icc`.
For any finite combinatorial surface with boundary embedded in the intrinsic boundary
of a finite combinatorial three-manifold, it constructs a PL embedding of the surface
times any nondegenerate compact interval. The bottom is fixed, positive heights lie off
the original boundary, and the image lies in the original manifold. It also returns a
finite combinatorial three-manifold triangulating the actual closed complement, with
the old-image and original-boundary intersection conditions preserved.

The proof performs finite induction over the actual vertex dual cells. It consumes the
shared-arc and finite triple-intersection producers, the generalized collar extension,
and the later-disk persistence theorem. No cell ordering, extension map, complement
manifold, or persistence conclusion is added as a hypothesis. The statement permits a
proper boundary subsurface; the whole boundary is a specialization.

Focused check: `check-surface-collar.log`, exit 0, zero warnings.
`AuditS89SurfaceCollar.lean` / `.log` audit the public endpoint; its closure contains only
`propext`, `Classical.choice`, and `Quot.sound`. No vendored or other-lane source changed.
The source hash is recorded at the next checkpoint.

Full 26.2 still requires the image-neighborhood property. The next proof restricts the
product embedding to a disk neighborhood in the boundary and uses the exact boundary of
its three-ball complement to exclude the base point from that complement. The bundled
I2 target-type issue and other milestone obligations are unchanged.

### S-M4 completed: whole-boundary collar and its neighborhood property

The finite product-embedding construction is committed and pushed as `e9feba0c2`;
its integration merge was already up to date. `CollarNeighborhood.lean` proves
`IsPLHomeomorphOn.mem_nhdsSetWithin_boundaryComplex`: a PL product embedding of the
whole intrinsic boundary, with its bottom fixed and its image in the manifold, has an
image which is a relative neighborhood of that boundary. At each boundary point, the
proof chooses a disk neighborhood, restricts the product to its three-ball prism, and
uses the exact complementary-boundary formula. The original boundary remainder and
the exposed top and side faces both avoid the chosen point, so the closed complement
does not contain it. The neighborhood assertion is proved, not included in the input.

`IsCombinatorialManifoldWithBoundary.exists_collar` is the resulting Moise 26.2 endpoint
for a finite combinatorial three-manifold with boundary in any finite-dimensional real
normed ambient space. It produces a polyhedral W contained in K.space, a PL homeomorphism
from the entire intrinsic boundary times [0,1] onto W, the relative-neighborhood property,
the bottom identity, the exact boundary intersection, and positive-height boundary
avoidance. No containing-ball, collar, compatibility, Schoenflies, or chart assumption is
required beyond the finite combinatorial manifold hypotheses. This completes the S-M4
finite-complex interface in NIGHT_PLAN. Transport to an arbitrary abstract PL charted
ambient manifold is a separate interface and is not asserted by this endpoint.

Focused check: `check-collar-neighborhood.log`, exit 0, zero warnings.
`AuditS90CollarNeighborhood.lean` / `.log` contain both new public declarations; each
has only `propext`, `Classical.choice`, and `Quot.sound`. No vendored or other-lane
source changed. The source hash is recorded in the final bookkeeping entry.

The next S-M5 obligation is 26.3: identify the two components adjacent to a two-sided
surface and prove their closures are combinatorial manifolds, then apply the collar
endpoint. The bundled I2 target-type issue remains unchanged; I2 is not marked delivered.

### S-M4 final publication checkpoint, 2026-09-16

The three new source checkpoints are committed and pushed: `691c7329d` (arbitrary finite
boundary-arc covers), `e9feba0c2` (finite surface-collar induction), and `f778f73ff`
(whole-boundary neighborhood property and `exists_collar`). All nine changed Lean modules
have focused-check exit 0 and zero warnings. AuditS88/S89/S90 contain twelve entries, all
with only the standard three axioms. Each source checkpoint was followed by fetch and merge
of the integration branch, still already up to date at `8fb887bb9`.

This bookkeeping commit updates the S-M4 and S-M5 table entries and plan rows B.3/B.4 to the
verified scope. S-M4's finite-complex collar endpoint is complete. S-M3's exact bundled I2
signature still requires the target-type owner's boundary-compatible interface; the geometric
push producer is already proved. S-M5's next mathematical task is the actual two-component
and manifold-closure construction for 26.3. The P.4 obligations remain unchanged.
