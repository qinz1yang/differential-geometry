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
  （`$root` 已指向本工作树；olean 写进本车道隔离产物目录 `E:\differential-geometry-dev\.lake\scratch\s-verified-20260916`，
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
| S-M3 | done: I2 已交付（double 环境） | `LoopTheorem/DoubleBoundaryPush.lean`; AuditS114DoubleBoundaryPush: 7 | NIGHT_PLAN 6.1 target is `(double 3 K).space` with its constructed combinatorial charted space; direct E3 hpush signature checked; no additional unproved hypothesis |
| S-M4 | done: whole-boundary collar with the relative-neighborhood property for finite combinatorial three-manifolds in arbitrary finite-dimensional real normed spaces | `691c7329d`, `e9feba0c2`, `f778f73ff`; AuditS88--S90: 12; earlier layers and audits below | None for the finite-complex endpoint in NIGHT_PLAN; abstract PL charted ambient transport is not asserted |
| S-M5 | done: 26.1 in finite combinatorial carriers and general PL charted ambient spaces; arbitrarily small PL bicollars without connectedness assumptions | `ddf717a4b`; finite bicollar `3a55ac834`; general manifold bicollar `52d70d778`; relative topology `7746cff68`; AuditS101--S104: 18 | No remaining 26.1/26.3 obligation in these stated settings; I2 is now delivered in the double environment (S-M3) |
| S-M6 | partial: general relative 17.3 done; simultaneous supported vertex-fan straightening, polygonal target production, and simultaneous crosscut straightening in disjoint PL disks proved | `VertexStraightening`, `InteriorAccess`, `PolygonalCrosscut`; AuditS115: 7 new declarations | Handle degree-one endpoints and construct arbitrarily small compatible PL disk frames from the original graph; initial subarcs do not control later reentry |

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

### S-M5 continuation: the two components in a spherical link

`Connected/ClosedCover.lean` proves `connectedComponentIn_sdiff_inter_eq_sdiff`:
for two closed sets, a connected side of their union minus their intersection is the
corresponding full connected component. `SphericalComponents.lean` applies this to the
existing universe-polymorphic `exists_disk_decomposition_of_isPLSphere_one_subset_two`.
Its endpoint `IsPLSphere.exists_connectedComponentIn_pair_sdiff` proves that a PL circle
in a PL two-sphere has exactly two complementary connected components. Their closures
are parametrized PL disks, their common boundary is the given circle, and the closures
cover the sphere. This is the actual two-side producer needed in the vertex links of an
embedded surface; a mere non-connectedness assumption is not being substituted for it.

Both modules have focused-check exit 0, zero warnings (`check-connected-closed-cover.log`,
`check-spherical-components.log`). `AuditS91SphericalComponents.lean` / `.log` audit the
two new declarations and the reused disk-decomposition producer; all three contain only
`propext`, `Classical.choice`, and `Quot.sound`. No vendored or other-lane source changed.
The source hash is recorded at the next checkpoint.

26.3 remains partial. Next: transport these components through the radial cone model,
then identify the global components in a sufficiently small regular neighborhood and
prove that their closures have the required manifold boundaries before applying 26.2.

### S-M5 continuation: coned circles separate coned spheres into two balls

The spherical-link checkpoint is committed and pushed as `da8b336d9`.
`ConeComplement.lean` identifies the difference of two cones with the radial image of
`(K.space \ L.space) × (0, 1]`, proves connectedness, and computes its closure when the
base difference is dense. These results do not require finite-dimensional ambient space.
`ConeComponents.lean` proves `IsConeBase.exists_connectedComponentIn_pair_sdiff`:
when a PL circle is a subcomplex of a PL two-sphere, coning both from the same admissible
apex produces exactly two complementary connected components, each with PL three-ball
closure. The closures cover the ambient cone and meet exactly in the cone on the circle.
The proof uses an actual common subdivision of the two disk closures and radial uniqueness.

Both modules have focused-check exit 0, zero warnings (`check-cone-complement.log`,
`check-cone-components.log`). `AuditS92ConeComponents.lean` / `.log` contain five entries,
all using only `propext`, `Classical.choice`, and `Quot.sound`. No external assumptions,
vendored changes, or other-lane source edits were introduced.

26.3 still needs the global side and manifold-closure construction. For the local surface
trace, an arbitrary subcomplex need not intersect an ambient closed star in its own closed
star. The existing barycentric-star intersection lemma in `FrontierBoundary.lean` supplies
the correct trace after subdivision; the next step reuses it instead of assuming fullness.

### S-M5 continuation: arbitrarily small neighborhoods of embedded surfaces

The cone-component checkpoint is committed and pushed as `7e6e37d0f`.
`StarIntersection.lean` promotes the existing barycentric closed-star intersection proof
from `FrontierBoundary.lean` without changing its hypotheses or proof. The old consumer
imports that module; no duplicate proof remains. `StarComponents.lean` then identifies
the two actual components of the subdivided ambient closed star minus the surface.

`SurfaceNeighborhood.lean` proves
`IsCombinatorialManifoldWithBoundary.exists_isPLBall_neighborhood_pair_sdiff`.
For any point of a finite closed combinatorial surface lying in the interior of a finite
combinatorial three-manifold, every prescribed relative neighborhood contains a PL three-ball
neighborhood C. Its trace on the surface is a PL two-disk. The complement in C has exactly
two connected components with PL three-ball closures; the closures cover C and their
intersection is precisely the surface trace. Surface and ambient triangulations need only
have carrier inclusion; compatibility is produced by a common subdivision. No global
separation or two-sidedness assumption is used for this local result.

All four changed modules have focused-check exit 0 and zero warnings
(`check-star-intersection.log`, `check-frontier-boundary-star.log`,
`check-star-components.log`, `check-surface-neighborhood.log`).
`AuditS93SurfaceNeighborhood.lean` / `.log` contain six entries: the three new public
results, the two old boundary-ball consumers, and the existing whole-boundary collar.
All contain only `propext`, `Classical.choice`, and `Quot.sound`.

26.3 remains partial: the small local two-side models must still be globalized over each
connected two-sided surface component; the resulting closures must be identified as
combinatorial manifolds before applying and gluing the already proved collars.

### S-M5 continuation: global component count and closure propagation

The local surface-neighborhood checkpoint is committed and pushed as `68ed572a9`.
`Connected/LocalSeparation.lean` proves that a complementary component touching a connected
locally separating set has that whole set in its closure. There are at most two such
adjacent components. In a connected locally connected ambient set, every complementary
component of a nonempty closed subset touches that subset. Combining these facts proves
that a disconnected complement has exactly two components, whose closures cover the closed
ambient set and meet exactly in the separating set. None of these global conclusions is
assumed in the proof.

`PolyhedronLocalConnectedness.lean` supplies local connectedness for finite simplicial
carriers, using small intersections of closed stars with metric balls. The simplicial
result does not need a finite-dimensional ambient space. Its polyhedral corollary uses
the existing triangulation theorem.

`SurfaceComponents.lean` consumes the actual local PL neighborhood producer. Its endpoint
`IsCombinatorialManifoldWithBoundary.exists_connectedComponentIn_pair_sdiff_of_separating_surface`
proves the two-component conclusion and exact closure union/intersection for a connected
closed surface in the interior of a connected finite combinatorial three-manifold, when
the complement is disconnected. The local decomposition and local connectedness assumptions
are discharged. The separate propagation and adjacent-component endpoints remain available.

All three modules have focused-check exit 0 and zero warnings (`check-local-separation.log`,
`check-polyhedron-local-connectedness.log`, `check-surface-components.log`).
`AuditS94SurfaceComponents.lean` / `.log` contain twelve entries, all using only
`propext`, `Classical.choice`, and `Quot.sound`.

26.3 remains partial. The next step must choose a sufficiently small connected regular
neighborhood using `IsTwoSided`, thereby producing the disconnected-complement hypothesis
of the checked global count theorem. The remaining geometric obligation is that both
component closures are combinatorial manifolds with the surface as a boundary component;
only then can the existing collars be applied and glued. This entry does not label the
bicollar theorem complete or introduce a new unproved interface assumption.

### S-M5 publication checkpoint, 2026-09-16

All three source checkpoints are committed and pushed: `7e6e37d0f` (coned-circle
components), `68ed572a9` (arbitrarily small local surface neighborhoods), and `6294e3dd3`
(global components and closure formulas). The nine changed Lean modules have focused-check
exit 0 and zero warnings. AuditS92/S93/S94 contain 23 entries, all with only the standard
three axioms. Each checkpoint was followed by fetch and merge of the integration branch,
still already up to date at `8fb887bb9`. This final bookkeeping commit updates only the
S-M5 summary and B.4 plan row to that verified scope. The overall S-M5/26.3 status remains
partial, with the exact remaining obligations recorded above.

### S-M5 continuation: connected manifold neighborhoods and local boundary invariance

`ComponentComplex.lean` realizes every connected component of a simplicial carrier as
its restriction subcomplex. The vertex links are unchanged; both combinatorial manifolds
and combinatorial manifolds with boundary are preserved. These results do not require
finite-dimensional ambient space or finitely many faces.

`SubcomplexNeighborhood.lean` proves equality of vertex links when a subcomplex is a
relative neighborhood at the vertex, reusing `mem_faces_of_mem_nhdsWithin_space`.
Its boundary endpoint compares arbitrary finite triangulations: at a point where one
combinatorial manifold is a relative neighborhood inside another, intrinsic boundary
membership is equivalent. A common subdivision is produced in the proof.

`ConnectedNeighborhood.lean` proves
`IsCombinatorialManifoldWithBoundary.exists_connected_neighborhood`: a compact connected
set in a finite combinatorial manifold with boundary has arbitrarily small connected
finite combinatorial manifold neighborhoods. The proof takes the connected component
containing the set in the existing small manifold neighborhood, and uses local
connectedness to retain the neighborhood property. The result works in every positive
dimension and arbitrary finite-dimensional real normed ambient space.

All three focused checks have exit 0 and zero warnings (`check-component-complex.log`,
`check-subcomplex-neighborhood.log`, `check-connected-neighborhood.log`).
`AuditS95ConnectedNeighborhood.lean` / `.log` audit seven new declarations and the reused
face-neighborhood lemma: all eight have only `propext`, `Classical.choice`, and `Quot.sound`.
The source commit hash will be recorded at the following checkpoint. No other-lane or
vendored source was modified.

26.3 remains partial. Next: apply two-sidedness in the subtype of the ambient manifold
to these connected neighborhoods and discharge the disconnected-complement input of
the global two-component theorem. Component closures still need their manifold structure
before the two existing collars can be glued into the bicollar.

### S-M5 continuation: two-sidedness produces the two complementary components

The connected-neighborhood checkpoint is committed and pushed as `6f9b12768`; the
following fetch and merge found integration still up to date at `8fb887bb9`.

`TwoSidedNeighborhood.lean` proves
`IsCombinatorialManifoldWithBoundary.exists_connected_neighborhood_sdiff_not_isPreconnected`
in every positive dimension. For a compact connected two-sided set, it produces an
arbitrarily small connected finite combinatorial manifold neighborhood with disconnected
complement. Two-sidedness is taken in the subtype `K.space`, so the result applies to
arbitrary finite-dimensional normed ambient spaces without assuming ambient dimension three.

The surface endpoint
`IsCombinatorialManifoldWithBoundary.exists_neighborhood_connectedComponentIn_pair_sdiff_of_twoSided`
constructs such a neighborhood for an interior connected closed combinatorial surface.
The surface stays in its intrinsic interior. The complement has precisely two actual
connected components; their closures cover the neighborhood and intersect exactly in
the surface. The disconnected-complement input of the earlier component theorem is now
proved from two-sidedness, rather than supplied as an additional assumption.

The focused check has exit 0 and zero warnings (`check-two-sided-neighborhood.log`).
`AuditS96TwoSidedNeighborhood.lean` / `.log` contain two entries, each using only
`propext`, `Classical.choice`, and `Quot.sound`. No vendored or other-lane source changed.
The source commit hash will be recorded at the following checkpoint.

26.3 remains partial: the two component closures must still be realized as finite
combinatorial manifolds with the surface as a boundary component, after which the two
existing collars can be glued. No unproved local-flatness or closure-manifold hypothesis
has been added to the public endpoint.

### S-M5 continuation: triangulating side closures and detecting manifold neighborhoods

The two-sided-neighborhood checkpoint is committed and pushed as `b7ba85f73`; integration
remained up to date after the required fetch and merge.

`ComplementComponents.lean` proves that the closure of any complementary connected
component of a subcomplex is precisely the carrier of its restriction subcomplex. A
common subdivision gives the polyhedral-closure result when only carrier inclusion of
two finite complexes is known. The proof propagates a component across the relative
interior of each simplex, then takes closures; it does not assume polyhedral components.

`ManifoldNeighborhood.lean` transfers vertex-link sphere/ball structure from a contained
relative manifold neighborhood to the ambient complex. It consequently proves
`isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods`: actual PL ball
neighborhoods at all points imply combinatorial manifold structure for any finite
triangulation, in every positive dimension.

Both focused checks have exit 0 and zero warnings (`check-complement-components.log`,
`check-manifold-neighborhood.log`). `AuditS97ComponentTriangulation.lean` / `.log` contain
five entries, all with only `propext`, `Classical.choice`, and `Quot.sound`.
The source commit hash will be recorded at the following checkpoint. No other-lane or
vendored source was modified.

26.3 remains partial: identify the actual local side-ball closures as neighborhoods in
each global component closure, apply the checked manifold criterion, identify the
surface boundary component, and glue its two collars.

### S-M5 continuation: the two side closures are manifolds with their exact boundaries

The component-triangulation checkpoint is committed and pushed as `92a27c0fb`; the
required integration merge was already up to date.

`Connected/ComponentNeighborhood.lean` proves that one of the two local component
closures is a relative neighborhood in a specified global component closure. The proof
uses points from both global components near the surface, so it does not silently identify
local components that could reconnect globally.

`ClosedStarNeighborhood.lean` generalizes the existing ball-neighborhood producer to
combinatorial manifolds with boundary and prescribed relative neighborhoods. The original
boundaryless theorem keeps its signature and becomes a corollary.

`SurfaceComponentClosure.lean` proves that every finite triangulation of either side
closure is a combinatorial three-manifold with boundary. Its boundary is exactly the
surface together with the part inherited from the ambient neighborhood boundary:
`Bd A = L.space ∪ (A.space ∩ Bd N)`. Away from the surface, local boundary membership
is inherited from N; at the surface, the actual two local PL three-balls meet in a PL
two-disk, placing the surface in the boundary of the appropriate side.

`TwoSidedNeighborhood.lean` now includes
`IsCombinatorialManifoldWithBoundary.exists_neighborhood_manifold_pair_of_twoSided`.
It produces an arbitrarily small connected manifold neighborhood N and connected finite
combinatorial manifolds A and B, with `A.space ∪ B.space = N.space`,
`A.space ∩ B.space = L.space`, both exact boundary formulas, and the relative-neighborhood
property along the whole surface. The only geometric input is the original two-sided
interior surface; neither side-manifold structure nor separation is an assumed interface.

All four changed modules have focused-check exit 0 and zero warnings
(`check-component-neighborhood.log`, `check-closed-star-neighborhood-boundary.log`,
`check-surface-component-closure.log`, `check-two-sided-neighborhood-manifolds.log`).
`AuditS98SurfaceComponentClosure.lean` / `.log` contain eight entries, all with only
`propext`, `Classical.choice`, and `Quot.sound`. The source commit hash will be recorded
at the following checkpoint. No other-lane or vendored source changed.

26.3 remains partial. The side-manifold construction and exact boundaries are now proved.
Next: restrict the existing boundary collars to this surface component, preserve their
relative-neighborhood property, and glue the two products along the middle surface.
The disconnected-surface case will then require combining the finitely many components.

### S-M5 continuation: arbitrarily small bicollars of connected two-sided surfaces

The side-closure checkpoint is committed and pushed as `927573c40`; the following
integration merge was already up to date.

`CollarRestriction.lean` restricts the proved whole-boundary collar to a polyhedral
boundary subset whose boundary complement is closed. It retains the relative-neighborhood
property, the identity bottom, the exact boundary trace, and interior positive levels.
Compactness of the image of the complementary part supplies the separating neighborhood.

`BicollarGluing.lean` reflects one collar parameter and glues the two PL maps along their
common bottom. It gives the product with `[-1,1]`, the identity middle surface, and negative
and positive levels in the respective sides away from that surface.

`Bicollar.lean` proves
`IsCombinatorialManifoldWithBoundary.exists_bicollar_of_isConnected`.
For a connected finite closed combinatorial surface in the interior of a finite
combinatorial three-manifold with boundary, two-sidedness in `K.space` produces, in every
prescribed relative neighborhood U, a polyhedral W and a PL homeomorphism
`L.space × [-1,1] -> W`. The image W is a relative neighborhood of the whole surface,
lies inside `K.space` away from its intrinsic boundary, lies in U, and the map is the
identity on the middle surface. No Schoenflies parameter or unproved interface is present.

All three focused checks have exit 0 and zero warnings (`check-collar-restriction.log`,
`check-bicollar-gluing.log`, `check-bicollar.log`). `AuditS99BicollarConnected.lean` / `.log`
contain three entries, all with only `propext`, `Classical.choice`, and `Quot.sound`.
The source commit hash will be recorded in the final bookkeeping entry. No other-lane or
vendored source was modified.

The connected finite-complex case of 26.3 is now proved. The general 26.3 row remains
partial: combine the finitely many surface components in pairwise disjoint neighborhoods,
then transport from finite-complex carriers to the requested general PL manifold setting.
The prior 26.1 interior-chart transport and P.4 obligations are unchanged.

### S-M5 connected bicollar publication checkpoint, 2026-09-16

The five mathematical checkpoints are committed and pushed: `6f9b12768` (small connected
manifold neighborhoods), `b7ba85f73` (two-sidedness and actual complementary components),
`92a27c0fb` (closure triangulations and local manifold criteria), `927573c40` (side manifolds
and exact boundary formulas), and `33e5a92d7` (arbitrarily small connected PL bicollars).
The twelve changed Lean modules have focused-check exit 0 and zero warnings.
AuditS95/S96/S97/S98/S99 contain 8/2/5/8/3 entries, respectively: 26 entries, all with
only `propext`, `Classical.choice`, and `Quot.sound`. Each source checkpoint was followed
by fetch and merge of the integration branch, still up to date at `8fb887bb9`.

This final bookkeeping commit updates only the S-M5 summary and B.4 plan row to the
verified scope. The overall 26.3 status remains partial; the connected finite-complex
case is proved, while the finite-component assembly and general manifold transport remain.
There is no new consultation blocker. The next mathematical step is the finite-component
assembly, using local connectedness and compactness for finiteness, pairwise disjoint
neighborhoods for the component bicollars, and finite PL gluing.

### S-M5 continuation: finite component decomposition and disjoint PL gluing

`ComponentComplex.lean` now defines `connectedComponentComplex K c`, indexed canonically
by `ConnectedComponents K.space`, and proves its carrier formula, finite face set,
connectedness, pairwise disjointness, and exact union. Both manifold predicates are
preserved. A finite polyhedral carrier has finitely many components, using compactness
and the already proved local connectedness.

`DisjointGluing.lean` proves `exists_isPLHomeomorphOn_iUnion_of_pairwise_disjoint` for a
finite family of PL homeomorphisms with pairwise disjoint source and target sets. The
global map agrees with every original map on its domain. `Connected/TwoSided.lean`
adds `IsTwoSided.preimage_connectedComponentIn`, so restricting an already two-sided
preimage to any target connected component preserves two-sidedness.

All three focused checks have exit 0 and zero warnings (`check-component-complex-finite.log`,
`check-disjoint-gluing.log`, `check-two-sided-components.log`).
`AuditS100FiniteComponents.lean` / `.log` contain twelve entries, each with only
`propext`, `Classical.choice`, and `Quot.sound`. No other-lane or vendored source changed.
The source commit hash will be recorded at the next checkpoint.

The next step assembles the existing connected bicollars in pairwise disjoint
neighborhoods of these finitely many components, removing the connectedness assumption
from the finite-complex bicollar endpoint. General PL charted ambient transport remains.

### S-M5 continuation: bicollars without a connectedness assumption

The finite-component decomposition and disjoint-gluing checkpoint is committed and
pushed as `7adcc0194`; the following integration merge was already up to date.

`Bicollar.lean` now proves
`IsCombinatorialManifoldWithBoundary.exists_bicollar` for any finite closed
combinatorial surface in the interior of a finite combinatorial three-manifold with
boundary. Two-sidedness in the carrier is the only separation assumption. The surface
can have multiple components or be empty. In every prescribed relative neighborhood U,
the theorem produces a polyhedral relative neighborhood W contained in U and away from
the manifold boundary, with a PL homeomorphism from the surface times `[-1,1]` that is
the identity on the middle surface. No Schoenflies parameter or unproved interface is
present. The proof separates the finitely many components by disjoint neighborhoods,
applies the connected endpoint, and glues the resulting PL maps.

The focused check has exit 0 and zero warnings (`check-bicollar-finite-components.log`).
`AuditS101Bicollar.lean` / `.log` contain two entries, both with only `propext`,
`Classical.choice`, and `Quot.sound`. No other-lane or vendored source changed.
The source commit hash will be recorded at the next checkpoint.

The finite-complex case of 26.3 is now proved. Transport to the general PL charted
manifold setting remains; the prior 26.1 interior-chart transport and P.4 obligations
are unchanged. I2's exact target-type compatibility issue is unchanged.

### S-M5 continuation: two-sidedness and PL piece parametrizations

The general finite-complex bicollar checkpoint is committed and pushed as `3a55ac834`;
the following integration merge was already up to date.

`Connected/TwoSided.lean` adds `IsTwoSided.preimage_of_isInducing`: two-sidedness pulls
back along a map inducing the domain topology whenever its range is a neighborhood
of the surface. Injectivity is unnecessary. Connected components pull back exactly,
and neighborhood images remain neighborhoods under the stated local range condition.

`PieceParametrization.lean` proves `PLPieceIn.isClosedEmbedding` for the restriction of
a finite-dimensional PL piece map to its carrier in a Hausdorff target. It defines
`PLPieceIn.precomp` to change a piece's parametrization by a PL homeomorphism, preserving
both directions of the chartwise PL condition. The new parameter ambient is finite
dimensional; the existing piece ambient need not be. Carrier and map formulas are explicit.

Both focused checks have exit 0 and zero warnings (`check-two-sided-transport.log`,
`check-piece-parametrization.log`). `AuditS102PieceTransport.lean` / `.log` contain five
entries, all with only `propext`, `Classical.choice`, and `Quot.sound`. No other-lane or
vendored source changed. The source commit hash will be recorded at the next checkpoint.

Next, choose a finite manifold neighborhood of the compact polyhedral surface, pull it
back into that piece, apply the finite-complex bicollar, and reparametrize its image piece.
General PL manifold 26.3 is not yet marked complete.

### S-M5 continuation: bicollars in general PL manifolds

The PL transport checkpoint is committed and pushed as `2c0c1c2a4`; the following
integration merge was already up to date.

`BicollarManifold.lean` proves `PLPieceIn.exists_bicollar_of_subset_interior` inside a
finite manifold piece, `PLPieceIn.exists_bicollar` in every prescribed neighborhood of
a two-sided finite polyhedral surface in a Hausdorff PL three-manifold, and the concrete
homeomorphism endpoints `PLPieceIn.exists_bicollar_homeomorph` and
`IsPolyhedralManifold.exists_bicollar`. The ambient manifold need not be compact or
second countable; the surface need not be connected. A finite surface piece already
supplies its compactness. The bicollar map is the identity at parameter zero, and its
image is a neighborhood of the entire surface contained in the prescribed U.

The PL certificate is explicit: the image has a `PLPieceIn (E x R) 3 X W` whose carrier
is exactly the chosen surface carrier times `[-1,1]`, and the delivered homeomorphism
`S x [-1,1] -> W` agrees with that piece map in the given surface parametrization.
Both the forward and inverse chartwise PL conditions are fields of this piece. The
proof obtains a finite manifold neighborhood, transports two-sidedness to its carrier,
applies the finite-complex bicollar, and changes its parametrization back.
`PieceParametrization.lean` adds the carrier homeomorphism and its evaluation formula.

Both final focused checks have exit 0 and zero warnings
(`check-piece-parametrization-homeomorph.log`, `check-bicollar-manifold.log`).
`AuditS103BicollarManifold.lean` / `.log` contain six entries, all with only `propext`,
`Classical.choice`, and `Quot.sound`. The endpoints have no Schoenflies or unproved
interface parameter. No other-lane or vendored source changed.
The source commit hash will be recorded at the next checkpoint.

The two requested settings for 26.3 are now proved: finite combinatorial manifolds with
boundary, and general Hausdorff PL charted three-manifolds. The prior 26.1 interior
transport for arbitrary K and the supported ambient graph extension in P.4 remain.
I2's exact target-type compatibility issue is unchanged.

### S-M5 completion: relative topology and two-sidedness in manifolds with boundary

The general PL-manifold bicollar checkpoint is committed and pushed as `52d70d778`;
the following integration merge was already up to date.

`ManifoldRelativeTopology.lean` closes the remaining 26.1 transport obligation directly
in the subtype topology of a finite combinatorial manifold K. For a finite manifold A
of the same dimension contained in K, it proves `closure_interior_preimage` from the
previous double-complement closure formula. If A avoids the intrinsic boundary of K,
`inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary` and
`frontier_preimage_space_eq_preimage_boundaryComplex` identify its relative frontier
with its intrinsic boundary. Neighborhood invariance of intrinsic boundary membership
supplies the previously missing reverse containment.

`IsCombinatorialManifoldWithBoundary.isTwoSided_boundaryComplex` and
`.isTwoSided_of_union_boundary_components` then prove the full boundary and any union
of its connected components are two-sided in K.space. These results hold in every
positive dimension and arbitrary finite-dimensional real normed ambient spaces.
Local connectedness of the boundary is proved via its finite complex and transported
to the subtype. No additional regular-closed, local-connectedness, chart, or separation
hypothesis is required. Constructing an interior charted-space instance is unnecessary
for this endpoint, so the earlier 26.1 interior-chart transport gap is removed.

The focused check has exit 0 and zero warnings (`check-manifold-relative-topology.log`).
`AuditS104RelativeTwoSided.lean` / `.log` contain five entries, all with only `propext`,
`Classical.choice`, and `Quot.sound`. No Schoenflies or unproved interface parameter is
present. No other-lane or vendored source changed. The source commit hash will be
recorded in the final bookkeeping entry.

S-M5's 26.1 and 26.3 endpoints are now proved in the finite-complex and general PL
charted settings described above. P.4's controlled supported graph extension remains;
I2's exact target-type compatibility issue is unchanged.

### S-M6 continuation: supported homeomorphism extension and finite gluing

The relative-topology and 26.1 checkpoint is committed and pushed as `7746cff68`;
the following integration merge was already up to date.

`Topology/Homeomorph/ClosedExtension.lean` defines `Homeomorph.extendById`: a
self-homeomorphism of a closed subset that fixes its frontier extends to the ambient
space by the identity. It agrees with the given map on the closed set, preserves that
set, and fixes the complement of its interior. No separation or metric hypothesis is
needed for this construction. In a pseudometric space its displacement is bounded by
the diameter of the closed set, and `dist_extendById_lt` gives pointwise positive-function
control from a sufficiently small diameter.

`Topology/Homeomorph/DisjointGluing.lean` proves
`Homeomorph.exists_gluing_of_pairwise_disjoint`: finitely many ambient homeomorphisms
supported in pairwise disjoint sets glue to a single homeomorphism agreeing with each
map on its set and fixing the complement of their union. `exists_gluing_dist_lt`
preserves the individual pointwise displacement bound without summing errors.

Both focused checks have exit 0 and zero warnings (`check-homeomorph-closed-extension.log`,
`check-homeomorph-disjoint-gluing.log`). `AuditS105SupportedHomeomorphs.lean` / `.log`
contain nine entries, all with only `propext`, `Classical.choice`, and `Quot.sound`.
No other-lane or vendored source changed. The source commit hash will be recorded in
the final bookkeeping entry.

These are supported-extension and control tools for P.4, not a proof of finite graph
tameness. The actual compatible sector homeomorphisms inside vertex disks and relative
straightening inside the edge frames still have to be constructed from the planar
Jordan/Schoenflies inputs. P.4 remains partial, and I2's target-type issue is unchanged.

### S-M5 completion and S-M6 publication checkpoint, 2026-09-16

The source checkpoints are committed and pushed as `7adcc0194` (finite component
complexes and disjoint PL gluing), `3a55ac834` (finite bicollars without connectedness),
`2c0c1c2a4` (two-sidedness and PL piece transport), `52d70d778` (general PL-manifold
bicollars), `7746cff68` (relative boundary topology and 26.1), and `6d1df9349`
(supported homeomorphism extension and finite gluing). The nine distinct Lean modules
changed across these checkpoints have focused-check exit 0 and zero warnings.
AuditS100--S105 contain 12/2/5/6/5/9 entries, respectively: 39 entries, all with only
`propext`, `Classical.choice`, and `Quot.sound`.

Every source checkpoint was followed by fetch and merge of the integration branch.
The final source checkpoint is clean and synchronized with origin/codex/moise-s;
origin/codex/moise-integration remains merged at `8fb887bb9`. This bookkeeping commit
updates the S-M5/S-M6 summary and plan rows B.1, B.4, and P.4 to the verified scope,
and removes the now-discharged B.4 prerequisites from B.2's remaining-work sentence.

S-M5 is complete in the stated finite-complex and general Hausdorff PL charted settings.
S-M6 remains partial: 17.3 is proved, while P.4 still requires the actual compatible
vertex-sector and edge-frame constructions. The supported extension and control tools
do not themselves imply graph tameness. I2's exact target-type issue is unchanged.
There is no new consultation blocker; the next step is relative straightening of arcs
inside a disk while fixing its boundary.

### S-M6 continuation: compatible boundary-arc extensions

The S-M5 completion and S-M6 bookkeeping is committed and pushed as `a7ccc3533`;
the following integration merge was already up to date.

`PlanarJordan/Transport.lean` proves `isArcBetween_image`,
`isJordanCurve_image`, and `image_inside` for ambient plane homeomorphisms.
The inside-image formula holds for every subset of the plane; bounded components
remain bounded because their closures are compact.

`PlanarJordan/ArcExtension.lean` proves `exists_homeomorph_extending_two_arcs`:
two arcs forming a Jordan curve, equipped with endpoint-compatible homeomorphisms
to a second such pair, admit one ambient extension realizing both prescribed maps.
The compact glued boundary map is a homeomorphism, and the proved relative
Jordan--Schoenflies theorem extends it. `exists_homeomorph_image_two_arcs` supplies
the maps by matching arc parameters. `exists_homeomorph_image_arc_polygonal`
simultaneously makes both arcs polygonal using the two halves of the model square.
No polygonality of either original arc is assumed.

Both focused checks have exit 0 and zero warnings (`check-planar-jordan-transport.log`,
`check-planar-arc-extension.log`). `AuditS106PlanarArcExtension.lean` / `.log`
contain six entries, all with only `propext`, `Classical.choice`, and `Quot.sound`.
No vendored or other-lane source changed. The source hash will be recorded at the
next checkpoint. The next step transports the proved polygonal crosscut theorem
to arbitrary embedded crosscuts, then constructs the boundary-fixed disk map.
P.4 remains partial; I2's target-type issue is unchanged.

### S-M6 continuation: crosscuts without a polygonality assumption

The compatible-arc extension layer is committed and pushed as `7e1951a69`; the
following integration merge was already up to date.

`PlanarJordan/Crosscut.lean` proves `crosscut_regions` for an arbitrary embedded
arc in a Jordan disk with its distinct endpoints on the boundary. The two labelled
sides are the interiors of the curves formed with the two boundary arcs; they are
disjoint, cover the disk minus the crosscut, and their closures meet the outer
boundary in the respective boundary arcs. `closed_crosscut_regions` proves that
the two closed sides cover the original closed disk and intersect exactly in the
crosscut. `arc_inter_curve_eq_pair` and `isJordanCurve_cut_arc_union` expose the
intersection and Jordan-curve facts used in the construction.

The proof first makes the crosscut polygonal by extending its compatible boundary
arc maps, applies the existing checked polygonal theorem, and transports its
regions and closures back. The public statements do not assume polygonality,
collars, local flatness, or an unproved separation theorem.

The focused check has exit 0 and zero warnings (`check-planar-crosscut.log`).
`AuditS107Crosscut.lean` / `.log` contain four entries, all with only `propext`,
`Classical.choice`, and `Quot.sound`. No vendored or other-lane source changed.
The source hash will be recorded at the next checkpoint. The next step extends
a prescribed crosscut homeomorphism over both closed sides, glues them, and extends
by the identity outside the disk. P.4 is still partial.

### S-M6 continuation: supported crosscut extension with displacement control

The general crosscut theorem is committed and pushed as `d9f27c4b4`; the following
integration merge was already up to date.

`PlanarJordan/CrosscutExtension.lean` proves
`exists_homeomorph_closed_disk_extending_crosscut`: any endpoint-preserving
homeomorphism between two embedded crosscuts of the same Jordan disk extends over
the closed disk and fixes its boundary pointwise. Neither crosscut needs to be
polygonal. Each labelled side receives the checked relative Jordan extension; the
two maps agree on the whole crosscut and their target sides meet exactly in its image,
so compact gluing gives a bijective continuous map with continuous inverse.

`exists_homeomorph_extending_crosscut` extends that disk map by the identity to
the plane. It agrees with the prescribed map on the original arc, fixes every point
outside the disk interior (including its boundary), and bounds displacement by the
closed disk diameter. `exists_homeomorph_image_crosscut_dist_lt` chooses the arc
homeomorphism and gives strict pointwise control for any positive function when
the disk diameter is smaller than that function throughout the disk.

`Homeomorph/CompactGluing.lean` contains the reusable compact-cover gluing theorem
for Hausdorff spaces. `ArcExtension.lean` now consumes it; its public statements
are unchanged and the repeated gluing proof is removed.

The three changed source modules and the Crosscut consumer have focused-check exit 0
and zero warnings (`check-homeomorph-compact-gluing.log`,
`check-planar-arc-extension.log`, `check-planar-crosscut.log`,
`check-crosscut-extension.log`). `AuditS108SupportedCrosscut.lean` / `.log`
contain eleven entries covering the new endpoints and the affected arc/crosscut
chain, all with only `propext`, `Classical.choice`, and `Quot.sound`.
No vendored or other-lane source changed. The source hash will be recorded in the
final publication entry.

P.4 remains partial. Its relative map inside a chosen Jordan frame is now proved;
the remaining geometric producers are compatible vertex sectors and sufficiently
small frames around the finite graph, with appropriate polygonal target arcs.
I2's exact target-type issue is unchanged.

### S-M6 crosscut publication checkpoint, 2026-09-16

The source checkpoints are committed and pushed as `7e1951a69` (compatible arc
extensions and planar transport), `d9f27c4b4` (arbitrary crosscut separation), and
`4ddbf78f4` (supported crosscut extension and compact gluing). All five Lean
modules have final focused-check exit 0 and zero warnings. AuditS106/S107/S108
contain 6/4/11 entries, respectively: 21 entries, all with only `propext`,
`Classical.choice`, and `Quot.sound`. S108 also rechecks the arc and crosscut
chain after factoring out compact gluing; these counts are audit entries,
not counts of distinct declarations.

The working branch is synchronized with origin/codex/moise-s. Fetch and merge
after each source checkpoint found origin/codex/moise-integration already merged
at `8fb887bb9`. This final bookkeeping commit updates only the S-M6 summary
and P.4 plan row to distinguish the proved relative map inside a given Jordan
frame from the still-missing finite-graph frame and vertex-sector producers.
S-M5 remains complete in its stated settings. There is no new consultation
blocker; the active continuation is the geometric construction required by P.4.

### S-M6 continuation: vertex arcs and crosscut-side selection

The supported-crosscut publication checkpoint is committed and pushed as `d97cab7af`;
the next integration merge was already up to date.

`PlanarJordan/VertexArcs.lean` proves `exists_initial_arc_to_frontier`: an embedded
arc leaving an open set has an initial subarc whose far endpoint is on the frontier
and whose remaining points stay in the open set. `Graph.IsDrawing.exists_vertex_arcs`
constructs these subarcs for every edge incident with a vertex. They meet pairwise
exactly at that vertex and have distinct frontier endpoints. It requires only an
open neighborhood whose closure contains no other graph vertex, with no finiteness
assumption on the graph. `exists_vertex_arcs_in_square` produces such a square
inside any specified neighborhood for a finite drawing and also avoids all
nonincident edges. The rest of an edge is allowed to return to the square later.

`Crosscut.lean` adds `subset_crosscut_side_of_mem_closure` and
`arc_diff_subset_crosscut_side`: a connected set in the complement of the crosscut
lies on the side identified by its limiting boundary point. This supplies the
geometric side-selection step for further vertex-fan cuts.

VertexArcs, Crosscut, and the affected CrosscutExtension consumer have focused-check
exit 0 and zero warnings (`check-planar-vertex-arcs.log`, `check-planar-crosscut.log`,
`check-crosscut-extension.log`). `AuditS109VertexArcs.lean` / `.log` contain eight
entries, all with only `propext`, `Classical.choice`, and `Quot.sound`. No vendored
or other-lane source changed. The source hash will be recorded at the next checkpoint.
P.4 remains partial: simultaneous straightening of the whole finite vertex fan and
the small edge frames still have to be constructed. I2's target-type issue is unchanged.

### S-M6 continuation: supported simultaneous straightening of two vertex arcs

The initial-arc and side-selection layer is committed and pushed as `3302febfc`;
the following integration merge was already up to date.

`PlanarJordan/VertexFan.lean` proves `exists_homeomorph_extending_two_vertex_arcs`:
two arcs from a common interior vertex to the boundary of one Jordan disk can be
mapped simultaneously to a second such pair, with their prescribed compatible arc
maps, by an ambient homeomorphism fixing the disk exterior and boundary. The union
map preserves the marked common vertex; merely choosing an arbitrary homeomorphism
of the combined crosscut would not ensure this. Compact gluing constructs that map,
and the checked supported-crosscut theorem extends it. Displacement is bounded by
the closed disk diameter.

`exists_homeomorph_image_two_vertex_arcs` chooses the arc maps.
`exists_homeomorph_image_two_vertex_arcs_radial` supplies the actual straight radial
targets in a square and fixes the common center. The finite-graph producer
`Graph.IsDrawing.exists_homeomorph_radial_vertex_arc_pair` constructs the square and
the two initial subarcs inside any specified neighborhood of a vertex. The square
avoids all nonincident edges, and the ambient map fixes everything outside its open
interior and moves points by at most its diameter.

The VertexFan focused check has exit 0 and zero warnings (`check-planar-vertex-fan.log`).
`AuditS110VertexFan.lean` / `.log` contain four entries, all with only `propext`,
`Classical.choice`, and `Quot.sound`. No vendored or other-lane source changed.
The source hash will be recorded at the next checkpoint. P.4 remains partial:
the rest of a finite vertex fan still needs simultaneous straightening by recursive
crosscut-side gluing; degree-one endpoints and the edge frames remain outstanding.
No general graph-tameness endpoint is claimed. I2's target-type issue is unchanged.

### S-M6 continuation: simultaneous extension of a finite boundary fan

The two-arc straightening layer is committed and pushed as `47062f7d4`; the following
integration merge was already up to date.

`PlanarJordan/BoundaryArc.lean` proves
`exists_isCutPair_inter_closed_eq_singleton`. From a point of a Jordan curve outside
a closed set meeting the curve, it constructs a cut pair whose first boundary arc
meets the closed set only at its far endpoint. The proof takes the first parameter
meeting the closed set and constructs the complementary arc from the remaining tail.
The result applies to arbitrary closed sets, not only finite endpoint sets.

`PlanarJordan/BoundaryFan.lean` proves `exists_homeomorph_image_boundary_fan` for any
finite family of embedded crosscuts sharing a common point on a Jordan boundary,
with distinct arcs meeting only at that point. Two such families with the same
boundary endpoints admit a simultaneous ambient matching fixing the disk exterior
and boundary. The proof selects the first remaining boundary endpoint, matches that
crosscut, and invokes induction in the remaining Jordan disk. The side-selection
lemma places every remaining arc in that disk; the induction fixes the matched arc.
No cyclic-order, sector-decomposition, or unproved extension hypothesis is added.

Both focused checks have exit 0 and zero warnings (`check-planar-boundary-arc.log`,
`check-planar-boundary-fan.log`). `AuditS111BoundaryFan.lean` / `.log` contain two
entries, both with only `propext`, `Classical.choice`, and `Quot.sound`.
No vendored or other-lane source changed. The source hash will be recorded at the
next checkpoint. The next step applies the boundary-fan theorem to the two sides
of the first matched pair at an interior vertex. P.4 is still partial; degree-one
endpoints and edge frames remain beyond that step. I2's target-type issue is unchanged.

### S-M6 continuation: supported straightening of a finite interior vertex fan

The finite boundary-fan layer is committed and pushed as `1b6245266`; the following
integration merge was already up to date.

`PlanarJordan/VertexFan.lean` now proves
`exists_homeomorph_image_vertex_fan_of_nontrivial`: two finite embedded fans with at
least two branches, a common interior vertex, and matching boundary endpoints admit
one ambient matching fixing the vertex and the disk exterior. After matching two
branches, their union is a crosscut. The remaining branches fall into its two labelled
sides according to their boundary endpoints. The finite boundary-fan theorem extends
each side, and disjointness from the other closed side makes their composition preserve
every branch already matched.

`exists_homeomorph_radial_vertex_fan` supplies the actual radial target segments in
a square, fixes its center and exterior, and bounds all displacement by its diameter.
`Graph.IsDrawing.exists_homeomorph_radial_vertex_fan` produces the square, every
incident initial subarc, and the simultaneous ambient straightening inside any given
neighborhood of a vertex with at least two incident edges. Nonincident edges are avoided.
This is a local geometric producer for the complete finite fan at that vertex. The
published two-arc radial statements retain their signatures and are now corollaries
of the finite-family statements.

The final VertexFan focused check has exit 0 and zero warnings (`check-planar-vertex-fan.log`).
`AuditS112FiniteVertexFan.lean` / `.log` contain eight entries covering all seven
VertexFan endpoints and the boundary-fan input, all with only `propext`,
`Classical.choice`, and `Quot.sound`. No vendored or other-lane source changed.
The source hash will be recorded in the final publication entry.

P.4 remains partial. The local vertex construction is proved for at least two
incident edges; degree-one endpoints still need a separate argument. The next
geometric work is small edge frames and polygonal crosscuts, followed by the
assembly over disjoint vertex and edge supports with the prescribed global control.
No new consultation blocker was found. I2's target-type issue is unchanged.

### S-M6 finite vertex-fan publication checkpoint, 2026-09-16

The source checkpoints are committed and pushed on `codex/moise-s`:

- `3302febfc`: initial vertex arcs and crosscut-side selection.
- `47062f7d4`: supported simultaneous straightening of two incident arcs.
- `1b6245266`: closed boundary-set selection and finite boundary-fan extension.
- `5889f3772`: finite interior vertex-fan matching and the local finite-graph producer.

The five changed Lean modules (VertexArcs, Crosscut, VertexFan, BoundaryArc, and
BoundaryFan) and the CrosscutExtension consumer all have final focused-check exit 0
with zero warnings. AuditS109, S110, S111, and S112 contain respectively 8, 4, 2, and
8 entries: 22 audit records, including deliberate rechecks of the two-arc corollaries
after refactoring. Every entry contains only `propext`, `Classical.choice`, and
`Quot.sound`. Logs and audit probes remain under `.lake/scratch` and are not committed.

After the last source push, `git fetch origin` and the requested integration merge
reported already up to date at `8fb887bb9`; the worktree and `origin/codex/moise-s`
were synchronized at `5889f3772`. This final documentation checkpoint updates only
the S-M6 summary and P.4 plan row to the verified scope.

P.4 remains partial: local simultaneous straightening is proved for all initial
subarcs at a vertex with at least two incident edges. Degree-one endpoints, small
edge frames, polygonal target crosscuts, and the global assembly with prescribed
support and positive control remain. Initial subarcs are used explicitly; later
parts of an incident edge may return to the chosen square. I2's target-type issue
is unchanged, and no new consultation blocker was found.

### Integration repair and fresh verification, 2026-09-16

NIGHT_PLAN section 6.2 is implemented against integration commit `314c2178f`.
The merge preserves both lanes' mathematics and the combined P.3/P.4 plan evidence.

- `BoundaryDerivedNeighborhood` now selects the root-level ball-intersection theorem
  by its fully qualified name, avoiding the newer namespaced theorem's shadowing.
- S's neighborhood module is now `SubcomplexNhdsWithin`; its three importers use
  that name. H's `SubcomplexNeighborhood` is retained unchanged.
- S's more general centroid lemma is named
  `pair_centroid_mem_barycentricSubdivision_of_subset_or_subset`. H's original
  declaration is retained unchanged and both are imported in the collision audit.
- `ManifoldFaces` imports H's canonical with-boundary face-extension theorem from
  `ManifoldConnectivity`. The duplicate is removed; the boundaryless wrapper keeps
  its existing public signature. With-boundary call sites use the canonical signature.

The earlier checks of BoundaryDerivedNeighborhood and its fourteen downstream
modules did not validate the current sources against fresh dependencies. Those
claims are superseded by this complete recheck. The manifest contains all 86 S
modules changed since `8fb887bb9`, with the renamed module substituted, plus H's
ManifoldConnectivity and SubcomplexNeighborhood: 88/88 focused checks exit 0,
zero warnings. The unchanged H DerivedCarrier module also has a fresh exit-0,
zero-warning check. `AuditS113IntegrationRepair.lean` imports these modules and
checks 307 public declarations, including both formerly colliding H declarations;
exit 0 and only `propext`, `Classical.choice`, and `Quot.sound`.

A second cache hazard was observed during verification: another check replaced the
shared FrontierBoundary artifact after S had checked it, removing an S declaration
from the artifact seen by PrismBoundary. S now writes artifacts to
`E:\differential-geometry-dev\.lake\scratch\s-verified-20260916`. Both authorized
local scripts use this directory first. Dependencies refer to existing artifacts
for source modules already obtained through integration; no other-lane source was
copied. Before compilation, check-f removes the target olean, ilean, private and
server artifacts with deletion failure treated as fatal. Each successful check
requires its new olean to exist. Source fingerprints for all 86 S modules, all 88
new target artifacts, and 484 unchanged dependency artifacts were verified after
the full run. The isolated PrismBoundary check passed without a source change.

Evidence remains in `.lake/scratch`: `s-night-recheck.txt`,
`s-snapshot-recheck-results.tsv`, per-module logs, artifact fingerprints,
`check-repair-derived-carrier.log`, and `AuditS113IntegrationRepair.log`.
The initial audit omitted the DerivedCarrier import; the corrected complete audit
above is the delivery record. I2 in the double environment is the next milestone.

### S-M3: I2 已交付（double 环境）, 2026-09-16

The integration-repair checkpoint is committed and pushed as `30102ea5d`.
A subsequent fetch and merge of integration reported already up to date.
The earlier I2 target-type blocker is resolved by NIGHT_PLAN section 6.1; this
entry supersedes that blocker in the historical notes above.

Three native modules provide five new public theorems:

- `PieceMap.lean`: `PLPieceIn.isPLOn_comp` turns a piecewise affine map into a
  PL piece into a chartwise PL map, in arbitrary source and target dimensions.
- `LoopTheorem/PolyhedralCell.lean`:
  `PLPieceIn.exists_nonsingular_two_cell_of_isPLBall` realizes a parametrized disk
  inside a PL piece as a nonsingular singular two-cell, with exact carrier and
  boundary-image equalities. The closed combinatorial-manifold specialization is
  `exists_nonsingular_two_cell_of_isPLBall_in_combinatorial_manifold`.
- `LoopTheorem/DoubleBoundaryPush.lean`:
  `exists_nonsingular_two_cell_of_boundary_disk` takes a finite combinatorial
  3-manifold with boundary in any finite-dimensional real normed space, and a
  parametrized disk in its boundary complex. It constructs a nonsingular
  `SingularTwoCell (double 3 K).space` in the second copy of K. Its boundary image
  and its intersection with that copy's boundary both equal the embedded original
  disk boundary. `exists_nonsingular_two_cell_of_disk_in_double_boundary` accepts
  the disk directly in that ambient boundary image and supplies E3's hpush.

Precisely, the copy map is
`simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)`, the affine extension of the
vertex embedding. The environment chart is
`combinatorialChartedSpace (double 3 K) (isCombinatorialManifold_double_succ_succ K hK)`.
The ambient inclusion used for the singular cell is `Subtype.val`. No charted-space
assumption on the original manifold with boundary is introduced. The construction
uses the checked intrinsic boundary-disk push and H's checked double; these endpoints
need no additional Schoenflies or other unproved hypothesis.

All three modules have focused-check exit 0 and zero warnings, against the isolated
S artifact directory. `AuditS114DoubleBoundaryPush.lean` / `.log` check all five new
public declarations and the two principal producers: seven entries, only `propext`,
`Classical.choice`, and `Quot.sound`. The same audit contains a silent example with
E3 SphereCase's exact hpush quantifiers and four conclusions, supplied directly by
the second endpoint; it elaborates successfully. No E3 source or vendored source
was changed. P.4 remains the next milestone, followed by S.6 as in NIGHT_PLAN 6.2.

### S-M6: controlled simultaneous planar straightening, 2026-09-16

I2's double-environment producer is committed and pushed as `b926417f6`.
The subsequent integration fetch and merge reported already up to date.

`PlanarJordan/VertexStraightening.lean` proves
`Graph.IsDrawing.exists_homeomorph_radial_vertex_fans`. Given a selected finite set
of vertices of a finite planar drawing, each with at least two incident edges, an
open neighborhood of those vertices, and a continuous positive error function, it
constructs pairwise disjoint closed vertex squares and one ambient homeomorphism
straightening every selected incident initial subarc to its radial segment. The
homeomorphism fixes every graph vertex and the prescribed neighborhood's exterior,
and its displacement is strictly less than the error function at every point.
The proof selects squares inside both the prescribed neighborhood and regions on
which the error function has a quantitative lower bound, then uses disjoint gluing.

`PiecewiseLinear/InteriorAccess.lean` proves line-segment accessibility from the
interior at every point of a full-dimensional finite combinatorial manifold with
boundary, in every positive Euclidean dimension. A top-dimensional simplex through
the point supplies the segment. The PL-ball specialization gives polygonal interior
access at every point of a planar PL disk, and `IsPLBall.exists_isCrosscut` constructs
a polygonal crosscut between any two distinct boundary points. No accessibility or
preselected polygonal target is assumed.

`PlanarJordan/PolygonalCrosscut.lean` proves
`exists_homeomorph_polygonal_crosscut`: an arbitrary topological crosscut of a planar
PL disk becomes polygonal under an ambient homeomorphism fixing the disk exterior
and boundary, with displacement bounded by the disk diameter. Its finite-family
version `exists_homeomorph_polygonal_crosscuts` straightens crosscuts in pairwise
disjoint PL disks simultaneously, fixes the complement of their interior union,
and satisfies a positive pointwise error bound when the given disk diameters do.
This result consumes disk frames; it does not construct them from arbitrary arcs.

All three modules have focused-check exit 0 and zero warnings. The final
`AuditS115PlanarStraightening.lean` / `.log` contain all seven new public declarations;
exit 0 and only `propext`, `Classical.choice`, and `Quot.sound`. No vendored source or
other-lane source changed, and the root aggregate remains untouched.

P.4 is still partial. The remaining geometric producers are the treatment of
arbitrary degree-one endpoints and arbitrarily small compatible PL disk frames
around the original edge pieces. A disk neighborhood containing an arc is not yet
a frame in which that arc is a crosscut: the precise boundary intersections and
later reentries must be controlled. Neither Jordan/Schoenflies extension alone nor
the vendored polygonal redrawing theorem supplies these ambient relative data.
The current results do not assume these missing producers under new proposition
names and do not claim the full Moise 10.8 endpoint.

### S.6 dependency check, 2026-09-16

The merged integration source at `314c2178f` contains no IsSphericalShell producer
or `exists_isPLSphere_separating_of_sphericalShell` declaration. The plan's I.4 row
still marks Moise 30.4 as new and S.6 explicitly depends on that result. Under the
instruction allowing only an explicit hSchoenflies, no additional 30.4 hypothesis
has been introduced and no completed 30.5 endpoint is claimed. The outstanding
external input is a PL 2-sphere in the shell interior separating its two boundary
components, as specified in I.4. Obtain future I-lane source only by integration merge.

### Publication checkpoint, 2026-09-16

- `30102ea5d`: integration merge and collision repairs; all 88 manifest modules and
  the additional DerivedCarrier check pass, with the 307-entry S113 audit.
- `b926417f6`: I2 in the double environment; three modules and the seven-entry S114
  audit pass, including the silent direct E3 hpush signature check.
- `8560f9a30`: simultaneous vertex and polygonal crosscut straightening; three modules
  and the final seven-entry S115 audit pass.

All source checkpoints are pushed to origin/codex/moise-s. The final integration
fetch and requested merge still report `314c2178f` and already up to date. This
plan-only publication update changes the S-owned P.4, B.2 and S.6 status cells to
match the verified endpoints and explicit remaining obligations. E3's L.2 consumer
row is left to that lane; its hpush producer is now available from DoubleBoundaryPush.

### Boundary parity for Moise 26.6, 2026-09-16

`OneManifoldBoundary.lean` proves that the intrinsic boundary of every finite
combinatorial one-manifold with boundary has even cardinality. The proof identifies
boundary points with degree-one vertices of its edge graph and applies the
handshaking lemma; interior vertices have degree two. The corollary
`boundaryComplex_one_space_ne_singleton` rules out exactly one boundary point.
The statements apply in every finite-dimensional real normed ambient space and
require no Schoenflies hypothesis.

Focused check: exit 0, zero warnings. `AuditS116BoundaryParity.lean` audits all three
new declarations; exit 0, only `propext`, `Classical.choice`, and `Quot.sound`.
This is the parity input to B.6, not yet the surface separation endpoint. The
remaining B.6 work is the single-crossing boundary-loop construction and its
relative general-position disk filling, followed by the component/frontier result.
Per the latest assignment, S.6 and B.8 are deferred; current order is B.6, the
internal two-sided Problem 26.3 endpoint, and the remaining P.4 producers.

### Boundary intersections under relative general position, 2026-09-16

`PreimageBoundary.lean` identifies the boundary of the transverse one-dimensional
preimage complex with the preimage of the target manifold on the source boundary.
A source-boundary point lies in a boundary face. The carrier-face dimension estimate
forces its preimage face to have one vertex; the existing degree classification
then identifies it as a boundary point. This closes the previously missing link
between graph parity and geometric boundary intersections.

`even_ncard_boundary_preimage_of_transverse_faces` gives even intersection count
for a transverse simplicial map. `even_ncard_boundary_preimage_of_transverse_boundary`
only assumes transversality and affine independence on the source boundary; the
interior is perturbed by `exists_small_simplicialMap_preimage_manifold_relative`,
which fixes that boundary pointwise. The results hold for source dimension m+1,
closed target dimension n+1, and ambient dimension m+n+1. No extra class or
Schoenflies assumption is present.

Focused check: exit 0, zero warnings. `AuditS117PreimageBoundary.lean` checks all
three public declarations; exit 0, only the standard three axioms. B.6 remains
partial pending the single-crossing loop producer and the global component result.

### Problem 26.3: two-sided disk neighborhoods delivered, 2026-09-16

`InteriorManifoldComplement.lean` constructs a finite combinatorial three-manifold
triangulating the actual closed complement of an interior finite submanifold.
`TwoSidedDiskNeighborhood.lean` applies the existing boundary-disk neighborhood
producer separately to the submanifold and that complement. It returns PL three-balls
on the two sides, both contained in any prescribed relative neighborhood of the disk;
each meets the intrinsic boundary in exactly that disk, and their mutual intersection
is exactly the disk. A full-dimensional ambient version uses `frontier`.

`ManifoldPieceInclusion.lean` gives a reusable parameterization restriction to any
polyhedral manifold with boundary. `TwoSidedDiskNeighborhoodManifold.lean` transports
the ball pair to an abstract Hausdorff PL three-manifold. The final endpoint is
`IsPolyhedralManifoldWithBoundary.exists_isPolyhedralBall_pair_inter_frontier_eq`:
for polyhedral three-manifold N, N contained in the interior of M, polyhedral two-ball
D in frontier N, and any set neighborhood U of D, it constructs polyhedral three-balls
C1 and C2 with C1 contained in N, C2 contained in closure (M minus N), both contained
in U, and all three intersections C1 with frontier N, C2 with frontier N, and C1 with
C2 equal to D. The ambient set M need not carry additional compactness or triangulation
assumptions. The PL chart groupoid on the ambient space supplies the local environment.

All four new modules pass the focused checks with exit 0 and zero warnings.
`AuditS118TwoSidedDisk.lean` / `.log` cover all six public declarations: exit 0,
only `propext`, `Classical.choice`, and `Quot.sound`. No hSchoenflies or unproved
auxiliary proposition is required. The parameterized core and ambient-neighborhood
selection are separate mathematical interfaces; this also avoids dependent-dimension
elaboration blowup without resource overrides. B.2's remaining two-sided Problem 26.3
obligation is now delivered. B.6 and the remaining P.4 producers are still in progress.

### Transverse segments and PL paths in open sets, 2026-09-16

`OpenPLPath.lean` proves that any two points of an open preconnected set in a real
normed space can be joined by a PL path, without a finite-dimensional assumption.
`TransverseSegment.lean` constructs a transverse segment through the relative
interior of a codimension-one maximal simplex, meeting the complex only at its
midpoint. Its surface corollary supplies such a segment for every nonempty finite
combinatorial two-manifold in a three-dimensional ambient space.

Both focused checks pass with exit 0 and zero warnings. `AuditS119TransversePath`
checks all four public declarations; exit 0, only the standard three axioms. These
are geometric producers for the B.6 contradiction. The single-crossing circle map,
relative disk filling, and global separation theorem remain to be completed.

### Single-intersection circles and relative parity, 2026-09-16

Merged integration `4401dd9d1` at `8e57b8304`. The local check and audit recipes now
use only the shared olean library, in accordance with NIGHT_PLAN section 8. All
new S modules from the boundary-parity checkpoint onward were checked sequentially
into that library; no private artifact directory remains on LEAN_PATH. Pause Lean
when integration review requests it and resume only after the explicit release.

`CircleMap.lean` constructs a PL map on any PL circle from two PL interval maps
with matching endpoints. `SingleIntersectionCircle.lean` uses this producer and
open-complement PL paths to build an actual circle map with a singleton preimage
of the target surface. It extends the map to the entire source ambient space and
proves that a small translation moves the unique intersection away from any finite
source set while keeping the return arc in the complement.

`PreimageBoundaryRelative.lean` proves even boundary-intersection cardinality when
only a subcomplex containing all intersections is transverse. Relative general
position fixes that subcomplex, while compactness gives a positive perturbation
margin on the remaining boundary faces. Thus the return path need not satisfy
unnecessary affine-independence hypotheses before perturbation.

All eleven new S modules in this sequence have shared-library focused checks with
exit 0 and zero warnings. `AuditS120CircleParity.lean` / `.log` re-audit all twenty
public declarations, including B.2 and the new circle/relative-parity inputs; exit 0,
only the standard three axioms. B.6 is still in progress: the remaining step is to
assemble the triangulated disk and its transverse crossing face, apply relative
parity, and derive the global components/frontier statement. P.4 remains pending.

### Closed surfaces disconnect three-dimensional space, 2026-09-16

`BoundaryCrossingObstruction.lean` proves that a unique boundary preimage point in
a transverse source facet is impossible. Its local form needs only the target
open-simplex condition and the sum-of-direction-spaces condition at that point.
`SurfaceSeparation.lean` assembles the actual PL disk map: it glues the transverse
segment to a complementary PL path, extends the circle map, triangulates the disk
and crossing arc, and translates the map to avoid all source vertices. The source
crossing face is therefore an edge, its image is nondegenerate and transverse, and
the local parity obstruction applies.

The headline `IsCombinatorialManifold.not_isPreconnected_compl` proves that the
complement of any nonempty finite closed combinatorial two-manifold in any real
normed space of dimension three is not preconnected. No connectedness assumption
on the surface or Schoenflies hypothesis is needed for this separation step.
Both new modules pass focused checks with exit 0 and zero warnings.
`AuditS121SurfaceSeparation.lean` / `.log` audit the two obstruction declarations
and the separation headline; exit 0, only the standard three axioms. B.6's remaining
endpoint work is exactly two complementary components, their common frontier,
and two-sidedness for a connected surface.

### Moise 26.6: surface complement and two-sidedness delivered, 2026-09-16

`SurfaceComplement.lean` combines the proved parity obstruction with local
separation neighborhoods. For a connected finite closed combinatorial two-manifold
in a three-dimensional real normed space, it constructs exactly two complementary
connected components, proves their closures cover the ambient space and intersect
in the surface, and proves that each component has frontier equal to the surface.
It also proves `Topology.IsTwoSided` for the surface.

`EuclideanPolyhedralManifold.lean` identifies the Euclidean chart definition of a
polyhedral manifold with an embedded finite simplicial complex. The resulting
`PolyhedralSurfaceComplement.lean` endpoints apply directly to a connected
`IsPolyhedralManifold (n := 3) 2 S` in Euclidean three-space:
`IsPolyhedralManifold.exists_connectedComponentIn_pair_compl` and
`IsPolyhedralManifold.isTwoSided`. Its disconnection theorem only requires S to be
nonempty. No Schoenflies parameter or additional unproved input is present.

All three focused checks return exit 0 with zero warnings.
`AuditS122SurfaceComplement.lean` / `.log` audit all seven public declarations;
exit 0, only `propext`, `Classical.choice`, and `Quot.sound`. With no Lean process
running, `fresh.py` reports all sixteen changed modules fresh, zero stale or
missing artifacts, and zero forbidden-pattern hits. B.6 is complete; B.2 was
completed at the preceding disk-neighborhood milestone. The remaining active work
is P.4's endpoint and small-disk producers.

### Exact small vertex neighborhoods after simultaneous straightening, 2026-09-16

`PlanarJordan/ArcNeighborhood.lean` proves that a nondegenerate initial subarc is
a relative neighborhood of the endpoint in the entire arc.
`PlanarJordan/VertexNeighborhood.lean` uses this to shrink each radial fan to an
actual square with exact full-edge intersections. The endpoint
`Graph.IsDrawing.exists_homeomorph_radial_vertex_neighborhoods` constructs, for any
finite selection of vertices with at least two incident edges, pairwise disjoint
small squares and an ambient homeomorphism. Each transformed incident edge meets
its square in exactly one radial segment, all nonincident transformed edges avoid
the square, the only graph vertex in the square is its center, and the radial
boundary endpoints are distinct. The homeomorphism fixes every graph vertex and
the complement of the specified open set and obeys the continuous positive
pointwise error bound.

Both module checks return exit 0 with zero warnings. `AuditS123VertexNeighborhood`
audits all three new public declarations; exit 0, only the standard three axioms.
With no Lean process running, `fresh.py` reports 18 changed modules fresh, no stale
or missing artifacts, and no forbidden patterns. This removes later edge reentry
from the vertex-square interface. P.4 still needs arbitrary degree-one endpoints
and the compatible edge-disk frames and final graph assembly; it is not complete.

### Arbitrarily small PL disk neighborhoods of planar arcs, 2026-09-16

`PlanarJordan/ArcDiskNeighborhood.lean` constructs a polygonal Jordan curve J for
any planar arc A and any set neighborhood U of A, with A contained in inside J
and closure (inside J) contained in U. The construction refines a chain of small
square boundaries along the arc, uses the proved outer-chain theorem to control
all points outside the prescribed thickening, and obtains J as the boundary cycle
of the unbounded face of the finite two-connected graph.

`PiecewiseLinear/PolygonalJordan.lean` bridges the cyclic polygon presentations
and proves that every polygonal Jordan curve is a native PL one-sphere.
`PiecewiseLinear/PlanarArcNeighborhood.lean` consequently produces an actual PL
two-ball D with A contained in interior D and D contained in U. Its finite-family
version produces pairwise disjoint such disks for pairwise disjoint arcs, each
inside its independently prescribed neighborhood.

All three focused checks return exit 0 with zero warnings.
`AuditS124ArcNeighborhood.lean` / `.log` audit the four public declarations;
exit 0, only the standard three axioms. The native adaptation of the upstream
square-chain proof is recorded in `docs/third_party/PlanarArcNeighborhood.md`;
no vendored source was modified.

Moise printed pages 76-77 clarify the remaining degree-one producer: first apply
the no-endpoint construction to the locally finite graph obtained by deleting
the endpoints, then trace a complementary arc alongside the resulting locally
polygonal open edge with shrinking support toward its endpoint. The present
finite fan and disk results do not yet implement this infinite construction.
The edge-frame obligation also still includes the exact two boundary crossings
of the entire truncated edge; merely containing a compact arc is insufficient.
P.4 remains partial with these obligations explicit.

## Contracting families of supported homeomorphisms (2026-09-16)

`Homeomorph/UniformGluing.lean` proves
`Homeomorph.exists_gluing_of_pairwise_disjoint_of_tendstoUniformly` for an arbitrary
index type and an arbitrary uniform space: pairwise disjoint supported
homeomorphisms that converge uniformly to the identity along the cofinite filter
glue to a homeomorphism, with the specified map on every support and the identity
outside their union. The proof constructs both inverse maps and obtains their
continuity from the net of finite gluings; it does not assume local finiteness,
completeness, or countability. Metric corollaries preserve a prescribed positive
pointwise displacement bound and produce the uniform convergence from bounded
supports whose diameters tend to zero.

`PlanarJordan/PolygonalCrosscut.lean` now gives
`exists_homeomorph_polygonal_crosscuts_of_tendsto_diam` for arbitrary pairwise
disjoint contracting families of PL disks and actual crosscuts. The original
finite-family signature is preserved as a corollary. Both module checks exit 0
with zero warnings. AuditS125UniformGluing checks six public declarations; exit 0,
only `propext`, `Classical.choice`, and `Quot.sound`.

This supplies the infinite gluing operation used by Moise 10.7--10.8. It does not
produce the endpoint auxiliary arc or the edge frames: P.4 still needs those
geometric constructions and the final graph assembly.

## Several crosscuts in one disk (2026-09-16)

`PiecewiseLinear/PolygonalArcBall.lean` bridges every simple polygonal arc to the
native `IsPLBall 1` predicate by induction over the normalized polygonal chain.
`PlanarJordan/CrosscutFamily.lean` proves
`exists_homeomorph_polygonal_crosscuts_in_disk`: a finite family of crosscuts in
one PL disk, with intersections allowed on the disk boundary, can be made
simultaneously polygonal by an ambient homeomorphism fixing the disk interior's
complement. Its displacement is at most the disk diameter. Crosscut endpoints
need not be distinct across the family. The proof straightens one arc, cuts the
disk into two PL disks along that image, assigns each remaining arc to a side,
and applies strong induction; both later maps fix the separating arc.

Both focused checks exit 0 with zero warnings. AuditS126CrosscutFamily checks
three public declarations, exit 0, only the standard three axioms. This offers a
route for edge neighborhoods with finitely many boundary contacts, including
contacts that return immediately to the same side. The producer of that finite
crosscut decomposition from the original edge is still required; no P.4
completion is claimed.

## Straightening an arc with finite boundary contacts (2026-09-16)

`PlanarJordan/ArcStraightening.lean` proves
`exists_homeomorph_polygonal_arc_of_finite_frontier_inter`. For a planar arc with
both endpoints outside the interior of a PL disk, finitely many contacts with
the disk frontier, and a polyhedral part outside the disk interior, it constructs
an ambient homeomorphism making the whole arc polygonal, fixing the disk
interior's complement, and moving points by at most the disk diameter.

The proof produces the crosscuts from the arc parametrization: the last outside
parameter before an interior point and the first outside parameter after it
bound an interval lying in the disk interior. The finite set of boundary
parameters indexes all such intervals. Different resulting arcs can meet only
on the disk boundary, including immediate returns to the same side, so the
previous finite-family theorem applies. The unchanged exterior part and the
polygonalized interior pieces form a polyhedron; the whole image is still an
arc, hence polygonal. No exact-two-crossings assumption is used.

Focused check exit 0, zero warnings. AuditS127ArcStraightening checks the public
endpoint, exit 0, only the standard three axioms. The remaining P.4 geometry is
to choose small edge disks whose frontiers have finite intersection with the
already straightened endpoint germs, followed by the degree-one construction
and the full graph assembly.
