# 夜间计划（2026-09-15 → 09-16）：四条车道各 10 小时以上的自主任务

各车道在下一次汇报后按本文件自己的一节工作，直到早上。本文件放在整合分支；先合并整合分支再读。

## 0. 夜间规则

1. 每个里程碑做完：聚焦检查 exit=0 零 warning、命名空间感知的 `#print axioms` 审计（审计文件留在本工作树 `.lake\scratch`）、
   提交、推送，然后 `git fetch origin && git merge --no-ff origin/codex/moise-integration`（计划文件冲突两边都保留）。
2. 别的车道的东西只能通过合并整合分支取得；不复制、不 cherry-pick、不直接合并别的车道分支。别的车道的文件不改。
3. 需要别的车道尚未交付的定理时：按 §1 的接口写成**显式假设**（结构或参数，不是 sorry），继续做；交付后在下一次合并时消掉。
   不得为了绕开缺口弱化端点或把缺口做成结论型假设。
4. 单进程 Lean，不跑 `lake build`，不登记根聚合。每个里程碑在自己的 HANDOFF 文件末尾记一段：定理名、提交哈希、审计条数、确切缺口。
   夜里没有人回复；遇到 §1 之外的真实数学障碍，记录后跳到本节的下一个里程碑。
5. 早上的汇报：按里程碑列"done / partial / blocked + 确切义务"，给最后的提交哈希。

## 1. 跨车道接口（签名尽量照写；定义文件归括号里的车道）

- **I1（F → S）** `isSimplyEmbedded_of_isPLSphere_two (I : SchoenfliesInput) (hS : IsPLSphere 2 S) : IsSimplyEmbedded S`
  与 `exists_isPLBall_of_isPLSphere_two`（`SchoenfliesInput.lean`、S.4 端点文件，归 F）。S 用 `schoenflies_input` 实例化后消掉
  `hSchoenflies : ∀ S, IsPLSphere 2 S → IsSimplyEmbedded S`。F 交付前 S 继续带显式参数。
- **I2（S → E3）** 推离，一般环境：`E` 有限维赋范空间，`K` 有限带边组合 3-流形，`M := K.space`（`combinatorialChartedSpace K hK`，`VertexChart.lean`），
  `BdM := (boundaryComplex K).space` 的像。
  ```lean
  theorem exists_nonsingular_two_cell_of_boundary_disk (hK : IsCombinatorialManifoldWithBoundary 3 K)
      {D : Set E} {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D) (hD : D ⊆ frontier-of-K) :
      ∃ D₁ : SingularTwoCell K.space, D₁.IsNonsingular ∧
        Subtype.val '' Set.range D₁.boundary = r '' stdSimplexBoundary 2 ∧
        Subtype.val '' (D₁ '' D₁.domain) ∩ BdM = r '' stdSimplexBoundary 2
  ```
  （`LoopTheorem/BoundaryPush.lean` 已有 ℝ³ 版本 `exists_nonsingular_two_cell_in_boundary_ball`；一般版本由 S 写，允许显式
  `hSchoenflies`。）E3 交付前用同形显式假设 `hpush`。
- **I3（F → E3）** 奇异 2-胞腔的正规形式（Moise 书页 184 Lemma 2 前言），文件 `SingularNormalForm.lean`（归 F，F 夜间第一个里程碑就是写好定义并推送）：
  ```lean
  structure IsNormalSingularCell {M} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      (D : SingularTwoCell M) (BdM B' : Set M) : Prop where
    locallyInjective : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, Set.InjOn D U
    fiber_le_two : ∀ y, (D.domain ∩ D ⁻¹' {y}).encard ≤ 2
    boundary_image_subset : Set.range D.boundary ⊆ B'
    image_inter_boundary : D '' D.domain ∩ BdM = Set.range D.boundary
    doublePointSet_triangulated : ∃ (P : Set M) (T : PLPiece 3 M P)
        (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T.ambientDim))),
        G.faces.Finite ∧ G.faces ⊆ T.piece.complex.faces ∧ IsCombinatorialManifoldWithBoundary 1 G ∧
        T.piece.map '' G.space = doublePointSet D D.domain ∧
        T.piece.map '' (boundaryComplex G).space = doublePointSet D D.domain ∩ BdM
    crossing : ∀ y ∈ doublePointSet D D.domain, ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source) (e y)
  ```
  边界双点用 `HasPLBoundaryDoubleCrossingAt`（半空间图卡）作第二个析取项。F 的 F5.2 端点 = "任意小扰动后 `IsNormalSingularCell`"；
  E3 的 L.3 只从这个结构出发（多边形/折线分支、原像的环带结构由 E3 从一维组合流形与 crossing 推出）。
- **I4（H → E3）** `orientationCocycle`、`orientationCocycle_isCoboundary_iff`、`exists_orientationCocycle_of_not_isOrientable`
  （`HANDOFF_CODEX_H.md` §7.3）。E3 的 C.4 交付前用显式假设。
- **I5（H → E3）** 23.19′：`theorem bettiOne_pos_of_boundary_component_not_sphere (hK : IsCombinatorialManifoldWithBoundary 3 K)
  (hor : IsOrientable 3 K) (hconn : connected) (B : 边界分支) (hB : ¬ IsPLSphere 2 B) : 0 < bettiOne K`（`HandleCount.lean`，归 H）。

## 2. F 车道（`codex/moise-smoothing`）

顺序：S.4 收尾 → I3 定义 → F5.2 的分层通用位置路线（§17.1）。
- **F-M1** S.4 M2、M3（`HANDOFF_CODEX_F.md` §17.2）：Lemma 2–6 与拼装，端点 I1，计划行 S.4 改 done（条件于 `SchoenfliesInput`）。
- **F-M2** `SingularNormalForm.lean`：I3 的结构定义与基本 API（限制到子集、沿图卡搬运）。只定义与简单引理，先推送，E3 在等。
- **F-M3** `TwoFoldCrossing.lean`：两张曲面沿同一平面内两条不同折线折叠、各半片横截、折线互异 ⟹ `HasPLCrossingAt`
  （§15.1 第 3 条的显式线性构造：折叠平面上由 `ℓ₁ ↦ y` 轴、`ℓ₂ ↦ z` 轴决定，两侧各解 `e_x` 像的线性方程）。
- **F-M4** `ArrangementGeneralPosition.lean`：有限平面族 `𝒜` 的分层通用位置。顶点限制在所在层（平面交的仿射子空间）的相对内部，
  相对生产者：固定顶点集 + 可动顶点的通用位移，结论为 `HalfSpaceGeneralPosition.lean` 中单平面版本的推广
  （`exists_small_vertexMap_transverse_in_halfSpace` → `_in_arrangement`）。
- **F-M5** `RelativeNormalForm.lean` 重写：假设固定部分 `𝒜`-通用（§15 修订：不允许重合固定折边），结论：位移后凡涉及可动片的双点皆
  crossing（平/平、折/平、折/折共面用 F-M3），整体仍 `𝒜`-通用；半空间边界版本。
- **F-M6** `SingularNormalForm.lean` 端点：F6.2 的紧致片 `K_T`，星图卡族与各自仿射细分的公共细分 `K*`（图卡变换在 `K*` 单形上仿射），
  折痕 `Ξ` = `K*` 的 2-骨架；按图卡归纳（可动顶点 = 闭星整个映入该球的顶点；不变量：已处理区域 crossing 且 `Ξ`-分层通用），
  得 `exists_small_isNormalSingularCell`。做到哪算哪，缺口记 §16 风格。
估计：M1 4–6 小时，M2 1 小时，M3 2 小时，M4–M6 8 小时以上。

## 3. S 车道（`codex/moise-s`）

顺序：Problem 26.1 → I2 → 26.2 → 26.1/26.3 → 17.3/P.4。全部允许显式 `hSchoenflies`。
- **S-M1** Moise §23 书页 169 的正则邻域片：二次导出细分里的 `N(v)`、`N′(σ) = Cl(N(σ) − N(Bd σ))`；每片是 PL 3-球（`N(v)` 是锥；`N′(σ)`
  边界为 PL 2-球面且落在某 `Int |St v|`，用 23.9）；两片相交则交集是各自边界上的一个 2-胞腔。
- **S-M2** 盘的 shelling：`IsPLDiskDecomposition.exists_two_free_disk_cells`（一般 17.2，`FreeDiskCell.lean`）给三角形顺序，每个新三角形沿一条弧贴上；片按此顺序并入，
  用 23.11（`BallGluingManifold`）归纳：`N(D)` 是 PL 3-球，`N(D) ⊆ K.space`、`D ⊆ N(D)`。这就是 Problem 26.1。
- **S-M3** I2：`exists_isPLBall_inter_frontier_eq_of_subset` + `exists_nonsingular_two_cell_in_boundary_ball` 推广到 `K.space`（一般 `E`），
  按 I2 的签名写，推送后在 HANDOFF 里标"I2 已交付"。
- **S-M4** 26.2 领邻域（B.3）：Moise 书页 192 的归纳，每步的 3-胞腔邻域由 S-M2 给；产品结构由 P.2 边界延拓 + 锥延拓；
  端点 `exists_collar (hK) : ∃ ρ : PLH (Bd K.space × [0,1]) ↔ W, W ∈ 𝓝 Bd, ρ(P,0) = P`。
- **S-M5** B.1（26.1 两侧性，书页 191）与 B.4（26.3 双领：紧致两侧 `M² ⊆ Int M³`，`N − M²` 恰两分支，各用 26.2）。
- **S-M6** 17.3（避开指定真盘子复形的自由胞腔）；P.4 用 `External/Schoenflies` 的 `jordan_schoenflies_homeomorph`（`REUSE_AUDIT.md`）。
估计：M1–M2 5 小时，M3 1 小时，M4 4 小时，M5 3 小时，M6 余下。

## 4. E3 车道（`codex/moise-e3`）

顺序：一般化 → L.3 → L.4 骨架 → C.5/C.4 接线。
- **E3-M1** 把 `SphereCase.lean` 的条件端点与 `hpush` 从 ℝ³ 一般化到 I2 的设定（`M := K.space`，`combinatorialChartedSpace`，一般 `E`）：
  L.4 的归纳要在覆盖空间 `K̃₁`（C.3 的提升复形，不在 ℝ³ 里）上用 Lemma 1/2，所以 ℝ³ 版本不够。`hpush` 按 I2 写成显式假设。
- **E3-M2** L.3 = Moise 25 Lemma 2，条件于 I3。文件 `LoopTheorem/NormalCell.lean`、`LoopTheorem/CutAndPaste.lean`、`LoopTheorem/LemmaTwo.lean`：
  1. 从 `IsNormalSingularCell` 推出奇点集的分支结构：闭分支是多边形 `Γ_i ⊆ Int M`，非闭分支是折线 `A_j`，端点在 `B'`
     （一维带边组合流形的分支 = 多边形或折线）；每个 `Γ_i` 的原像 `D⁻¹(Γ_i)` 是 `Δ` 中一条多边形（`D|J` 二对一，Case 1）或两条不交多边形（Case 2）
     —— 二对一局部同胚限制到圆周是圆周的二重覆盖，用 C.1；每个 `A_j` 的原像是两条不交折线 `a₁b₁, a₂b₂`。
  2. 复杂度 = `m + n`；Case 1（柱形图与环带 `A` 的重定义，把 `D|A` 改成同胚 `A ↔ A′`）、Case 2（内侧多边形 `J₁` 界定 `Δ₁`，
     `Int J₂` 同胚映到 `Δ₁` 后推离）、Case 3/4（沿 `A_j` 切开得 `D₁, D₂`，书页 186–187 的字计算：`L` 是 `L₁, L₂` 共轭的乘积）。
     每个 Case 结论：复杂度更小的正规奇异 2-胞腔，且 `L(B') ∩ N' = ∅` 保持。归纳得非奇异 `D₁`。
  3. 需要的几何工具：环带 `A ⊆ Δ` 的正则邻域（F4.2）、P.2 的盘边界延拓、S 的 `SphericalDiskExtension`；
     推离用 I2。字计算用 L.1 的共轭类 API。
- **E3-M3** L.4 骨架（`LoopTheorem/LemmaThree.lean`）：正规系统复杂度归纳，显式假设 Lemma 1（E3-M1）、Lemma 2（E3-M2）、
  24.7/24.8（I4/I5 之后 C.4/C.5 提供）；提升用 C.1 `exists_unique_lift_of_isPLBall`、C.3 `exists_lift_simplicialComplex`、`relDerived`；
  "提升后复杂度不增，相等则 `g||D̃|` 同胚、`(g||D̃|)*` 满、与指标 2 矛盾"。然后 L.5（25.2）作为推论。
- **E3-M4** C.5：`Topology/Homology/Coefficients`（Bennett）+ `SimplicialBoolCocycle`：`H₁(K;ℤ) ↠ ℤ₂` ⟹ 非上边缘 ℤ₂ 上循环 ⟹ 连通二重覆盖；
  与 I5 接口对接。C.4：I4 对接 `DoubleCoverComplex`；覆盖可定向（Problem 24.11）需 H.2a 的 PL 不变性 + C.3 的流形性保持。
估计：M1 2 小时，M2 8 小时以上，M3 3 小时，M4 2 小时。

## 5. H 车道（`codex/moise-h`）

顺序按 `HANDOFF_CODEX_H.md` §7.3 与 §4：
- **H-M1** H.2b：`orientationCocycle` 与 I4 三条端点（§7.3）。
- **H-M2** H.6（`MayerVietorisSubcomplex.lean`，28.11）：导出邻域的形变收缩已由 L.1 的 `DerivedNeighborhoodRetraction.lean` 提供
  （整合分支），直接用；MV 用 `Reduced/MayerVietoris` 与 Bennett 的 `Reduced/MayerVietorisCoefficients`。
- **H-M3** H.4a（`SurfaceHomology.lean`）：闭曲面 `b₂`、`χ = 2 − b₁`（可定向）/`1 − b₁`；用 H.2a 的可定向性与 `eulerChar_geometricSpace_eq_faceEulerChar`。
- **H-M4** H.5（`HandleCount.lean`）：23.18′ `χ(Bd N) = 2χ(N)` 与 23.19′（I5）。`h(B)` 用 `bettiOne/2` 的定义（D3′）。
- **H-M5** 若有余力：`isOrientable` 的 24.11（覆盖可定向）所需的"二重覆盖复形的定向"引理，供 E3 的 C.4。
估计：M1 3 小时，M2 3 小时，M3 3 小时，M4 3 小时。

## 6. 2026-09-16 早上：夜间复核结果、接口修订与今日里程碑

### 6.0 复核（Opus 复核代理，独立重编 + 命名空间审计；整合分支 `aa6bf91e5`）

- H、E3、F 全部通过并并入：H 19/19 模块、392 项审计；E3 25/25、363 项；F 71/71、398 项；全部只含标准三公理，零 warning，
  无禁用模式，无重名。重述过陈述的 14 个声明的 84 个下游模块也已在整合树里重编，全部通过。
- **S 未并入**，两个原因：(1) 文件名碰撞 `SubcomplexNeighborhood.lean`（H 351 行 / S 51 行，内容不同）——处理办法已定：S 的版本改名
  `SubcomplexNhdsWithin.lean`，S 的三个 importer（`ManifoldNeighborhood`、`ManifoldRelativeTopology`、`TwoSidedNeighborhood`）同步改；
  (2) S 自己的源码不编译：`BoundaryDerivedNeighborhood.lean:151` 的裸名 `inter_subset_boundaryComplex_of_isPLBall` 在
  `theorem IsCombinatorialManifoldWithBoundary.…` 的体内被后加的 `IsCombinatorialManifoldWithBoundary.inter_subset_boundaryComplex_of_isPLBall`
  （`SubcomplexBallGluing.lean:161`，21:45）遮蔽；该模块 20:35 后没再检查过，它的 14 个下游（`Bicollar`、`BicollarManifold`、`BoundaryDiskNeighborhood`、
  `BoundaryDiskPush`、`CollarExtension`、`CollarNeighborhood`、`CollarRestriction`、`DiskCollar`、`DiskCollarComplement`、`DiskDerivedNeighborhood`、
  `FreeTriangleNeighborhood`、`LoopTheorem/CombinatorialBoundaryPush`、`SimplexDerivedNeighborhood`、`SurfaceCollar`）都是对着旧 olean "通过"的，不算数。
  另有两处 H×S 重名：`pair_centroid_mem_barycentricSubdivision`（S 的假设更弱、更一般）与
  `IsCombinatorialManifoldWithBoundary.exists_face_superset_card_eq`（陈述相同）。S 的 72 个未受影响模块的 292 项审计全部标准。
- **检查脚本已修**：`check-f.ps1` 现在先删目标 olean/ilean 再编译，失败的模块不再留下旧 olean 让下游"通过"。
- 计划文件的重复行已归并（提交 "Reconcile duplicated plan rows…"），C.4 取了 H 的更新文本。

### 6.1 接口修订（今日起生效）

- **环境（I2、I3 共用）**：`SingularTwoCell X` 要求无边界的 `ChartedSpace ℝ³ X`。带边流形 `K`（`IsCombinatorialManifoldWithBoundary 3 K`）
  的环境统一取 H 的 double：`X := (double 3 K).space`，图卡 `combinatorialChartedSpace (double 3 K) (isCombinatorialManifold_double_succ_succ K hK)`
  （`Orientation.lean`，`double n K : SimplicialComplex ℝ (E × E × ℝ)` 是 `gluedComplex (boundaryRelSubdivision n K) K` 沿边界的粘合）；
  `M := ` K 那一份拷贝的像（`Gluing.lean` 的 `glueEmbed₂`），`BdM := ` 其 `boundaryComplex` 的像。E3 的
  `exists_nonsingular_two_cell_of_sphere_boundary_map`（`X`、`ι : X → E`、集合在 `E` 中）已是这个形状。
  **I2 改为**：输入 `(K, hK)` 与 `D ⊆ (boundaryComplex K).space` 的参数化 `r`，输出 `SingularTwoCell (double 3 K).space`，
  非奇异、像在 `M` 内、`range boundary = 像(r '' ∂)`、`像 ∩ BdM = 像(r '' ∂)`。S 交付；E3 消费时先把 `X := (double 3 K).space` 代入。
  L.4 的覆盖空间：对 `double 3 K₁` 用 C.3 提升，得到 `K̃₁` 的无边界环境。
- **I1**（F 的 17.12）未交付：S 继续带显式 `hSchoenflies`。
- **I5** 未交付且路线修订：不再等奇异同调的顶维基本类。`h(B)` 用 `χ_face`：可定向闭曲面分支 `h(B) := (2 − χ_face B)/2`；
  23.18′/23.19′ 用 `faceEulerChar`、H.1、H-M2 的 MV 与 H-M4 已有的 Euler 层证 `bettiOne K ≥ h(Bd K)`；"B 不是 PL 2-球面 ⟹ h(B) ≥ 1"
  需要 **H.4b 球面识别**（今日 H 的第一里程碑）。E3 的 C.5、L.4 在 I5 到位前保持显式假设。

### 6.2 今日里程碑

**F**：F-M1 的 §19.56（相对层圆周删除）→ S.4 的 M2、M3 → 交付 I1（S 随后消参）。之后 F-M5（`IsVertexMapGeneralInArrangement` ⟹ 每个实际双点的
`IsArrangementGeneralFoldPair`）与 F-M6 的余面异侧定理 → `exists_small_isNormalSingularCell`。

**S**：先做三件修理再合并：(1) `BoundaryDerivedNeighborhood.lean:151` 改成全限定名 `_root_.DifferentialGeometry.Topology.PiecewiseLinear.inter_subset_boundaryComplex_of_isPLBall`
（或用 `hK.inter_subset_boundaryComplex_of_isPLBall` 显式选用新版本），重检它和上面 14 个下游；(2) 把 `SubcomplexNeighborhood.lean` 改名为
`SubcomplexNhdsWithin.lean` 并改三个 importer；(3) 重名：删掉自己的 `exists_face_superset_card_eq`（与 H 的 `ManifoldConnectivity.lean` 版本同陈述，改为 import 它），
把自己的 `pair_centroid_mem_barycentricSubdivision` 改名 `pair_centroid_mem_barycentricSubdivision_of_subset_or_subset`（保留更一般的版本，H 的不动）。
然后合并整合分支（`aa6bf91e5`）、全量重检本车道昨夜改过的模块（脚本已改，旧 olean 不再掩盖失败）、审计、推送并汇报。
之后 S-M3 按 6.1 的 I2 形状交付并在 HANDOFF 标"I2 已交付（double 环境）"；再 S-M6 的 P.4（`External/Schoenflies` 路线）；再 S.6（30.5，显式 `hSchoenflies`）。

**E3**：E3-M1 按 6.1 把 `X := (double 3 K).space` 代入并与 S 的 I2 对接（I2 未到前显式）；E3-M2 剩余：两盘沿边界 1-球贴合后
frontier = 两侧补弧之并的表示引理 → Case 3/4 的 `L₁` 识别与复杂度下降 → Case 1/2（环带重定义、内盘替换与推离）→ Lemma 2 端点
（条件于 I3）。之后 L.4 骨架接 Lemma 2；C.5 等 I5。

**H**：H.4b 球面识别（`IsCombinatorialManifold 2 B` 连通闭、`faceEulerChar B = 2` ⟹ `IsPLSphere 2 B.space`；路线：1-骨架生成树 `T` 与对偶生成树 `T*`，
Euler 数迫使每条边恰属其一，沿 `T*` 粘合的三角形是一个 PL 盘，`B` 是该盘沿树 `T` 折叠边界的商，按树边归纳折叠得球面）；
然后 23.19′ = I5（`bettiOne_pos_of_boundary_component_not_sphere`，按 6.1 用 `χ_face`）；再回 H-M3 的顶维类（可推迟）。

## 7. 2026-09-16 中午：`NormalSystem` 的表示缺陷（E3 发现，属实）与下一批里程碑

### 7.1 `NormalSystem` 加一个字段（批准；文件归 E3）

E3 的诊断成立，是 §1 的 L.1 设计（本方写的）欠规定。现状只有像集层面的联系：

```lean
  loop_space : loopComplex.space = simplicialMap sourceComplex vertexMap '' frontier sourceComplex.space
  boundaryLoop : freeLoop (normalSystemBoundaryNeighborhoodSpace …)
  boundaryLoop_range : Set.range (fun θ => (boundaryLoop θ : E)) = loopComplex.space
```

`boundaryLoop` 只被要求"像集等于边界多边形"，因此它可以绕两圈、反向或任意重参数化，而 Moise 书页 186–187 的 Case 3/4
字计算要求 `L = Bd D`：把 `Δ` 的边界恰好走一圈后用 `D` 推下去。补一个字段把它钉死（`loopCircle` 见
`Topology/LoopSpace/Basic.lean`，`freeLoop Q = C(loopCircle, Q)`）：

```lean
  boundaryParam : loopCircle ≃ₜ frontier sourceComplex.space
  boundaryLoop_eq : ∀ θ, (boundaryLoop θ : E) =
    simplicialMap sourceComplex vertexMap (boundaryParam θ : EuclideanSpace ℝ (Fin 2))
```

`boundaryLoop_range` 随即成为推论（保留为定理，签名不变，下游不受影响）。只有**生产者**需要补这两项：
`frontier sourceComplex.space` 是 PL 1-球面（`IsPLBall.isPLSphere_frontier`），与 `loopCircle`（= `UnitAddCircle`）的同胚
由你 §16 的 PL 圆分类加 `BoundaryGeneration.lean` 里已经做过的"自由环满射到指定多边形"的构造给出；
若两处给的是到标准圆的 PL 同胚，再与 `loopCircle` 的标准同胚复合。改完重检 `SingularCell.lean` 及其下游，审计后推送，并在 §4 表里更新 L.1 行。

### 7.2 割贴后的正规性是 L 车道自己的义务，不是 I3 的缺口

I3（F 的 `IsNormalSingularCell`）是**定义加基本 API**；"沿 `A_j` 切开后两片仍正规、奇点图重建、复杂度严格下降"
是 Lemma 2 证明本身的内容，不要等 F。可用的材料与路线：

- 局部单射与纤维 ≤ 2 的限制：F 已给 `IsNormalSingularCell.locallyInjective_restrict`、`fiber_le_two_restrict`。
- 奇点图重建：切开后 `doublePointSet (D|Δ₁) Δ₁ = doublePointSet D Δ \ (被切掉的分支)`，因为两片的原像对被分到不同片；
  一维带边组合流形性对"去掉若干整个连通分支"的子复形是封闭的（`IsCombinatorialManifoldWithBoundary 1` 对并集分支的限制）。
- crossing 条款逐点保持：`HasPLDoubleCrossingAt` 的两个不交源邻域在切开后仍落在同一片内（切缝是原像弧，
  与双点的两个源邻域可取到不交）。
- 复杂度严格下降：切掉的分支 `A_j` 至少消掉一对碰撞顶点，用 `complexity` 的定义（`vertexCollisionPairs` 的基数）。

### 7.3 里程碑

**E3**：7.1 的字段 → 7.2 的割贴正规性四条 → Case 3/4 的 `L₁` 字计算与复杂度下降 → Case 1/2（盘内 PL 圆的环带邻域用 F4.2，
柱形图用 Moise 书页 185 Figure 25.2 的显式模型；Case 2 的内盘替换用 S 的 I2 推离）→ Lemma 2 端点（条件于 I3）。
L.4 仍保持显式参数，直到 Lemma 2 为真定理。

**S**：I2 已交付，谢谢。S.6 确实被 I.4（30.4）挡住，而 I.4 又要 B.5（26.4 扩展环定理，等 L 车道），所以暂时不碰。
改做 §26 里不依赖环定理的三项，它们是 §32/§33 的直接输入：
- **B.6 = Moise 26.6**（书页 194）：ℝ³ 中紧致连通多面体 2-流形 `M²` 两侧，`ℝ³ − M²` 恰两个连通分支 `I`、`E`，
  公共 frontier 为 `M²`。路线正是 F5.1：取从无界分支 `P` 到 `Q` 的折线 `B`，`B ∩ M²` 是单点且落在 `B` 的边内部与
  `M²` 的 2-单形内部；反设 `Q` 也在无界分支，取 `B ∩ M² = ∅` 的折线 `B′`，`B ∪ B′` 是单连通的，故存在 PL 映射
  `ρ : Δ → ℝ³`（`Δ` 为 2-胞腔），`ρ|Bd Δ` 同胚到 `B ∪ B′`；用 F 的
  `exists_small_simplicialMap_preimage_manifold_relative`（`GeneralPosition.lean`：任意子复形相对细分、原像是
  一维带边组合流形、源边界点度数 1、源内部点度数 2）把 `G := ρ⁻¹(ρ(Δ) ∩ M²)` 化为一维带边组合流形，
  `G ∩ Bd Δ` 恰一点 `R`；一维紧致带边组合流形的边界点个数是偶数（这条要先证，`boundaryComplex` 的基数模 2），
  与"恰一个"矛盾。再由正则邻域 `N`：`N − M²` 至多两个连通分支（用 S-M5 的双领 26.3），故恰两个。
- **B.2 = Problem 26.3**（书页 196）：`d ⊆ Bd N`、`N ⊆ Int M³` ⟹ `d` 在 `M³` 中的每个邻域含两侧的多面体 3-胞腔
  `C₁ ⊆ N`、`C₂ ⊆ Cl(M³ − N)`，`d = C₁ ∩ Bd N = C₂ ∩ Bd N`。Problem 26.1、26.2 已由 S-M2、S-M4 交付，本条用它们两侧各取一次。
- **P.4 余项**：度 1 端点与小盘框架。
三项都允许显式 `hSchoenflies`。`B.8`（26.8 可定向）先不做：它要 3-球面的顶维同调生成元，是 H 的开口。

**F**：不变（§6.2）。**H**：不变（H.4b 球面识别 → I5）。

## 8. 2026-09-16 上午：验证协议（简化）与共享 olean 的使用规则

### 8.1 两档验证

- **平时**：`python .lake/scratch/tools/fresh.py`。不跑 Lean，一秒。做两件事：改动/未跟踪 `.lean` 的禁用模式扫描；
  每个这样的文件在共享库里的 olean 是否比源码新。后者之所以有意义，是因为 `check-f.ps1` 现在**编译前先删目标 olean/ilean**，
  所以"olean 存在且更新"等价于"这份源码编译成功过"。
- **重量级**（聚焦检查 + 命名空间感知的 `#print axioms`）只在三种场合做：宣布里程碑 done；端点模块并入整合分支前；
  某个声明的陈述被重述后的下游。

### 8.2 `fresh.py` 的两个前提（脚本会自己打印）

1. 本工作树没有 `lean.exe` 在跑。有人在编译时 olean 正被删了重建，读数无效。
2. git 合并/检出会在同一瞬间重写一批文件的 mtime，内容未必变。一组 stale 条目共享同一时间戳就是合并造成的；
   这时按 `git log -1 --stat` 只重检合并真正改过的文件，不要全量重检。

### 8.3 共享 olean 库的使用规则（今早发生过一次实际污染）

共享库 `E:\differential-geometry-dev\.lake\build\lib\lean` 是所有工作树共用的**唯一** olean 存储。一次事故：
整合验证正在复核 E3 的分支时，E3 车道自己用**尚未推送**的源码重写了 `SingularCell.olean` 与 `CutAndPaste.olean`，
验证代理因此先编译失败、随后又可能对着别人的源码"通过"。规则：

- **同一时刻只有一个工作树可以编译同一个模块。** 我要复核某条车道的合并时，会先通知该车道暂停 Lean；收到"恢复"再继续。
- 车道之间文件不重叠，所以平时并行编译没问题；冲突只发生在"车道与整合验证同时动同一批文件"。
- 整合工作树写共享库，因此共享库的内容始终是最近一次被验证过的状态。

（试过给每条车道一个私有 olean 目录并前置到 `LEAN_PATH`：不行。Lean 会认定第一个含 `DifferentialGeometry`
目录的搜索根，然后不再回退到共享库，于是所有未私有编译过的依赖都报 "object file … does not exist"。
要走这条路必须先把共享库的 9157 个 olean 全部硬链接进私有目录，代价与收益不成比例，已放弃。）

## 9. 2026-09-16 下午：I5 已交付；H 车道转 §21–§22 与 §28.20

### 9.1 I5 交付

`bettiOne_pos_of_boundary_component_not_sphere`（`HandleCount.lean`）与支撑层 `BoundaryHomology.lean` 已并入整合分支。
E3 的 C.5 解除阻塞：`H₁(K;ℤ) ↠ ℤ₂` 的输入现在有了，接 C.2 的 `SimplicialBoolCocycle` 即可。

### 9.2 H 车道的下一批（按被消费的广度排序）

- **H-M6 = 22.11**：单连通的闭多面体 2-流形是 PL 2-球面。几乎是 H.4b 的推论：单连通 ⟹ `bettiOne = 0` ⟹
  `faceEulerChar = 2`（用 `eulerChar_eq_one_sub_bettiOne_add_bettiTwo` 与 `faceEulerChar_le_two` 的两侧夹逼，
  `b₂` 的上界由闭曲面顶维消失给出）⟹ `isPLSphere_two_of_faceEulerChar_eq_two`。消费者：§30.6、§32。
- **H-M7 = H.3（§21 的 χ 运算）+ T.9（28.20）**：开胞腔复形的 χ 在运算 α–δ 下不变、21.6–21.8、21.10–21.11；
  然后定义沿 2-胞腔 `Δ` 的分裂运算并证 `χ(M₁²) = χ(M²) + 2`。消费者最广：§30.3–30.4、§30.6、§32、§33 L3–L7、§34 Op.1。
- **H-M8 = 22.5–22.7**：紧致带边曲面 `χ = 2 − (2h + m)`，以及 `p¹` 与 `χ` 的关系。`h(B)` 已按 D3′ 用 `(2 − χ)/2`，
  本条把它与实际手柄数对齐。消费者：§23.18–19 的加强、§33 L7/L11/L12。
- **H-M9 = B.8（26.8）**：ℝ³ 中紧致连通多面体 2-流形可定向。**不要走计划行里写的 H₃ ≅ ℤ 路线**（顶维基本类是你后推的项）。
  改用 S 车道刚交付的 26.6：`IsPolyhedralManifold.isTwoSided` 与 `exists_connectedComponentIn_pair_compl` 给出补集恰两个分支
  `I`、`E`，于是每个顶维面的两侧可以全局一致地区分为"朝 `I`"与"朝 `E`"；把这个法向选择与 ℝ³ 的标准定向组合，
  直接构造 `CoherentOrientation`，或等价地证明 H.2b 的定向上循环是上边缘。消费者：§33 L11。

顺序 H-M6 → H-M7 → H-M8 → H-M9。B.8 需要先合并含 S 的 26.6 的整合分支。其余规则同 §0 与 §8。

## 10. 2026-09-16 下午：S 车道转 §24 后半（实心环面）与 §30 前半

B.6、B.2、P.4（有限图范围）均已交付且不带 `hSchoenflies`。S 的既有车道行到此基本清空，S.6 仍被 30.4 挡住。
下面三项都不在环定理之后，可以立刻做，且解锁面很大。

### 10.1 C.6 = 24.9–24.10（书页 179，PDF 189）：组合实心环面

定义层照书：`S = ⋃_{i=1}^n C_i³`，各 `C_i³` 是组合 3-胞腔，`C_i³ ∩ C_j³ ≠ ∅` 当且仅当 `i`、`j` 模 `n` 相邻，
此时交集是各自边界中的一个 2-胞腔；这样的 `S` 叫 CST。端点：

- 24.9：`S` 是 CST 当且仅当存在 PL 满射 `φ : σ² × [0,1] ↠ S`，`σ² × {0}` 与 `σ² × {1}` 映到同一个 2-胞腔，
  其余地方是同胚。这样的 `φ` 叫柱形图。
- 24.10：任意两个 CST 组合等价。

消费者：§28、§30.7、§31。这一层是纯组合与粘合，材料你都有（S-M1 的片、`BallGluingManifold` 的 23.11、P.2 的边界延拓）。

### 10.2 C.7 = 24.11–24.12（书页 179–180）

- 24.11：可定向三角剖分 3-流形中，多边形 `J` 在使 `J` 成为子复形的细分里的正则邻域是 CST。
  证明就是把 `J` 的顶点与边的正则邻域 `N(v_i)`、`N′(e_i) = Cl(N(e_i) − N(Bd e_i))` 按 `J` 上的循环顺序排成
  `C₁³, …, C₂ₙ³`，正是你在 S-M1 为 Problem 26.1 造的那批片；再由 23.17（可定向流形的子流形可定向）排除"full Klein bottle"。
  若 H 车道尚未交付 23.17，就把它写成显式假设 `hsub : ∀ K K', IsOrientable → 子复形 → IsOrientable`，交付后消参。
- 24.12：`J` 在 `M` 中可缩时，正则邻域是 CST，`M` 不必可定向。书用 Theorem 7 的二重覆盖（E3 的 C.4）；
  C.4 未到之前把二重覆盖写成显式假设。

消费者：§28.19、§31、§34 L1。

### 10.3 I.1、I.2 = 30.1–30.2

- I.1（30.1）：`X` 单连通、局部连通、其连通开集道路连通；闭集 `C ∪ D` 分离 `H` 与 `K` ⟹ `C` 或 `D` 分离。
  你新造的 `SurfaceSeparation.lean`、`SurfaceComplement.lean` 里的分离词汇直接复用；"单连通 ⟹ 圆周上的映射延拓到圆盘"
  用 Mathlib 的 `SimplyConnectedSpace` 加你 P.5 的平面材料。
- I.2（30.2）：闭集有有限个连通分支且分离 ⟹ 某个分支分离。对分支数归纳，用 I.1。

消费者：§30.4、§30.6、§33 L5/L6/L10、§32 Step 2。这是球壳定理 30.4 的前两块，30.4 本身仍要等 26.4。

### 10.4 顺序与规则

C.6 → C.7 → I.1 → I.2；有余力再做 B.7（26.7，`§32 Type 2` 的输入，路线是 2.7 的三维类比）。
显式假设只允许用于别的车道未交付的定理（23.17、C.4、26.4），交付后在下一次合并时消掉。其余规则同 §0 与 §8。

## 11. 2026-09-16 傍晚：L₂ 的表示层缺口属实；补"沿分支切开并分离"的生产者

### 11.1 E3 的判断成立（书上证据）

`branchCarrier c ⊆ doublePointSet G G.domain` 这条证明说明：只在源侧交叉重贴，被选分支仍留在奇点集里，
所以那不可能是 Moise 的降复杂度 `L₂`。把端点改名为 `exists_cross_reglued_cell_of_boundaryBranch` 是对的。

书上的证据在 Figure 25.4（书页 186）与 Figure 25.6（书页 187）：`|D|` 画成一个"8 字形"，`A_j` 是中间那段竖直线段，
四条路径 `σ, υ`（上）与 `φ, τ`（下）交于 `A_j` 与基点 `P₀`。"cut `|D|` apart at `A_j`"就是把这个 8 字在 `A_j` 处**打开**，
得到一个小环 `L₁ = συ⁻¹` 与一个大环 `L₂ = σφυτ`（Case 4 是 `L₁ = συ`、`L₂ = στ⁻¹υφ⁻¹`）。
打开之后 `A_j` 不再是任何一张新胞腔的奇点分支，这正是复杂度下降的来源。所以这个运算必须真正把两张片分开，
而不是把源盘重新粘一遍。参照 §30 定理 3 与 28.20 前的讨论：书里的"split apart at Δ"同样是用正则邻域在环境里真正分开。

### 11.2 缺的生产者：沿一条紧致分支把两张片分离

```lean
theorem exists_separated_along_branch (hD : IsNormalSingularCell D BdM B')
    (c : 触边分支) (W : Set M) (hW : W ∈ 𝓝ˢ (branchCarrier c)) :
    ∃ D' : (从 Δ 沿 c 的两条原像弧切开后的源) → M,
      (在 W 外与 D 逐点相等) ∧ IsNormalSingularCell D' BdM B' ∧
      doublePointSet D' = doublePointSet D \ branchCarrier c ∧
      (其余分支及其 crossing、纤维 ≤ 2、局部单射、边界像条款全部保持)
```

架构（局部到整体，材料都在整合分支上）：

1. **局部模型**：分支内部的点由 `HasPLDoubleCrossingAt` 给出两个不交源邻域、到像的 PL 同胚与环境 crossing 模型
   （两张横截平面）；端点由 `HasPLBoundaryDoubleCrossingAt` 的半空间模型给出。在这两个模型里把一张片沿
   crossing 的横截方向推开是显式线性构造，支撑落在给定的小邻域内。
2. **沿分支globalize**：`branchCarrier c` 是紧致一维带边组合流形，取有限个上述图卡覆盖它，按 §16/§17 已经证过的
   PL 圆/区间分类给出的次序逐段推开；相邻图卡的重叠区用同一方向的推移，靠线性插值拼接。
3. **粘回全局**：用 F 车道 `Topology/Pasting.lean` 与 `SingularPasting.lean` 的既有接口
   （`exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective`、`exists_isPLBall_patches_at_doublePoint_within`、
   `exists_isPLBall_postcomp_neighborhood_at_doublePoint_in_manifold`）。它们正是为"在一个邻域内改，邻域外精确不变，
   并保住纤维计数"设计的；本条要做的是把单点版本沿紧致分支串起来。
4. **源盘的切开**：切开后的源就是 `Δ` 沿两条原像弧切开再按 Figure 25.3/25.5 的方式重连；你已有三盘分解与
   `exists_isPLHomeomorphOn_branch_sheets` 的 `g`，把重连写成 `IsGlueIso` 即可。

归属：这条归 E3（分支结构、crossing 数据、三盘分解都在你手里），允许直接消费 F 的 pasting 接口。
若第 2 步沿分支的串接在现有接口下闭合不了，写清确切缺口后汇报；届时我把它移交 F 车道，在 17.12 之后与 F5.2 的
图卡归纳一起做——那两件事的技术内容是同一类。

### 11.3 之后

拿到 `exists_separated_along_branch` 后：Case 3/4 的 `D₁`、`D₂` 与 `L₁`、`L₂` 的字等式 → 复杂度严格下降
（你已有的跨复形比较层）→ Case 1/2（盘内 PL 圆的环带邻域与柱形图；Case 2 的内盘替换用 S 的 I2）→ Lemma 2 端点。
