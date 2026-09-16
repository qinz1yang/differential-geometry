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
