# 到 36.1 的条件骨架（2026-09-16）

Phase 3 的终点已经归约成一句话：`plApproximationManifold_three_of_moise352 : Moise352 3 → PLApproximationManifold 3`
（`Endgame.lean`，已证，仅标准三公理）。所以整个工程只差 `Moise352`。

但 `Moise352` 是一个巨大的洞。本文件把这个洞拆成书上关键路径的一条具名链：每个结点是 Moise 书里的一条定理，
在 `MoiseChain.lean` 里写成显式 `Prop`，箭头是书里真正做的归约。目标是让最终陈述读作
"三维 PL 逼近定理成立，只要下面这些经典命题成立"，每条都带页码，任何人都可以独立地去消掉其中一条。

## 主链（自下而上）

| 结点 | 书中定理（页） | Lean `Prop` | 现状 |
|---|---|---|---|
| 25.1 | Stallings 形式的环定理（183） | `Moise251` ✔已陈述 | 开。L1 已有条件版（E3 `SphereCase`）；L2 卡在"沿分支切开并分离"（`NIGHT_PLAN` §11）；L3 未开始 |
| 25.2 | 环定理第一形式（183） | `Moise252` ✔已陈述 | 开。**箭头便宜**：书上从 25.1 推出只用"把 `Int|D₁|` 推离 `Bd M`"，即 S 已交付的 I2 |
| 26.4 | 扩展环定理（193） | `Moise264` ✔已修正陈述 | 开。结论已补盘边界包含映射在曲面中非零伦；用 25.2 与 26.3 双领（S 已交付） |
| 30.4 | 球壳定理（216） | `Moise304` ✔已陈述 | 开。用 26.4、23.8、26.1（S 已证）、28.19、28.20（H 已证）、30.3 |
| 30.5 | 嵌套拓扑 3-胞腔（216） | `Moise305` 已陈述；`moise305_tame_of_moise304` 已证 | §34 的 tame 条件箭头及双领口生产者已合入；30.4 仍是显式未证输入。一般 wild 版仍开，旧 10k–18k 前置不适用于 tame 路线 |
| 30.6 | 环壳定理（216–217） | `Moise306` ✔已陈述 | 开。用 30.7、van Kampen、§22 |
| 30.7 | 拓扑实心环面之间有 CST（217） | `Moise307` ✔已陈述 | 开。用 30.6、28.1、24.9–24.12（S 正在做） |
| 30.8 | 脊生成 `π(S)`（218） | `Moise308` | 开。用 §31 |
| 31.1–31.2 | 典范实心环面构形 | `Moise311` | 开 |
| 32.1–32.4 | 管、对偶胞腔、伪胞腔 | `Moise321` | 开。定义层可先建（F4.3 partial） |
| 33.1 | 线性图的正则邻域逼近 | `Moise331` ✔已陈述 | 开 |
| 34.1 | PL 球上的逼近 | `Moise341` ✔已陈述 | 开 |
| 35.1 | 流形中 1 维多面体的正则邻域逼近 | `Moise351` ✔已陈述 | 开 |
| 35.2 | 局部有限多面体 3-流形上的逼近 | `Moise352` ✔已陈述 | 开；`Transition361.lean` 已定义 |
| 36.1 | 开集上的逼近 | — | **已证**，条件于 `Moise352`（`Transition361.lean`、`Endgame.lean`） |

## 侧向输入（不在主链上，但被多个结点消费）

- §17：17.12 PL Schoenflies —— F 车道进行中；17.2–17.11 已交付。`SchoenfliesInput` 是它的接口结构。
- §22：22.5–22.7（条件于显式 `IsRefinement` 见证）、22.11 已证；22.8–22.10 分类仍开。
- §23：23.9–23.11（条件于 17.12）、23.17（`IsOrientable.of_le`）、23.18′、23.19′ 已证。
- §24：24.1–24.6 已证；24.8 = C.5 已证；24.7 = C.4 partial；24.9–24.12 partial（S）。
- §26：26.1、26.2、26.3、26.6 已证（S）；26.7、26.8 —— 26.8 已证（H）。
- §28：28.11、28.20 已证（H）；28.1–28.10、28.19 开。

## 便宜的箭头（一条车道优先做这些）

1. `Moise252` ← `Moise251`（书页 183 末段）：把 25.1 用在 `N = ⟨1⟩`，再用 I2 把 `Int |D₁|` 推离 `Bd M`。
2. `Moise305` ← `Moise304`（书页 216）：取 `B` 分离 `Bd C₁` 与 `Bd C₂`，`C` 取 `ℝ³ − B` 中含 `C₁` 的分支的闭包。
3. `Moise264` ← `Moise252` + 26.3（书页 193）：四种情形的归纳，材料都在树上。

## 规矩

- 每个 `Prop` 的陈述一旦被别的定理消费就冻结；改动必须回写本表与 `PHASE3_APPROXIMATION_PLAN.md` §4。
- 陈述必须是书上的定理本身，不得为了好证而弱化，也不得把结论塞进假设。
- 箭头证明只能用已证的东西与本表里明确列出的 `Prop`，不得引入新的未证假设。


## 已在 `MoiseChain.lean` 里陈述并通过编译的结点（2026-09-16 夜）

`Moise251`、`Moise252`、`Moise264`、`Moise304`、`Moise305`、`Moise306`、`Moise307`、`Moise331`、`Moise341`、`Moise351`，
以及它们需要的词汇 `IsNullHomotopic`、`IsTopologicalCell`、`IsSphericalShell`、`IsPLTorus`、`IsToroidalShell`、
`IsTopologicalSolidTorus`、`HasCylindricalDiagram`。`Moise352` 在 `Transition361.lean`，36.1 与终局端点已证。

尚未陈述：30.8（脊生成 `π(S)`，需要"脊"与"生成"的表述）、§31 的典范实心环面构形、§32 的管与伪胞腔。
这三块是书里最细的部分，留待写的时候逐条对照 Figure 31.x/32.x，不要草率定型。

`HasCylindricalDiagram` 用 S 车道的 `IsCylindricalDiagram` 表述，这是 Moise 24.9 给出的 CST 等价刻画之一侧；
书里 CST 的原始定义是有限个 3-胞腔的循环链，两者的等价就是计划行 C.6（partial）。下游一律用
`HasCylindricalDiagram`，等 C.6 闭合后可自由互换。

## §31 的实际难度比表里写的低（2026-09-16 夜，读书页 220–221 后修正）

§31"典范构形"是一个**定义**加四条几乎直接的推论，不是新的硬定理：

- 定义（书页 220）：在 `xy` 平面右半平面取点 `P_j`、线段 `P_jP_{j+1}`、2-胞腔 `D_j`，满足
  `P_jP_{j+1} ⊆ Int D_j`、`D_j ∩ D_{j+1}` 是 2-胞腔、`D_i ∩ D_{i+2} = ∅`；绕 `y` 轴旋转得圆 `J_j`、环带 `A_j`、
  实心环面 `S_j`；`N = ⋃_{j=i}^{i+2} S_j`，`h : N ↔ N' ⊆ ℝ³` 同胚；再取多面体实心环面 `S''_j`，
  `A'_j ⊆ Int S''_j ⊆ S''_j ⊆ Int S'_j`，且 `T''_j` 两两一般位置、`T''_j ∩ T''_{j+1}` 是有限个不交多边形且横截。
- 定理 1（`S''_j` 存在）："follows by repeated applications of Theorem 30.7"。
- 定理 2（`J'_j`、`J'_{j+1}` 携带 `π(S''_j)` 的生成元）："follows by repeated applications of Theorem 30.8"。
- 定理 3（`S''_i ∩ S''_{i+2} = ∅`）：三行，由 `D_i ∩ D_{i+2} = ∅`。
- 定理 4：用 30.8 的路径与一维闭链的同调计算。

所以 §31 的代价主要在**写下定义**和 30.7/30.8 的重复应用，不在新数学。计划里把 §31 与 §32 并列为"未开始的硬块"
是高估了；真正硬的是 §32（管与伪胞腔）、§33、§34。

## §32 确认是最硬的一块（书页 223–225）

定义层：1 维复形 `K` 在 PL 3-流形 `M` 中的正则邻域 `N`，每条边 `σ¹` 中点处的正交 2-胞腔 `D`（**分裂盘**）把 `N` 切成
含单个顶点的多面体 3-胞腔 `C_v`（**对偶胞腔**）；`h : N ↔ N' ⊆ M'` 同胚（不必 PL），`N'` 叫**管**，像叫 `N'` 的分裂盘与对偶胞腔。
**伪胞腔** `E = U ∪ J`：`U` 是开 2-胞腔，`J` 是 1-球面，`U ∩ J = ∅`，`Ū = U ∪ J`，某点 `P ∈ U` 使 `U − P` 是多面体。
书里明说：这里构造出的伪胞腔一般**连边界处都不局部连通**。

定理 32.1 的证明把 `Int D' − {P'}` 分解成双向无穷的同心环带列 `…A₋₁, A₀, A₁…`，对每三个相继的 `S_i, S_{i+1}, S_{i+2}`
套用 §31 的典范构形，再做 Lemma 1–3 与若干步分裂。**这是全书这一段里唯一需要无穷构造的地方**，也是 §32 真正的难点。

因此顺序是 30.7 / 30.8 → §31（便宜）→ §32（硬）→ §33 → §34。把 §31 从"硬块"里拿掉之后，
剩下的硬块是 §32、§33、§34 三章加上环定理 §25。

## §33 的两个被漏掉的前置（书页 236–238，重要）

读 §33 定理 1 的证明（Lemma 11–13 与收尾）发现两条计划里没有明确列出的依赖：

1. **22.9（紧致曲面分类：可定向性加 χ 决定同胚型）是必需的，不是可选的。** Lemma 11 证 `Bd X ≅ Bd N` 的方式是：
   由 Lemma 10 得 `π(Bd X) ≅ π(Bd N)`，于是 `p¹` 相等；再由 26.8（H 已证）两者可定向；**然后直接引用 22.9**。
   Lemma 12（每个 `A'_v` 是圆盘或带洞圆盘）也靠 `p¹` 的计数。所以 H 车道后推的 22.8–22.10 必须做，
   否则 §33 走不通。计划里 H.4 的"22.8–22.10 分类"要从"备选"升级为主链前置。
2. **3-胞腔之间的边界 PLH 延拓（书里写作"Theorem 18.2"）是收尾步骤。** 证明最后一句是"By repeated applications of
   Theorem 18.2, `f` can be extended to all of `N`"，也就是把 `Bd N ↔ Bd X` 延拓到每个对偶胞腔上。
   这正是计划行 S.7；它是 P.2（2-胞腔版本，S 已证）的三维类比。同一段证明里还显式引用了 5.4（2-胞腔版本）。

另外 Lemma 13 的构造（把 `Bd N` 的每块 `A_v` 与 `A'_v` 对应起来）反复使用 5.4，并用"否则 `Bd X` 会含 Möbius 带"
来定顺序——这一步又要 26.8 的可定向性。

结论：主链上 §33 之前必须补两项：**22.9** 与 **S.7（3-胞腔边界延拓）**。两者都不在原来的"便宜箭头"名单里。

## 更正：30.5 ← 30.4 不是便宜箭头（2026-09-16 夜，尝试后）

`SphereComplement.lean` 的 `IsPLSphere.exists_isPLBall_complement_components` 已经把书上那句
"令 `C` 为 `ℝ³ − B` 中含 `C₁` 的分支的闭包，则 `C` 是多面体 3-胞腔"变成了真定理。但把箭头补完还差一步，
而这一步不在树里：

**缺的输入**：拓扑 3-胞腔 `C₂ ⊆ ℝ³` 的补集连通（等价地：ℝ³ 中拓扑 2-球面的 Jordan–Brouwer 分离，
外侧分支唯一）。

为什么需要：设 `B` 是 30.4 给出的分离球面，`D` 是它界定的 PL 3-球。要判定 `C₁` 落在有界侧、`ℝ³ − C₂` 落在无界侧，
必须排除"`C₂ᶜ` 有一个有界分支落在 `interior D` 里"。已经能证的部分是：`B ⊆ interior X ⊆ interior C₂`
（`X = Cl(C₂ − C₁)` 是壳，`frontier C₁`、`frontier C₂` 由不变域落在 `frontier X` 上，故与 `interior X` 不交），
以及 `C₁` 连通且与 `B` 不交，因此 `C₁` 整个落在某一侧；`C₂ᶜ` 的无界分支落在 `Dᶜ` 一侧。
但没有"`C₂ᶜ` 连通"就无法排除另一侧也含 `C₂ᶜ` 的点。

树里的相关材料：`Topology/SphereSeparation/JordanBrouwer.lean` 的
`hasTwoComplementComponents_of_isCompact_of_alexanderDualityH0Certificate` 已把任意紧致像的 `H₀` 证书转为恰两个补分支；
光滑性不在这个末端。缺的是证书生产者：`SpecializedAlexanderDuality` 仍只是条件，而从两分支反推它的现有定理对本目标循环。
任意拓扑球可为 wild sphere，不能走 smooth/open-bicollar；树中也没有 Čech或紧支撑上同调。H-M3 评估认为最窄专门
Alexander 对偶实现约 10k–18k 行，完整可复用基础约 20k–35k 行，未获批准前不启动。

所以"便宜箭头"名单里只剩 25.2 ← 25.1 与 26.4 ← 25.2 + 26.3 两条；30.5 ← 30.4 要先补上面这条拓扑输入。

## 三条"便宜箭头"共用同一个缺口：连续映射的 PL 逼近（2026-09-16 夜，逐条核对后）

把三条箭头的书面证明逐句拆开之后，发现它们都停在同一类前置上，而树里没有：

| 箭头 | 书上那句话 | 真正需要的东西 |
|---|---|---|
| 25.2 ← 25.1（183） | "we assume (with no loss of generality) that `L` and the contraction of `L` are PL" | 把连续的环与收缩换成 PL 的，即**连续映射的 PL 逼近**（单纯逼近，§6） |
| 26.4 ← 25.2 + 26.3（193） | "Let `D : Δ → M³` be a PL singular 2-cell … with `L` not contractible in `M²`" | `ker i*` 非平凡只给出**连续**的奇异盘，要先 PL 化，同上 |
| 30.5 ← 30.4（216） | "let `C` be the closure of the component of `ℝ³ − B` that contains `C₁`" | 拓扑 3-胞腔补集连通（拓扑 Jordan–Brouwer） |

因此新增两个具名 `Prop`（`MoiseChain.lean`）：

- `PLMapApproximation`：紧致多面体上的连续映射可被逐点 ε-接近的逐片仿射映射逼近。
  树里**没有**任何单纯逼近/连续映射 PL 化的结果；`Approximation.lean` 的 `PLApproximation` 是同胚的 PL 逼近，
  是终点本身，不是这个。
- `TopologicalCellComplementConnected`：ℝ³ 中拓扑 3-胞腔的补集连通。
  `Topology/SphereSeparation/JordanBrouwer.lean` 有条件于 `H₀` 证书的紧致像版本；任意拓扑 2-球面的证书需要真正的
  Alexander 对偶，不能由现有 smooth bicollar 或循环的 `specializedAlexanderDuality_of_componentCount` 得到。

结论：**"便宜箭头"这一类其实不存在**。Moise 用一段话带过的归约，靠的是前面章节的经典逼近定理。
单纯逼近是其中最值钱的一条：它同时解锁 25.2 与 26.4，而且几乎每一章的开头都用它把连续对象换成 PL 对象。
下一步若要推进主链，`PLMapApproximation` 是性价比最高的目标。

## `PLMapApproximation` 已证（2026-09-16 夜）

`MapApproximation.lean` 的 `exists_isPiecewiseAffineOn_dist_lt`：`E` 有限维赋范空间中的紧致多面体 `P`、
任意赋范空间 `F`、`P` 上连续的 `f : E → F`、`ε > 0`，则存在逐片仿射的 `g` 使 `∀ x ∈ P, dist (g x) (f x) < ε`。
`MoiseChain.lean` 的 `plMapApproximation` 由它给出。审计仅标准三公理。

证明是经典的顶点插值，目标凸所以不需要完整的单纯逼近定理：`P` 紧致给一致连续，取 `δ`；用 `Mesh.lean` 的
`exists_isSubdivision_diam_lt` 把三角剖分细分到每个单形直径 `< δ`；令 `g := simplicialMap K' f`，
即在顶点上取 `f` 值、在每个单形上重心插值；对 `x` 落在的面 `s`，`g x − f x = ∑ w_v • (f v − f x)`，
每个 `‖f v − f x‖ < ε/2`（因为 `dist v x ≤ diam < δ`），权非负且和为 1，故 `‖g x − f x‖ ≤ ε/2 < ε`。

**这消掉了两条箭头里的一半缺口。** 25.2 ← 25.1 与 26.4 ← 25.2 需要的是**映入 PL 3-流形**的版本；
目标是 ℝ³（或任意赋范空间）的情形已经有了，流形版按图卡归约即可，但要处理像跨图卡时的拼接，
这是下一步。凡目标本来就是 ℝ³ 的地方（§26.6、§30 的若干处）现在可以直接用。

## 又一个定义层缺口：`IsPolyhedron` 只覆盖紧致情形（2026-09-16 夜）

树里 `IsPolyhedron P := ∃ 有限族 H-多胞形，P = 它们的并`，因此**总是紧致**。
Moise §32 的伪胞腔定义要求"`U − P` 是多面体"，而 `U` 是开 2-胞腔、非紧；书里 §7 的"多面体"允许非紧
（`M = |K|`，`K` 可以是无限复形）。所以在写 §32 的定义层之前，必须先加一个非紧的多面体概念，
例如"局部有限复形的载体"，或"每点有邻域与某个有限多面体交为多面体"。

F 车道的 `LocallyFinitePieceTower`（F6.3）已经给了非紧 PL 流形的表示层，可以作为参照，
但它是流形层的，不覆盖一般的一维或二维非紧多面体。这一条不补，§32 的 `IsPseudoCell` 就写不出忠实的定义。
已把 §32 的定义层从"可先建"改为"先补非紧多面体概念"。

同夜新增：`IsSpine` 与 `Moise308`（脊生成 `π(S)`，用包含映射诱导的 `π₁(J) → π₁(S)` 的像生成整个群来表述，
避免共轭类与基点的额外实例要求）。

## 相对版逼近的确切剩余步骤（2026-09-16 夜，数学核心已证）

目标：`P` 紧致多面体、`Q ⊆ P` 子多面体、`f` 在 `P` 上连续且在 `Q` 上已经是逐片仿射，则存在逐片仿射的 `g`，
在 `Q` 上与 `f` **逐点相等**，在 `P` 上 `dist (g x) (f x) < ε`。Moise 每次"设某映射已经是 PL 的"都用这一条。

数学核心已经证了：`MapApproximation.lean` 的 `simplicialMap_eqOn_of_affineOn` —— 若 `f` 在一个闭单形上与某仿射映射相等，
则顶点插值 `simplicialMap` 在该单形上就等于 `f` 本身。于是只要三角剖分做到"`Q` 是子复形且 `f` 在 `Q` 的每个面上仿射"，
误差在 `Q` 上自动为零，其余部分用已证的小网格估计。

剩下的是纯组合的拼装，四步都有现成接口：

1. `IsPolyhedron.exists_simplicialComplex` 把 `P` 三角剖分成 `K`。
2. `StarSubdivision.lean` 的 `exists_isSubdivision_subcomplexes_closedStars_subset_openStar`（取单个多面体 `Q`）
   给细分 `R₀`，使 `(restrict R₀ Q).space = Q`，即 `Q` 成为子复形。
3. `PiecewiseAffineSimplicial.lean` 的 `exists_isSubdivision_affineOn_faces_finite` 用在子复形 `restrict R₀ Q` 上
   （`f` 在它的载体 `Q` 上逐片仿射），得 `L'`，使 `f` 在 `L'` 的每个面上仿射。
4. `RelativeSubdivision.lean` 的 `exists_isSubdivision_extension_of_disjoint`（取 `A` 为空复形）把 `L'` 扩成整个 `R₀` 的细分 `R₁`。
5. 最后用 `exists_isSubdivision_diam_lt` 把 `R₁` 再细分到小网格；因为仿射映射限制到子单形仍仿射，
   第 3 步的性质在再细分后保持，所以 `Q` 上仍然精确相等。

要注意的一点：第 5 步之后要说明 `Q` 仍是最终复形的子复形（从而 `Q` 中点的载体面落在 `Q` 内），
这需要 `IsSubdivision` 对 `restrict` 的相容性引理；没找到现成的就得补一条。

## 相对版逼近已证（2026-09-16 夜）

`MapApproximation.lean` 的 `exists_isPiecewiseAffineOn_dist_lt_eqOn`：`P` 紧致多面体、`Q ⊆ P` 多面体、
`f` 在 `P` 上连续且在 `Q` 上逐片仿射、`ε > 0`，则存在逐片仿射的 `g`，在 `Q` 上与 `f` 逐点相等，
且 `∀ x ∈ P, dist (g x) (f x) < ε`。审计仅标准三公理。

拼装用到的现成接口正是上一节列的四条：`exists_isSubdivision_restrict_space`（把 `Q` 变成子复形）、
`exists_isSubdivision_affineOn_faces_finite`（在 `Q` 的三角剖分上让 `f` 逐面仿射）、
`exists_isSubdivision_extension_of_disjoint`（把 `Q` 的细分扩到整个 `P`，`A` 取空复形）、
`exists_isSubdivision_diam_lt`（小网格）。上一节担心的"`restrict` 与细分相容"其实已经有了：
`IsSubdivision.restrict`（`Subcomplex.lean`）。再加本轮的 `simplicialMap_eqOn_of_affineOn`，误差在 `Q` 上恰为零。

至此欧氏目标的逼近层完整：绝对版、相对版、以及仿射还原引理。**剩下的是把目标从赋范空间换成 PL 3-流形**，
按图卡归约；难点是像跨图卡时的拼接，F 车道的 `Topology/Pasting.lean` 与 `SingularPasting.lean` 是为这类拼接建的。

## 单图卡的流形版逼近已证（2026-09-16 夜）

`ManifoldApproximation.lean` 的 `exists_isPLOn_dist_lt_of_mapsTo_chart`：`P ⊆ ℝⁿ` 紧致多面体、
`N` 为带 `plGroupoid m` 的度量流形、`f : ℝⁿ → N` 在 `P` 上连续且把 `P` 映进某张极大图册里的图卡 `e` 的定义域、
`ε > 0`，则存在 `g` 使 `IsPLOn n m g P` 且 `∀ x ∈ P, dist (g x) (f x) < ε`。审计仅标准三公理。

关键步骤：`e ∘ f` 的像紧致且含于开集 `e.target`，用 `IsCompact.exists_thickening_subset_open` 取余量 `r`；
在闭厚化 `cthickening (r/2)`（紧致）上 `e.symm` 一致连续，取 `δ`；用欧氏版逼近以 `min δ (r/2)` 逼近 `e ∘ f`，
所得 `g'` 仍落在 `e.target` 内；`g := e.symm ∘ g'`，PL 性由 F 车道的
`isPLOn_iff_isPiecewiseAffineOn_comp_chart` 给出，误差由 `e.symm` 的一致连续性给出。

**逼近层的剩余部分只有一件**：像跨多张图卡时的整体版本。书里每次用"设某映射是 PL 的"时，像通常不在单张图卡里，
所以还要做覆盖归纳：把 `P` 剖分成有限块使每块的像落在一张图卡内，逐块逼近并在交界处拼接。
F 车道的 `Topology/Pasting.lean` 与 `SingularPasting.lean` 正是为这种"改一块、界外不变、保住纤维"的拼接建的。
相对版（本轮已证的 `exists_isPiecewiseAffineOn_dist_lt_eqOn`）是归纳步骤的关键：逐块处理时前面已处理的部分要保持不动。

## 流形版逼近已证，逼近层关闭（2026-09-17）

`ManifoldApproximation.lean` 现在给出无图卡限制的版本：

- `exists_isPLOn_dist_lt`：`P ⊆ ℝⁿ` 紧致多面体、`N` 为带 `plGroupoid m` 的度量流形、`f` 在 `P` 上连续、`ε > 0`，
  则存在 `g` 使 `IsPLOn n m g P` 且 `∀ x ∈ P, dist (g x) (f x) < ε`。
- `exists_isPLOn_dist_lt_eqOn`：相对版，`Q ⊆ P` 子多面体上 `f` 已是 PL 时，`g` 在 `Q` 上与 `f` 逐点相等。
- `MoiseChain.lean` 的 `PLManifoldMapApproximation` / `plManifoldMapApproximation` 记录这一结点。审计仅标准三公理。

架构（四层，每层都是独立可用的定理）：

1. `MapApproximation.lean` 的 `exists_isPiecewiseAffineOn_dist_lt_eqOn_of_dist_le`：欧氏相对版的推广——
   不再要求 `f` 本身在 `Q` 上逐片仿射，而是给定一个在 `Q` 上逐片仿射、与 `f` 相距 `≤ δ` 的 `u`，
   结论是 `g` 在 `Q` 上**等于 `u`**、在 `P` 上与 `f` 相距 `< δ + ε`。顶点映射取 `Q.piecewise u f`，
   其余与原证明相同。原来的相对版是 `δ = 0` 的特例。
2. `ManifoldApproximation.lean` 的 `exists_pos_forall_exists_isPLOn_dist_lt_eqOn_of_mapsTo_chart`：
   单图卡版，但**先给出容差 `η`**：`∃ η > 0, ∀ u, (u 在 Q 上 PL 且与 f 相距 < η) → ∃ g …`。
   量词次序是归纳能跑通的关键——处理第 `k+1` 块时，先由这块定出 `η`，再让前 `k` 块以 `min ε η` 的精度完成。
   N 侧不能用 `cthickening`（一般度量空间非 proper），改用 `ChartedSpace.locallyCompactSpace` +
   `exists_compact_between` 取紧邻域，再在其上用 `e` 的一致连续性。
3. `exists_isPLOn_dist_lt_eqOn_of_biUnion`：对有限族 `C : ι → Set ℝⁿ`（每块是多面体且像落在一张图卡里）
   按 `Finset.induction_on` 逐块处理，归纳假设对**所有** `ε` 成立，因此误差的递减时间表自动产生。
   拼接用 `Pasting.lean` 的 `IsPLOn.piecewise_of_isClosed`（本轮从 `LoopTheorem/CellGluing.lean` 的 private 提上来）。
4. `exists_finsetBiUnion_eq_mapsTo_chart`：造覆盖。对每点取 `f ⁻¹' (chartAt (f x)).source` 的开邻域，
   `lebesgue_number_lemma_of_metric` 给 Lebesgue 数 `d`，`exists_isSubdivision_diam_lt` 把三角剖分细到直径 `< d`，
   闭单形即为各块（空面用 `Finset.filter` 去掉，否则无法给出图卡）。

**影响**：`MOISE_CHAIN.md` 上"三条便宜箭头共用同一个缺口"里的**逼近缺口已经消掉**。
25.2 ← 25.1 与 26.4 ← 25.2 + 26.3 两条箭头现在只差书上本身的论证，不再缺前置定理。
30.5 ← 30.4 仍缺 `TopologicalCellComplementConnected`（拓扑 Jordan–Brouwer），那是同调侧的工作。

## 单纯逼近定理已证（2026-09-17）

`SimplicialApproximation.lean`：

- `exists_isSubdivision_simplicialApproximation`：`K`、`L` 为有限单纯复形，`f` 在 `|K|` 上连续且映入 `|L|`，
  则存在 `K` 的细分 `K'` 与顶点映射 `φ`，使 `∀ s ∈ K'.faces, s.image φ ∈ L.faces`，
  且 `∀ x ∈ |K|, simplicialMap K' φ x ∈ convexHull (carrierFace L (f x))`。
- `exists_isPiecewiseAffineOn_mapsTo_dist_lt`：先把 `L` 细分到网格 `< ε`，得到逐片仿射、**像仍落在 `|L|` 内**、
  且与 `f` 处处相距 `< ε` 的 `g`。
- `mapsTo_lineMap_of_mem_convexHull_carrierFace`：直线同伦 `(1-t)f + tg` 全程落在 `|L|` 内
  （两端同在 `carrierFace L (f x)` 的凸包里）。于是逼近与原映射在 `|L|` 中同伦，边界环路的同伦类不变。
- `eqOn_simplicialApproximation_of_mem_carrierFace_singleton`：`f x` 落在 `L` 的顶点上时逼近与 `f` 相等。

审计仅标准三公理。

证明是经典的星形条件：`L` 的顶点开星 `openStar L w` 覆盖 `|L|`（`exists_vertex_mem_openStar`）；
`avoidingUnion` 闭（`isClosed_avoidingUnion`）故开星是 `|L|` 的相对开集，用 `continuousOn_iff'` 拉回成环境开集；
`lebesgue_number_lemma_of_metric` 给 Lebesgue 数 `d`；`exists_isSubdivision_diam_lt` 把 `K` 细分到直径 `< d`，
于是每个顶点的闭星落在半径 `d` 的球里，从而整体落在某个 `f⁻¹(openStar L w)` 内，令 `φ(v) := w`。
关键一步 `w ∈ carrierFace L y ← y ∈ openStar L w` 直接由 `avoidingUnion` 的定义得到
（`mem_carrierFace_of_mem_openStar`）。

**为什么这条比图卡版更要紧**：`NormalSystem`（`LoopTheorem/SingularCell.lean`）的 `vertexMap` 与
`source_faces_map` 字段要求的正是"源复形的每个面在顶点映射下的像是环境复形的面"，即单纯逼近的结论本身；
而 `Moise252` 里的环境是带边组合流形 `K`，其图卡模型是半空间，`IsPLOn n 3`（图卡模型为 `ℝ³`）对不上。
因此 25.2 ← 25.1 这条箭头要用的是本条，不是 `ManifoldApproximation.lean` 的图卡版。
图卡版仍然适用于 `IsNormalSingularCell`（其环境 `M` 是无边的 `ChartedSpace (EuclideanSpace ℝ (Fin 3)) M`）。

## 读 26.4 与 31 的原文后的两条更正（2026-09-17）

### 1. 26.4 不是"四种情形的归纳，材料都在树上"（书页 193，Theorem 4）

原文的证明结构是：
`ker i*` 非平凡 → 取 PL 奇异 2-胞腔 `D : Δ → M³`，`Bd D = L ⊆ M²`，`L` 在 `M²` 中不可缩
→ 用 I2 把 `|D|` 推离 `Bd M³` → 取 `M²` 在 `Int M³` 中的**双领域** `W`（26.3 = 书上 Theorem 3，S 已交付）
→ 把 `D` 放到相对 `Bd W` 的一般位置，使 `D⁻¹(|D| ∩ Bd W)` 是有限条不交多边形 `J₁,…,J_n`，且每条有环形邻域
一侧映入 `Int W`、另一侧映入 `M³ − W` → 取不含其他 `J_i` 的 `d₁` → Case 1/2 把 `D(d₁)` 推过去以减少 `n`
→ Case 3 对 `Cl(M³ − W)` 与 `L = D||J₁|` 用环定理（25.2），得 `Δ₁`，再补上环带 `A = ρ(C × [0,1])` 得 `Δ = Δ₁ ∪ A`。

也就是说 26.4 需要：**奇异盘相对一张曲面的一般位置**（= 计划里 F5.2 那一类）、双领域的 `ρ` 参数化、
以及"沿一条多边形把盘推过双领域"的重定义。这些都不是现成的。原先"箭头便宜"的判断只对第一步
（把连续的零伦换成 PL 的）成立，那一步现在已经有工具了。

### 2. 相对单纯逼近需要"相对子复形的细分"，树里没有

要得到 `Bd D = L` 恰好等于给定的 PL 环路，必须在 `|K₀|`（这里是圆周）上让逼近与 `f` **逐点相等**。
经典做法是"在 `K₀` 之外细分"：保持 `K₀` 的面不动，只细分其余部分。树里 `RelativeSubdivision.lean` 的
`exists_isSubdivision_extension_of_disjoint` 要求 `A.space` 与 `B.space` **不交**，因此不能用来
"保持 `K₀` 不动、把别处细到小网格"；`Mesh.lean` 的 `exists_isSubdivision_diam_lt` 也没有相对版。

注意这**不能**像欧氏相对逼近那样绕过去。欧氏版能绕过，是因为 `simplicialMap_eqOn_of_affineOn`：
`f` 在一个面上仿射时，再细分后顶点插值仍等于 `f`。但单纯逼近还要求顶点的像是**目标复形的顶点**，
而细分产生的新顶点 `v` 的像 `f v` 一般落在某个单形的内部，不是顶点。两个要求不能同时满足。

**两条出路**（留给下一轮）：

- (a) 补"相对子复形的细分"：`∃ K', IsSubdivision K' K ∧ K₀.faces ⊆ K'.faces ∧
  ∀ s ∈ K'.faces, s ∉ K₀.faces → diam (convexHull s) < ε`。这是标准 PL 基础设施，值得单独做。
- (b) **环带技巧**，不需要 (a)：先用绝对版单纯逼近得到 PL 的 `g`，`g|∂Δ` 与给定的 `L` 之间有直线同伦
  （`mapsTo_lineMap_of_mem_convexHull_carrierFace` 保证全程落在 `|L|` 内），而 `L` 与 `g|∂Δ` 都是 PL，
  所以这条直线同伦在 `[0,1] × ∂Δ` 上是逐片仿射的；把这个环带粘到 `g` 的盘上再重新参数化成盘，
  就得到边界恰为 `L` 的 PL 奇异盘。需要的拼接接口在 `Gluing.lean` / `PlanarDiskUnion.lean` / `CellGluing.lean`。

### 3. §31 的定义层：先补两件词汇再写

读书页 220–221 后确认 §31 的定义需要：绕 `y` 轴的旋转体（把右半 `xy` 平面里的点/线段/2-胞腔变成
圆周 `J_j` / 环带 `A_j` / 实心环面 `S_j`），以及"`T''_j` 与 `T''_{j+1}` 在每条交多边形处**横截相交**"。
前者容易写（`{p | ∃ q ∈ S, 0 ≤ q 0 ∧ p 1 = q 1 ∧ p 0 ^ 2 + p 2 ^ 2 = q 0 ^ 2}`）；
后者树里没有两张曲面互相横截的谓词（只有 `HasPLDoubleCrossingAt` 这种针对奇异集的），
不要临时造一个。四条定理里 Theorem 2、4 都要"某圆周携带 `π(S'')` 的生成元"，
直接复用 `Moise308` 已经用过的写法（包含映射诱导的像生成整个基本群）即可。

## 树里已有的两件东西，改变了"相对逼近"的路线（2026-09-17）

### 1. `GeneralPosition.lean` 已经有"保持子复形不动的一般位置"

`exists_small_simplicialMap_transverse_on_subcomplex`（约 3771 行）与它的边界版（约 4961 行）：
输入一个单纯映射 `simplicialMap K φ₀` 与子复形 `B`（或 `boundaryComplex (m+1) K`），
输出细分 `K'` 与新顶点映射 `φ`，满足 `B.faces ⊆ K'.faces`、`EqOn (simplicialMap K' φ) (simplicialMap K φ₀) B.space`、
`dist < ε`，加上横截性与双点复形 `G` 是一维带边组合流形。边界版还给出 `G` 的顶点在边界上度数为 1、内部度数为 2。

"连续 → 单纯 →（保持边界不动的）一般位置"这条流水线的两段都在树上了：
前一段用本轮的 `exists_isSubdivision_simplicialApproximation`，后一段用上面这条。
它建立在 `RelativeDerived.lean` 的 `relDerived`（相对导出细分）之上，`faces_subset_relDerived` 保证子复形的面被原样保留。

**但两段不能直接串**，有一条必须补上的条款：一般位置那一步是在环境向量空间 `F` 里把顶点像挪动 `< ε`，
`GeneralPosition.lean` 里**没有任何结论说扰动后的像仍落在某个给定复形的载体里**
（全文只有一处 `MapsTo (simplicialMap K φ) …`，且是单个单形之间的，不是全局的）。
而 Moise 用它的时候，盘必须始终留在 `M³` 内。所以还需要一条"扰动保持像落在 `|K_amb|` 内"的版本，
或者在应用处用"像落在 `Int M³` 的某个紧子集里、`ε` 取得比到边界的距离小"来补。这一条要先确认，再谈串联。

### 2. 但迭代 `relDerived` **不会**把靠近子复形的单形变小

`relDerived` 的面形如 `τ ∪ {一串重心}`，其中 `τ` 是被保留的子复形 `B` 的面。含有整个 `τ` 的面，
直径总是 `≥ diam τ`，无论迭代多少次。因此"保持 `K₀` 不动、把别处细到小网格"这个想法**不成立**，
上一节列的出路 (a) 要重新设计，不能简单地迭代相对导出细分。

经典的相对单纯逼近（Spanier 3.4.8）之所以还成立，是因为对 `K₀` 的顶点 `v`，星条件
`f(openStar v) ⊆ openStar_L (f v)` 在 `|K₀|` 内部分自动满足（`f` 在那里是单纯的，重心坐标里 `f v` 的系数为正），
只有跨出 `|K₀|` 的那部分需要控制；这一步不是"把网格变小"能直接给的。所以这条定理要按原证明逐条搬，
不要指望用现有的网格引理拼出来。

**因此推荐走出路 (b)（环带技巧）**，它只需要：一个多边形环带的三角剖分 + 顶点映射（外圈取给定 PL 环路的顶点值，
内圈取逼近的顶点值），由相邻两圈顶点的像同在 `L` 的一张面里保证像落在 `|L|` 内；再用
`Gluing.lean` / `PlanarDiskUnion.lean` 把环带与盘粘起来重新参数化。注意**直线同伦本身不是 PL 的**：
`(1-t) A x + t B x` 含 `t·x` 项，在任何有内点的块上都不是仿射的，所以必须用棱柱三角剖分而不是直线同伦。

### 3. `Mesh.lean` 已有 Lebesgue 数 + 细分的打包版

`exists_isSubdivision_closedStars_subset_cover`：给 `|K|` 的一个相对开覆盖，返回细分 `R` 使
`∀ s ∈ R.faces, ∃ i, (⋃ v ∈ s, closedStar R v) ⊆ U i`。本轮的单纯逼近里这一步是手写的
（Lebesgue 数 + `exists_isSubdivision_diam_lt` + 闭星落在球里）；以后写同类证明可以直接用这条。

## 逼近层已接到链条的词汇上（2026-09-17 续）

`SimplicialApproximation.lean` 现在还提供三条把分析陈述翻译成链条词汇的桥：

- `exists_isPiecewiseAffineOn_mapsTo_dist_lt` 扩充了两条结论：直线同伦
  `(t, x) ↦ (1-t) • f x + t • g x` 在 `Icc 0 1 ×ˢ |K|` 上连续，且把它映进 `|L|`。
- `homotopic_restrict_of_continuousOn`：一般拓扑的桥。给定 `f`、`g` 在 `S` 上连续且映进 `T`，
  以及一条在 `Icc 0 1 ×ˢ S` 上连续、映进 `T`、两端分别是 `f`、`g` 的同伦，
  则限制成的 `C(↥S, ↥T)` 两个映射是 `ContinuousMap.Homotopic` 的。
- `exists_isPiecewiseAffineOn_mapsTo_dist_lt_homotopic`：上面两条的合成，直接给出
  `C(↥|K|, ↥|L|)` 层面的同伦。
- `exists_isPiecewiseAffineOn_freeLoop_homotopic`：给一条多边形圆周的参数化 `e : loopCircle ≃ₜ |J|`，
  任意 `γ : freeLoop |L|` 在 `|L|` 中同伦于一条逐片仿射的环路。
  于是 `IsNullHomotopic` 这个假设在换成 PL 环路后不变，`Moise252`、`Moise264` 的
  "不妨设 `L` 是 PL 的"这句话有了对应的定理。

`MoiseChain.lean` 里现在有三个逼近结点，都是已证的（审计仅标准三公理）：
`plMapApproximation`（目标是赋范空间）、`plPolyhedronMapApproximation`（目标是有限复形的载体，像不出界）、
`plManifoldMapApproximation`（目标是带 `plGroupoid` 的度量流形，相对版）。
书里"不妨设某映射是 PL 的"这句话，按目标是向量空间 / 多面体 / 流形三种情形，分别对应这三条。

## 多边形圆周的参数化已证（2026-09-17）

`CircleParametrization.lean`：

- `exists_ne_mem_of_isPLSphere_one`：PL 1-球面至少有两个不同的点（用 `stdSimplexBoundary 2` 的两个顶点）。
- `nonempty_homeomorph_loopCircle_of_isPLSphere_one`：任意 PL 1-球面 `S` 都有 `loopCircle ≃ₜ ↥S`。

证明：`CircleArcs.lean` 的 `exists_arc_decomposition_of_isPLSphere_one` 把 `S` 分成两条弧 `A`、`B`，
`A ∪ B = S`、`A ∩ B = {p, q}`，各自由 `Icc 0 1` 的 PL 同胚参数化。把第一条正向、第二条反向接起来得
`Path ⟨p⟩ ⟨p⟩`，`pathToCircle` 给出 `loopCircle → ↥S`。单射性按 `Path.trans_apply` 分四种情形：
两端同在前半段或同在后半段时由弧的单射性得出；跨段时公共值落在 `A ∩ B = {p, q}` 里，
取值 `p` 只能是两端点 `t₁ = 0`、`t₂ = 1`（在 `AddCircle 1` 里同一点），取值 `q` 则与半段的严格不等式矛盾。
满射性由 `A ∪ B = S`。最后用紧致到 Hausdorff 的连续双射是同胚。审计仅标准三公理。

这条正好配 `NormalSystem.boundaryParam : loopCircle ≃ₜ frontier sourceComplex.space`：
`sourceComplex.space` 是 PL 2-球，`frontier` 是 PL 1-球面（`IsPLBall.isPLSphere_frontier`），
所以那条字段现在可以由定理给出，不必当作数据携带。
`exists_isPiecewiseAffineOn_freeLoop_homotopic` 需要的参数化输入也由这条供给。

## PL 棱柱与 PL 同伦（2026-09-17，整日）

上一节记的"出路 (b)（环带技巧）"所缺的那块已经建好了。直线同伦 `(1-t)A x + t B x` 含 `t·x` 项，
在任何有内点的块上都不仿射，所以棱柱必须切开。四个模块：

1. `PrismMap.lean`
   - `upperPrismTriangle`、`lowerPrismTriangle`：单位正方形被对角线切成的两块，都是 H-多胞形。
   - `prismSquareMap a b c d`：在上三角取仿射映射 `a + t•(c-a) + λ•(d-c)`，下三角取 `a + λ•(b-a) + t•(d-b)`，
     两者在对角线上都等于 `a + t•(d-a)` 故可拼。四条边分别是四个角值的仿射插值，像落在 `hull {a,b,c,d}` 内。
   - `prismStripMap p q a b c d`：沿仿射重标度搬到 `Icc p q ×ˢ Icc 0 1` 上。
2. `PrismInterval.lean`
   - `exists_isPiecewiseAffineOn_prism_of_partition`：给定 `[0,1]` 的分划 `s 0 = 0 < … < s n = 1`，
     两个映射在每个格上都是端点值的仿射插值，则把各条 strip 沿竖直线段 `{s k} × [0,1]` 归纳拼起来，
     得到正方形上的逐片仿射映射：底边是 `f`，顶边是 `g`，两侧是端点值的直线插值，
     每个格上方的像落在该格四个角值的凸包里。
   - `..._of_loop`：两端是环路时两侧相等，于是映射降到环带上。
   - `mapsTo_of_forall_mem_convexHull_cell`：四角值都在凸集里时整块棱柱落在该凸集里。
3. `BrokenLine.lean`
   - `exists_partition_affineOn_two`：`[0,1]` 上两个逐片仿射映射共用一个分划，在每格上都是仿射插值。
     证明：`IsPolyhedron.exists_simplicialComplex` 把 `[0,1]` 三角剖分，
     `exists_isSubdivision_affineOn_faces_finite` 细分到两个映射都逐面仿射，取所有面的顶点作有限集 `P`，
     用 `Finset.orderIsoOfFin` 排序；相邻两点之间没有 `P` 的点，故每个格落在某一个面里。
   - `affineMap_apply_eq_interp`：仿射映射就是端点值的插值。
4. `PrismHomotopy.lean`
   - `exists_isPiecewiseAffineOn_prism`：去掉分划假设的版本。
   - `exists_isPiecewiseAffineOn_prism_mapsTo`：两端都映进凸集时整块映进该凸集。
   - `exists_isPiecewiseAffineOn_annulus_of_partition`：两条 PL 环路在每格四角同落一张面里时，
     得到**落在 `|L|` 内的 PL 奇异环带**，底是 `f`、顶是 `g`、两侧粘合。
   - `exists_face_of_cell_of_mem_convexHull_carrierFace`：上一条的面条件由"单纯逼近"自动给出——
     若 `f` 把每个格映进一张闭单形，而 `g x` 落在 `carrierFace L (f x)` 的凸包里，则四角同面。

全部只依赖标准三公理。

### 同日补完的三件

5. `BrokenLine.lean` 的分划现在可以**任意细**，并且可以**强制包含调用者给的一组点**：
   `exists_partition_affineOn_two hf hg hδ T hT` 返回的分划满足 `s (i+1) - s i < δ`、
   `T ⊆ {s i}`、以及"`T` 的点不落在任何格的内部"。
   这一条是必需的：面条件（四角同落一张面）只有在**格不跨过任何一个折点**时才可能成立——
   若 `f` 是单纯的而某个格跨过它的一个顶点，两端的像分别落在相邻两张面里，一般没有公共面。
   调用者把 `f`、`g` 的折点作为 `T` 传进来，就能逐格验证面条件。
6. `PrismHomotopy.lean` 的 `exists_isPiecewiseAffineOn_prism_mapsTo_space` /
   `..._annulus_mapsTo_space`：假设写成"任意两个参数只要相距 `< δ` 且中间没有 `T` 的点，
   四个值就同落一张面"，结论是像落在 `|L|` 内的 PL 棱柱 / 环带。这是可检验的接口。
7. `PrismArc.lean`：沿 PL 参数化把棱柱搬到嵌入的 PL 弧上
   （`exists_isPiecewiseAffineOn_prism_of_isPLHomeomorphOn`，同时给出两条竖直边的值），
   再把两条弧的棱柱沿 `{p, q} × [0,1]` 拼起来，得到**嵌入的 PL 圆周上的棱柱**
   （`exists_isPiecewiseAffineOn_prism_of_isPLSphere_one`，结论是"两端映进凸集则整体映进"）。
   落在 `|L|` 内的版本也有了：`exists_isPiecewiseAffineOn_prism_of_isPLHomeomorphOn_mapsTo_space`（弧）
   与 `exists_isPiecewiseAffineOn_prism_of_arcs_mapsTo_space`（圆周）。
   圆周版把两条弧及其参数化取作**输入**，这样面条件是关于调用者手里的数据说的，可以逐条验证；
   若把弧取作存在量词产生的数据，调用者就无法陈述假设——这是接口设计上必须这样写的原因。

### 离"边界指定的 PL 奇异盘"还差的一步

把环带贴到逼近好的盘上。做法已经确定：取盘的模型为方块 `[-1,1]²`（`Prism.lean` 的
`isPLBall_unit_square`），内方块 `[-1/2,1/2]²` 上放 `G(2z)`，方形环带
`A = [-1,1]² ∖ int [-1/2,1/2]²` 上放本轮的环带映射，两者在 `∂[-1/2,1/2]²` 上相等，用
`IsPiecewiseAffineOn.piecewise_of_isClosed` 拼起来。

所缺的只有 `A` 与 `[0,1]²` 之间的 PL 对应。注意**径向参数化 `p ↦ p/‖p‖_∞` 不是 PL 的**；
必须把每条边对应的梯形切成两个三角形，写出 8 片仿射映射。等价地：本轮的 `prismSquareMap`
用在 `f := ∂[-1,1]² 的折线参数化`、`g := 它的一半` 上，得到的就是 `[0,1]² → A` 的那个映射；
剩下要证的是它在 `[0,1) × [0,1]` 上单射、像恰为 `A`。这是显式坐标计算，没有新的数学内容。

另一条更彻底的出路是 PL 正则邻域的**收缩**：树里 `DerivedNeighborhoodRetraction.lean` 的
`subcomplexBarycentricProjection = (mass)⁻¹ • moment` 是**射影映射，不是逐片仿射的**
（取 `a₁=(0,0)`、`a₂=(1,0)` 在 `L` 上、`b=(0,1)` 不在，投影是 `(x,y) ↦ (x/(1-y), 0)`），
所以它不能用来把逼近的像拉回 `|L|`。要走这条路得另造一个 PL 收缩。

## 一个重要的重新框定：乘积领口不需要环带（2026-09-17 末）

上面说"离边界指定的 PL 奇异盘还差方形环带的显式构造"。这对**盘相对整条边界**是对的，
但对**乘积形状的定义域**根本不需要环带：

`P ×ˢ [0,1]` 相对 `P × {0}` 的领口就是 `P ×ˢ [0,ε]`，**本身就是乘积**，
所以本轮的棱柱可以直接用上，没有径向参数化的问题。具体路线：

1. 用 `exists_isPiecewiseAffineOn_mapsTo_dist_lt`（单纯逼近）把 `f` 在 `P ×ˢ [0,1]` 上逼近成 `G`，
   且 `G z ∈ convexHull (carrierFace L (f z))`。
2. `G` 限制到切片 `P × {ε}` 仍逐片仿射（与仿射映射 `x ↦ (x, ε)` 复合）。
3. 在 `P ×ˢ [0,ε]` 上放棱柱映射，底是 `f(·,0)`（已假设是 PL 的），顶是 `G(·,ε)`；
   `ε` 取得足够小时 `f(·,ε)` 与 `f(·,0)` 接近，于是面条件成立。
4. 在 `P ×ˢ [ε,1]` 上用 `G`，两块沿 `P × {ε}` 相等，用 `piecewise_of_isClosed` 拼起来。

结论形状：**`f` 在 `P ×ˢ [0,1]` 上连续、映进 `|L|`、在 `P × {0}` 上已是 PL，则存在 PA 的 `g`
映进 `|L|` 且在 `P × {0}` 上与 `f` 逐点相等。** 取 `P` 为 PL 圆周，这就是
"环路的同伦可以在保持初始环路不动的前提下取成 PL 的"，Moise §26（双领域）与 §24（柱形图）里反复要用。

**唯一真正需要环带的是"盘相对整条边界"**（即把 `Bd D` 指定成给定环路）。那一条仍然要写方形环带的
8 片仿射映射，或者等价地证明本轮 `prismSquareMap` 用在 `f := 边界的折线参数化`、`g := 它的一半`
上时在 `[0,1) × [0,1]` 上单射、像恰为环带。

第 3 步里还缺一件：面条件要求 `f(·,0)` 的每个格的像落在一张面里。PA 映射映进 `|L|` 时这不是自动的
（一条线段可以穿过若干张面），但穿过的参数值只有有限个（都是多面体交点），所以在这些值处再细分即可。
树里 `GeneralPosition.lean` 的 `G.space = K.space ∩ simplicialMap K' φ ⁻¹' L.space` 那一类构造是同一件事。

本轮为此补了工具：`PiecewiseAffineCover.lean` 的
`exists_isPiecewiseAffineOn_of_affine_cover`（由有限覆盖上两两相容的仿射片拼出逐片仿射映射）、
`mapsTo_of_affine_cover`、`eqOn_of_affineMap_eq_of_mem_segment`（两个仿射映射在线段两端相等则沿线段相等，
这是三角形共边时验证相容性的办法）。

### 乘积领口的拼接已证（同日）

`PrismHomotopy.lean` 新增两条：

- `exists_isPiecewiseAffineOn_prism_height_mapsTo_space`：棱柱的高度可以取任意 `h > 0`
  （与 `(x,t) ↦ (x, t/h)` 复合）。
- `exists_isPiecewiseAffineOn_glue_prism_collar`：给定 `G` 在正方形上逐片仿射且映进 `|L|`、
  `f` 在 `[0,1]` 上逐片仿射、`ε > 0`，以及"相距 `< δ` 且中间无 `T` 点的 `a, b` 使
  `{f a, f b, G (a,ε), G (b,ε)}` 同落一张面"这一条件，则存在 `g` 逐片仿射、映进 `|L|`、
  **在底边等于 `f`**、在 `[0,1] ×ˢ [ε,1]` 上等于 `G`。

`PiecewiseAffineCover.lean` 提供的是另一类工具（由有限覆盖上的仿射片拼出映射），
两者都可以用来做这类"改一条边、其余不变"的构造。

**剩下两小步就能得到"乘积相对一端的 PL 逼近"**：

1. 把 `f` 沿 `t` 方向重参数化成在 `[0,ε]` 上与 `t` 无关（`f'(x,t) := f (x, max 0 ((t-ε)/(1-ε)))`），
   这样 `f'` 连续、在 `[0,ε]` 上恒等于 `f(·,0)`，且与 `f` 相对底边同伦。
2. 对 `f'` 用单纯逼近得 `G`（`G z ∈ convexHull (carrierFace L (f' z))`）。
   于是 `G (a, ε) ∈ convexHull (carrierFace L (f (a,0)))`，
   只要底边映射的每个格的像落在一张面 `u` 里，就有 `carrierFace L (f (a,0)) ⊆ u`，
   四个点同落 `u` —— `hface` 成立。这一步是**关键**：先重参数化再逼近，
   逼近的顶边值就自动与底边值贴合，否则 `G(·,ε)` 逼近的是 `f(·,ε)`，与 `f(·,0)` 无关。
3. 第 2 步还需要"底边映射每个格的像落在一张面里"。PA 映射映进 `|L|` 时这不自动成立，
   但线段穿过面的参数只有有限个，在那里再细分即可（用本轮 `exists_partition_affineOn_two`
   的 `T` 参数把这些点钉进分划）。

## 乘积相对一端的 PL 逼近已证（2026-09-17 收尾）

`RelativeSquareApproximation.lean`：

- `exists_isPiecewiseAffineOn_square_eqOn_bottom_of_cells`：`f` 在 `[0,1]²` 上连续、映进 `|L|`，
  底边映射 `x ↦ f (x,0)` 逐片仿射且**每个格的像落在 `L` 的一张面里**，
  则存在逐片仿射的 `g`，映进 `|L|`，且在底边与 `f` 逐点相等。审计仅标准三公理。
- 证明按上一节列的三步：`collarReparam` 把 `f` 沿 `t` 重参数化成在 `[0,1/2]` 上与 `t` 无关；
  对重参数化后的映射做单纯逼近得 `G`；于是 `G (a, 1/2) ∈ convexHull (carrierFace L (f (a,0)))`，
  面条件自动成立；最后用 `exists_isPiecewiseAffineOn_glue_prism_collar` 把领口棱柱贴上去。
  **先重参数化再逼近是关键**，反过来 `G(·,1/2)` 逼近的是 `f(·,1/2)`，与底边无关，面条件不成立。
- `exists_face_of_no_partition_point_between`：把"逐格的像在一张面里"翻译成棱柱要的
  "中间没有分划点的两个参数的像在一张面里"（用 `Nat.findGreatest` 找 `a` 所在的格）。
- 面条件现在都带 `a ≤ b`，因为它们只在格的两端用到。

**结论**：`P ×ˢ [0,1]` 相对 `P × {0}` 这一形状（`P = [0,1]`）已经通了。取 `P` 为 PL 圆周的版本
只差把同一套论证沿 `PrismArc.lean` 的弧分解搬一遍，是机械工作。
真正还没做的仍然只有"盘相对整条边界"，需要方形环带的显式 8 片仿射映射。

## 大目标：相对 PL 逼近层（2026-09-17 起，进行中）

目标：**给定映进 `|L|` 的连续映射，若它在某个子多面体上已是 PL，则换成映进 `|L|` 的 PL 映射且在那里逐点相等。**
Moise 每一章开头"不妨设某映射是 PL 的"都是这一条。分三个里程碑：

- **M1 乘积相对一端：已证。** `[0,1] ×ˢ [0,1]` 相对底边（`RelativeSquareApproximation.lean` 的
  `exists_isPiecewiseAffineOn_square_eqOn_bottom_of_cells`），以及一般多面体底 `J ×ˢ [0,1]` 相对 `J × {0}`
  （`PrismProdCollar.lean` 的 `exists_isPiecewiseAffineOn_prod_eqOn_bottom_of_arcs`，`J` 为嵌入的 PL 圆周，
  取两条弧的分解作输入）。配套工具：`heightRescaleProd`（棱柱高度任意）、
  `exists_isPiecewiseAffineOn_glue_collar_prod`（任意多面体底上的领口拼接）。
- **M2 锥的径向分层：已证。** `ConeLayers.lean`：`hull{0,a,b}` 等于 `{αa+βb : α,β ≥ 0, α+β ≤ 1}`
  （`convexHull_zero_pair`）；按 `α+β` 切出的层等于四个缩放顶点的凸包（`coneCoeffSet_eq_convexHull`）。
  `StdConeLayers.lean`：在标准三角形 `stdCone` 上层是 `z.1 + z.2` 的切片，层内对角线 `σ' z.1 + σ z.2 = σ'σ`
  把它切成两个三角形，三者都是 H-多胞形，连续两层的并仍是一层（`stdConeLayer_union_consecutive`）。
  `LayerAffineMap.lean` 给出 `layerLowMap`、`layerHighMap`、`centralConeMap` 三族仿射映射及其顶点值；
  `ConeLayerMap.lean` 把一层的两块拼成一张 PA 映射并界定每块的像；
  `ConeAssembly.lean` 的 `exists_isPiecewiseAffineOn_stdCone_of_layers` 对层归纳拼出整锥上的 PA 映射：
  锥顶取指定值，外边按最外一对顶点值的仿射映射，两条径向边上等于顶点值在层参数处的折线，
  且每点的像落在所在层四个顶点值的凸包里。

- **M3 三角形相对一条边：已证。** `StdConeSector.lean` 把 `stdCone` 按过斜边的射线切成扇形
  `stdConeSector u u'`（五条线性不等式，H-多胞形），并给出把扇形线性地搬到 `stdCone` 的坐标
  `sectorCoord`（它保持 `z.1 + z.2`，故径向分层在扇形之间自动对齐），两条边界射线分别对应两条直角边。
  `ConeFan.lean`：
  - `exists_isPiecewiseAffineOn_stdConeSector`：把 M2 的锥映射搬到一个扇形上；
  - `exists_isPiecewiseAffineOn_stdCone_fan`：对扇形归纳拼接（相邻扇形只交于公共射线，
    两侧在射线上都等于同一条折线，故相容），得到整个三角形上的 PA 映射，斜边上恰是
    指定顶点值 `w (N+1) j` 的折线，每点的像落在所在格四个顶点值的凸包里，并记录该点所在的层与扇形；
  - `exists_isPiecewiseAffineOn_stdCone_fan_mapsTo`：若每个格的四个顶点值落在 `L` 的同一个闭单形里，
    则整张映射映进 `|L|`；
  - `exists_pos_forall_exists_isPiecewiseAffineOn_stdCone_dist_le`：**度量版相对逼近**。给定 `stdCone` 上
    的连续 `f` 与 `ε > 0`，先给出 `δ > 0`；此后任何网距 `< δ` 的角度分划与任何在分划点处与 `f` 相差 `≤ ε`
    的边界数据，都能扩成 `stdCone` 上的 PA 映射，在斜边上恰是指定折线，且处处与 `f` 相差 `≤ 2ε`。

这条路线**不需要**方形环带的径向参数化（那不是 PL 的），因为分层是按 `α+β` 的线性切片做的。

`DiskRelBoundary.lean` 的 `exists_pos_forall_exists_isPiecewiseAffineOn_stdCone_eqOn_boundary`
是**盘相对整条边界**的度量版：锥顶取三角形的直角顶点后，两条直角边就是径向边、斜边是角向边，
于是整条边界都由数据给定。给定 `stdCone` 上的连续 `f` 与 `ε > 0`，先给出 `δ > 0`；此后任何两个网距
`< δ` 的分划（径向 `σ`、角向 `u`）与任何在分划点处与 `f` 相差 `≤ ε`、且在三个顶点处彼此相容的边界数据，
都能扩成 `stdCone` 上的 PA 映射，在三条边上恰是指定的折线，且处处与 `f` 相差 `≤ 2ε`。

`ConeFanCarrier.lean` 与 `ConeStarCover.lean` 把这条结论搬进了 `|L|`：
- `exists_isPiecewiseAffineOn_stdCone_fan_carrierFace`：若每个格的四个顶点值都取在"承载该格像的开星"里，
  则拼出的映射把每点送进 `convexHull (carrierFace L (f z))`，从而映进 `|L|`；
- `exists_pos_forall_exists_vertex_image_subset_openStar`：`stdCone` 上的 Lebesgue 数（照
  `SimplicialApproximation.lean` 里的同一套 `continuousOn_iff'` + `lebesgue_number_lemma_of_metric`）；
- `eq_of_mem_openStar_of_vertex`：若 `y` 是 `L` 的顶点且 `y ∈ openStar L v`，则 `v = y`。
  这条是关键：它保证**在边界上 Lebesgue 选出的顶点就是 `f` 自己的值**，于是边界格与内部格的顶点值自动相容；
- `exists_pos_forall_exists_isPiecewiseAffineOn_stdCone_mapsTo_of_vertex_boundary`：
  **边界为单纯映射时的相对 PL 逼近**。`f` 在 `stdCone` 上连续且映进 `|L|`，先给出 `δ > 0`；
  此后任何网距 `< δ`、且在边界分划点处 `f` 取 `L` 顶点值的两个分划，都给出 `stdCone` 上的 PA 映射：
  三条边上是 `f` 在边界分划点处取值的折线（故当 `f|∂` 对该分划已是仿射时即 `Ψ = f`），
  每点的像落在 `convexHull (carrierFace L (f z))` 里，整体映进 `|L|`。

**之后还缺的**（按代价排序）：
1. **盘相对整条边界**（循环版）：把上面的扇形换成平面多边形绕内点的扇形 `hull{0, p_j, p_{j+1}}`，
   构造与相容性论证逐字相同（`sectorCoord` 换成 2×2 逆矩阵），只是"相邻扇形只交于公共射线"
   要作为假设由调用方验证。角度归纳的最后一步还要把扇形 `M` 与扇形 `0` 粘回去。
2. **一般边界数据（非单纯）的 `|L|` 版**：上面那条要求边界分划点处 `f` 取顶点值。
   若只假设 `f|∂` 是 PA 而非单纯，混合格（两角是给定的边界点、两角是选出的顶点）就没有公共单形，
   这正是 Zeeman 1964 相对单纯逼近定理的难点，标准解法是先取 `K₀` 的导出邻域再在领口上插值。
   目前的 M1（乘积相对一端）加上述结论应该够走这条路，但需要把导出邻域的柱形结构接上。
3. **搬到任意 PL 三角形：已证。** `TriangleRelBoundary.lean` 的
   `exists_pos_forall_exists_isPiecewiseAffineOn_triangle_eqOn_boundary`：对任意仿射无关的
   `v : Fin 3 → E`，在 `convexHull ℝ (range v)` 上给出同一条结论，三条边写成
   `AffineMap.lineMap (v 0) (v 2)`、`lineMap (v 0) (v 1)`、`lineMap (v 2) (v 1)` 的参数化。
   证明用 `triangleAffineMap` 与 `IsPLHomeomorphOn` 的 `invFunOn` 分支把 `stdCone` 版本搬过去。

## 四条车道 2026-09-17 的交付（整合分支已合入并逐模块重编）

- **F（`codex/moise-smoothing`）**
  - `LocallyPolyhedralImage.lean`：局部多面体性经 PL 同胚搬运（§32 要把 `IsLocallyPolyhedral (U \ P)`
    在图卡间搬运）。
  - `ArcChainCover.lean`：紧致 PL 弧的从属链覆盖（参数化 + Lebesgue 数 + 均匀分划）。
  - `ModelSlide.lean`：标准模型里沿分支滑出的显式 PL 自同构（`slideMap`），双射、支撑在盒内、
    实际把一条模型带滑离另一条。
  - `ChartSlide.lean`：经图卡共轭成环境自映射，保持逐片仿射、单射、支撑外恒等与分离。
  - 更正了一条早先的分析：**横向推移不能分开两条相交的带**（显式反例），触边分支靠沿分支滑出，
    圆分支在书里本来就不走分离而走内盘替换。
- **S（`codex/moise-s`）** `BallCyclePair.lean`：一般循环分解（任意 ≥3 个 PL 三球，循环相邻交为二维盘、
  非相邻不交、无三重交）给出两球判据的实际数据 `A, B, D₀, D₁`。这闭合了 C.6 三项遗留义务的第一项。
- **H（`codex/moise-h`）** `ConeEuler.lean`：锥的组合 Euler 数恒为 1；沿 PL 圆封盘使 Euler 数加一。
  这是 §33 Lemma 12 里"逐分支封 PL 盘"的 Euler 记账层（G.5 的窄生产者之一）。
- **E3（`codex/moise-e3`）** `BranchSignChain.lean`：沿图卡链的横向侧选择恒可解（`ZMod 2` 部分和），
  循环情形的障碍恰是 `∑ τ ≠ 0`。配合 F 的更正，这给出触边弧情形可行、圆情形不走这条路的确切理由。

四条车道都先合入了整合分支的相对逼近层（`ConeAssembly` → `ConeFan` → `DiskRelBoundary` →
`TriangleRelBoundary`、`ConeFanCarrier`、`ConeStarCover`）。

### 细分使有限多个点成为顶点（以及为什么它不直接去掉顶点假设）

`SubdivisionVertices.lean` 的 `exists_isSubdivision_forall_singleton_mem`：对有限复形 `K` 与
`K.space` 中任意有限多个点，存在 `K` 的细分 `K'`，`K'.space = K.space`，且每个点都是 `K'` 的顶点。
证明把 `exists_isSubdivision_subcomplexes` 用在单点多面体族上，再由"面落在单点集里且非空"推出该面就是该单点。

它**不能**直接去掉 `ConeStarCover` 那条端点里的"边界分划点处 `f` 取 `L` 顶点值"假设：那条定理的 `δ`
由 `L` 的开星覆盖的 Lebesgue 数给出，而细分 `L → L'` 会让开星变细、`δ` 变小；新的分划又产生新的边界值，
于是又要再细分 `L`。这个循环没有单调性保证收敛。真正的困难仍是混合格（两角是给定边界值、两角是选出顶点）
不一定张成同一个单形，即 Zeeman 1964 的那一步；标准解法是先取子复形的导出邻域再在领口上插值。

### 任意三角形相对整条边界、映进 `|L|` 的相对逼近

`TriangleComplexBoundary.lean` 的
`exists_pos_forall_exists_isPiecewiseAffineOn_triangle_mapsTo_of_vertex_boundary`
把 `ConeStarCover` 的 `stdCone` 版本经 `triangleAffineMap` 搬到任意仿射无关三点张成的三角形上：
`f` 在三角形上连续且映进 `|L|`，先给出 `δ > 0`；此后任何两个网距 `< δ` 的分划、且在三条边的分划点处
`f` 取 `L` 顶点值，就给出三角形上的 PA 映射 `Ψ`，三条边上是 `f` 在那些点取值的折线
（故 `f|∂` 对该分划仿射时 `Ψ = f`），且处处 `Ψ x ∈ convexHull (carrierFace L (f x))`，
从而 `MapsTo Ψ T L.space`，并且 `Ψ` 到 `f` 的直线同伦整个落在 `|L|` 里。

这条是"不妨设某映射是 PL 的"在二维带边界情形的实际生产者（边界已是单纯映射时）。

## 2026-09-18 第二轮：滑距不受限，于是分支只需一张乘积邻域

### F：`ModelSlideLong.lean` / `ChartSlideLong.lean`

把前一轮固定滑距 1 的模型按滑距 `d` 与锥度半径 `R` 参数化：
`slideAmountLong d R = max 0 (min (d * (1 - |y| - |z|)) ((R - |x|)/2))`，
`slideMapLong d R p = (p.1 - slideAmountLong d R p, p.2.1, p.2.2)`。

- 单射性只用到"锥度对 `x` 是 (1/2)-Lipschitz 而宽度因子不含 `x`"，与 `d` 无关；
  故**滑距可以任意大，代价全在锥度半径**：`disjoint_slideMapLong_image_slideBandA` 的定量条件是
  `0 ≤ d`、`c + 2*d ≤ R`、`c - d < a`。
- `slideMapLong` 只动第一坐标，所以 `bijOn_slideMapLong_prod` 给出：任意
  `T ⊆ ℝ × ℝ` 对应的 `{p | p.2 ∈ T}` 被双射保持。取半空间或其边界平面即得端点处
  "滑动与 `Bd M` 相切"，不必另造半空间模型。
- `ChartSlideLong.lean` 把它经 PL 图卡共轭：整体逐片仿射、整体单射、支撑外恒等、分离两条带的像。

**这改变了 E3 §44 的计划**：既然滑距无上界，就不需要把有限多张 crossing 图卡沿分支排成链、
再在重叠上插值；只要分支有**一张沿弧的乘积邻域**，一次滑动即可清掉整条触边分支。
下一步的正确目标因此是乘积邻域（沿弧的相容平凡化），而不是逐张图卡的同向推移。

### H：`CapDeletion.lean`

把封盘复形的面集等式翻成载体等式（`capComplex_space`、`space_inter_coneComplex_space`、
`capComplex_space_sdiff_coneComplex_space`），再消费 `SphericalDiskComplement.lean` 现成的
`IsPLSphere.isPLBall_closure_sdiff`，得到删盘识别
`isPLBall_space_of_isPLSphere_capComplex`：封盘后是 PL 2-球面时，原曲面是 PL 2-球（盘）。
唯一额外前提是 `A.space ⊆ closure (A.space \ L.space)`（曲面是它去掉边界圆后的闭包），
按车道规矩写成显式前提；它的组合 2-流形版生产者尚未写。

### H：`ManifoldInteriorDensity.lean`（去掉上面那条密度前提）

`IsCombinatorialManifoldWithBoundary.space_subset_closure_sdiff_space`：若 `L.faces ⊆ K.faces`
且 `L` 的每个面至多 `n` 个顶点，则 `K.space ⊆ closure (K.space \ L.space)`。
证明用既有的**纯性** `exists_face_superset_card_eq`：任意点落在某面的开单形里，把该面扩成
`n+1` 顶点的顶面 `t`，由顶点数 `t ∉ L.faces`，于是 `openSimplex t ⊆ K.space \ L.space`，
再用 `convexHull t ⊆ closure (openSimplex t)`。对一般 `n` 成立。

于是 `isPLBall_space_of_isPLSphere_capComplex_of_isCombinatorialManifoldWithBoundary`
把删盘识别的假设换成 `IsCombinatorialManifoldWithBoundary 2 A`，不引入其他新假设；
`L` 的顶点数界由已有的 `IsPLSphere 1 L.space` 免费给出。G.5 的封盘—删盘这一整段因此闭合，
只剩不经 `HurewiczLowDegrees` 的一维 Hurewicz 桥（H 已给出 HB1–HB6 的成本分解，未启动）。

### F：`BranchSlideSeparation.lean` / `TransversePlaneCoordinates.lean`

`IsBranchSlideChart R c a b P Q e`（七个字段：两向逐片仿射、`slideSupportLong R` 与两条带都含于
`e.target`、两张片分别等于 `e.symm '' slideBandA c` 与 `e.symm '' slideBandQ a b`）把"一张沿整条分支
平凡化 crossing 的 PL 图卡"打包成谓词。谓词里**不含滑距 `d`**——滑距由消费者按 §19.110 的定量条件选。

- `exists_supported_separation_of_isBranchSlideChart`：在 `0 ≤ d`、`c + 2*d ≤ R`、`c - d < a` 下给出
  §44 要的 `h`（整体逐片仿射、单射、支撑外恒等、`Disjoint (h '' P) Q`），见证就是
  `e.conjugateMap (slideMapLong d R)`。
- `exists_supported_separation_of_isBranchSlideChart_boundary` 追加 `h '' (U ∩ B) ⊆ B`，
  即 §44 的 `h (U ∩ BdM) ⊆ BdM`；走更一般的 `mapsTo_chartSlideLong_of_forall_mem_iff`
  （任何在图卡里由两个横向坐标条件切出的集合都被保持）。
- `TransversePlaneCoordinates.lean`：从 `HasPLCrossingAt` 实际携带的数据（两张平面 `finrank = 2`、
  交线 `finrank = 1`、张成全空间）造出 `E ≃ₗ[ℝ] ℝ × ℝ × ℝ`，把两张平面送到两个坐标平面、
  交线送到第一坐标轴（滑动方向）。

**剩下的确切输入**（缺的是定理，不是装配）：紧 PL 弧 `S`、沿 `S` 横截相交的两张 PL 面片 `A`、`B`、
`W ∈ 𝓝ˢ S`，要一张 `e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ)`，满足 `S ⊆ e.source ⊆ W`、两向 PL、
`e '' (A ∩ e.source) ⊆ {p.2.2 = 0}`、`e '' (B ∩ e.source) ⊆ {p.2.1 = 0}`，并且 `e.source` 不碰第三张片
（最后这条正是 §44 那句"不产生邻近的新交线"的来源，属于生产者而非滑动）。
把两张相邻的逐点平凡化粘成一张需要 **PL 球对的正则邻域唯一性（相对 Alexander trick）**；
本树只有单复形、非相对、非配对的版本（`ConeExtension`、`ConeAmbientExtension`）。
`exists_subordinate_chain_of_isPLBall_one` 不关联任意两张图卡，`exists_sideChoice_of_chain` 是
`ZMod 2` 陈述、产不出 PL 同胚，二者都不足以补这个缺口。

另有一条小义务：上述三条活在有限维赋范环境、结论是 `IsPiecewiseAffineOn h univ`，
而 E3 的消费者要带图卡的 3-流形与 `IsPL 3 3 h`；路线机械（经
`ℝ × ℝ × ℝ ≃ EuclideanSpace ℝ (Fin 3)`、用 `bijective_slideMapLong` 升成 `Homeomorph`、
再用既有的 `isPL_conjugateHomeomorph`）但未做。

### E3：`BranchSlideConjugation.lean` / `BranchSeparation.lean`

`NormalSingularCellData.exists_separated_along_branch` 以乘积图卡为显式前提，给出 §44 的输出条款
（`IsOpen U`、`branchCarrier cb ⊆ U`、`closure U ⊆ W`、`IsPL 3 3 h`、单射、`EqOn h id Uᶜ`、
`MapsTo h U U`、边界条款、`Disjoint (h '' (D '' P)) (D '' Q)`）。走**两步共轭**：
外层是流形图卡 `M → EuclideanSpace ℝ (Fin 3)`，内层是矫直到 `ℝ × ℝ × ℝ`，因此不需要两个模型之间的线性桥。
为此把 `isPL_conjugateHomeomorph` 推广成 `isPL_conjugateMap`（任意逐片仿射自映射，不要求 `Homeomorph`——
`slideMapLong` 只知是连续双射），并把 F 的两条图卡引理推广到任意拓扑源
（`OpenPartialHomeomorph.injective_conjugateMap`、`disjoint_conjugateMap_image`）。

`exists_separated_cell_along_branch` 给出 `IsPLOn 2 3 g D.domain`、局部单射、纤维至多二、
支撑外纤维不变，以及**双点集等式的两个方向**
`doublePointSet g D.domain = doublePointSet D D.domain \ branchCarrier cb`，其中
`g = P.piecewise (h ∘ D) D`。"不产生邻近的新交线"那一半由分离条款加 `MapsTo h U U` 得到。

**§44 的两处陈述错误被查出并改正**：
1. 分离条款里的 `Q` 必须是第二条细带而非贴合余片；取余片时结论恒假，因为缝 `P ∩ Pc` 被 `h` 固定、
   同时落在两个像里。贴合改用 `P` 与另设的 `Pc`，`P ∪ Pc = D.domain`。
2. 把定位写成 `D '' P ⊆ E.symm '' (e.symm '' slideBandA c)` 使假设自相矛盾：由 `0 ≤ d`、`c + 2*d ≤ R`
   得 `slideBandA c ⊆ slideSupportLong R`，于是 `D '' P ⊆ W`，与"缝的像避开 `W`"合起来强迫
   `P ∩ Pc = ∅`。定位只能约束支撑上方的部分。同理，消费 F 的 `IsBranchSlideChart` 时要注意
   `sheet_eq` 是等式，不能把那个 `P` 当作贴合条带。

**边界端点的保持性未解决（更正前一条记录）**：F 的 `mapsTo_chartSlideLong_boundary` 只对**平行于分支**的
边界成立（`{p | p.2 ∈ T}` 是平行于滑动方向的直线之并）。而 `HasPLBoundaryCrossingAt` 在端点把双点线放成
**横截于 `Bd M`**：取 `Bd M = {x = 0}`、`M = {x ≥ 0}`，`slideMapLong d R (0, y, 0)` 的第一坐标是
`-max 0 (min (d(1-|y|)) (R/2)) < 0`（`|y| < 1`），点被推出 `M`。需要端点处锥度降到零的模型，或两步构造。

### S：从多边形的收缩到邻域的相容定向（义务 3）

七个模块把 24.12 需要的"收缩 ⟹ 邻域可定向"搭成一条完整证明链，剩下的都是显式假设：

- `CocycleMonodromy.lean`：`SimplicialBoolCocycle.walkMonodromy` 定义在**既有的**
  `SimplicialComplex.edgeGraph` 上（没有新造图），带 `_cons`/`_append`/`_reverse`，
  并给出双向刻画 `isCoboundary_iff_forall_walkMonodromy_eq_zero`。
  E3 的 `BranchSignChain` 是被复用而非重证：`loopMonodromy_eq_zero_of_isCoboundary` 即
  `sum_sideJump_eq_zero_of_cycle`，`not_isCoboundary_of_loopMonodromy_ne_zero` 即
  `not_exists_sideChoice_of_cycle`。
- `PolygonNeighborhoodOrientation.lean`：`isOrientable_iff_forall_walkMonodromy_eq_zero`，双向。
- `SimplicialWalkHomotopy.lean`：边路同伦（回溯与二维单形移动）；三角形那一步恰是上圈条件本身。
- `CocycleWalkLift.lean`：真正的提升。`walkPath` 把走化成折线路径，`exists_walkLift` 用既有的
  `coveringEdgeLift`、`coveringNeighbor_side` 拼接，再用 Mathlib 的 `eq_liftPath_iff'` 与
  `liftPath_apply_one_eq_of_homotopicRel` 得到 `walkMonodromy_eq_zero_of_homotopic_refl`：
  在 `K.space` 中零伦的闭边路单值为零。
- `SubcomplexOrientationCocycle.lean`：局部化桥，完全用公开 API 补上（关键是
  `carrierFace_eq_of_faces_subset`），未动 `OrientationCocycle.lean` 的私有引理。
- `AmbientPolygonOrientation.lean`：端点 `isOrientable_of_ambient_nullHomotopic_polygon`——
  `L` 是环境 `K` 的子复形，`barycentricSubdivision L` 的闭边路在**环境空间**里零伦，
  加生成假设，给出 `IsOrientable n L`。

剩余义务：生成假设 `hgen`（多边形生成邻域的单值）要正则邻域向核的形变收缩；
`Fin` 循环族与 `Walk` 两种表示未互译（`NeighborhoodCycle` 交来的多边形需手工转成闭走）；
多边形与其收缩本身由 24.12 提供。义务 2（无扭盘丛分类）未动。

## 2026-09-18 晚：可行性复盘与两项决定

当日整合分支自 `0ec8fc1a4` 起 202 个 commit、77 个新 Lean 模块、约 1.34 万行，全部落在 25.1 的 L2
（触边分支分离：F 图卡层 + E3 月牙 + H 球对/弧链）、30.7 的输入 C.6（S）与侧向输入 G.5（H）内部；
主链 `Moise2xx/3xx` 结点本日无一被证出。主链 15 结点开 13，其中三个卡在决定而非数学：

1. **30.5 的 `TopologicalCellComplementConnected`**（wild 球面的 Alexander 对偶，H-M3 估 10k–18k 行，未批）。
   决定：先派只读核查——30.5 在主链上的每个消费者是否都能用 tame（多面体/双领口）胞腔版本满足；
   若能，则改造消费者而非实现对偶。结果回写本文件。
2. **§33 的一维 Hurewicz 桥**：材料在 `origin/codex/pc-sorry-free`（七文件 2629 行、无 `sorry`），
   闭包 163 文件约 4.56 万行不在 Moise 分支。实测：merge-base `806b541e9`（2026-09-11），双侧改动仅 3 文件
   （均在 `PlanarJordan/`），dry-run 2 个冲突；对方分支 `PiecewiseLinear/` 为 0 文件，597 个 PL 模块不受影响。
   决定：在专用分支 `codex/moise-hurewicz-merge`（工作树 `D:\differential-geometry-moise-hw`）合并、
   只编译七文件的传递闭包与 `PlanarJordan` 的 PL 消费者、做跨车道 `#print axioms`，通过后再并入整合分支。
3. **§31/§32 的定义层**未陈述；§32 是全书唯一无穷构造。待 L2 与 C.6 闭合后再开。

车道调整：S 继续到 C.6 闭合（最近的主链推进）；H 继续弧链（25.1 L2 关键路径）；E3 做完 `D₂` 后转
**L₂ 重贴胞腔的 §43 障碍**（25.1 上唯一没动过的硬点）；F 做完 F5.2 共享前置后转 **26.4 的相对子复形细分**。

当日过程事实：各车道自我更正约十次，其中四个曾报"已关"的项被查出空或不可满足
（`hgen` 等价于自身结论、`IsGeneratedByPolygon` 在 ℕ 上不可满足、`hJoff` 强迫空交、`hfiber` 对盘形片恒假）。
自此每个端点的收尾要求同时做两项审计：假设是否扛着结论、假设在目标实例中是否可满足。
2026-09-18 追加第三项（H 在 `exists_chart_two_sheets_of_transverse_vertex` 上查出，F 已按 (β) 修）：结论形如 `∃ x, … ∧ (hyp x → …)` 时，检查消费者能否对被存在量词藏住的那个 `x` 实际供给 `hyp x`；供不了就把 `hyp` 提到顶层假设、把 `x` 变成参数，见 HANDOFF_CODEX_F §19.143。
"便宜箭头"名单只剩 25.2←25.1 与 26.4←25.2+26.3，且后者已确认需要树里没有的相对子复形细分。

### 2026-09-18 晚：边界分支的"滑动 + 月牙"路线作废，改回经典切贴（决定）

E3 的 `LuneCell.lean`（`exists_lune_base_off_graphArc`）证明：月牙在参数 `s` 处的底点映到弧的**滑动前**位置；
在边界分支端点那是 `(0,0,0)`，同时也是余片一点的像。原因是结构性的：`slideMapFwd` 沿**分支方向**推 `P`，
任何把 `P` 的边界弧扫回 `Bd M` 的 2-胞腔都要经过 `{(t,0,0) : 0 ≤ t ≤ d}`，即分支线本身（落在 `D '' Q` 内）。
至少角点 `(0,0,0)` 重新成为双点，而它在 `branchCarrier` 中，故 `hgdouble` 一贴月牙即被破坏；换 `B`、抬底、
缩弧三种修补均不成立或只移动角点（§79）。**结论：对触边分支，"环境滑动 + 修复边界"不可能同时保持
`Bd D ⊆ Bd M` 与分支删除。** 滑动机制、`PlanarGraphRegion`（其中"`0 < a` 于 `Ioo 0 1`"是必要条件）与
四个字段生产者作为定理仍正确，保留。

改走书上 Case 3/4 的经典切贴：`α ∪ α'` 把源盘切成 `A`、`C`、`B`，`D₁ := A ∪ B` 沿 `α ≅ α'`（分支恒等）
粘合、映射不变；`C` 闭合为环带或莫比乌斯带（Case 3/4 二分，四弧字已编码）。于是 `Bd D₁ ⊆ Bd M` 自动成立、
分支不再是双线、无需环境映射。粘合引擎为 `LoopTheorem/CellGluing.lean:375`。
待核：§43 所记"顺序交叉贴合保留分支"的构造取的是"第一次缝与第二次缝各一个原像"（`HANDOFF_CODEX_L.md` §43），
即把三块并成**一个**带两条缝的胞腔；若确认，则该障碍是输出形状造成，`A ∪ B` 与 `C` 分开即可通。

## 2026-09-18（F）：26.4 的相对子复形细分——定案、反证、`Moise264` 结论缺一条

- 26.4 消费的是**限制形**（`K'` 细分 `K` 且 `restrict K' L.space` 细分 `L`，网格任意小）：
  `IsSubdivision.restrict` + `exists_isSubdivision_diam_lt`，现打包为 `SubcomplexMesh.lean` 的
  `exists_isSubdivision_diam_lt_restrict_isSubdivision`。理由：`Moise264` 的假设是基本群元，边界环路由我们选，
  只须留在 `|L|` 里且同伦于代表，所以上面第 314 行要求的"逐点相等"不必要；环带路线 (b) 的棱柱格子四顶点值
  同在 `L` 的一个闭单形里，靠的正是"细边落在粗边里"这条限制形。
- 上面第 327 行的出路 (a)（`L` 固定、`L` 外的面全小）**为假**：只要 `L` 有一个面在 `K` 里有真余面，
  `ε ≤ diam τ` 时不存在这样的细分——`not_exists_isSubdivision_faces_subset_forall_diam_lt`。
  第 362 行"迭代 `relDerived` 不会变小"由此升级为"任何构造都不行"。
- **`Moise264` 的结论少了 "Bd Δ 在 M² 中不可缩"**：按现有陈述，一张推离 `S` 的小盘（26.3 的双领域里取
  在 `∂σ` 上为零的 PL 高度函数的图）就满足它，30.4 无法消费。它尚未被消费，改陈述即可。
细节与 26.4 仍缺的四件事见 HANDOFF_CODEX_F §19.144。
### 2026-09-18 晚：30.5 不需要 wild 球面的 Alexander 对偶（只读核查结论）

书中 Theorem 30.5 全书**只被引用一次**：§34 Lemma 3（p. 240）。那里交给 30.5 的胞腔是 `C₁' = h(C₁)`、`C₂' = h(C₂)`，
`C₁, C₂ ⊆ U` 是 2-单形 `σ` 的**多面体** 3-胞腔邻域、`h : U → ℝ³` 是**开集**上的嵌入（§34 开头的归约 = 计划 A.1），
所以 `frontier C₂'` 是双领口的，wild 情形从不出现。30.5 的证明重构（本文件"更正：30.5 ← 30.4"一节）只需 `C₂` tame，
`C₁` 可保持任意拓扑胞腔。

而**双领口情形在树里已是无条件定理**：`TubularExcision.lean:170 hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1`
+ `SphereH1.lean:189 isZero_integerSingularHomology_sphereTwo_one`（无假设，Mayer–Vietoris）+ `JordanBrouwer.lean:28`，
纯拓扑、不要光滑性；核查者用一个 scratch 文件实际编译并审计（只含三条标准公理）。另有
`VanKampen/TwoSidedCollarSeparation.lean:246` 给"补集至多两个分支"、不要同调，且避免了树里没有的 `SphereTwo ≃ₜ frontier C` 参数化。
**H-M3 评估已过时**：它只查了 `DualityAssembly`/`SpecializedDuality` 那支（确需光滑 + 循环），漏了 `TubularExcision → BicollarCertificates`。

拟定受限陈述（不改 `MoiseChain.lean`）：`IsBicollared S := ∃ Φ : S × ℝ → ℝ³, IsOpenEmbedding Φ ∧ ∀ x, Φ (x,0) = x`；
`BicollaredCellComplementConnected`；`Moise305Tame` 在 30.5 的假设上加 `IsBicollared (frontier C₂)`。
§34 L3 侧要生产的每一步材料都在（`PolyhedralSurfaceComplement.lean:29`、`BicollarManifold.lean:135`、
`InvarianceOfDomain.lean:346/508`），只缺"拓扑胞腔在同胚下的 `frontier`/`interior` 桥"（H-M3 原也列为 0.5k–1k）。
修正估计 **约 1k–2k 行**（未原型化），原 10k–18k 作废。30.5 仍等 30.4（I.4，4k–6k，等 26.4）；本核查只移除了较大的那个阻塞。
一般（wild）版 `TopologicalCellComplementConnected` 仍在原成本之外，但 Moise 链不需要它。

### 2026-09-18 晚：L₁ 早已存在；边界分支的整条滑动链无实例；L₂ 改走"交叉重贴 + 横向楔推"（决定）

E3 核对后三条事实（`HANDOFF_CODEX_L.md` §80–§81）：

1. **`A ∪ B` 就是 `L₁`，且早已完整交付**：`CutAndPaste.lean:1373 exists_boundary_surgery_cell_of_boundaryBranch`
   （`Bd D₁ ⊆ Bd M`、双点集等式、`Nonempty (NormalSingularCellData G BdM B)` 五字段、边界字 `σ.trans ω`）与
   `:2425 …_with_simplicialComplexity_lt`（严格下降）。§43 所记"重贴保留分支"的构造是把三块并成一个带两条缝的胞腔
   （`:1214`），那是关于像的真陈述，与 `A ∪ B` 无关。本文件上一条要 E3"重新审视经典切贴"的指示是多余的——它已经在树里。
2. **§46–§73 的滑动链对边界分支无实例**：由 `map_boundary`，边界分支是两端点都在 `BdM` 的多面体 1-球；
   `hSK + hA + hB + hinjP + hinjQ + hPcQ + hW` 把每个分支点放到图卡轴上，`hBdE/hBd₁` 又令 `BdM = {p.1 = 0}`，
   轴与之只交于一点，故两端点重合。那些定理是正确的条件式，但**路线为空**。根源是一端的边界模型 `{x = 0}`
   被当成了整条分支的边界模型；两端都在 `BdM` 的弧不可能落在横截 `BdM` 的直线上。
3. **`L₂` 的真正路线**（书上第二个半步）：交叉重贴（已有 `:1214`）后，把两条缝各自**横向楔推**进开象限
   `(0, ε, ε)` / 反向，推移**无 `p.1` 分量**，故 `Bd M` 逐点保持——这就是边界环的"8 字"光滑化，不需要任何边界修复。
   形状是 `P'.piecewise (ψ₊ ∘ G) (ψ₋ ∘ G)`；新义务是楔推版的 `doublePointSet G' = doublePointSet G \ branchCarrier`。
   §19.107 的反例（两张**平**带无法横推分离）不适用：重贴后每条缝两侧是一张**折**片、占两个相邻象限，楔推可分。

决定：采纳 3。阻塞接口改为**板状图卡**：沿整条分支的乘积邻域中两张片是坐标平面、`M` 是板 `{0 ≤ x ≤ c} × ℝ²`、
`Bd M` 是两个端面 `{x = 0}` 与 `{x = c}`（F 的 `TransversePlaneNormalForm` 在两端各用一次 + F 的链 + H 的球对）。
滑动机制（`ModelSlide*`、`ChartSlide*`、`BranchSlide*`）保留为已证基础设施，但不在主链路径上。

## 2026-09-18 Codex: essential boundary in the extended loop theorem

`Moise264` now requires that the inclusion of `r '' stdSimplexBoundary 2` into
`S` is not `ContinuousMap.Nullhomotopic`. The boundary inclusion proof is an
existential typing witness already implied by the preceding intersection equality;
it is not an additional geometric hypothesis. This records essentiality of the
produced boundary, without requiring that it represent the particular input `g`.
The theorem itself remains unproved. There were no source importers or consumers
of `Moise264` at the time of this correction.

After root registration and the owner-authorized required headers were added, the
changed module compiled with the standard syntax linter set, explicit header and
long-line checks, and no diagnostic output. Its exported definition was inspected,
and the default environment linters
were checked with only `docBlame` and `docBlameThm` excluded. These are local checks
against the current imported objects, not a fresh certification of the entire
integration source dependency graph.
