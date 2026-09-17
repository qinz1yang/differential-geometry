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
| 26.4 | 扩展环定理（193） | `Moise264` ✔已陈述 | 开。用 25.2 与 26.3 双领（S 已交付） |
| 30.4 | 球壳定理（216） | `Moise304` ✔已陈述 | 开。用 26.4、23.8、26.1（S 已证）、28.19、28.20（H 已证）、30.3 |
| 30.5 | 嵌套拓扑 3-胞腔（216） | `Moise305` ✔已陈述 | 开。**箭头便宜**：书上从 30.4 五行推出 |
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
`hasTwoComplementComponents_of_alexanderDualityH0Certificate` 给出了这个结论，但条件于一个 `H₀` 证书，
只对标准球面无条件成立。把该证书对任意拓扑 2-球面证出来，就是 Alexander 对偶的一个实例，属于同调侧的工作。

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
  `Topology/SphereSeparation/JordanBrouwer.lean` 有条件于 `H₀` 证书的版本，把证书对任意拓扑 2-球面证出来即可。

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

全部只依赖标准三公理。

**还缺的一步**（写 `Moise252 ← Moise251` 时会立刻撞上）：`loopCircle ≃ₜ |J|` 这个参数化本身。
树里 `LoopTheorem/CellGluing.lean` 用 `pathToCircle` 加紧致到 Hausdorff 的连续双射造过
`loopCircle ≃ₜ frontier P`（约 155 行），`NormalSystem.boundaryParam` 也是这个类型。
所以材料在，只是还没有"任意 PL 1-球面都能这样参数化"的独立陈述。这条很短，值得单独补。
