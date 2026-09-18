# HANDOFF — lane T（tame 30.5）

分支 `codex/moise-tame305`，worktree `D:\differential-geometry-moise-t`，基点
`origin/codex/moise-integration`（`7b0f92ac1`）。本车道把 Moise 30.5 从"任意拓扑 3-胞腔"
收窄到"外胞腔边界双领口"，因为主链上唯一的消费者 §34 Lemma 3 只会喂进
`h '' P`（`P` 多面体 3-胞腔、`h` 为开集上的嵌入），其边界必然双领口。

验证方式：`.lake/scratch/tools/check-f.ps1`（聚焦检查，写共享 olean）与
`.lake/scratch/tools/audit-f.ps1`（`#print axioms`，不写任何工件），两者的 `$root`
已改指本 worktree。每次编译前检查全局 `lean.exe` 数 < 4。新模块一律不登记进根聚合文件。

## T.1 — 双领口边界的紧集补集连通（done）

`DifferentialGeometry/Topology/BicollaredComplement.lean`

- `IsBicollared (S : Set X) : Prop := Nonempty (ThreeManifold.TwoSidedCollar (Subtype.val : S → X))`
  ——字面就是既有 `TwoSidedCollar` 层的存在性，故 `VanKampen/TwoSidedCollarSeparation.lean`
  与 `Manifold/BicollarComponents.lean` 的全部引理直接适用，无需任何改写。
  `isBicollared_iff_exists_isOpenEmbedding` 给出等价的显式形式
  `∃ Φ : S × ℝ → X, IsOpenEmbedding Φ ∧ ∀ x : S, Φ (x, 0) = x`。
- `compl_frontier_eq_interior_union_compl`：`C` 闭 ⟹ `(frontier C)ᶜ = interior C ∪ Cᶜ`。
- `compl_eq_negativeSide_or_positiveSide_of_isBicollared_frontier`：在
  `[T2Space X] [ConnectedSpace X] [LocallyPathConnectedSpace X]`、`C` 闭、`frontier C`
  紧且连通、`interior C` 与 `Cᶜ` 非空之下，`Cᶜ` 恰等于领口的一侧。
- `isConnected_compl_of_isBicollared_frontier`：同样前提下 `IsConnected Cᶜ`。

关键点：只用到 `TwoSidedCollarSeparation.lean:434`
`complement_eq_negativeSide_union_positiveSide`（"补集至多两个分支"），它**不需要**
`SimplyConnectedSpace X`，也不需要任何同调；`negativeSide`/`positiveSide` 的连通性来自
`BicollarComponents.lean:137/141`，只要 `[Nonempty S]`。因此本层完全避开了
`SphereTwo ≃ₜ frontier C` 参数化（树中不存在）与 Alexander 对偶。

聚焦检查 exit=0、7.8 秒、零 warning；`AuditT1` 五项仅 `propext`、`Classical.choice`、
`Quot.sound`。

注意 `compl_eq_negativeSide_or_positiveSide_of_isBicollared_frontier` 的结论提到
`h.negativeSide`，而后者要求 `[Nonempty ↥(frontier C)]`，故该实例写成绑定式实例参数，
调用方先 `haveI := hfrconn.nonempty.to_subtype`。

## T.2 — 拓扑不变域桥：开集上嵌入的像的内部与前沿（done）

`DifferentialGeometry/Topology/OpenEmbeddingFrontier.lean`（对任意有限维实内积空间 `E`）

- `isOpen_range_of_isOpen_subtype`：开集上的连续单射（子类型形式）的像开。
  由既有 `InvarianceOfDomain.lean:508` 取 `I := modelWithCornersSelf ℝ E`、`M := E` 得到；
  `[HasInvarianceOfDomain E]` 实例来自 `FixedPoint/Brouwer.lean:216`，故本模块 import 它。
- `isOpen_image_of_subset_of_injOn`：`InvarianceOfDomain.lean:346` 的直接特化。
- `interior_image_eq_image_interior`：`U` 开、`f` 在 `U` 上连续单射、`P ⊆ U` ⟹
  `interior (f '' P) = f '' interior P`。难的一半（`⊆`）用
  `ContinuousOn.isOpen_inter_preimage` 造出 `U ∩ f ⁻¹' interior (f '' P)`，再用 `InjOn` 证它落在 `P` 内。
- `image_sdiff_interior`（纯集合论，已 `omit` 掉内积与有限维）、
  `frontier_image_eq_image_frontier`：再加 `IsCompact P` ⟹ `frontier (f '' P) = f '' frontier P`。
- `closure_interior_image_eq_image`：再加 `closure (interior P) = P` ⟹
  `closure (interior (f '' P)) = f '' P`。`P` 是 PL 3-球时该前提由
  `PiecewiseLinear/BallFrontier.lean:60` `IsPLBall.closure_interior` 提供。
- `interior_range_eq_image_preimage_interior`：`A` 紧、`g : ↥A → E` 连续单射 ⟹
  `interior (range g) = g '' (val ⁻¹' interior A)`。这条是拓扑胞腔那一半要的形式：
  `g` 由紧致性升为闭嵌入，`IsEmbedding.toHomeomorph` 给出 `↥A ≃ₜ ↥(range g)`，
  把 `interior (range g)` 拉回 `A` 内再用一次不变域，排除"边界点成为内点"。

树中原有的 `Geometry/Boundary/EmbeddingFrontier.lean` 是**光滑**版本
（`ContMDiff` + `mfderiv` 单射），对拓扑同胚不可用；本模块是它的拓扑对应物。

聚焦检查 exit=0、11.2 秒、零 warning；`AuditT2` 七项仅标准三公理。

## T.3 — 拓扑 3-胞腔的紧致性、内部、前沿（done）

`DifferentialGeometry/Topology/ClosedBallImage.lean`（对任意有限维实内积空间 `E`）

设 `φ : ↥C ≃ₜ ↥(Metric.closedBall (0 : E) 1)`。注意 `MoiseChain.lean:61` 的
`IsTopologicalCell n C` 按定义就是 `Nonempty (↥C ≃ₜ ↥(closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))`，
所以本模块的每条结论对 `IsTopologicalCell` 直接可用，且**不必** import `MoiseChain.lean`。

- `closedBallParam φ : ↥(closedBall 0 1) → E := fun b => (φ.symm b : E)`，配套
  `continuous_closedBallParam`、`injective_closedBallParam`、`range_closedBallParam`（`= C`）。
- `isCompact_of_homeomorphClosedBall`、`isCompact_frontier_of_homeomorphClosedBall`。
- `interior_eq_image_of_homeomorphClosedBall`：`interior C = closedBallParam φ '' (val ⁻¹' ball 0 1)`。
  由 T.2 的 `interior_range_eq_image_preimage_interior` 加 `interior_closedBall` 得到；
  这一条同时给出"球面上的点不会成为 `C` 的内点"，是不变域真正用力的地方。
- `frontier_eq_image_sphere_of_homeomorphClosedBall`：`frontier C = closedBallParam φ '' (val ⁻¹' sphere 0 1)`。
- `isConnected_frontier_of_homeomorphClosedBall (hrank : 1 < Module.rank ℝ E)`：`frontier C` 连通
  （`isConnected_sphere` 的连续像）。
- `interior_nonempty_of_homeomorphClosedBall`、`compl_nonempty_of_isCompact [NoncompactSpace E]`。
- **`isConnected_compl_of_homeomorphClosedBall_of_isBicollared`**：
  `[NoncompactSpace E] → 1 < Module.rank ℝ E → (φ : ↥C ≃ₜ ↥(closedBall 0 1)) →
   IsBicollared (frontier C) → IsConnected Cᶜ`。
  这就是 `BicollaredCellComplementConnected` 的实质内容，只差一层把
  `IsTopologicalCell 3 C` 的 `Nonempty` 拆开的包装。

聚焦检查 exit=0、10.6 秒、零 warning；`AuditT3` 八项仅标准三公理。

## 状态：四块砖

| 砖 | 内容 | 状态 |
|---|---|---|
| 1 | `IsBicollared` + 双领口边界补集连通 | **done**（T.1 + T.3）。命名端点 `BicollaredCellComplementConnected` 尚未写成 `MoiseChain` 词汇的那一行包装 |
| 2 | 拓扑不变域桥（开集嵌入的 interior/frontier/closure） | **done**（T.2） |
| 3 | `Moise305Tame` | **未开始** |
| 4 | §34 侧的 `IsBicollared (frontier (h '' C₂))` 生产者 | **未开始** |

无 `git stash`：工作区干净，三个模块全部 exit=0、零 warning、审计干净（5 + 7 + 8 = 20 项）。
没有留下任何不编译的编辑。

## 确切的下一步

1. 新模块 `DifferentialGeometry/Topology/PiecewiseLinear/TameNestedCells.lean`
   （import `MoiseChain`、`ClosedBallImage`、`OpenEmbeddingFrontier`），写

   ```
   def BicollaredCellComplementConnected : Prop :=
     ∀ C : Set (EuclideanSpace ℝ (Fin 3)),
       IsTopologicalCell 3 C → IsBicollared (frontier C) → IsConnected Cᶜ
   ```

   证明就是 `intro C ⟨φ⟩ hbi; exact isConnected_compl_of_homeomorphClosedBall_of_isBicollared
   (by rw [← Module.finrank_eq_rank']; norm_num) φ hbi`（rank 前提照
   `SphereSeparation/StandardSphere.lean:21` 的 `unitSphere_connected` 写法）。
   这一步预计十几行，风险低。

2. 同一模块写

   ```
   def Moise305Tame : Prop :=
     ∀ (C₁ C₂ : Set (EuclideanSpace ℝ (Fin 3))),
       IsTopologicalCell 3 C₁ → IsTopologicalCell 3 C₂ → C₁ ⊆ interior C₂ →
       IsSphericalShell (closure (C₂ \ C₁)) (frontier C₁) (frontier C₂) →
       IsBicollared (frontier C₂) →
       ∃ C, IsPLBall 3 C ∧ C₁ ⊆ interior C ∧ C ⊆ interior C₂
   ```

   并证 `Moise304 → Moise305Tame`（**不要**把对 30.4 的依赖藏起来；`Moise304` 在
   `MoiseChain.lean:71` 只是陈述，未证）。证明按 `MOISE_CHAIN.md` §"更正：30.5 ← 30.4"：
   取 30.4 给的 PL 2-球面 `B ⊆ interior X`，用
   `PiecewiseLinear/SphereComplement.lean:9 IsPLSphere.exists_isPLBall_complement_components`
   拿到 `D`，令 `C := closure`（含 `C₁` 的 `Bᶜ` 分支）；唯一缺的输入
   "`ℝ³ ∖ C₂` 连通"现在由第 1 步提供。

3. 第四块砖（§34 侧生产者）：`frontier C₂` 是 PL 2-球面 ⟹
   `PolyhedralSurfaceComplement.lean:29 IsPolyhedralManifold.isTwoSided` 给两侧性，
   `BicollarManifold.lean:135 IsPolyhedralManifold.exists_bicollar` 给闭双领口
   `ρ : S × Icc (-1) 1 ≃ₜ W`；限制到 `Ioo (-1) 1` 后用 T.2 的
   `isOpen_range_of_isOpen_subtype` 升成 `IsOpenEmbedding`，再用 `h` 推前
   （`h` 在开集 `U` 上是嵌入，同样由 T.2 得开映射），配合 T.2 的
   `frontier_image_eq_image_frontier` 得到 `IsBicollared (frontier (h '' C₂))`。
   注意 `IsBicollared` 的领口参数是 `S × ℝ`（`TwoSidedCollar` 的形状），
   而 `exists_bicollar` 给的是 `S × Icc (-1) 1`，需要一次 `Ioo (-1) 1 ≃ₜ ℝ` 的重参数化；
   树中 `VanKampen/TwoSidedCollarRescale.lean` 可能已有可复用的重参数化，动手前先 grep 它。

## 结论（只读核查阶段的判决，已被协调者接受并记入 MOISE_CHAIN.md / MOISE_PLAN.md §7）

判决 (b)：主链不需要任意（可能 wild）拓扑 3-胞腔的 Jordan–Brouwer。证据两条：

- 全书只在一处引用 Theorem 30.5——§34 Lemma 3（书页 240）："Each σ has arbitrarily
  small 3-cell neighborhoods C₁ and C₂ … Therefore σ′ has the same property. By Theorem 30.5 …"。
  而 §34 定理 1 的开头把 `h` 归约到 `K` 的开邻域 `U` 上，`A′ = h(A)`，所以喂给 30.5 的
  两个胞腔都是"多面体 3-胞腔在开集嵌入下的像"，边界必然双领口。
- 树里早已有纯拓扑、无条件的双领口分离：
  `SphereSeparation/TubularExcision.lean:170 hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1`
  只要 `IsOpenEmbedding Φ`，而它的球面 `H₁` 前提由
  `SphereSeparation/SphereH1.lean:189 isZero_integerSingularHomology_sphereTwo_one`
  无条件提供（Mayer–Vietoris，两个可缩的去点半球，不经 cellular comparison）。
  与 `SphereSeparation/JordanBrouwer.lean:28` 合成后，只读阶段的探针
  编译并审计通过，仅 `propext`、`Classical.choice`、`Quot.sound`。

因此 `HANDOFF_CODEX_H.md` §H-M3 的 10k–18k 行估计对主链是过时的：它只考察了
`DualityAssembly.lean` / `SpecializedDuality.lean` 那条需要光滑嵌入且反向循环的路线，
漏掉了 `TubularExcision → BicollarCertificates` 这条拓扑路线，也没有注意到消费者
从不递交非双领口的胞腔。本车道实际选用的是更省的 `TwoSidedCollar` 路线（连同调都不需要）。

**尚未测量**：本车道只完成四块砖中的两块，因此不修正先前 1k–2k 行的估计。
已落地的三个模块共 358 行（`BicollaredComplement` 105 + `OpenEmbeddingFrontier` 128 +
`ClosedBallImage` 125），剩余第 3、4 块砖未写，无测量值。
