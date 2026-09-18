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
