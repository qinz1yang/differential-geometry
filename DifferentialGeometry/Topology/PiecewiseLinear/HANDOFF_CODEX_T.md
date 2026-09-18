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
