# HANDOFF — lane T（tame 30.5）

分支 `codex/moise-tame305`，worktree `D:\differential-geometry-moise-t`，基点
`origin/codex/moise-integration`（`7b0f92ac1`）。本车道把 Moise 30.5 从"任意拓扑 3-胞腔"
收窄到"外胞腔边界双领口"，因为主链上唯一的消费者 §34 Lemma 3 只会喂进
`h '' P`（`P` 多面体 3-胞腔、`h` 为开集上的嵌入），其边界必然双领口。

验证方式：每个模块使用 Lean 4.33.1 聚焦编译，只写本车道目标的共享 olean/ilean；
探针放在项目树外。`LEAN_PATH` 先列工具链标准库，再列 Mathlib/包工件和共享项目工件。
每次编译前检查全局 `lean.exe` 数 < 4，并服从协调者分配的单编译器槽。
协调者已授权本车道在 T 的平面根聚合文件登记叶模块；整合根仍由整合车道负责。
共享上游工件在其他车道中有混合版本，因此局部验证不认证整个源依赖闭包的新鲜度。

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
| 1 | `IsBicollared` + 双领口边界补集连通 | **done**（T.1 + T.3 + T.5；命名端点已实现） |
| 2 | 拓扑不变域桥（开集嵌入的 interior/frontier/closure） | **done**（T.2） |
| 3 | `Moise305Tame` | **done，条件蕴含**（T.5；显式依赖 `Moise304`） |
| 4 | §34 PL 球像前沿的双领口生产者 | **done**（T.4a/T.4b；11 条声明；整合根构建尚待） |

前三砖交接时没有 `git stash` 或未编译编辑；当时三模块 exit=0、零 warning，
审计记录为 20 项。T.5 重新检查本车道全部 41 个公开声明。

## 确切的剩余工作

四块局部数学砖均已实现。第三砖是精确的 `Moise304 -> Moise305Tame`，
没有假装证明 `Moise304`，也没有证明原始、允许 wild 外胞腔的 `Moise305`。

- 整合车道运行最终 `lake build DifferentialGeometry`，刷新并检查所需的源依赖闭包；
  本车道按协调要求未并发运行全根构建。
- `Moise304` 的生产者，以及 §34 消费者改用 tame 接口，仍属后续主链工作。
  本层保留该条件，未改写 `MoiseChain.lean` 或现有消费者。
- 最终整分支合并须满足协调者的其余 §5 门禁；局部编译和提交并不替代这些门禁。

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

**当前计量**：七个本车道模块合计 709 行（含必需文件头）：先前三个模块 385 行，
第四砖 201 行（通用桥 106、PL 生产者 95），第三砖及命名包装 123 行。
这些计量不表示整个 Moise 主链或无条件的 Moise 30.5 已经完成。

## T.4a — Compact closed bicollars give open bicollars (2026-09-18)

`Topology/BicollarNeighborhood.lean` supplies a reusable bridge independent of PL
charts and invariance of domain:

- `ThreeManifold.TwoSidedCollar.isEmbedding_e` and `.isBicollared_range` identify
  the embedded central slice and reparameterize it by its actual image.
- `exists_twoSidedCollar_of_closedInterval` assumes a compact parameter space,
  `a > 0`, an embedding `rho : S x Icc (-a) a -> X`, its central-slice equation,
  and that its range is a neighborhood of the central image. It produces an
  actual `TwoSidedCollar e` whose range stays inside the given closed collar.
  The proof uses compactness to choose one smaller interval inside the ambient
  interior, then `TwoSidedCollar.ofOpenInterval`. No Hausdorff or manifold
  assumption is needed for this bridge.
- `ThreeManifold.TwoSidedCollar.isBicollared_image` transports a collar through
  an open embedding on any set containing its full range.

Before implementation, a temporary probe compiled the concrete PL 3-ball
`stdProj 2 '' stdSimplex Real (Fin 4)` together with the identity map on all of
Euclidean 3-space. The five imported bicollar, frontier, and reparameterization
interfaces had only `propext`, `Classical.choice`, and `Quot.sound`.

All four new declarations passed a focused compile and the full environment
linter set excluding `docBlame` and `docBlameThm`; a silent axiom check allowed
only the same three foundational axioms. No new leaf was registered in the root
aggregate, which remains the integration lane's responsibility. These checks use
the currently imported shared artifacts and do not certify freshness of their
entire source dependency closure. The PL/image-frontier producer remains the
next dependency-closed layer.

## T.4b — PL ball image frontiers are bicollared (2026-09-18)

The generic layer was committed and pushed as `39e444622`.
`PiecewiseLinear/BicollarEmbedding.lean` now supplies the fourth brick:

```lean
theorem IsPLBall.isBicollared_frontier_image
    {P U : Set (EuclideanSpace ℝ (Fin 3))} (hP : IsPLBall 3 P)
    (hU : IsOpen U) {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : ContinuousOn f U) (hinj : InjOn f U) (hPU : P ⊆ U) :
    IsBicollared (frontier (f '' P))
```

The reusable primary PL theorem is
`IsPolyhedralManifold.exists_twoSidedCollar`: in any Hausdorff PL 3-manifold,
any two-sided finite polyhedral 2-manifold has an actual `TwoSidedCollar` inside
every prescribed neighborhood. It needs no connectedness or ambient compactness.
`IsPolyhedralManifold.isBicollared_image` transports this through any open embedding
on that neighborhood. The Euclidean corollaries are `IsPLSphere.isBicollared_image`,
`IsPLSphere.isBicollared`, `IsPLBall.isBicollared_frontier_image`, and
`IsPLBall.isBicollared_frontier`.

Proof chain: the native PL closed bicollar producer, the compact uniform shrinking
bridge, invariance of domain for the continuous injection on the open neighborhood,
and the existing exact image-frontier equation. The full closed bicollar need not
have open image; the shrinking step explicitly puts its smaller band inside the
ambient interior. No conclusion-equivalent hypothesis is added.

Validation: both new modules compiled under the repository's configured focused
Lean options. All eleven declarations passed the standard environment-linter audit
excluding `docBlame` and `docBlameThm`, and their transitive axioms were contained in
`propext`, `Classical.choice`, and `Quot.sound`. A concrete endpoint application
using `f = id`, `U = univ`, and `P = stdProj 2 '' stdSimplex Real (Fin 4)` compiled.
The new source files contain no inline comments, declaration docstrings,
diagnostics, axioms, sorrys, resource overrides, or linter suppressions. `git diff --check` passed.

After the owner clarified the mandatory-header exception, both new modules were
checked with `linter.style.header=true` and `linter.style.longLine=true`, in addition
to the standard environment checks. The header linter activation depends on root
import registration (`isInLibraryRoot`), not on a Lake manifest. T root and PL
`AGENTS.md` and `NAMING.md` now record the owner-approved exception.
The shared imported artifacts were used; their entire source dependency closure
was not rebuilt. No shared upstream object was refreshed by this layer.

The coordinator authorized flat-root registration in T: both new leaves and the
three prior T leaves (`BicollaredComplement`, `OpenEmbeddingFrontier`, and
`ClosedBallImage`) are now imported by `DifferentialGeometry.lean`. The integration
root was not changed. Per coordination, no concurrent full T root build was started;
`lake build DifferentialGeometry` and full-branch integration remain outstanding.

At this checkpoint the named wrapper and third brick remained; T.5 below closes
both locally, leaving the explicit upstream dependency and integration gates.
`MoiseChain.lean`, the fourth brick's existing consumers, and all other source trees
were left unchanged. Completing this producer does not complete Moise 30.5.

## T.5 — Separating spheres and tame nested cells (2026-09-18)

`PiecewiseLinear/SphereNesting.lean` proves the reusable theorem
`IsPLSphere.exists_isPLBall_between_of_separates`. Its assumptions are a PL 2-sphere
`B` in Euclidean 3-space, a closed connected inner set `C1`, a compact outer set
`C2` with preconnected complement, `B` contained in the interior of
`closure (C2 \ C1)`, and separation of their frontiers. Its conclusion supplies
an actual PL 3-ball `D` with `frontier D = B`, `C1` contained in `interior D`,
and `D` contained in `interior C2`. It assumes neither a cell parameterization
nor a bicollar, and inner compactness is unnecessary.

The proof uses the existing PL Schoenflies complement-components producer.
Preconnectedness and unboundedness place the outer complement on the unbounded
side. Separation prevents the connected inner set from lying on that same side.
All witnesses retain their producing equations; no shell-boundary identification
or conclusion-equivalent hypothesis is added.

`PiecewiseLinear/TameNestedCells.lean` adds the two requested propositions and
proofs:

```lean
def BicollaredCellComplementConnected : Prop :=
  ∀ C : Set (EuclideanSpace ℝ (Fin 3)),
    IsTopologicalCell 3 C → IsBicollared (frontier C) → IsConnected Cᶜ

theorem bicollared_cell_complement_connected : BicollaredCellComplementConnected

def Moise305Tame : Prop :=
  ∀ C₁ C₂ : Set (EuclideanSpace ℝ (Fin 3)),
    IsTopologicalCell 3 C₁ → IsTopologicalCell 3 C₂ → C₁ ⊆ interior C₂ →
    IsSphericalShell (closure (C₂ \ C₁)) (frontier C₁) (frontier C₂) →
    IsBicollared (frontier C₂) →
    ∃ C, IsPLBall 3 C ∧ C₁ ⊆ interior C ∧ C ⊆ interior C₂

theorem moise305_tame_of_moise304 (h304 : Moise304) : Moise305Tame
```

Before implementing the implication, an external probe checked a concrete pair:
the concentric closed balls of radii 1 and 2. It constructed the radial shell
homeomorphism, proved its exact endpoint-frontier equations, supplied both cell
homeomorphisms and strict nesting, and constructed an exponential radial bicollar
of the outer frontier. The final regression also applies the new conditional
implication to those same witnesses. The separate tetrahedron/identity image
regression continues to check the fourth brick.

All seven T modules passed the final sequential focused compile with the standard
syntax set and explicit `linter.style.header=true`, `linter.style.longLine=true`.
The exhaustive 41-declaration audit used `getChecks true none none`, excluding
only the short linter names `docBlame` and `docBlameThm`. It rejected any other
linter result and any transitive axiom outside `propext`, `Classical.choice`, and
`Quot.sound`. That audit and both concrete regressions finished with exit 0 and
zero diagnostic output. An explicit `#print axioms` receipt for all five new
declarations reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The new implication remains conditional on its explicit
`Moise304` argument. The checks read the currently imported shared artifacts;
they do not certify the freshness of the entire source dependency closure.
Only this lane's seven target objects were refreshed, and no full T root build
was run. The remaining integration gate is explicitly outstanding.
Both new leaves are registered in the T flat aggregate. The three prior T leaves
also received the owner-required copyright headers and module titles; their
mathematical declarations are unchanged. Required headers are the sole source
comment/docstring exception, with no inline comments or declaration docstrings.
No other source tree, `MoiseChain.lean`, or existing consumer was edited.
