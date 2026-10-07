import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SurvivorJP6ST3
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalAlternativeTransport
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

/-!
# S-c OPEN-C：整 component 型（positive / round）transfer 的拓扑与 comparison 部分（O-CH11-STAB3 G4）

D-9：「涉及整块区域或整个 component，必须覆盖那个对象」。`positive` / `round` alternative 的 domain 是
**整个** `connectedComponent x`，故 transfer 需要 component 全体存活。本文件（后缀 `_P6ST3`）证明：
* `image_connectedComponent_of_subset_source_P6ST3`（一般拓扑）：`M` 紧、`connectedComponent x ⊆ e.source`
  ⇒ `e '' connectedComponent x = connectedComponent (e x)`（像连通 + clopen：紧 ⇒ 闭，局部连通 ⇒ 开）。
* **`wholeComponent_survivor_P6ST3`**（event 层）：`RegularCrossing p q` +
  `connectedComponent p ⊆ interior (val '' old)` ⇒ `∃ J`（G2 survivor）：`J p = q`、
  `J '' comp(p) = comp(q)`、`g⁻ = J*g⁺`，且对任意阶 `k`、`δ > 0`，
  `t → s⁻` eventually `MetricComparisonOn (g t) g⁺ J comp(p) {0} k δ` —— comparison 覆盖
  **整个** component
  （G1 的 P-C，`U = K = comp(p)`：component 开且紧）。
* `positiveComponent_of_survivor_P6ST3`：`PositiveComponent comp(p)` ⇒ `PositiveComponent comp(q)`
  （树内 `positiveComponent_transport_of_partialDiffeomorph` + 上面的 component 等式）。
OPEN-C 剩余（不在本文件，见 DELIVERIES G4 块 repair target）：`SecLower` 的 `C²`-扰动传递、round 型
`SpatialRoundComponent` 的空间版 transport、component 直径的外侧 margin（`D ⊆ B(2r)` 在 `(1±δ)` 下需余量）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **component 搬运**：`M` 紧、`connectedComponent x ⊆ e.source` ⇒
`e '' connectedComponent x = connectedComponent (e x)`。 -/
theorem image_connectedComponent_of_subset_source_P6ST3 {M N : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [CompactSpace M] [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [T2Space N] (e : PartialDiffeomorph I3 I3 M N ∞) {x : M}
    (h : connectedComponent x ⊆ e.source) :
    (e : M → N) '' connectedComponent x = connectedComponent (e x) := by
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ThreeSpace M
  have hcont : ContinuousOn (e : M → N) (connectedComponent x) :=
    e.contMDiffOn_toFun.continuousOn.mono h
  apply Subset.antisymm
  · exact (isConnected_connectedComponent.image _ hcont).isPreconnected.subset_connectedComponent
      ⟨x, mem_connectedComponent, rfl⟩
  · have hclosed : IsClosed ((e : M → N) '' connectedComponent x) :=
      (isClosed_connectedComponent.isCompact.image_of_continuousOn hcont).isClosed
    have hopen : IsOpen ((e : M → N) '' connectedComponent x) :=
      image_opens_isOpen e (U := ⟨connectedComponent x, isOpen_connectedComponent⟩) h
    exact IsClopen.connectedComponent_subset ⟨hclosed, hopen⟩ ⟨x, mem_connectedComponent, rfl⟩

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

/-- **OPEN-C（拓扑 + comparison 部分）**：crossing 点 `p` 的整个 component 存活（⊆ `interior (val '' old)`）⇒
survivor `J` 把 `comp(p)` 映满 `comp(q)`，且 `C^k` comparison 覆盖整个 `comp(p)`。 -/
theorem wholeComponent_survivor_P6ST3 (E : MetricCutCapEvent P Q a s) {p : P.Carrier}
    {q : Q.Carrier} (hcross : E.RegularCrossing p q)
    (hcomp : connectedComponent p ⊆ interior (Subtype.val '' E.old)) :
    ∃ J : PartialDiffeomorph ThreeModel ThreeModel P.Carrier Q.Carrier ∞,
      J p = q ∧ connectedComponent p ⊆ J.source ∧
      (J : P.Carrier → Q.Carrier) '' connectedComponent p = connectedComponent q ∧
      (∀ (x : P.Carrier) (hx : x ∈ E.incoming.terminalRegularOpen), x ∈ J.source →
        ∀ v w : TangentSpace ThreeModel x,
          E.outputMetric.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
            (mfderiv ThreeModel ThreeModel J x w) = E.terminal.metric.inner ⟨x, hx⟩ v w) ∧
      ∀ (k : ℕ) (δ : ℝ), 0 < δ → ∀ᶠ t in 𝓝[<] s,
        Nonempty (MetricComparisonOn (fun _ => E.incoming.flow.base.metric t)
          (fun _ => E.outputMetric) J (connectedComponent p) {0} k δ) := by
  have : LocallyConnectedSpace P.Carrier := ChartedSpace.locallyConnectedSpace ThreeSpace P.Carrier
  obtain ⟨J, hJsrc, hJ, -, hiso⟩ := E.exists_survivorJ_P6ST3 hcross
  have hsub : connectedComponent p ⊆ J.source := hJsrc ▸ hcomp
  have hΩ : connectedComponent p ⊆ E.incoming.terminalRegularOpen :=
    hcomp.trans (interior_subset.trans E.image_old_subset_terminalRegularOpen_P6ST3)
  refine ⟨J, hJ, hsub, ?_, hiso, fun k δ hδ => ?_⟩
  · rw [image_connectedComponent_of_subset_source_P6ST3 J hsub, hJ]
  · let U : Opens P.Carrier := ⟨connectedComponent p, isOpen_connectedComponent⟩
    exact E.eventually_comparison_of_terminal_P6ST3 J U
      isClosed_connectedComponent.isCompact subset_rfl hsub hΩ
      (fun x hx hxK => hiso x hx (hsub hxK)) k hδ

/-- **OPEN-C（positive 型拓扑数据）**：`PositiveComponent comp(p)` + 整 component 存活 ⇒
`PositiveComponent comp(q)`（`J` = survivor，树内
`positiveComponent_transport_of_partialDiffeomorph`）。 -/
theorem positiveComponent_of_survivor_P6ST3 (E : MetricCutCapEvent P Q a s) {p : P.Carrier}
    {q : Q.Carrier} (hcross : E.RegularCrossing p q)
    (hcomp : connectedComponent p ⊆ interior (Subtype.val '' E.old))
    (data : PositiveComponent (M := P.Carrier) (connectedComponent p)) :
    Nonempty (PositiveComponent (M := Q.Carrier) (connectedComponent q)) := by
  obtain ⟨J, -, hsub, himage, -, -⟩ := E.wholeComponent_survivor_P6ST3 hcross hcomp
  rw [← himage]
  exact positiveComponent_transport_of_partialDiffeomorph data J hsub

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
