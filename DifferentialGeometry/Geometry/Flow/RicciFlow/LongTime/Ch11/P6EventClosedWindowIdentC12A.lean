import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeBornGramEventC11SP

set_option autoImplicit false

/-!
# C12-5：event 时刻 incoming flow 的闭窗光滑识别（通用 API，后缀 `_C12A`）

NATIVE-BORN O2（`commonFlow_closedGram_traced_C11SP`）在 event 时刻用 `backwardSurvivorSlabMetric` 与
`TerminalLimitMetric.extendedMetric` 的 `_before` / `_terminal` 把公共 flow 的度量认成 slab 的局部拉回。
这里把该识别抽成**任意 `IncomingSlab` 终端**的引理，不涉及 `ObservedHistory` / survivor 数据：
* `localPull_extendedMetric_ident_C12A`（PROVED）：`ψ : N → G.terminalRegularOpen` 局部微分同胚，
  `g v`（`v ∈ [c, s)`）= incoming 度量限制到 `terminalRegularOpen` 的 `ψ`-局部拉回，`g s` = 终端极限度量
  的拉回 ⇒ `[c, s]` 上 `g v = localPull (L.extendedMetric v) ψ`；
* `chartGramMatrix_closedWindow_extended_C12A`（PROVED）：同前提 + `a ≤ c < s` ⇒ 闭窗 `[c, s]`
  上 chart Gram 联合光滑（reset Shi 的 event 时刻右端可直接用）。
前提只有两条识别式（`hbefore`、`hterm`），无新结构、无 `hpos`。
-/

noncomputable section

open Set Bundle Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

private local instance terminalSigmaCompactC12A {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

/-- **闭窗识别（`_C12A`，PROVED）**：任意 `IncomingSlab` 终端。 -/
theorem localPull_extendedMetric_ident_C12A {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} (L : G.TerminalLimitMetric)
    {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    [T2Space N] (ψ : N → G.terminalRegularOpen)
    (hψ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ ψ)
    (g : ℝ → SmoothRiemannianMetric ThreeModel N) {c : ℝ}
    (hbefore : ∀ v, c ≤ v → v < s →
      g v = localPullMetric ((G.flow.base.metric v).restrictOpen G.terminalRegularOpen) ψ hψ)
    (hterm : g s = localPullMetric L.metric ψ hψ) :
    ∀ v ∈ Icc c s, g v = localPullMetric (L.extendedMetric v) ψ hψ := by
  intro v hv
  rcases lt_or_eq_of_le hv.2 with hvs | hvs
  · rw [hbefore v hv.1 hvs, L.extendedMetric_before hvs]
  · subst hvs
    rw [hterm, L.extendedMetric_terminal]

/-- **闭窗 chart Gram 联合光滑（`_C12A`，PROVED）**：任意 `IncomingSlab` 终端，`a ≤ c < s`。 -/
theorem chartGramMatrix_closedWindow_extended_C12A {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} (L : G.TerminalLimitMetric)
    {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    [T2Space N] (ψ : N → G.terminalRegularOpen)
    (hψ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ ψ)
    (g : ℝ → SmoothRiemannianMetric ThreeModel N) {c : ℝ} (hac : a ≤ c) (hcs : c < s)
    (hbefore : ∀ v, c ≤ v → v < s →
      g v = localPullMetric ((G.flow.base.metric v).restrictOpen G.terminalRegularOpen) ψ hψ)
    (hterm : g s = localPullMetric L.metric ψ hψ)
    (x₀ : N) (i k : Fin (Module.finrank ℝ ThreeSpace)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × N => Tensor.Coordinates.chartGramMatrix (g q.1) x₀ q.2 i k)
      (Icc c s ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet) := by
  have hid := localPull_extendedMetric_ident_C12A L ψ hψ g hbefore hterm
  refine chartGramMatrix_joint_contMDiffOn_of_pullback L.extendedMetric (Icc c s)
    (L.extendedMetric_jointContMDiffOn hac hcs) g ψ hψ.contMDiff ?_ x₀ i k
  intro t ht x u w
  rw [hid t ht, localPullMetric_inner]

end GC.LongTime.Ch11
