import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapRestriction

set_option autoImplicit false

/-!
# O-C12X-P5L (T8) G1：linked canonical window 的两个搬运（后缀 `_C12X`）

S14 P5Linked（`LateLinkedRecordsSupply_C11E`）供给的 linked 条件装配：

* `linkedCanonicalWindow_restrictCanonicalWindow_C12X`：`restrictCanonicalWindow` 缩小模型窗口
  （半径 / 阶 / 精度）保持 insertion datum `(x₀, δ', k, d)` 与 `S.delta`，故保持 link
  `δ' ≤ S.delta ∧ 2⌊δ'⁻¹⌋₊ ≤ k`（同 `hasCanonicalWindow_restrictCanonicalWindow`，多带两个 link 分量）；
* `linkedCanonicalWindow_of_terminal_heq_C12X`：两个 event 的 terminal 开集 / terminal metric `HEq`
  （例如 native event 与其平移在 tower 上的 `SamePresentation` 像）时，`S` 的 linked window 搬到
  `S'`，只要 scaffold 相等、`S'.delta = S.delta`、neck scale 与 window metric 相同、`S'` 有
  canonical window（覆盖子句取自它）。datum 的搬运只 `cases` 分量（`p5l_datum_transport`），不识别整个 event。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open Set
open scoped Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

/-- 缩小模型窗口保持 linked canonical window（datum 与 static delta 不变）。 -/
theorem linkedCanonicalWindow_restrictCanonicalWindow_C12X
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D D' ε ε' : ℝ} {m m' : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b) (hS : S.hasCanonicalWindow)
    (hD' : 0 < D') (hD'D : D' ≤ D) (hm : m' ≤ m) (hε : ε ≤ ε')
    (hcap : StandardCap.transitionEnd < D' + 1)
    (hlink : linkedCanonicalWindow_C11E S) :
    linkedCanonicalWindow_C11E (S.restrictCanonicalWindow hS hD' hD'D hm hε) := by
  obtain ⟨x₀, δ, k, d, w, hscale, hmetric, hcover, hδ, hk⟩ := hlink
  let w' := (w.weakenOrderAccuracy hm hε).restrictWindow hD' hD'D
  have heq : w.windowMetric = S.witness.windowMetric :=
    SmoothRiemannianMetric.ext_inner fun x v z =>
      (hmetric x v z).trans (S.window_inner x v z).symm
  have heq' : w'.windowMetric =
      (S.restrictCanonicalWindow hS hD' hD'D hm hε).witness.windowMetric := by
    rw [MetricCutCapEvent.PresentedStaticCap.restrictCanonicalWindow_windowMetric]
    dsimp only [w']
    rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric,
      StandardCap.CanonicalStaticInsertionWitness.weakenOrderAccuracy_windowMetric,
      heq]
  refine ⟨x₀, δ, k, d, w', hscale, ?_, ?_, hδ, hk⟩
  · intro x v z
    rw [heq']
    exact (S.restrictCanonicalWindow hS hD' hD'D hm hε).window_inner x v z
  · intro z
    obtain ⟨x, hx, hpoint⟩ := hcover z
    refine ⟨⟨x.val, hx.trans_lt hcap⟩, hx, ?_⟩
    change S.window
      ⟨x.val, (hx.trans_lt hcap).trans_le (add_le_add hD'D (le_refl 1))⟩ =
        S.inclusion (S.witness.cap z)
    exact hpoint

/-- insertion datum 沿 terminal 开集 / metric 的 `HEq` 搬运（只 `cases` 分量）。 -/
private theorem p5l_datum_transport {P P' : OrientedThreeStage.{u}} (hP : P = P')
    {U : TopologicalSpace.Opens P.Carrier} {U' : TopologicalSpace.Opens P'.Carrier}
    (hU : HEq U U') {h : SmoothRiemannianMetric ThreeModel U}
    {h' : SmoothRiemannianMetric ThreeModel U'} (hh : HEq h h')
    {δ : ℝ} {k : ℕ} (x₀ : U) (d : normalizedDatum h x₀ δ k) {A : ℝ} {hA : 0 < A}
    {D ε : ℝ} {m : ℕ}
    (w : StandardCap.CanonicalStaticInsertionWitness
      d A hA D m ε) :
    ∃ (x₀' : U') (d' : normalizedDatum h' x₀' δ k)
      (w' : StandardCap.CanonicalStaticInsertionWitness
        d' A hA D m ε),
      w'.windowMetric = w.windowMetric ∧ metricScalarAt h' x₀' = metricScalarAt h x₀ := by
  subst hP
  cases hU
  cases hh
  exact ⟨x₀, d, w, rfl, rfl⟩

/-- linked canonical window 沿 terminal 分量 `HEq` 从 `S` 搬到 `S'`：`S'` 与 `S` 有相同的 static
delta、neck scale、window metric，且 `S'` 有 canonical window（覆盖子句）。 -/
theorem linkedCanonicalWindow_of_terminal_heq_C12X
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {E' : MetricCutCapEvent P' Q' a' s'}
    (hP : P = P')
    (hU : HEq E.incoming.terminalRegularOpen E'.incoming.terminalRegularOpen)
    (hh : HEq E.terminal.metric E'.terminal.metric)
    {fixed fixed' : StaticCapScaffold} (hfixed : fixed = fixed') {D ε : ℝ} {m : ℕ}
    {b : E.RetainedBoundaryIndex} {b' : E'.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b) (S' : E'.PresentedStaticCap fixed' D m ε b')
    (hS' : S'.hasCanonicalWindow) (hdelta : S'.delta = S.delta)
    (hscale : S'.neck.scale = S.neck.scale)
    (hwin : S'.witness.windowMetric = S.witness.windowMetric)
    (hlink : linkedCanonicalWindow_C11E S) : linkedCanonicalWindow_C11E S' := by
  subst hfixed
  obtain ⟨x₀, δ, k, d, w, hscale0, hmetric, -, hδ, hk⟩ := hlink
  obtain ⟨-, -, -, -, -, -, -, hcover⟩ := hS'
  obtain ⟨x₀', d', w', hw', hsc'⟩ := p5l_datum_transport hP hU hh x₀ d w
  have heq : w.windowMetric = S.witness.windowMetric :=
    SmoothRiemannianMetric.ext_inner fun x v z =>
      (hmetric x v z).trans (S.window_inner x v z).symm
  refine ⟨x₀', δ, k, d', w', hsc'.trans (hscale0.trans hscale.symm), ?_, hcover,
    hδ.trans_eq hdelta.symm, hk⟩
  intro x v z
  rw [hw', heq, ← hwin]
  exact S'.window_inner x v z

end GC.LongTime.Ch11
