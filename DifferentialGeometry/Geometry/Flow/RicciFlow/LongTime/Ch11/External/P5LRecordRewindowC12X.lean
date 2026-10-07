import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.P5LLinkedTransportC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepRetention
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.EventTimeTranslation

set_option autoImplicit false

/-!
# O-C12X-P5L (T8) G2：tower event 上换窗口重装 cutoff record（后缀 `_C12X`）

S14 P5Linked 的单 event 核心 `exists_rewindowed_linked_record_C12X`。输入（outer tuple 的两个子句
给的形状）：

* tower history `H` 的 event `j` 上的 record `R`（参数 `q`，tube 数据满足 `q` 的界）；
* native history `K` 的 event `i` 上的 fine record `FR`（参数 `fp`，fine 模型窗口），其平移
  `translate_retained_event (K.coreEvent i) c` 与 `H` 的 event `j` 有 `SamePresentation`；
* tube 级 `HEq`：`R.delta ≍ FR.delta`、`R.order ≍ FR.order`、`R.neck ≍ FR.neck`；
* tower event 上的 raw caps（fine 窗口，`hasCanonicalWindow`，delta / order / neck / window metric
  与 `FR.static b` 相同，`b ≍ b'`）；`FR` 的 static 是 linked。

输出：同一 tower event 上参数 `q.withModelWindow D m ζ` 的 record，static 是 raw cap 缩到窗口
`(D, m, ζ)`，tube 数据沿用 `R`，且每个 static linked。recenter 五项与 `order_lower` 的 `m + 6`
从 `FR` 搬来（`p5l_recenter_transport`：只 `cases` 分量 `P, Q, discarded, capped, transition,
terminal open, terminal metric` 与 tube 函数，不识别整个 event——static family 的类型依赖整个
event，其 `HEq` 不可应用）。
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

/-- 分量级搬运：tube 数据 `(δ, o, N)` 与 static neck `SN` 从 transition `X`（terminal `U, h`）
搬到 `X'`（`U', h'`）：static scale，以及 recenter 的 mark / delta / scale comparison / chart /
in-buffer。 -/
private theorem p5l_recenter_transport
    {P P' Q Q' D₀ N₀ D₁ N₁ : OrientedThreeStage.{u}}
    (hP : P = P') (hQ : Q = Q') (hD : D₀ = D₁) (hN : N₀ = N₁)
    {X : SmoothCutCapTransition P Q D₀ N₀} {X' : SmoothCutCapTransition P' Q' D₁ N₁}
    (hX : HEq X X')
    {U : TopologicalSpace.Opens P.Carrier} {U' : TopologicalSpace.Opens P'.Carrier}
    (hU : HEq U U') {h : SmoothRiemannianMetric ThreeModel U}
    {h' : SmoothRiemannianMetric ThreeModel U'} (hh : HEq h h')
    {δ : X.trace.tubes.Index → ℝ} {δ' : X'.trace.tubes.Index → ℝ} (hδ : HEq δ' δ)
    {o : X.trace.tubes.Index → ℕ} {o' : X'.trace.tubes.Index → ℕ} (ho : HEq o' o)
    {N : ∀ α, NormalizedNeck h (δ α) (o α)} {N' : ∀ α, NormalizedNeck h' (δ' α) (o' α)}
    (hNk : HEq N' N)
    (b : {β : X.trace.tubes.Boundary //
      ∀ y, X.trace.tubes.coreBoundarySphere β y ∈ X.trace.retainedCore})
    (b' : {β : X'.trace.tubes.Boundary //
      ∀ y, X'.trace.tubes.coreBoundarySphere β y ∈ X'.trace.retainedCore})
    (hb : HEq b b')
    {sδ sδ' : ℝ} {sk sk' : ℕ} (hsδ : sδ' = sδ) (hsk : sk' = sk)
    {SN : NormalizedNeck h sδ sk} {SN' : NormalizedNeck h' sδ' sk'} (hSN : HEq SN' SN)
    (rc : ℝ) :
    SN'.scale = SN.scale ∧
    (SN.sphereMark = (N b.1.1).sphereMark → SN'.sphereMark = (N' b'.1.1).sphereMark) ∧
    (sδ = rc * δ b.1.1 → sδ' = rc * δ' b'.1.1) ∧
    (|SN.scale / (N b.1.1).scale - 1| ≤ rc * δ b.1.1 →
      |SN'.scale / (N' b'.1.1).scale - 1| ≤ rc * δ' b'.1.1) ∧
    ((∀ x : neckBuffer sδ,
        ∀ hx : (x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (δ b.1.1),
        SN.chart x = (N b.1.1).chart ⟨(x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)), hx⟩) →
      ∀ x : neckBuffer sδ',
        ∀ hx : (x.1.1, (if b'.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (δ' b'.1.1),
        SN'.chart x =
          (N' b'.1.1).chart ⟨(x.1.1, (if b'.1.2 then 1 else -1) * (1 + x.1.2)), hx⟩) ∧
    ((∀ x : neckBuffer sδ,
        (x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (δ b.1.1)) →
      ∀ x : neckBuffer sδ',
        (x.1.1, (if b'.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (δ' b'.1.1)) := by
  subst hP hQ hD hN
  cases hX
  cases hU
  cases hh
  cases hδ
  cases ho
  cases hNk
  cases hb
  subst hsδ hsk
  cases hSN
  exact ⟨rfl, id, id, id, id, id⟩

/-- 分量级搬运：tube order 的下界。 -/
private theorem p5l_order_transport
    {P P' Q Q' D₀ N₀ D₁ N₁ : OrientedThreeStage.{u}}
    (hP : P = P') (hQ : Q = Q') (hD : D₀ = D₁) (hN : N₀ = N₁)
    {X : SmoothCutCapTransition P Q D₀ N₀} {X' : SmoothCutCapTransition P' Q' D₁ N₁}
    (hX : HEq X X') {o : X.trace.tubes.Index → ℕ} {o' : X'.trace.tubes.Index → ℕ}
    (ho : HEq o' o) (c : ℕ) (hc : ∀ α, c ≤ o α) : ∀ α, c ≤ o' α := by
  subst hP hQ hD hN
  cases hX
  cases ho
  exact hc

private theorem p5l_metric_cast_open_heq {P : OrientedThreeStage.{u}}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    (g : SmoothRiemannianMetric ThreeModel U) : HEq (hUV ▸ g) g := by
  cases hUV
  exact HEq.rfl

/-- native event `i`（平移 `c` 后）与 tower event `j` 的 `SamePresentation` 给出的分量等式。 -/
theorem native_tower_components_C12X {H K : RetainedCoreHistory.{u}} {j : Fin H.eventCount}
    {i : Fin K.eventCount} {c : ℝ}
    (hsame : MetricCutCapEvent.SamePresentation
      (GC.GeneralFlow.translate_retained_event (K.coreEvent i) c).toMetricCutCapEvent
      (H.toHistory.event j)) :
    K.stage i.castSucc = H.stage j.castSucc ∧ K.stage i.succ = H.stage j.succ ∧
    (K.toHistory.event i).discarded = (H.toHistory.event j).discarded ∧
    (K.toHistory.event i).capped = (H.toHistory.event j).capped ∧
    HEq (K.toHistory.event i).transition (H.toHistory.event j).transition ∧
    HEq (K.toHistory.event i).incoming.terminalRegularOpen
      (H.toHistory.event j).incoming.terminalRegularOpen ∧
    HEq (K.toHistory.event i).terminal.metric (H.toHistory.event j).terminal.metric := by
  have hopen := GC.GeneralFlow.translated_terminal_open (K.coreEvent i).incoming c
  have hmetric : HEq (GC.GeneralFlow.translate_retained_event (K.coreEvent i) c).terminal.metric
      (K.coreEvent i).terminal.metric :=
    p5l_metric_cast_open_heq hopen.symm (K.coreEvent i).terminal.metric
  exact ⟨hsame.incomingStage_eq, hsame.outgoingStage_eq, hsame.discarded_eq, hsame.capped_eq,
    hsame.transition_heq, (heq_of_eq hopen.symm).trans hsame.terminalRegion_heq,
    hmetric.symm.trans hsame.terminalMetric_heq⟩

/-- **单 event 核心**：tower event `j` 上的 record `R` + native fine record `FR`（平移后与 `j`
同 presentation，tube 数据 `HEq`）+ tower 上与 `FR.static` 同几何的 raw caps + `FR` 的 linked
windows ⇒ 同一 tower event 上参数 `q.withModelWindow D m ζ` 的 record，每个 static linked。 -/
theorem exists_rewindowed_linked_record_C12X {H K : RetainedCoreHistory.{u}}
    {j : Fin H.eventCount} {i : Fin K.eventCount} {c : ℝ} {q fp : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory j q) (FR : GeometricCutoffRecord K.toHistory i fp)
    (hsame : MetricCutCapEvent.SamePresentation
      (GC.GeneralFlow.translate_retained_event (K.coreEvent i) c).toMetricCutCapEvent
      (H.toHistory.event j))
    (hδ : HEq R.delta FR.delta) (ho : HEq R.order FR.order) (hN : HEq R.neck FR.neck)
    (hfixed : fp.fixed = q.fixed) (hrc : fp.recenterConstant = q.recenterConstant)
    (hraw : ∀ b' : (H.toHistory.event j).RetainedBoundaryIndex,
      ∃ (b : (K.toHistory.event i).RetainedBoundaryIndex)
        (raw : (H.toHistory.event j).PresentedStaticCap q.fixed fp.modelRadius fp.modelOrder
          fp.modelAccuracy b'),
        HEq b b' ∧ raw.hasCanonicalWindow ∧ raw.delta = (FR.static b).delta ∧
        raw.order = (FR.static b).order ∧ HEq raw.neck (FR.static b).neck ∧
        raw.witness.windowMetric = (FR.static b).witness.windowMetric)
    (hlink : ∀ b, linkedCanonicalWindow_C11E (FR.static b))
    {D ζ : ℝ} {m : ℕ} (hD : 0 < D) (hcap : StandardCap.transitionEnd < D + 1)
    (hDfp : D ≤ fp.modelRadius) (hm : m ≤ fp.modelOrder) (hζ : fp.modelAccuracy ≤ ζ) :
    ∃ R' : GeometricCutoffRecord H.toHistory j
        (q.withModelWindow D m ζ hD (fp.modelAccuracy_pos.trans_le hζ)),
      ∀ b', linkedCanonicalWindow_C11E (R'.static b') := by
  obtain ⟨hP, hQ, hD₀, hN₀, hX, hU, hh⟩ := native_tower_components_C12X hsame
  choose bf raw hb hcan hrd hro hrn hrw using hraw
  have ht := fun b' => p5l_recenter_transport hP hQ hD₀ hN₀ hX hU hh hδ ho hN (bf b') b'
    (hb b') (hrd b') (hro b') (hrn b') q.recenterConstant
  have horder : ∀ α, m + 6 ≤ R.order α :=
    p5l_order_transport hP hQ hD₀ hN₀ hX ho (m + 6) fun α =>
      (Nat.add_le_add_right hm 6).trans ((le_max_left _ _).trans (FR.order_lower α))
  let S' : ∀ b', (H.toHistory.event j).PresentedStaticCap q.fixed D m ζ b' := fun b' =>
    (raw b').restrictCanonicalWindow (hcan b') hD hDfp hm hζ
  refine ⟨{ R with
      order_lower := fun α => max_le (horder α) ((le_max_right _ _).trans (R.order_lower α))
      static := S'
      recenter_scale := fun b' => (S' b').neck.scale_scalar
      recenter_mark := fun b' => (ht b').2.1 (FR.recenter_mark (bf b'))
      recenter_delta := fun b' => (ht b').2.2.1 (by
        rw [← hrc]
        exact FR.recenter_delta (bf b'))
      recenter_scale_comparison := fun b' => (ht b').2.2.2.1 (by
        rw [← hrc]
        exact FR.recenter_scale_comparison (bf b'))
      recenter_chart := fun b' => (ht b').2.2.2.2.1 (FR.recenter_chart (bf b'))
      recenter_in_buffer := fun b' => (ht b').2.2.2.2.2 (FR.recenter_in_buffer (bf b')) }, ?_⟩
  intro b'
  exact linkedCanonicalWindow_restrictCanonicalWindow_C12X (raw b') (hcan b') hD hDfp hm hζ hcap
    (linkedCanonicalWindow_of_terminal_heq_C12X hP hU hh hfixed (FR.static (bf b')) (raw b')
      (hcan b') (hrd b') (ht b').1 (hrw b') (hlink (bf b')))

end GC.LongTime.Ch11
