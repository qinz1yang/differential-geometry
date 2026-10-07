import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialQualitySurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialBirthBlockLookup
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCanonicalWindowData

/-!
# S-CH11-FIX12 port of astra `PreparedSpatialRawCaps`（`PortC11P`）

来源：donor `PreparedSpatialRawCaps.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* `TerminalStaticPresentation` 是 `CutoffRecordConcatenation` 里的 `private structure`。donor 的
  `open private TerminalStaticPresentation … Canonical from …CutoffRecordConcatenation` 只打开了
  结构名与 3 个 def，**字段投影**（`delta` / `order` / `neck` / `witness` / `inclusion`）是 private，
  点记号 `T.delta`、`(S b).witness` 报 "Field `delta` from structure … is private"（约 40 处），
  `T.Canonical` 报 "Invalid field `Canonical`"（2 处，点记号只查非 private 名）→ 把五个投影加进
  `open private … from` 清单，点记号处一律改成全名应用 `TerminalStaticPresentation.delta T`
  （机械替换，`T.witness.Output` ↦ `(TerminalStaticPresentation.witness T).Output`）；
* 两处 hypothesis 里行尾点号 `….toMetricCutCapEvent).` 换行后接 `SamePresentation` 在本树
  parser 报 "Invalid field notation: Identifier or numeral expected"（l.187 / 222）→
  `.SamePresentation` 接回同一行（语义同）；
* private 引理 `terminal_parent_centers_and_scales` 的 `{ι ι' : Type u}` 与调用处不符：调用处的
  `ι := (…event i).transition.trace.tubes.Index : Type`（`HEq.{1}` vs 期望 `HEq.{u + 1}`），
  `u` 是固定的 universe 参数 ⇒ 改成 `{ι ι' : Type}`（该引理只有这一处调用，且只在本文件内可见）；
* 点记号替换后的陈述行超过 100 列 → 重排换行（项不变）；
* 两处 `simpa only [H.toHistory.event_output j] using …`（`raw.inclusion_metric x v z` 与
  `hwactual x v z`）里 simp 先把 `(H.toHistory.event j).outputMetric` 投影化简成
  `(H.coreEvent j).toMetricCutCapEvent.outputMetric`，`event_output` 再也匹配不上：前者先 `have`
  取 `raw.inclusion_metric x v z`，`rw [H.toHistory.event_output j] at` 它再 `exact`；后者的目标含依赖
  类型（`T` 的类型挂着 `outputMetric`），`rw` 报 motive 不 type correct → 改
  `(hwactual x v z).trans (congrArg (fun G => … G.inner …) (H.toHistory.event_output j))`
  （FIX7 heartbeat 坑 (2) 的 congrArg 写法）；

原路径 `PreparedSpatialRawCaps` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set Filter Manifold DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal Topology
namespace GC.GeneralFlow
universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

open private TerminalStaticPresentation TerminalStaticPresentation.ofPresented
  TerminalStaticPresentation.toPresented TerminalStaticPresentation.Canonical
  TerminalStaticPresentation.delta TerminalStaticPresentation.order
  TerminalStaticPresentation.neck TerminalStaticPresentation.witness
  TerminalStaticPresentation.inclusion from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation

private theorem metric_cast_open_heq
    {P : OrientedThreeStage.{u}} {U V : TopologicalSpace.Opens P.Carrier}
    (hUV : U = V) (g : SmoothRiemannianMetric ThreeModel U) :
    HEq (hUV ▸ g) g := by
  cases hUV
  exact HEq.rfl

private theorem translated_terminal_metric_heq
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : RetainedCoreEvent P Q a s) (c : ℝ) :
    HEq (translate_retained_event E c).terminal.metric E.terminal.metric :=
  metric_cast_open_heq (translated_terminal_open E.incoming c).symm E.terminal.metric

/-- Transport only the terminal tuple. The incoming slabs are not identified. -/
private theorem terminal_cap_family_transport
    {P Q D₀ N₀ P' Q' D₁ N₁ : OrientedThreeStage.{u}}
    {X : SmoothCutCapTransition P Q D₀ N₀}
    {X' : SmoothCutCapTransition P' Q' D₁ N₁}
    {U : TopologicalSpace.Opens P.Carrier} {U' : TopologicalSpace.Opens P'.Carrier}
    {h : SmoothRiemannianMetric ThreeModel U}
    {h' : SmoothRiemannianMetric ThreeModel U'} {g : Q.Metric} {g' : Q'.Metric}
    (hP : P = P') (hQ : Q = Q') (hD : D₀ = D₁) (hN : N₀ = N₁)
    (hX : HEq X X') (hU : HEq U U') (hh : HEq h h') (hg : HEq g g')
    {fixed fixed' : StaticCapScaffold} (hfixed : fixed = fixed')
    {D ε : ℝ} {m : ℕ}
    (S : ∀ b : {b : X.trace.tubes.Boundary //
      ∀ y, X.trace.tubes.coreBoundarySphere b y ∈ X.trace.retainedCore},
      TerminalStaticPresentation X U h g fixed D m ε b)
    (hS : ∀ b, (TerminalStaticPresentation.Canonical (S b)))
    (b' : {b : X'.trace.tubes.Boundary //
      ∀ y, X'.trace.tubes.coreBoundarySphere b y ∈ X'.trace.retainedCore}) :
    ∃ (b : {b : X.trace.tubes.Boundary //
        ∀ y, X.trace.tubes.coreBoundarySphere b y ∈ X.trace.retainedCore})
      (T : TerminalStaticPresentation X' U' h' g' fixed' D m ε b'),
      HEq b b' ∧ TerminalStaticPresentation.Canonical T ∧
      TerminalStaticPresentation.delta T = TerminalStaticPresentation.delta (S b) ∧
      TerminalStaticPresentation.order T = TerminalStaticPresentation.order (S b) ∧
      HEq (TerminalStaticPresentation.neck T) (TerminalStaticPresentation.neck (S b)) ∧
      HEq (TerminalStaticPresentation.witness T) (TerminalStaticPresentation.witness (S b)) ∧
      (TerminalStaticPresentation.witness T).Output =
        (TerminalStaticPresentation.witness (S b)).Output ∧
      HEq (TerminalStaticPresentation.witness T).metric
        (TerminalStaticPresentation.witness (S b)).metric ∧
      HEq (TerminalStaticPresentation.inclusion T) (TerminalStaticPresentation.inclusion (S b)) ∧
      HEq (TerminalStaticPresentation.witness T).cap
        (TerminalStaticPresentation.witness (S b)).cap ∧
      HEq (TerminalStaticPresentation.witness T).retained
        (TerminalStaticPresentation.witness (S b)).retained ∧
      HEq (TerminalStaticPresentation.witness T).collapse
        (TerminalStaticPresentation.witness (S b)).collapse ∧
      (TerminalStaticPresentation.witness T).windowMetric =
        (TerminalStaticPresentation.witness (S b)).windowMetric ∧
      (∀ x : standardCapWindow D,
        HEq (((TerminalStaticPresentation.inclusion T).comp
            (TerminalStaticPresentation.witness T).window) x)
          (((TerminalStaticPresentation.inclusion (S b)).comp
            (TerminalStaticPresentation.witness (S b)).window) x)) ∧
      (TerminalStaticPresentation.neck T).scale = (TerminalStaticPresentation.neck (S b)).scale ∧
      ∃ (x₀ : U) (δ : ℝ) (k : ℕ) (d : normalizedDatum h x₀ δ k)
        (w : StandardCap.CanonicalStaticInsertionWitness d
          fixed.collarLength fixed.collar_pos D m ε),
        metricScalarAt h x₀ = (TerminalStaticPresentation.neck T).scale ∧
        (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
          (TerminalStaticPresentation.neck T).scale * g.inner
            (((TerminalStaticPresentation.inclusion (S b)).comp
              (TerminalStaticPresentation.witness (S b)).window) x)
            (mfderiv ThreeModel ThreeModel
              ((TerminalStaticPresentation.inclusion (S b)).comp
                (TerminalStaticPresentation.witness (S b)).window) x v)
            (mfderiv ThreeModel ThreeModel
              ((TerminalStaticPresentation.inclusion (S b)).comp
                (TerminalStaticPresentation.witness (S b)).window) x z)) ∧
        (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
          (TerminalStaticPresentation.neck T).scale * g'.inner
            (((TerminalStaticPresentation.inclusion T).comp
              (TerminalStaticPresentation.witness T).window) x)
            (mfderiv ThreeModel ThreeModel
              ((TerminalStaticPresentation.inclusion T).comp
                (TerminalStaticPresentation.witness T).window) x v)
            (mfderiv ThreeModel ThreeModel
              ((TerminalStaticPresentation.inclusion T).comp
                (TerminalStaticPresentation.witness T).window) x z)) ∧
        ∀ z : ThreeBall, ∃ x : standardCapWindow D,
          ‖x.val‖ ≤ StandardCap.transitionEnd ∧
          ((TerminalStaticPresentation.inclusion T).comp
            (TerminalStaticPresentation.witness T).window) x =
            TerminalStaticPresentation.inclusion T
              ((TerminalStaticPresentation.witness T).cap z) := by
  cases hP
  cases hQ
  cases hD
  cases hN
  cases eq_of_heq hX
  cases eq_of_heq hU
  cases eq_of_heq hh
  cases eq_of_heq hg
  cases hfixed
  obtain ⟨x₀, δ, k, d, w, hscale, hmetric, hcap⟩ := hS b'
  exact ⟨b', S b', HEq.rfl, hS b', rfl, rfl, HEq.rfl, HEq.rfl,
    rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl,
    fun _ => HEq.rfl, rfl, x₀, δ, k, d, w, hscale, hmetric, hmetric, hcap⟩

/-- Once terminal metrics and record-neck data agree, the signed parent chart
point is the same. This lemma never projects an event-indexed static family. -/
private theorem terminal_parent_centers_and_scales
    {P P' : OrientedThreeStage.{u}}
    {U : TopologicalSpace.Opens P.Carrier} {U' : TopologicalSpace.Opens P'.Carrier}
    {g : SmoothRiemannianMetric ThreeModel U}
    {g' : SmoothRiemannianMetric ThreeModel U'}
    (hP : P = P') (hU : HEq U U') (hg : HEq g g')
    {ι ι' : Type} (hι : ι = ι')
    (δ : ι → ℝ) (δ' : ι' → ℝ) (hδ : HEq δ' δ)
    (k : ι → ℕ) (k' : ι' → ℕ) (hk : HEq k' k)
    (N : ∀ i, NormalizedNeck g (δ i) (k i))
    (N' : ∀ i, NormalizedNeck g' (δ' i) (k' i)) (hN : HEq N' N)
    (i : ι) (i' : ι') (hi : HEq i i')
    (side side' : Bool) (hside : side = side')
    {x : U} {x' : U'} {q q' : ℝ}
    (hx : ∃ h : ((N i).sphereMark, (if side then (1 : ℝ) else -1)) ∈ neckBuffer (δ i),
      x = (N i).chart ⟨((N i).sphereMark, (if side then (1 : ℝ) else -1)), h⟩)
    (hx' : ∃ h : ((N' i').sphereMark, (if side' then (1 : ℝ) else -1)) ∈ neckBuffer (δ' i'),
      x' = (N' i').chart ⟨((N' i').sphereMark, (if side' then (1 : ℝ) else -1)), h⟩)
    (hq : q = metricScalarAt g x) (hq' : q' = metricScalarAt g' x') :
    HEq x x' ∧ q = q' := by
  cases hP
  cases eq_of_heq hU
  cases eq_of_heq hg
  cases hι
  cases eq_of_heq hδ
  cases eq_of_heq hk
  cases eq_of_heq hN
  cases eq_of_heq hi
  cases hside
  obtain ⟨_, hx⟩ := hx
  obtain ⟨_, hx'⟩ := hx'
  have hxx : x = x' := hx.trans hx'.symm
  exact ⟨heq_of_eq hxx, hq.trans ((congrArg (metricScalarAt g) hxx).trans hq'.symm)⟩

/-- The transition itself, rather than the whole event, identifies its labels. -/
private theorem index_data_of_same_transition
    {P Q D₀ N₀ P' Q' D₁ N₁ : OrientedThreeStage.{u}}
    {X : SmoothCutCapTransition P Q D₀ N₀}
    {X' : SmoothCutCapTransition P' Q' D₁ N₁}
    (hP : P = P') (hQ : Q = Q') (hD : D₀ = D₁) (hN : N₀ = N₁)
    (hX : HEq X X')
    (b : {b : X.trace.tubes.Boundary //
      ∀ y, X.trace.tubes.coreBoundarySphere b y ∈ X.trace.retainedCore})
    (b' : {b : X'.trace.tubes.Boundary //
      ∀ y, X'.trace.tubes.coreBoundarySphere b y ∈ X'.trace.retainedCore})
    (hb : HEq b b') :
    X.trace.tubes.Index = X'.trace.tubes.Index ∧
      HEq b.val.1 b'.val.1 ∧ b.val.2 = b'.val.2 := by
  cases hP
  cases hQ
  cases hD
  cases hN
  cases eq_of_heq hX
  cases eq_of_heq hb
  exact ⟨rfl, HEq.rfl, rfl⟩

private theorem static_center_eq_parent_neck_chart
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) :
    ∃ h : ((R.neck b.val.1).sphereMark,
        (if b.val.2 then (1 : ℝ) else -1)) ∈ neckBuffer (R.delta b.val.1),
      (R.static b).neck.center = (R.neck b.val.1).chart
        ⟨((R.neck b.val.1).sphereMark,
          (if b.val.2 then (1 : ℝ) else -1)), h⟩ := by
  let x : neckBuffer (R.static b).delta :=
    ⟨((R.static b).neck.sphereMark, 0), by
      have hpos := inv_pos.mpr (R.static b).neck.delta_pos
      constructor <;> linarith⟩
  have hmem := R.recenter_in_buffer b x
  have hcenter := R.recenter_chart b x hmem
  have hparent : ((R.neck b.val.1).sphereMark,
      (if b.val.2 then (1 : ℝ) else -1)) ∈ neckBuffer (R.delta b.val.1) := by
    simpa only [x, add_zero, mul_one, R.recenter_mark] using hmem
  refine ⟨hparent, ?_⟩
  calc
    (R.static b).neck.center = (R.static b).neck.chart x := by
      simpa only [x] using (R.static b).neck.marked.symm
    _ = (R.neck b.val.1).chart
        ⟨((R.neck b.val.1).sphereMark,
          (if b.val.2 then (1 : ℝ) else -1)), hparent⟩ := by
      simpa only [x, add_zero, mul_one, R.recenter_mark] using hcenter

private theorem translated_record_static_centers_and_scales
    {N H : RetainedCoreHistory.{u}} {i : Fin N.eventCount} {j : Fin H.eventCount}
    (c : ℝ) (pFine pCoarse : CutoffParameters)
    (fine : GeometricCutoffRecord N.toHistory i pFine)
    (coarse : GeometricCutoffRecord H.toHistory j pCoarse)
    (hPresent : ((translate_retained_event (N.coreEvent i) c).toMetricCutCapEvent).SamePresentation
      (H.toHistory.event j))
    (hDelta : HEq coarse.delta fine.delta)
    (hOrder : HEq coarse.order fine.order)
    (hNeck : HEq coarse.neck fine.neck)
    (b : (N.toHistory.event i).RetainedBoundaryIndex)
    (b' : (H.toHistory.event j).RetainedBoundaryIndex) (hb : HEq b b') :
    HEq (fine.static b).neck.center (coarse.static b').neck.center ∧
      (fine.static b).neck.scale = (coarse.static b').neck.scale := by
  have hIndex := index_data_of_same_transition
    hPresent.incomingStage_eq hPresent.outgoingStage_eq
    hPresent.discarded_eq hPresent.capped_eq hPresent.transition_heq b b' hb
  have hOpen : HEq (N.toHistory.event i).incoming.terminalRegularOpen
      (H.toHistory.event j).incoming.terminalRegularOpen :=
    (heq_of_eq (translated_terminal_open (N.coreEvent i).incoming c).symm).trans
      hPresent.terminalRegion_heq
  have hMetric : HEq (N.toHistory.event i).terminal.metric
      (H.toHistory.event j).terminal.metric :=
    (translated_terminal_metric_heq (N.coreEvent i) c).symm.trans
      hPresent.terminalMetric_heq
  exact terminal_parent_centers_and_scales hPresent.incomingStage_eq hOpen hMetric
    hIndex.1 fine.delta coarse.delta hDelta fine.order coarse.order hOrder
    fine.neck coarse.neck hNeck b.val.1 b'.val.1 hIndex.2.1
    b.val.2 b'.val.2 hIndex.2.2
    (static_center_eq_parent_neck_chart fine b)
    (static_center_eq_parent_neck_chart coarse b')
    (fine.recenter_scale b) (coarse.recenter_scale b')

private theorem exists_raw_cap_of_translated_record_necks
    {N H : RetainedCoreHistory.{u}} {i : Fin N.eventCount} {j : Fin H.eventCount}
    (c : ℝ) (pFine pCoarse : CutoffParameters)
    (fine : GeometricCutoffRecord N.toHistory i pFine)
    (coarse : GeometricCutoffRecord H.toHistory j pCoarse)
    (hFine : ∀ b, (fine.static b).hasCanonicalWindow)
    (hfixed : pCoarse.fixed = pFine.fixed)
    (hPresent : ((translate_retained_event (N.coreEvent i) c).toMetricCutCapEvent).SamePresentation
      (H.toHistory.event j))
    (hDelta : HEq coarse.delta fine.delta)
    (hOrder : HEq coarse.order fine.order)
    (hNeck : HEq coarse.neck fine.neck)
    (b' : (H.toHistory.event j).RetainedBoundaryIndex) :
    ∃ (b : (N.toHistory.event i).RetainedBoundaryIndex)
      (raw : (H.toHistory.event j).PresentedStaticCap pCoarse.fixed
        pFine.modelRadius pFine.modelOrder pFine.modelAccuracy b'),
      HEq b b' ∧ raw.hasCanonicalWindow ∧
      raw.delta = (fine.static b).delta ∧ raw.order = (fine.static b).order ∧
      HEq raw.neck (fine.static b).neck ∧
      HEq raw.witness (fine.static b).witness ∧
      raw.witness.Output = (fine.static b).witness.Output ∧
      HEq raw.witness.metric (fine.static b).witness.metric ∧
      HEq raw.inclusion (fine.static b).inclusion ∧
      HEq raw.witness.cap (fine.static b).witness.cap ∧
      HEq raw.witness.retained (fine.static b).witness.retained ∧
      HEq raw.witness.collapse (fine.static b).witness.collapse ∧
      raw.witness.windowMetric = (fine.static b).witness.windowMetric ∧
      (∀ x : standardCapWindow pFine.modelRadius,
        HEq (raw.window x) ((fine.static b).window x)) ∧
      raw.neck.scale = (coarse.static b').neck.scale ∧
      (∀ z : ThreeBall,
        raw.inclusion (raw.witness.cap z) =
          (coarse.static b').inclusion ((coarse.static b').witness.cap z)) ∧
      (∀ (z : ThreeBall) (y : (H.stage j.succ).Carrier),
        (H.toHistory.event j).transition.trace.presentation
          ((H.toHistory.event j).transition.trace.capping.cap b'.val z) = Sum.inl y →
        raw.inclusion (raw.witness.cap z) = y) ∧
      (∀ x (v z : TangentSpace ThreeModel x), raw.witness.metric.inner x v z =
        (H.initialMetric j.succ).inner (raw.inclusion x)
          (mfderiv ThreeModel ThreeModel raw.inclusion x v)
          (mfderiv ThreeModel ThreeModel raw.inclusion x z)) ∧
      ∃ (x₀ : (N.toHistory.event i).incoming.terminalRegularOpen) (δ : ℝ) (k : ℕ)
        (d : normalizedDatum (N.toHistory.event i).terminal.metric x₀ δ k)
        (w : StandardCap.CanonicalStaticInsertionWitness d
          pFine.fixed.collarLength pFine.fixed.collar_pos
          pFine.modelRadius pFine.modelOrder pFine.modelAccuracy),
        metricScalarAt (N.toHistory.event i).terminal.metric x₀ = raw.neck.scale ∧
        (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
          raw.neck.scale * (N.toHistory.event i).outputMetric.inner ((fine.static b).window x)
            (mfderiv ThreeModel ThreeModel (fine.static b).window x v)
            (mfderiv ThreeModel ThreeModel (fine.static b).window x z)) ∧
        (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
          raw.neck.scale * (H.initialMetric j.succ).inner (raw.window x)
            (mfderiv ThreeModel ThreeModel raw.window x v)
            (mfderiv ThreeModel ThreeModel raw.window x z)) ∧
        ∀ z : ThreeBall, ∃ x : standardCapWindow pFine.modelRadius,
          ‖x.val‖ ≤ StandardCap.transitionEnd ∧
          raw.window x = raw.inclusion (raw.witness.cap z) := by
  have hOpen : HEq (N.toHistory.event i).incoming.terminalRegularOpen
      (H.toHistory.event j).incoming.terminalRegularOpen :=
    (heq_of_eq (translated_terminal_open (N.coreEvent i).incoming c).symm).trans
      hPresent.terminalRegion_heq
  have hMetric : HEq (N.toHistory.event i).terminal.metric
      (H.toHistory.event j).terminal.metric :=
    (translated_terminal_metric_heq (N.coreEvent i) c).symm.trans
      hPresent.terminalMetric_heq
  obtain ⟨b, T, hb, hT, hdelta, horder, hneck, hwitness, hOutput, hmetric,
      hinclusion, hcap, hretained, hcollapse, hwindowMetric, hwindow, hscale,
      x₀, δ, k, d, w, hwscale, hwnative, hwactual, hwcap⟩ :=
    terminal_cap_family_transport hPresent.incomingStage_eq hPresent.outgoingStage_eq
      hPresent.discarded_eq hPresent.capped_eq hPresent.transition_heq
      hOpen hMetric hPresent.outputMetric_heq hfixed.symm
      (fun b => TerminalStaticPresentation.ofPresented (fine.static b)) hFine b'
  let raw : (H.toHistory.event j).PresentedStaticCap pCoarse.fixed
      pFine.modelRadius pFine.modelOrder pFine.modelAccuracy b' :=
    TerminalStaticPresentation.toPresented T
  have hcommonScale : raw.neck.scale = (coarse.static b').neck.scale :=
    hscale.trans (translated_record_static_centers_and_scales c pFine pCoarse
      fine coarse hPresent hDelta hOrder hNeck b b' hb).2
  refine ⟨b, raw, hb, hT, hdelta, horder, hneck, hwitness, hOutput, hmetric,
    hinclusion, hcap, hretained, hcollapse, hwindowMetric, hwindow,
    hcommonScale, ?_, ?_, ?_, x₀, δ, k, d, w, hwscale, hwnative, ?_, hwcap⟩
  · intro z
    exact Sum.inl.inj ((raw.cap_eq z).symm.trans ((coarse.static b').cap_eq z))
  · intro z y hy
    exact Sum.inl.inj ((raw.cap_eq z).symm.trans hy)
  · intro x v z
    have hmetric := raw.inclusion_metric x v z
    rw [H.toHistory.event_output j] at hmetric
    exact hmetric
  · intro x v z
    refine (hwactual x v z).trans ?_
    exact congrArg (fun G : (H.stage j.succ).Metric => raw.neck.scale * G.inner (raw.window x)
      (mfderiv ThreeModel ThreeModel raw.window x v)
      (mfderiv ThreeModel ThreeModel raw.window x z)) (H.toHistory.event_output j)

/-- Preserve the same surgery and attach the original fine cap at every actual event. -/
theorem PreparedSpatialChain.exists_surgery_with_retained_raw_caps
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0}
    (S : PreparedSpatialChain pBase C P g)
    (hS : ∀ n, (S.state n).DistanceData Cdist)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
      (S.accuracy n) (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n))
    (hshift : ∀ n, (S.state (n + 1)).shift =
      (S.state n).history.time (Fin.last (S.state n).history.eventCount))
    (hoffset : ∀ n, (S.state (n + 1)).offset = (S.state n).history.eventCount)
    (hdrop : ∀ n, S.accuracy n ≤
      (S.state n).parameters.delta (preparedSpatialHorizon n) / 4)
    (a₀ : ℝ)
    (initialControl : ∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory i q),
      (
      (
      F.tower = S.tower ∧
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount),
        ((F.tower.history n).toHistory.event i).HasUniformDistanceScalar Cdist) ∧
      (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
        q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy ∧
        q.recenterConstant = pBase.recenterConstant) ∧
      (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      (∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
        q.delta t = (S.observation n).parameters.delta t ∧
        q.neckRadius t = (S.observation n).parameters.neckRadius t ∧
        q.protectedRadius t = (S.observation n).parameters.protectedRadius t) ∧
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
        (j : Fin (S.observation n).history.eventCount), i.val = j.val →
        HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
        HEq (records n i).delta ((S.observation n).records j).delta ∧
        HEq (records n i).order ((S.observation n).records j).order ∧
        HEq (records n i).neck ((S.observation n).records j).neck ∧
        HEq (records n i).static ((S.observation n).records j).static) ∧
      (∀ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
        (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
        (q.neckRadius t ^ 2)⁻¹ < metricScalarAt
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t)
          C.epsilon (max C.C1s C.Cbirth) (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) x,
          W.capTubeHasNeckChart C.epsilon) ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) C.epsilon t) ∧
      (∃ hc : Monotone (fun n => (F.tower.history n).eventCount),
        ∀ (m n : ℕ) (hmn : m ≤ n),
          (F.tower.initial m).IsPrefixOf (F.tower.initial n) ∧
          ∀ i : Fin (F.tower.history m).eventCount,
            HEq (records n (i.castLE (hc hmn))).nominalRadius (records m i).nominalRadius ∧
            HEq (records n (i.castLE (hc hmn))).delta (records m i).delta ∧
            HEq (records n (i.castLE (hc hmn))).order (records m i).order ∧
            HEq (records n (i.castLE (hc hmn))).neck (records m i).neck ∧
            HEq (records n (i.castLE (hc hmn))).static (records m i).static) ∧
      Filter.Tendsto q.delta Filter.atTop (nhds (0 : ℝ)) ∧
      ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
        ∀ t : ℝ, T ≤ t → ∀ n : ℕ,
        ∀ i : Fin (F.tower.history n).eventCount,
          (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
          ∀ h, (records n i).nominalRadius h ≤ η * q.neckRadius t
      ) ∧
      (∀ t : ℝ, 0 ≤ t →
        q.delta t = (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta t ∧
        q.neckRadius t =
          (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius t) ∧
      (∀ t : ℝ, 0 < t → q.delta t < S.diagonalLargerBallAccuracy (2 * t) (2 * t)) ∧
      (∀ n, (∀ x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) ∧
      (∀ m : ℕ, ∀ i : Fin (S.state (m + 1)).native.eventCount,
        let s := (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift;
        s ∈ Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
        q.delta s = S.accuracy m ∧
        (∀ u : ℝ, s ≤ u → q.delta u ≤ S.accuracy m) ∧
        (∀ T : ℝ, T ∈ Icc s (2 * s) →
          (S.state (m + 1)).radius ≤ q.neckRadius T) ∧
        (∀ A : ℝ, 0 < A → q.delta s < S.diagonalLargerBallAccuracy A s →
          A < 12 * (3 : ℝ) ^ m) ∧
        ∀ n : ℕ, s ≤ (n : ℝ) →
        ∃ j : Fin (F.tower.history n).eventCount,
          j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
          (F.tower.history n).time j.succ = s ∧
          HEq (records n j).nominalRadius ((W m).fineRecords i).nominalRadius ∧
          HEq (records n j).delta ((W m).fineRecords i).delta ∧
          HEq (records n j).order ((W m).fineRecords i).order ∧
          HEq (records n j).neck ((W m).fineRecords i).neck ∧
          HEq (records n j).static
            (fun z => translate_presented_static_cap
              ((S.state (m + 1)).native.coreEvent i) (S.state (m + 1)).shift
              ((((W m).fineRecords i).restrictModelWindow ((W m).fineWindows i)
                (S.state m).parameters.modelRadius_pos
                (W m).full_radius (W m).full_order (W m).full_accuracy).static z))) ∧
      (∀ (m n : ℕ) (j : Fin ((F.tower.history n).eventCount + 1)),
        (S.state (m + 1)).offset ≤ j.val →
        ∀ (y : ((F.tower.history n).stage j).Carrier) (s : ℝ),
          s ∈ Ioo ((F.tower.history n).time j)
            ((F.tower.history n).toHistory.stageEndTime j) →
          s < (3 : ℝ) ^ (m + 1) →
          ((S.state (m + 1)).radius ^ 2)⁻¹ <
            metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y →
          |derivWithin (fun u =>
            metricScalarAt ((F.tower.history n).toHistory.stageMetric j u) y) (Iic s) s| ≤
            C.Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y ^ 2)
      ) ∧
      (∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
        ∃ m : ℕ, m ≤ n ∧ ∃ i : Fin (S.state (m + 1)).native.eventCount,
          (S.state m).history.eventCount ≤ j.val ∧
          j.val < (S.state (m + 1)).history.eventCount ∧
          j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
          (F.tower.history n).time j.succ =
            (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ∧
          (F.tower.history n).time j.succ ∈
            Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
          ((translate_retained_event ((S.state (m + 1)).native.coreEvent i)
            (S.state (m + 1)).shift).toMetricCutCapEvent).SamePresentation
              ((F.tower.history n).toHistory.event j) ∧
          q.delta ((F.tower.history n).time j.succ) = S.accuracy m ∧
          Dcut m ≤ (W m).fineParameters.modelRadius ∧
          mcut m ≤ (W m).fineParameters.modelOrder ∧
          (W m).fineParameters.modelAccuracy ≤ εcut m ∧
          ∀ b' : ((F.tower.history n).toHistory.event j).RetainedBoundaryIndex,
            ∃ (b : ((S.state (m + 1)).native.toHistory.event i).RetainedBoundaryIndex)
              (raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap q.fixed
                (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder (W m).fineParameters.modelAccuracy b'),
              HEq b b' ∧ raw.hasCanonicalWindow ∧
              raw.delta = (((W m).fineRecords i).static b).delta ∧ raw.order = (((W m).fineRecords i).static b).order ∧
              HEq raw.neck (((W m).fineRecords i).static b).neck ∧
              HEq raw.witness (((W m).fineRecords i).static b).witness ∧
              raw.witness.Output = (((W m).fineRecords i).static b).witness.Output ∧
              HEq raw.witness.metric (((W m).fineRecords i).static b).witness.metric ∧
              HEq raw.inclusion (((W m).fineRecords i).static b).inclusion ∧
              HEq raw.witness.cap (((W m).fineRecords i).static b).witness.cap ∧
              HEq raw.witness.retained (((W m).fineRecords i).static b).witness.retained ∧
              HEq raw.witness.collapse (((W m).fineRecords i).static b).witness.collapse ∧
              raw.witness.windowMetric = (((W m).fineRecords i).static b).witness.windowMetric ∧
              (∀ x : standardCapWindow (W m).fineParameters.modelRadius,
                HEq (raw.window x) ((((W m).fineRecords i).static b).window x)) ∧
              raw.neck.scale = ((records n j).static b').neck.scale ∧
              (∀ z : ThreeBall,
                raw.inclusion (raw.witness.cap z) =
                  ((records n j).static b').inclusion (((records n j).static b').witness.cap z)) ∧
              (∀ (z : ThreeBall) (y : ((F.tower.history n).stage j.succ).Carrier),
                ((F.tower.history n).toHistory.event j).transition.trace.presentation
                  (((F.tower.history n).toHistory.event j).transition.trace.capping.cap b'.val z) = Sum.inl y →
                raw.inclusion (raw.witness.cap z) = y) ∧
              (∀ x (v z : TangentSpace ThreeModel x), raw.witness.metric.inner x v z =
                ((F.tower.history n).initialMetric j.succ).inner (raw.inclusion x)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x v)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x z)) ∧
              ∃ (x₀ : ((S.state (m + 1)).native.toHistory.event i).incoming.terminalRegularOpen) (δ : ℝ) (k : ℕ)
                (d : normalizedDatum ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ δ k)
                (w : StandardCap.CanonicalStaticInsertionWitness d
                  (W m).fineParameters.fixed.collarLength (W m).fineParameters.fixed.collar_pos
                  (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder (W m).fineParameters.modelAccuracy),
                metricScalarAt ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ = raw.neck.scale ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((S.state (m + 1)).native.toHistory.event i).outputMetric.inner ((((W m).fineRecords i).static b).window x)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x v)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x z)) ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((F.tower.history n).initialMetric j.succ).inner (raw.window x)
                    (mfderiv ThreeModel ThreeModel raw.window x v)
                    (mfderiv ThreeModel ThreeModel raw.window x z)) ∧
                ∀ z : ThreeBall, ∃ x : standardCapWindow (W m).fineParameters.modelRadius,
                  ‖x.val‖ ≤ StandardCap.transitionEnd ∧
                  raw.window x = raw.inclusion (raw.witness.cap z)) := by
  obtain ⟨F, q, κ, records, hOld⟩ :=
    S.exists_surgery_with_retained_quality hS εcut Dcut mcut W hshift hoffset
      hdrop a₀ initialControl
  have hTower := hOld.1.1
  have hStatic := hOld.1.2.2.1
  have hForward := hOld.2.2.2.2.1
  refine ⟨F, q, κ, records, hOld, ?_⟩
  intro n j
  obtain ⟨m, hmn, i, hleft, hright, hindex, hbirth, hblock, hbound, hPresent⟩ :=
    S.exists_native_birth_block_of_observation_event hoffset hTower n j
  have hEntry := hForward m i
  obtain ⟨j', hjindex, _, _, hDelta, hOrder, hNeck, _⟩ :=
    hEntry.2.2.2.2.2 n (hbirth.symm.trans_le hbound)
  have hj : j' = j := Fin.ext (hjindex.trans hindex.symm)
  subst j'
  have hδ : q.delta ((F.tower.history n).time j.succ) = S.accuracy m := by
    rw [hbirth]
    exact hEntry.2.1
  refine ⟨m, hmn, i, hleft, hright, hindex, hbirth, hblock, hPresent, hδ,
    (W m).fine_radius, (W m).fine_order, (W m).fine_accuracy, ?_⟩
  intro b'
  exact exists_raw_cap_of_translated_record_necks (S.state (m + 1)).shift
    (W m).fineParameters q ((W m).fineRecords i) (records n j)
    ((W m).fineWindows i) (hStatic.1.trans (W m).fine_fixed.symm)
    hPresent hDelta hOrder hNeck b'

private theorem raw_cap_request_premise_of_selected_family
    {H : RetainedCoreHistory.{u}} {j : Fin H.eventCount}
    {q pFine : CutoffParameters}
    (coarse : GeometricCutoffRecord H.toHistory j q)
    (εreq Rreq : ℝ) (mreq : ℕ)
    (hR : Rreq ≤ pFine.modelRadius) (hm : mreq ≤ pFine.modelOrder)
    (hε : pFine.modelAccuracy ≤ εreq)
    (raw : ∀ b : (H.toHistory.event j).RetainedBoundaryIndex,
      (H.toHistory.event j).PresentedStaticCap q.fixed
        pFine.modelRadius pFine.modelOrder pFine.modelAccuracy b)
    (hCanonical : ∀ b, (raw b).hasCanonicalWindow)
    (hScale : ∀ b, (raw b).neck.scale = (coarse.static b).neck.scale) :
    ∀ b : (H.toHistory.event j).RetainedBoundaryIndex,
      ∃ (Dbig ζ : ℝ) (m : ℕ)
        (R : (H.toHistory.event j).PresentedStaticCap q.fixed Dbig m ζ b),
        Rreq ≤ Dbig ∧ mreq ≤ m ∧ ζ ≤ εreq ∧ R.hasCanonicalWindow ∧
          R.neck.scale = (coarse.static b).neck.scale := by
  intro b
  exact ⟨pFine.modelRadius, pFine.modelAccuracy, pFine.modelOrder, raw b,
    hR, hm, hε, hCanonical b, hScale b⟩

end GC.GeneralFlow
