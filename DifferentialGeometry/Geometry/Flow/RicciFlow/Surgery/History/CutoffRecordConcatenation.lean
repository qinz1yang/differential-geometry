import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.ConcatenationHorizon
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordSplicing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows

set_option autoImplicit false
noncomputable section

open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace GC.GeneralFlow

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- O-CH11-FIX3：本树的 `omega` 不再展开 `Fin.last` / `Fin.succ` 的 `val`，先 `simp only` 再 `omega`。 -/
local macro "omega_fin" : tactic =>
  `(tactic| ((try simp only [Fin.val_last, Fin.val_succ, Fin.val_castSucc] at *) <;> omega))

open private castStageMap castStageMap_smooth from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordEventExtension

private def cast_open_neck {P : OrientedThreeStage.{u}}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck h δ k) : NormalizedNeck (hUV ▸ h) δ k := by
  cases hUV
  exact N

private theorem cast_open_neck_heq {P : OrientedThreeStage.{u}}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck h δ k) : HEq (cast_open_neck hUV N) N := by
  cases hUV
  exact HEq.rfl

private theorem cast_open_neck_normalizedMetric {P : OrientedThreeStage.{u}}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck h δ k) : (cast_open_neck hUV N).normalizedMetric = N.normalizedMetric := by
  cases hUV
  rfl

private theorem cast_open_neck_chart {P : OrientedThreeStage.{u}}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck h δ k) (x : neckBuffer δ) :
    ((cast_open_neck hUV N).chart x).val = (N.chart x).val := by
  cases hUV
  rfl

/-- The same terminal neck after translating the incoming slab. -/
def translate_terminal_neck
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : RetainedCoreEvent P Q a s) (c : ℝ)
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck E.terminal.metric δ k) :
    NormalizedNeck (translate_retained_event E c).terminal.metric δ k :=
  cast_open_neck (translated_terminal_open E.incoming c).symm N

theorem translate_terminal_neck_heq
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : RetainedCoreEvent P Q a s) (c : ℝ)
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck E.terminal.metric δ k) :
    HEq (translate_terminal_neck E c N) N :=
  cast_open_neck_heq (translated_terminal_open E.incoming c).symm N

private theorem translated_neck_normalizedMetric
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (E : RetainedCoreEvent P Q a s) (c : ℝ)
    {E' : RetainedCoreEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a + c) (hs : s' = s + c)
    (hE : HEq E' (translate_retained_event E c))
    {δ : ℝ} {k : ℕ} {N : NormalizedNeck E.terminal.metric δ k}
    {N' : NormalizedNeck E'.terminal.metric δ k} (hN : HEq N' N) :
    N'.normalizedMetric = N.normalizedMetric := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  have hn : N' = translate_terminal_neck E c N :=
    eq_of_heq (hN.trans (translate_terminal_neck_heq E c N).symm)
  rw [hn]
  exact cast_open_neck_normalizedMetric _ N

private theorem translated_neck_chart
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (E : RetainedCoreEvent P Q a s) (c : ℝ)
    {E' : RetainedCoreEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a + c) (hs : s' = s + c)
    (hE : HEq E' (translate_retained_event E c))
    {δ : ℝ} {k : ℕ} {N : NormalizedNeck E.terminal.metric δ k}
    {N' : NormalizedNeck E'.terminal.metric δ k} (hN : HEq N' N)
    (f : C(neckBuffer δ, P.Carrier)) (hf : ∀ x, f x = (N.chart x).val) :
    ∀ x, castStageMap hP.symm f x = (N'.chart x).val := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  have hn : N' = translate_terminal_neck E c N :=
    eq_of_heq (hN.trans (translate_terminal_neck_heq E c N).symm)
  rw [hn]
  intro x
  exact (hf x).trans (cast_open_neck_chart _ N x).symm

private theorem translated_event_crossing
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : RetainedCoreEvent P Q a s) (c : ℝ)
    (x : P.Carrier) (y : Q.Carrier) :
    (translate_retained_event E c).toMetricCutCapEvent.RegularCrossing x y ↔
      E.toMetricCutCapEvent.RegularCrossing x y := Iff.rfl

private theorem translated_crossing_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (E : RetainedCoreEvent P Q a s) (c : ℝ)
    {E' : RetainedCoreEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a + c) (hs : s' = s + c)
    (hE : HEq E' (translate_retained_event E c)) {δ : ℝ}
    (f : C(neckBuffer δ, P.Carrier)) (g : C(neckBuffer δ, Q.Carrier))
    (hf : ∀ x, E.toMetricCutCapEvent.RegularCrossing (f x) (g x)) :
    ∀ x, E'.toMetricCutCapEvent.RegularCrossing
      (castStageMap hP.symm f x) (castStageMap hQ.symm g x) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact fun x => (translated_event_crossing E c _ _).mpr (hf x)

private theorem translated_metric_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (E : RetainedCoreEvent P Q a s) (c : ℝ)
    {E' : RetainedCoreEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a + c) (hs : s' = s + c)
    (hE : HEq E' (translate_retained_event E c)) {δ : ℝ}
    (f : C(neckBuffer δ, P.Carrier)) (t : ℝ) (x : neckBuffer δ)
    (V W : TangentSpace NeckCylinderModel x) :
    (E'.incoming.flow.base.metric t).inner (castStageMap hP.symm f x)
      (mfderiv NeckCylinderModel ThreeModel (castStageMap hP.symm f) x V)
      (mfderiv NeckCylinderModel ThreeModel (castStageMap hP.symm f) x W) =
    (E.incoming.flow.base.metric (t - c)).inner (f x)
      (mfderiv NeckCylinderModel ThreeModel f x V)
      (mfderiv NeckCylinderModel ThreeModel f x W) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  rfl

/-- The time translation is defined on the whole real line. Clamping before the new
time origin retains the positivity requirements of `CutoffParameters`. -/
def translate_cutoff_parameters (p : CutoffParameters) (c : ℝ) : CutoffParameters where
  delta t := p.delta (max (t - c) 0)
  neckRadius t := p.neckRadius (max (t - c) 0)
  protectedRadius t := p.protectedRadius (max (t - c) 0)
  delta_pos t _ := p.delta_pos _ (le_max_right _ _)
  delta_lt_one t _ := p.delta_lt_one _ (le_max_right _ _)
  neckRadius_pos t _ := p.neckRadius_pos _ (le_max_right _ _)
  protectedRadius_pos t _ := p.protectedRadius_pos _ (le_max_right _ _)
  fixed := p.fixed
  modelRadius := p.modelRadius
  modelRadius_pos := p.modelRadius_pos
  modelOrder := p.modelOrder
  modelAccuracy := p.modelAccuracy
  modelAccuracy_pos := p.modelAccuracy_pos
  recenterConstant := p.recenterConstant
  recenterConstant_ge_four := p.recenterConstant_ge_four

theorem translate_cutoff_parameters_eval (p : CutoffParameters) (c t : ℝ) (ht : 0 ≤ t) :
    (translate_cutoff_parameters p c).delta (t + c) = p.delta t ∧
    (translate_cutoff_parameters p c).neckRadius (t + c) = p.neckRadius t ∧
    (translate_cutoff_parameters p c).protectedRadius (t + c) = p.protectedRadius t := by
  simp only [translate_cutoff_parameters, add_sub_cancel_right, max_eq_left ht,
    and_self]

/- The following presentation removes only the incoming slab's time indices. It
allows equality elimination on the terminal open set without asserting equality
of events at different times. All geometric fields are the original fields. -/
private structure TerminalStaticPresentation
    {P Q D₀ N₀ : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D₀ N₀)
    (U : TopologicalSpace.Opens P.Carrier) (h : SmoothRiemannianMetric ThreeModel U)
    (g : Q.Metric) (fixed : StaticCapScaffold) (D : ℝ) (m : ℕ) (ε : ℝ)
    (b : {b : X.trace.tubes.Boundary //
      ∀ y, X.trace.tubes.coreBoundarySphere b y ∈ X.trace.retainedCore}) where
  delta : ℝ
  order : ℕ
  neck : NormalizedNeck h delta order
  witness : StaticCapWitness neck fixed D m ε
  inclusion : C(witness.Output, Q.Carrier)
  inclusion_smooth : IsSmoothEmbedding ThreeModel ThreeModel ∞ inclusion
  inclusion_metric : ∀ x V W, witness.metric.inner x V W =
    g.inner (inclusion x) (mfderiv ThreeModel ThreeModel inclusion x V)
      (mfderiv ThreeModel ThreeModel inclusion x W)
  cap_eq : ∀ x : ThreeBall,
    X.trace.presentation (X.trace.capping.cap b.1 x) = Sum.inl (inclusion (witness.cap x))
  attaching_eq : (witness.attaching : Sphere 2 → Sphere 2) = X.trace.capping.attaching b.1
  retainedPoint : (x : neckRetainedCollar delta) →
    {p : X.trace.tubes.core // p ∈ X.trace.retainedCore}
  retained_point_eq : ∀ x : neckRetainedCollar delta, ∀ hx : x.1 ∈ neckBuffer delta,
    (retainedPoint x).1.1 = (neck.chart ⟨x.1, hx⟩).1
  retained_eq : ∀ x,
    X.trace.presentation (X.trace.capping.coreInclusion (retainedPoint x).1) =
      Sum.inl (inclusion (witness.retained x))

private def TerminalStaticPresentation.ofPresented
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b) :
    TerminalStaticPresentation E.transition E.incoming.terminalRegularOpen
      E.terminal.metric E.outputMetric fixed D m ε b where
  delta := S.delta
  order := S.order
  neck := S.neck
  witness := S.witness
  inclusion := S.inclusion
  inclusion_smooth := S.inclusion_smooth
  inclusion_metric := S.inclusion_metric
  cap_eq := S.cap_eq
  attaching_eq := S.attaching_eq
  retainedPoint := S.retainedPoint
  retained_point_eq := S.retained_point_eq
  retained_eq := S.retained_eq

private def TerminalStaticPresentation.toPresented
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : TerminalStaticPresentation E.transition E.incoming.terminalRegularOpen
      E.terminal.metric E.outputMetric fixed D m ε b) :
    E.PresentedStaticCap fixed D m ε b where
  delta := S.delta
  order := S.order
  neck := S.neck
  witness := S.witness
  inclusion := S.inclusion
  inclusion_smooth := S.inclusion_smooth
  inclusion_metric := S.inclusion_metric
  cap_eq := S.cap_eq
  attaching_eq := S.attaching_eq
  retainedPoint := S.retainedPoint
  retained_point_eq := S.retained_point_eq
  retained_eq := S.retained_eq

private def TerminalStaticPresentation.castOpen
    {P Q D₀ N₀ : OrientedThreeStage.{u}} {X : SmoothCutCapTransition P Q D₀ N₀}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {g : Q.Metric}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {b : {b : X.trace.tubes.Boundary //
      ∀ y, X.trace.tubes.coreBoundarySphere b y ∈ X.trace.retainedCore}}
    (S : TerminalStaticPresentation X U h g fixed D m ε b) :
    TerminalStaticPresentation X V (hUV ▸ h) g fixed D m ε b := by
  cases hUV
  exact S

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

private def TerminalStaticPresentation.Canonical
    {P Q D₀ N₀ : OrientedThreeStage.{u}} {X : SmoothCutCapTransition P Q D₀ N₀}
    {U : TopologicalSpace.Opens P.Carrier} {h : SmoothRiemannianMetric ThreeModel U}
    {g : Q.Metric} {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {b : {b : X.trace.tubes.Boundary //
      ∀ y, X.trace.tubes.coreBoundarySphere b y ∈ X.trace.retainedCore}}
    (S : TerminalStaticPresentation X U h g fixed D m ε b) : Prop :=
  ∃ (x₀ : U) (δ : ℝ) (k : ℕ) (d : normalizedDatum h x₀ δ k)
    (w : DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness
      d fixed.collarLength fixed.collar_pos D m ε),
    metricScalarAt h x₀ = S.neck.scale ∧
    (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
      S.neck.scale * g.inner ((S.inclusion.comp S.witness.window) x)
        (mfderiv ThreeModel ThreeModel (S.inclusion.comp S.witness.window) x v)
        (mfderiv ThreeModel ThreeModel (S.inclusion.comp S.witness.window) x z)) ∧
    ∀ z : ThreeBall, ∃ x : standardCapWindow D,
      ‖x.val‖ ≤ DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd ∧
      (S.inclusion.comp S.witness.window) x = S.inclusion (S.witness.cap z)

private theorem TerminalStaticPresentation.castOpen_canonical
    {P Q D₀ N₀ : OrientedThreeStage.{u}} {X : SmoothCutCapTransition P Q D₀ N₀}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {g : Q.Metric}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {b : {b : X.trace.tubes.Boundary //
      ∀ y, X.trace.tubes.coreBoundarySphere b y ∈ X.trace.retainedCore}}
    (S : TerminalStaticPresentation X U h g fixed D m ε b) (hS : S.Canonical) :
    (S.castOpen hUV).Canonical := by
  cases hUV
  exact hS

private theorem TerminalStaticPresentation.castOpen_geometry
    {P Q D₀ N₀ : OrientedThreeStage.{u}} {X : SmoothCutCapTransition P Q D₀ N₀}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {g : Q.Metric}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {b : {b : X.trace.tubes.Boundary //
      ∀ y, X.trace.tubes.coreBoundarySphere b y ∈ X.trace.retainedCore}}
    (S : TerminalStaticPresentation X U h g fixed D m ε b) :
    (S.castOpen hUV).delta = S.delta ∧ (S.castOpen hUV).order = S.order ∧
    HEq (S.castOpen hUV).neck S.neck ∧
    HEq (S.castOpen hUV).witness S.witness ∧
    (S.castOpen hUV).witness.Output = S.witness.Output ∧
    HEq (S.castOpen hUV).witness.metric S.witness.metric ∧
    HEq (S.castOpen hUV).inclusion S.inclusion ∧
    HEq (S.castOpen hUV).witness.cap S.witness.cap ∧
    HEq (S.castOpen hUV).witness.retained S.witness.retained ∧
    HEq (S.castOpen hUV).witness.collapse S.witness.collapse ∧
    (S.castOpen hUV).witness.windowMetric = S.witness.windowMetric ∧
    (S.castOpen hUV).inclusion.comp (S.castOpen hUV).witness.window =
      S.inclusion.comp S.witness.window := by
  cases hUV
  exact ⟨rfl, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl,
    HEq.rfl, HEq.rfl, rfl, rfl⟩

/- O-CH11-FIX3B：elaboration 辅助引理（`exact` 的期望类型传播在 `hasCanonicalWindow` 与
`Canonical` 之间 whnf 超时；拆成三步）。 -/
private theorem TerminalStaticPresentation.toPresented_canonical
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : TerminalStaticPresentation E.transition E.incoming.terminalRegularOpen
      E.terminal.metric E.outputMetric fixed D m ε b) (hS : S.Canonical) :
    S.toPresented.hasCanonicalWindow := hS

private theorem TerminalStaticPresentation.ofPresented_canonical
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b) (hS : S.hasCanonicalWindow) :
    (TerminalStaticPresentation.ofPresented S).Canonical := hS

/-- The selected cap at a translated event. The original output geometry and
canonical insertion datum are transported across the equality of terminal opens;
the distinct event time indices are never identified. -/
def translate_presented_static_cap
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : RetainedCoreEvent P Q a s) (c : ℝ)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {b : E.toMetricCutCapEvent.RetainedBoundaryIndex}
    (S : E.toMetricCutCapEvent.PresentedStaticCap fixed D m ε b) :
    (translate_retained_event E c).toMetricCutCapEvent.PresentedStaticCap fixed D m ε b :=
  TerminalStaticPresentation.toPresented
    ((TerminalStaticPresentation.ofPresented S).castOpen
      (translated_terminal_open E.incoming c).symm)

theorem translate_presented_static_cap_canonical
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : RetainedCoreEvent P Q a s) (c : ℝ)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {b : E.toMetricCutCapEvent.RetainedBoundaryIndex}
    (S : E.toMetricCutCapEvent.PresentedStaticCap fixed D m ε b)
    (hS : S.hasCanonicalWindow) :
    (translate_presented_static_cap E c S).hasCanonicalWindow := by
  unfold translate_presented_static_cap
  have h1 := TerminalStaticPresentation.ofPresented_canonical S hS
  have h2 := (TerminalStaticPresentation.ofPresented S).castOpen_canonical
    (translated_terminal_open E.incoming c).symm h1
  exact TerminalStaticPresentation.toPresented_canonical _ h2

/-- Every listed object is the supplied cap's geometry. Equality of complete
`PresentedStaticCap` values would additionally identify the event time indices,
so the public contract states the actual geometric equalities instead. -/
theorem translate_presented_static_cap_geometry
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : RetainedCoreEvent P Q a s) (c : ℝ)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {b : E.toMetricCutCapEvent.RetainedBoundaryIndex}
    (S : E.toMetricCutCapEvent.PresentedStaticCap fixed D m ε b) :
    (translate_presented_static_cap E c S).delta = S.delta ∧
    (translate_presented_static_cap E c S).order = S.order ∧
    HEq (translate_presented_static_cap E c S).neck S.neck ∧
    HEq (translate_presented_static_cap E c S).witness S.witness ∧
    (translate_presented_static_cap E c S).witness.Output = S.witness.Output ∧
    HEq (translate_presented_static_cap E c S).witness.metric S.witness.metric ∧
    HEq (translate_presented_static_cap E c S).inclusion S.inclusion ∧
    HEq (translate_presented_static_cap E c S).witness.cap S.witness.cap ∧
    HEq (translate_presented_static_cap E c S).witness.retained S.witness.retained ∧
    HEq (translate_presented_static_cap E c S).witness.collapse S.witness.collapse ∧
    (translate_presented_static_cap E c S).witness.windowMetric = S.witness.windowMetric ∧
    (translate_presented_static_cap E c S).window = S.window := by
  unfold translate_presented_static_cap
  have h := (TerminalStaticPresentation.ofPresented S).castOpen_geometry
    (translated_terminal_open E.incoming c).symm
  exact h

private theorem retained_event_transport_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : RetainedCoreEvent P Q a s) :
    HEq (RetainedCoreEvent.transport hP hQ ha hs E) E := by
  cases hP
  cases hQ
  cases ha
  cases hs
  exact HEq.rfl

private theorem append_core_event_old_heq
    {Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u}) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hi : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) (i : Fin H.eventCount) :
    HEq ((H.appendEvent hs E hi).coreEvent i.castSucc) (H.coreEvent i) := by
  change HEq (H.extendCoreEventFamily E i.castSucc) (H.coreEvent i)
  rw [H.extendCoreEventFamily_castSucc]
  exact retained_event_transport_heq _ _ _ _ _

private theorem append_core_event_last_heq
    {Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u}) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hi : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    HEq ((H.appendEvent hs E hi).coreEvent (Fin.last H.eventCount)) E := by
  change HEq (H.extendCoreEventFamily E (Fin.last H.eventCount)) E
  rw [H.extendCoreEventFamily_last]
  exact retained_event_transport_heq _ _ _ _ _

/-- The entire translated finite tail, including its selected events. This stores
presentation identities, not cutoff records or estimates. The endpoint `n` may
be an intermediate construction stage. -/
structure AffineEventPrefix
    (K J : RetainedCoreHistory.{u}) (c : ℝ) (offset : ℕ)
    (n : Fin (K.eventCount + 1)) where
  count_eq : J.eventCount = offset + n.val
  time_eq : ∀ j : Fin (n.val + 1),
    J.time ⟨offset + j.val, by omega⟩ =
      K.time (j.castLE (by omega)) + c
  stage_eq : ∀ j : Fin (n.val + 1),
    J.stage ⟨offset + j.val, by omega⟩ = K.stage (j.castLE (by omega))
  initialMetric_heq : ∀ j : Fin (n.val + 1),
    HEq (J.initialMetric ⟨offset + j.val, by omega⟩)
      (K.initialMetric (j.castLE (by omega)))
  event_heq : ∀ j : Fin n.val,
    HEq (J.coreEvent ⟨offset + j.val, by omega⟩)
      (translate_retained_event (K.coreEvent (j.castLE (by omega))) c)

private theorem retained_event_incoming_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : RetainedCoreEvent P Q a s} {E' : RetainedCoreEvent P' Q' a' s'}
    (hE : HEq E E') (t : ℝ) :
    HEq (E.incoming.flow.base.metric t) (E'.incoming.flow.base.metric t) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact HEq.rfl

/-- The affine presentation retains the actual incoming metric at every real
time, including the times needed to transport backward parabolic necks. -/
theorem AffineEventPrefix.incoming_metric_heq
    {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    {n : Fin (K.eventCount + 1)} (A : AffineEventPrefix K J c offset n)
    (j : Fin n.val) (t : ℝ) :
    HEq ((J.coreEvent ⟨offset + j.val, by have := A.count_eq; omega⟩).incoming.flow.base.metric t)
      ((K.coreEvent (j.castLE (by omega))).incoming.flow.base.metric (t - c)) := by
  have hmetric := retained_event_incoming_heq
    (A.stage_eq j.castSucc) (A.stage_eq j.succ)
    (A.time_eq j.castSucc) (A.time_eq j.succ) (A.event_heq j) t
  exact hmetric.trans (heq_of_eq
    ((K.coreEvent (j.castLE (by omega))).incoming.timeTranslate_metric c t))

def AffineEventPrefix.eventIndex
    {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount))
    (i : Fin K.eventCount) : Fin J.eventCount :=
  ⟨offset + i.val, by have := A.count_eq; omega_fin⟩

/-- An actual backward neck remains entirely in the translated tail: its source
left endpoint is nonnegative, so its translated left endpoint is at least the
join time. Old-prefix events therefore never require a new chart. -/
def AffineEventPrefix.translateBackwardNeck
    {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount)) (hc : 0 ≤ c)
    {i : Fin K.eventCount} {δ r : ℝ} {k : ℕ}
    {N : NormalizedNeck (K.coreEvent i).terminal.metric δ k}
    {N' : NormalizedNeck (J.coreEvent (A.eventIndex i)).terminal.metric δ k}
    (hneck : HEq N' N) (B : IncomingBackwardNeck K.toHistory i N r) :
    IncomingBackwardNeck J.toHistory (A.eventIndex i) N' r := by
  have hcount := A.count_eq
  have htime (j : Fin K.eventCount) :
      J.time (A.eventIndex j).succ = K.time j.succ + c := A.time_eq j.succ
  have hjoin : J.time ⟨offset, by omega⟩ = c := by
    simpa only [Fin.val_zero, Nat.add_zero, Fin.castLE_zero, K.time_zero, zero_add]
      using A.time_eq 0
  have hleft : c ≤ J.time (A.eventIndex i).succ - r ^ 2 := by
    rw [htime]
    linarith [B.left_nonneg]
  have after (j : Fin J.eventCount)
      (ha : J.time (A.eventIndex i).succ - r ^ 2 < J.time j.succ) : offset ≤ j.val := by
    by_contra h
    have hj : j.succ ≤ (⟨offset, by omega⟩ : Fin (J.eventCount + 1)) := by
      change j.val + 1 ≤ offset
      omega
    have hb := J.time_strictMono.monotone hj
    rw [hjoin] at hb
    linarith
  let old (j : Fin J.eventCount) (hj : j.val ≤ (A.eventIndex i).val)
      (ha : J.time (A.eventIndex i).succ - r ^ 2 < J.time j.succ) : Fin K.eventCount :=
    ⟨j.val - offset, by have := after j ha; change j.val ≤ offset + i.val at hj; omega⟩
  have index_old (j : Fin J.eventCount) (hj : j.val ≤ (A.eventIndex i).val)
      (ha : J.time (A.eventIndex i).succ - r ^ 2 < J.time j.succ) :
      A.eventIndex (old j hj ha) = j := by
    apply Fin.ext
    have := after j ha
    simp only [AffineEventPrefix.eventIndex, old, Fin.val_mk]
    omega
  have old_le (j : Fin J.eventCount) (hj : j.val ≤ (A.eventIndex i).val)
      (ha : J.time (A.eventIndex i).succ - r ^ 2 < J.time j.succ) :
      (old j hj ha).val ≤ i.val := by
    have := after j ha
    change j.val ≤ offset + i.val at hj
    change j.val - offset ≤ i.val
    omega
  have old_time (j : Fin J.eventCount) (hj : j.val ≤ (A.eventIndex i).val)
      (ha : J.time (A.eventIndex i).succ - r ^ 2 < J.time j.succ) :
      J.time j.succ = K.time (old j hj ha).succ + c := by
    have h := htime (old j hj ha)
    rw [index_old j hj ha] at h
    exact h
  have old_left (j : Fin J.eventCount) (hj : j.val ≤ (A.eventIndex i).val)
      (ha : J.time (A.eventIndex i).succ - r ^ 2 < J.time j.succ) :
      K.time i.succ - r ^ 2 < K.time (old j hj ha).succ := by
    have h1 := old_time j hj ha
    have h2 := htime i
    linarith
  let chart (j : Fin J.eventCount) (hj : j.val ≤ (A.eventIndex i).val)
      (ha : J.time (A.eventIndex i).succ - r ^ 2 < J.time j.succ) :
      C(neckBuffer δ, (J.stage j.castSucc).Carrier) :=
    castStageMap
      ((congrArg (fun l : Fin J.eventCount => J.stage l.castSucc)
        (index_old j hj ha)).symm.trans (A.stage_eq (old j hj ha).castSucc)).symm
      (B.stageChart (old j hj ha) (old_le j hj ha) (old_left j hj ha))
  refine {
    radius_pos := B.radius_pos
    left_nonneg := hc.trans hleft
    stageChart := chart
    stageChart_smooth := fun j hj ha => castStageMap_smooth _ _ (B.stageChart_smooth _ _ _)
    terminal_chart := ?_
    crossing := ?_
    metric := B.metric
    terminal_metric := B.terminal_metric.trans ?_
    metric_on_slab := ?_
    timeDifferenceJet := B.timeDifferenceJet
    timeDifferenceJet_eq := B.timeDifferenceJet_eq
    parabolic_closeness := B.parabolic_closeness
    metric_smooth := B.metric_smooth }
  · intro ha
    have hi : old (A.eventIndex i) le_rfl ha = i := by
      apply Fin.ext
      simp only [old, AffineEventPrefix.eventIndex, Fin.val_mk, Nat.add_sub_cancel_left]
    have key : ∀ (o : Fin K.eventCount) (ho : i = o) (h1 : o.val ≤ i.val)
        (h2 : K.time i.succ - r ^ 2 < K.time o.succ)
        (hst : J.stage (A.eventIndex i).castSucc = K.stage o.castSucc),
        ∀ x, castStageMap hst.symm (B.stageChart o h1 h2) x = (N'.chart x).1 := by
      intro o ho h1 h2 hst
      subst ho
      exact translated_neck_chart (K.coreEvent i) c
        (A.stage_eq i.castSucc) (A.stage_eq i.succ)
        (A.time_eq i.castSucc) (A.time_eq i.succ) (A.event_heq i) hneck
        (B.stageChart i h1 h2) (B.terminal_chart _)
    dsimp only [chart]
    exact key _ hi.symm (old_le _ le_rfl ha) (old_left _ le_rfl ha)
      ((congrArg (fun l : Fin J.eventCount => J.stage l.castSucc)
        (index_old _ le_rfl ha)).symm.trans (A.stage_eq (old _ le_rfl ha).castSucc))
  · intro j hj
    dsimp only
    intro ha hn
    let j₀ := old j hj.le ha
    let next : Fin J.eventCount := ⟨j.val + 1, by
      have h1 : j.val < (A.eventIndex i).val := hj
      have h2 := (A.eventIndex i).isLt
      omega⟩
    let next₀ : Fin K.eventCount := ⟨j₀.val + 1, by
      have := after j ha
      change j.val < offset + i.val at hj
      dsimp [j₀, old]
      omega⟩
    have hj₀ : j₀.val < i.val := by
      have := after j ha
      change j.val < offset + i.val at hj
      dsimp [j₀, old]
      omega
    have hn₀ : old next (by
        have h1 : j.val < (A.eventIndex i).val := hj
        have h2 : (A.eventIndex i).val = offset + i.val := rfl
        change j.val + 1 ≤ offset + i.val; omega) hn = next₀ := by
      apply Fin.ext
      have := after j ha
      dsimp [old, next, next₀, j₀]
      omega
    have heqj := index_old j hj.le ha
    have heqn : A.eventIndex next₀ = next := by
      rw [← hn₀]
      exact index_old next (by
        have h1 : j.val < (A.eventIndex i).val := hj
        change j.val + 1 ≤ (A.eventIndex i).val
        omega) hn
    have hstagej : J.stage j.castSucc = K.stage j₀.castSucc :=
      (congrArg (fun l : Fin J.eventCount => J.stage l.castSucc) heqj).symm.trans
        (A.stage_eq j₀.castSucc)
    have hstagen : J.stage next.castSucc = K.stage next₀.castSucc :=
      (congrArg (fun l : Fin J.eventCount => J.stage l.castSucc) heqn).symm.trans
        (A.stage_eq next₀.castSucc)
    have hev : HEq (J.coreEvent j) (translate_retained_event (K.coreEvent j₀) c) :=
      (heq_apply_of_eq J.coreEvent heqj).symm.trans (A.event_heq j₀)
    have hstart : J.time j.castSucc = K.time j₀.castSucc + c :=
      (congrArg (fun l : Fin J.eventCount => J.time l.castSucc) heqj).symm.trans
        (A.time_eq j₀.castSucc)
    have hend : J.time j.succ = K.time j₀.succ + c := old_time j hj.le ha
    have hnextleft : K.time i.succ - r ^ 2 < K.time next₀.succ := by
      have hh := old_left next (by
        have h1 : j.val < (A.eventIndex i).val := hj
        have h2 : (A.eventIndex i).val = offset + i.val := rfl
        change j.val + 1 ≤ offset + i.val; omega) hn
      rwa [hn₀] at hh
    change ∀ x, (J.toHistory.event j).RegularCrossing (chart j hj.le ha x)
      (chart next (by
        have h1 : j.val < (A.eventIndex i).val := hj
        have h2 : (A.eventIndex i).val = offset + i.val := rfl
        change j.val + 1 ≤ offset + i.val; omega) hn x)
    have hnle : next.val ≤ (A.eventIndex i).val := by
      have h1 : j.val < (A.eventIndex i).val := hj
      change j.val + 1 ≤ (A.eventIndex i).val
      omega
    have key : ∀ (o : Fin K.eventCount) (ho : next₀ = o) (h1 : o.val ≤ i.val)
        (h2 : K.time i.succ - r ^ 2 < K.time o.succ)
        (hst : J.stage next.castSucc = K.stage o.castSucc),
        ∀ x, (J.toHistory.event j).RegularCrossing
          (castStageMap hstagej.symm
            (B.stageChart j₀ (old_le j hj.le ha) (old_left j hj.le ha)) x)
          (castStageMap hst.symm (B.stageChart o h1 h2) x) := by
      intro o ho h1 h2 hst
      subst ho
      exact translated_crossing_transport (K.coreEvent j₀) c
        hstagej hstagen hstart hend hev
        (B.stageChart j₀ hj₀.le (old_left j hj.le ha))
        (B.stageChart next₀ h1 h2)
        (B.crossing j₀ hj₀ (old_left j hj.le ha) hnextleft)
    dsimp only [chart]
    exact key _ hn₀.symm (old_le next hnle hn) (old_left next hnle hn)
      ((congrArg (fun l : Fin J.eventCount => J.stage l.castSucc)
        (index_old next hnle hn)).symm.trans (A.stage_eq (old next hnle hn).castSucc))
  · exact (translated_neck_normalizedMetric (K.coreEvent i) c
      (A.stage_eq i.castSucc) (A.stage_eq i.succ)
      (A.time_eq i.castSucc) (A.time_eq i.succ) (A.event_heq i) hneck).symm
  · intro j hj ha v hv hlo hhi x V W
    let j₀ := old j hj ha
    have hindex := index_old j hj ha
    have hstage : J.stage j.castSucc = K.stage j₀.castSucc :=
      (congrArg (fun l : Fin J.eventCount => J.stage l.castSucc) hindex).symm.trans
        (A.stage_eq j₀.castSucc)
    have hstage' : J.stage j.succ = K.stage j₀.succ :=
      (congrArg (fun l : Fin J.eventCount => J.stage l.succ) hindex).symm.trans
        (A.stage_eq j₀.succ)
    have hstart : J.time j.castSucc = K.time j₀.castSucc + c :=
      (congrArg (fun l : Fin J.eventCount => J.time l.castSucc) hindex).symm.trans
        (A.time_eq j₀.castSucc)
    have hend : J.time j.succ = K.time j₀.succ + c := old_time j hj ha
    have hev : HEq (J.coreEvent j) (translate_retained_event (K.coreEvent j₀) c) :=
      (heq_apply_of_eq J.coreEvent hindex).symm.trans (A.event_heq j₀)
    have hlo₀ : K.time j₀.castSucc ≤ K.time i.succ + r ^ 2 * v := by
      change J.time j.castSucc ≤ J.time (A.eventIndex i).succ + r ^ 2 * v at hlo
      rw [hstart, htime] at hlo
      linarith
    have hhi₀ : K.time i.succ + r ^ 2 * v < K.time j₀.succ := by
      change J.time (A.eventIndex i).succ + r ^ 2 * v < J.time j.succ at hhi
      rw [hend, htime] at hhi
      linarith
    have hmetric := translated_metric_transport (K.coreEvent j₀) c
      hstage hstage' hstart hend hev
      (B.stageChart j₀ (old_le j hj ha) (old_left j hj ha))
      (J.time (A.eventIndex i).succ + r ^ 2 * v) x V W
    rw [show J.time (A.eventIndex i).succ + r ^ 2 * v - c =
      K.time i.succ + r ^ 2 * v by rw [htime]; ring] at hmetric
    exact (B.metric_on_slab j₀ (old_le j hj ha) (old_left j hj ha)
      v hv hlo₀ hhi₀ x V W).trans (congrArg ((r ^ 2)⁻¹ * ·) hmetric.symm)

structure RawInitialPrefix (H J : RetainedCoreHistory.{u}) where
  count_le : H.eventCount ≤ J.eventCount
  time_eq : ∀ j : Fin (H.eventCount + 1),
    J.time (j.castLE (Nat.succ_le_succ count_le)) = H.time j
  stage_eq : ∀ j : Fin (H.eventCount + 1),
    J.stage (j.castLE (Nat.succ_le_succ count_le)) = H.stage j
  event_heq : ∀ j : Fin H.eventCount,
    HEq (J.coreEvent (j.castLE count_le)) (H.coreEvent j)

def RawInitialPrefix.refl (H : RetainedCoreHistory.{u}) : RawInitialPrefix H H where
  count_le := le_rfl
  time_eq := fun _ => rfl
  stage_eq := fun _ => rfl
  event_heq := fun _ => HEq.rfl

private def RawInitialPrefix.append
    {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (hs : J.time (Fin.last J.eventCount) < s)
    (E : RetainedCoreEvent (J.stage (Fin.last J.eventCount)) Q
      (J.time (Fin.last J.eventCount)) s)
    (hi : E.incoming.flow.base.metric (J.time (Fin.last J.eventCount)) =
      J.initialMetric (Fin.last J.eventCount)) : RawInitialPrefix H (J.appendEvent hs E hi) where
  count_le := I.count_le.trans (Nat.le_succ _)
  time_eq j := (J.appendEvent_time_castSucc hs E hi _).trans (I.time_eq j)
  stage_eq j := (J.appendEvent_stage_castSucc hs E hi _).trans (I.stage_eq j)
  event_heq j := (append_core_event_old_heq J hs E hi _).trans (I.event_heq j)

private def RawInitialPrefix.extendHorizon
    {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    (T : ℝ) (hT : J.horizon ≤ T)
    (S : (J.stage (Fin.last J.eventCount)).ClosedSlab (J.time (Fin.last J.eventCount)) T)
    (hi : S.flow.base.metric (J.time (Fin.last J.eventCount)) =
      J.initialMetric (Fin.last J.eventCount)) : RawInitialPrefix H (J.extendHorizon T hT S hi) where
  count_le := I.count_le
  time_eq := I.time_eq
  stage_eq := I.stage_eq
  event_heq := I.event_heq

private theorem affine_prefix_start
    (H K : RetainedCoreHistory.{u}) (hH : HistoryEventControl H)
    (hs : K.stage 0 = H.stage (Fin.last H.eventCount))
    (hm : HEq (K.initialMetric 0) (H.initialMetric (Fin.last H.eventCount))) :
    AffineEventPrefix K (concatenation_start H K hH hs hm).history
      (H.time (Fin.last H.eventCount)) H.eventCount 0 := by
  refine ⟨by simp [concatenation_start], ?_, ?_, ?_, fun j => Fin.elim0 j⟩
  · intro j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    have h0 : ∀ (n : ℕ) (h : n ≤ K.eventCount + 1) (z : Fin n), z.val = 0 →
        K.time (Fin.castLE h z) = 0 := by
      intro n h z hz
      rw [show Fin.castLE h z = 0 from Fin.ext (by simp [hz])]
      exact K.time_zero
    simp only [concatenation_start, Fin.val_zero, Nat.add_zero]
    exact (zero_add _).symm.trans
      (congrArg (· + H.time (Fin.last H.eventCount)) (h0 _ _ _ (by simp)).symm)
  · intro j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    exact hs.symm
  · intro j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    exact hm.symm

/-- O-CH11-FIX3B：`concatenation_step` 内部 event 与 `hinit`（原 `by` 块里的 `let`/`have`）
的显式副本；本树 elaborator 不再从目标反推 `appendEvent` 的证明实参。 -/
private abbrev concatStepEvent {H K : RetainedCoreHistory.{u}} (i : Fin K.eventCount)
    (L : ConcatenationLayer H K i.castSucc) :=
  RetainedCoreEvent.transport L.stage_eq.symm rfl L.time_eq.symm rfl
    (translate_retained_event (K.coreEvent i) (H.time (Fin.last H.eventCount)))

private theorem concatStepEvent_init {H K : RetainedCoreHistory.{u}} (i : Fin K.eventCount)
    (L : ConcatenationLayer H K i.castSucc) :
    (concatStepEvent i L).incoming.flow.base.metric
      (L.history.time (Fin.last L.history.eventCount)) =
      L.history.initialMetric (Fin.last L.history.eventCount) := by
  let c := H.time (Fin.last H.eventCount)
  let E₀ := translate_retained_event (K.coreEvent i) c
  apply eq_of_heq
  exact (RetainedCoreEvent.transport_incoming_metric_heq L.stage_eq.symm rfl
    L.time_eq.symm rfl E₀ (L.history.time (Fin.last L.history.eventCount))).trans
    ((heq_of_eq (congrArg (fun t => E₀.incoming.flow.base.metric t) L.time_eq)).trans
    ((heq_of_eq (translated_event_initial (K.coreEvent i) c)).trans
    ((heq_of_eq (K.event_initial i)).trans L.metric_heq.symm)))

private theorem affine_prefix_step
    {H K : RetainedCoreHistory.{u}} (hK : HistoryEventControl K) (i : Fin K.eventCount)
    (L : ConcatenationLayer H K i.castSucc)
    (A : AffineEventPrefix K L.history (H.time (Fin.last H.eventCount))
      H.eventCount i.castSucc) :
    AffineEventPrefix K (concatenation_step hK i L).history
      (H.time (Fin.last H.eventCount)) H.eventCount i.succ := by
  let L' := concatenation_step hK i L
  have hcount := L'.count_eq
  have hbase := L.count_eq
  refine { count_eq := L'.count_eq, time_eq := ?_, stage_eq := ?_,
           initialMetric_heq := ?_, event_heq := ?_ }
  · intro j
    cases j using Fin.lastCases with
    | last =>
        change L'.history.time ⟨H.eventCount + (i.val + 1), _⟩ = _
        rw [show (⟨H.eventCount + (i.val + 1), by omega_fin⟩ :
            Fin (L'.history.eventCount + 1)) = Fin.last L'.history.eventCount by
          apply Fin.ext
          simpa only [Nat.add_assoc, Fin.val_succ, Fin.val_last] using L'.count_eq.symm]
        exact L'.time_eq
    | cast j =>
        let k : Fin (L.history.eventCount + 1) := ⟨H.eventCount + j.val, by
          have := A.count_eq
          omega_fin⟩
        exact (L.history.appendEvent_time_castSucc (concatStepEvent i L).incoming.lt
          (concatStepEvent i L) (concatStepEvent_init i L) k).trans (A.time_eq j)
  · intro j
    cases j using Fin.lastCases with
    | last =>
        change L'.history.stage ⟨H.eventCount + (i.val + 1), _⟩ = _
        rw [show (⟨H.eventCount + (i.val + 1), by omega_fin⟩ :
            Fin (L'.history.eventCount + 1)) = Fin.last L'.history.eventCount by
          apply Fin.ext
          simpa only [Nat.add_assoc, Fin.val_succ, Fin.val_last] using L'.count_eq.symm]
        exact L'.stage_eq
    | cast j =>
        let k : Fin (L.history.eventCount + 1) := ⟨H.eventCount + j.val, by
          have := A.count_eq
          omega_fin⟩
        exact (L.history.appendEvent_stage_castSucc
          (concatStepEvent i L).incoming.lt (concatStepEvent i L)
          (concatStepEvent_init i L) k).trans (A.stage_eq j)
  · intro j
    cases j using Fin.lastCases with
    | last =>
        have hj : (⟨H.eventCount + (i.val + 1), by omega_fin⟩ :
            Fin (L'.history.eventCount + 1)) = Fin.last L'.history.eventCount := by
          apply Fin.ext
          simpa only [Nat.add_assoc, Fin.val_succ, Fin.val_last] using L'.count_eq.symm
        change HEq (L'.history.initialMetric ⟨H.eventCount + (i.val + 1), _⟩) _
        rw [hj]
        exact L'.metric_heq
    | cast j =>
        let k : Fin (L.history.eventCount + 1) := ⟨H.eventCount + j.val, by
          have := A.count_eq
          omega_fin⟩
        exact (L.history.appendEvent_initialMetric_castSucc_heq
          (concatStepEvent i L).incoming.lt (concatStepEvent i L)
          (concatStepEvent_init i L) k).trans
          (A.initialMetric_heq j)
  · intro j
    cases j using Fin.lastCases with
    | last =>
        have hj : (⟨H.eventCount + i.val, by omega_fin⟩ :
            Fin L'.history.eventCount) = Fin.last L.history.eventCount := by
          apply Fin.ext
          exact L.count_eq.symm
        change HEq (L'.history.coreEvent ⟨H.eventCount + i.val, _⟩) _
        rw [hj]
        exact (append_core_event_last_heq L.history
          (concatStepEvent i L).incoming.lt (concatStepEvent i L)
          (concatStepEvent_init i L)).trans
          (retained_event_transport_heq _ _ _ _ _)
    | cast j =>
        let k : Fin L.history.eventCount := ⟨H.eventCount + j.val, by
          have := A.count_eq
          omega_fin⟩
        exact (append_core_event_old_heq L.history
          (concatStepEvent i L).incoming.lt (concatStepEvent i L)
          (concatStepEvent_init i L) k).trans (A.event_heq j)

private theorem concatenation_layers_with_presentations
    (H K : RetainedCoreHistory.{u}) (hH : HistoryEventControl H) (hK : HistoryEventControl K)
    (hs : K.stage 0 = H.stage (Fin.last H.eventCount))
    (hm : HEq (K.initialMetric 0) (H.initialMetric (Fin.last H.eventCount))) :
    ∀ i : Fin (K.eventCount + 1),
      ∃ L : ConcatenationLayer H K i,
        Nonempty (AffineEventPrefix K L.history (H.time (Fin.last H.eventCount))
          H.eventCount i) ∧ Nonempty (RawInitialPrefix H L.history) := by
  intro i
  induction i using Fin.induction with
  | zero => exact ⟨concatenation_start H K hH hs hm, ⟨affine_prefix_start H K hH hs hm⟩,
      ⟨RawInitialPrefix.refl H⟩⟩
  | succ i ih =>
      obtain ⟨L, ⟨A⟩, ⟨I⟩⟩ := ih
      exact ⟨concatenation_step hK i L, ⟨affine_prefix_step hK i L A⟩,
        ⟨I.append (concatStepEvent i L).incoming.lt (concatStepEvent i L)
          (concatStepEvent_init i L)⟩⟩

/-- The existing concatenation recursion retains a presentation of every selected
tail event, not only its final stage and metric. -/
theorem concatenation_layers_with_affine_prefix
    (H K : RetainedCoreHistory.{u}) (hH : HistoryEventControl H) (hK : HistoryEventControl K)
    (hs : K.stage 0 = H.stage (Fin.last H.eventCount))
    (hm : HEq (K.initialMetric 0) (H.initialMetric (Fin.last H.eventCount))) :
    ∀ i : Fin (K.eventCount + 1),
      ∃ L : ConcatenationLayer H K i,
        Nonempty (AffineEventPrefix K L.history (H.time (Fin.last H.eventCount))
          H.eventCount i) := by
  intro i
  obtain ⟨L, A, _⟩ := concatenation_layers_with_presentations H K hH hK hs hm i
  exact ⟨L, A⟩

private def AffineEventPrefix.extendHorizon
    {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    {n : Fin (K.eventCount + 1)} (A : AffineEventPrefix K J c offset n)
    (T : ℝ) (hT : J.horizon ≤ T)
    (S : (J.stage (Fin.last J.eventCount)).ClosedSlab (J.time (Fin.last J.eventCount)) T)
    (hi : S.flow.base.metric (J.time (Fin.last J.eventCount)) =
      J.initialMetric (Fin.last J.eventCount)) :
    AffineEventPrefix K (J.extendHorizon T hT S hi) c offset n where
  count_eq := A.count_eq
  time_eq := A.time_eq
  stage_eq := A.stage_eq
  initialMetric_heq := A.initialMetric_heq
  event_heq := A.event_heq

private theorem finite_history_concatenation_with_presentations
    (H K : RetainedCoreHistory.{u}) (hH : HistoryEventControl H) (hK : HistoryEventControl K)
    (hs : K.stage 0 = H.stage (Fin.last H.eventCount))
    (hm : HEq (K.initialMetric 0) (H.initialMetric (Fin.last H.eventCount)))
    (hB : H.horizon ≤ K.horizon + H.time (Fin.last H.eventCount)) :
    ∃ J : RetainedCoreHistory.{u},
      Nonempty (AffineEventPrefix K J (H.time (Fin.last H.eventCount))
        H.eventCount (Fin.last K.eventCount)) ∧
      Nonempty (RawInitialPrefix H J) ∧
      H.toHistory.IsPrefixOf J.toHistory ∧
      J.horizon = K.horizon + H.time (Fin.last H.eventCount) ∧
      HistoryEventControl J ∧
      ∀ t : ℝ,
        HEq (J.toHistory.stageMetric (Fin.last J.eventCount)
          (t + H.time (Fin.last H.eventCount)))
          (K.toHistory.stageMetric (Fin.last K.eventCount) t) := by
  obtain ⟨L, ⟨A⟩, ⟨I⟩⟩ := concatenation_layers_with_presentations H K hH hK hs hm
    (Fin.last K.eventCount)
  let c := H.time (Fin.last H.eventCount)
  have hhor : L.history.horizon ≤ K.horizon + c :=
    L.horizon_le.trans (max_le hB (by linarith [K.time_le_horizon]))
  rcases K.time_le_horizon.lt_or_eq with ht | ht
  · let S₀ := (K.finalSlab ht).timeTranslate c
    let S := transport_closed_slab L.stage_eq.symm L.time_eq.symm rfl S₀
    have hi : S.flow.base.metric (L.history.time (Fin.last L.history.eventCount)) =
        L.history.initialMetric (Fin.last L.history.eventCount) := by
      apply eq_of_heq
      exact (transport_closed_metric L.stage_eq.symm L.time_eq.symm rfl S₀ _).trans
        ((heq_of_eq (congrArg (fun t => S₀.flow.base.metric t) L.time_eq)).trans
        ((heq_of_eq ((K.finalSlab ht).timeTranslate_initial_metric c)).trans
        ((heq_of_eq (K.final_initial ht)).trans L.metric_heq.symm)))
    let J := L.history.extendHorizon (K.horizon + c) hhor S hi
    refine ⟨J, ⟨A.extendHorizon _ hhor S hi⟩, ⟨I.extendHorizon _ hhor S hi⟩,
      L.isPrefix.trans (actual_closed_extension_preserves_prefix L.history hhor S hi),
      rfl, history_control_extend L.history L.control hhor S hi, ?_⟩
    intro t
    have hlast : J.toHistory.time (Fin.last J.eventCount) < J.toHistory.horizon := by
      change L.history.time (Fin.last L.history.eventCount) < K.horizon + c
      rw [L.time_eq]
      exact add_lt_add_of_lt_of_le ht (le_refl c)
    rw [ObservedHistory.stageMetric_last_of_lt (h := hlast),
      ObservedHistory.stageMetric_last_of_lt (h := ht)]
    exact (transport_closed_metric L.stage_eq.symm L.time_eq.symm rfl S₀ (t + c)).trans
      (heq_of_eq ((K.finalSlab ht).timeTranslate_metric_add c t))
  · have heq : L.history.horizon = K.horizon + c := by
      apply le_antisymm hhor
      rw [← ht, ← L.time_eq]
      exact L.history.time_le_horizon
    refine ⟨L.history, ⟨A⟩, ⟨I⟩, L.isPrefix, heq, L.control, ?_⟩
    intro t
    have hlast : L.history.horizon ≤ L.history.time (Fin.last L.history.eventCount) := by
      rw [heq, L.time_eq, ht]
    rw [ObservedHistory.stageMetric_last_of_le (H := L.history.toHistory) hlast,
      ObservedHistory.stageMetric_last_of_le (H := K.toHistory) ht.ge]
    exact L.metric_heq

/-- Actual finite concatenation with every affine tail identity retained. The
last-stage metric identity also covers a nonempty final closed slab of the tail. -/
theorem finite_history_concatenation_with_affine_prefix
    (H K : RetainedCoreHistory.{u}) (hH : HistoryEventControl H) (hK : HistoryEventControl K)
    (hs : K.stage 0 = H.stage (Fin.last H.eventCount))
    (hm : HEq (K.initialMetric 0) (H.initialMetric (Fin.last H.eventCount)))
    (hB : H.horizon ≤ K.horizon + H.time (Fin.last H.eventCount)) :
    ∃ J : RetainedCoreHistory.{u},
      Nonempty (AffineEventPrefix K J (H.time (Fin.last H.eventCount))
        H.eventCount (Fin.last K.eventCount)) ∧
      H.toHistory.IsPrefixOf J.toHistory ∧
      J.horizon = K.horizon + H.time (Fin.last H.eventCount) ∧
      HistoryEventControl J ∧
      ∀ t : ℝ,
        HEq (J.toHistory.stageMetric (Fin.last J.eventCount)
          (t + H.time (Fin.last H.eventCount)))
          (K.toHistory.stageMetric (Fin.last K.eventCount) t) := by
  obtain ⟨J, A, _, hp, ht, hJ, hmetric⟩ :=
    finite_history_concatenation_with_presentations H K hH hK hs hm hB
  exact ⟨J, A, hp, ht, hJ, hmetric⟩

open private CutoffFields CutoffFields.mk CutoffFields.ofRecord CutoffFields.toRecord
  CutoffFields.transport
  CutoffFields.transport_neck_heq CutoffFields.transport_static_heq
  CutoffFields.transport_delta_heq CutoffFields.transport_order_heq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordEventExtension

open private transport_nominalRadius_heq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordSplicingPortC11P

private structure TerminalCutoffFields
    {P Q D₀ N₀ : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D₀ N₀)
    (U : TopologicalSpace.Opens P.Carrier) (h : SmoothRiemannianMetric ThreeModel U)
    (g : Q.Metric) (p : CutoffParameters) (s : ℝ) where
  nominalRadius : Nonempty X.trace.tubes.Index → ℝ
  nominal_pos : ∀ h, 0 < nominalRadius h
  nominal_small : ∀ h, nominalRadius h < (p.delta s)^2 * p.neckRadius s
  delta : X.trace.tubes.Index → ℝ
  delta_pos : ∀ α, 0 < delta α
  delta_le : ∀ α, delta α ≤ p.delta s
  order : X.trace.tubes.Index → ℕ
  order_lower : ∀ α, max (p.modelOrder + 6) (2 * ⌊(delta α)⁻¹⌋₊ + 4) ≤ order α
  neck : ∀ α, NormalizedNeck h (delta α) (order α)
  scale_eq : ∀ α, (neck α).scale = ((nominalRadius ⟨α⟩) ^ 2)⁻¹
  buffer_disjoint : Pairwise fun α β => Disjoint (Set.range (neck α).chart) (Set.range (neck β).chart)
  tube_eq : ∀ α, ∀ x : TubeDomain, ∀ hx : (x.1, x.2.1) ∈ neckBuffer (delta α),
    X.trace.tubes.tube α x = ((neck α).chart ⟨(x.1, x.2.1), hx⟩).val
  tube_in_buffer : ∀ α, ∀ x : TubeDomain, (x.1, x.2.1) ∈ neckBuffer (delta α)
  retained_terminal : ∀ x ∈ X.trace.retainedCore, x.1 ∈ U
  protected_interior : ∀ x : U,
    metricScalarAt h x ≤ ((p.protectedRadius s) ^ 2)⁻¹ →
    x.val ∈ interior (Subtype.val '' X.trace.retainedCore)
  retained_meets_protected : ∀ c : ConnectedComponents X.trace.tubes.core,
    (∃ x : X.trace.tubes.core, ConnectedComponents.mk x = c ∧ x ∈ X.trace.retainedCore) →
    ∃ x : U, ∃ hx : x.val ∈ X.trace.tubes.core,
      ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧
        metricScalarAt h x ≤ ((p.protectedRadius s) ^ 2)⁻¹
  one_retained_side : ∀ α,
    (∀ y, X.trace.tubes.coreBoundarySphere (α, true) y ∈ X.trace.retainedCore) ↔
      ¬ (∀ y, X.trace.tubes.coreBoundarySphere (α, false) y ∈ X.trace.retainedCore)
  no_cuts_discard : IsEmpty X.trace.tubes.Index →
    ∃ x : X.trace.tubes.core, x ∉ X.trace.retainedCore
  static : ∀ b : {b : X.trace.tubes.Boundary //
      ∀ y, X.trace.tubes.coreBoundarySphere b y ∈ X.trace.retainedCore},
    TerminalStaticPresentation X U h g p.fixed p.modelRadius p.modelOrder p.modelAccuracy b
  recenter_scale : ∀ b, (static b).neck.scale = metricScalarAt h (static b).neck.center
  recenter_mark : ∀ b, (static b).neck.sphereMark = (neck b.1.1).sphereMark
  recenter_delta : ∀ b, (static b).delta = p.recenterConstant * delta b.1.1
  recenter_scale_comparison : ∀ b,
    |(static b).neck.scale / (neck b.1.1).scale - 1| ≤ p.recenterConstant * delta b.1.1
  recenter_chart : ∀ b, ∀ x : neckBuffer (static b).delta,
    ∀ hx : (x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (delta b.1.1),
      (static b).neck.chart x = (neck b.1.1).chart
        ⟨(x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)), hx⟩
  recenter_in_buffer : ∀ b, ∀ x : neckBuffer (static b).delta,
    (x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (delta b.1.1)
  curvature_preserving : ∀ a : ℝ, 0 < a → (∀ x : U, InFixedHamiltonIveyRegion h a x) →
    ∀ x : Q.Carrier, InFixedHamiltonIveyRegion g a x
  scalar_preserving : ∀ L : ℝ, L ≤ 0 → (∀ x : U, L ≤ metricScalarAt h x) →
    ∀ x : Q.Carrier, L ≤ metricScalarAt g x

/-- O-CH11-FIX3B：`static` 字段单独成声明（原 struct-instance 内 isDefEq 超时）。 -/
private def TerminalCutoffFields.staticOf
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : RetainedCoreEvent P Q a s}
    {F : {δ : ℝ} → {k : ℕ} → NormalizedNeck E.terminal.metric δ k → ℝ → Type u}
    {p : CutoffParameters} (R : CutoffFields E.toMetricCutCapEvent F p)
    (b : E.toMetricCutCapEvent.RetainedBoundaryIndex) :
    TerminalStaticPresentation E.transition E.incoming.terminalRegularOpen E.terminal.metric
      E.outputMetric p.fixed p.modelRadius p.modelOrder p.modelAccuracy b :=
  TerminalStaticPresentation.ofPresented (CutoffFields.static R b)

private theorem TerminalCutoffFields.protected_interior_of
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : RetainedCoreEvent P Q a s}
    {F : {δ : ℝ} → {k : ℕ} → NormalizedNeck E.terminal.metric δ k → ℝ → Type u}
    {p : CutoffParameters} (R : CutoffFields E.toMetricCutCapEvent F p) :
    ∀ x : E.incoming.terminalRegularOpen,
      metricScalarAt E.terminal.metric x ≤ ((p.protectedRadius s) ^ 2)⁻¹ →
      x.val ∈ interior (Subtype.val '' E.transition.trace.retainedCore) := by
  intro x hx
  have h := CutoffFields.protected_interior R x hx
  exact h

private theorem TerminalCutoffFields.retained_meets_protected_of
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : RetainedCoreEvent P Q a s}
    {F : {δ : ℝ} → {k : ℕ} → NormalizedNeck E.terminal.metric δ k → ℝ → Type u}
    {p : CutoffParameters} (R : CutoffFields E.toMetricCutCapEvent F p) :
    ∀ c : ConnectedComponents E.transition.trace.tubes.core,
      (∃ x : E.transition.trace.tubes.core,
        ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
      ∃ x : E.incoming.terminalRegularOpen, ∃ hx : x.val ∈ E.transition.trace.tubes.core,
        ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧
          metricScalarAt E.terminal.metric x ≤ ((p.protectedRadius s) ^ 2)⁻¹ :=
  CutoffFields.retained_meets_protected R

private def TerminalCutoffFields.ofCutoffFields
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : RetainedCoreEvent P Q a s}
    {F : {δ : ℝ} → {k : ℕ} → NormalizedNeck E.terminal.metric δ k → ℝ → Type u}
    {p : CutoffParameters} (R : CutoffFields E.toMetricCutCapEvent F p) :
    TerminalCutoffFields E.transition E.incoming.terminalRegularOpen E.terminal.metric
      E.outputMetric p s where
  nominalRadius := CutoffFields.nominalRadius R
  nominal_pos := CutoffFields.nominal_pos R
  nominal_small := CutoffFields.nominal_small R
  delta := CutoffFields.delta R
  delta_pos := CutoffFields.delta_pos R
  delta_le := CutoffFields.delta_le R
  order := CutoffFields.order R
  order_lower := CutoffFields.order_lower R
  neck := CutoffFields.neck R
  scale_eq := CutoffFields.scale_eq R
  buffer_disjoint := CutoffFields.buffer_disjoint R
  tube_eq := CutoffFields.tube_eq R
  tube_in_buffer := CutoffFields.tube_in_buffer R
  retained_terminal := CutoffFields.retained_terminal R
  protected_interior := TerminalCutoffFields.protected_interior_of R
  retained_meets_protected := TerminalCutoffFields.retained_meets_protected_of R
  one_retained_side := CutoffFields.one_retained_side R
  no_cuts_discard := CutoffFields.no_cuts_discard R
  static := TerminalCutoffFields.staticOf R
  recenter_scale := CutoffFields.recenter_scale R
  recenter_mark := CutoffFields.recenter_mark R
  recenter_delta := CutoffFields.recenter_delta R
  recenter_scale_comparison := CutoffFields.recenter_scale_comparison R
  recenter_chart := CutoffFields.recenter_chart R
  recenter_in_buffer := CutoffFields.recenter_in_buffer R
  curvature_preserving := fun a ha hx => CutoffFields.curvature_preserving R a ha hx
  scalar_preserving := fun L hL hx => CutoffFields.scalar_preserving R L hL hx

private def TerminalCutoffFields.castOpen
    {P Q D₀ N₀ : OrientedThreeStage.{u}} {X : SmoothCutCapTransition P Q D₀ N₀}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {g : Q.Metric}
    {p : CutoffParameters} {s : ℝ} (R : TerminalCutoffFields X U h g p s) :
    TerminalCutoffFields X V (hUV ▸ h) g p s where
  nominalRadius := R.nominalRadius
  nominal_pos := R.nominal_pos
  nominal_small := R.nominal_small
  delta := R.delta
  delta_pos := R.delta_pos
  delta_le := R.delta_le
  order := R.order
  order_lower := R.order_lower
  neck := fun α => cast_open_neck hUV (R.neck α)
  scale_eq := by cases hUV; exact R.scale_eq
  buffer_disjoint := by cases hUV; exact R.buffer_disjoint
  tube_eq := by cases hUV; exact R.tube_eq
  tube_in_buffer := R.tube_in_buffer
  retained_terminal := by cases hUV; exact R.retained_terminal
  protected_interior := by cases hUV; exact R.protected_interior
  retained_meets_protected := by cases hUV; exact R.retained_meets_protected
  one_retained_side := R.one_retained_side
  no_cuts_discard := R.no_cuts_discard
  static := fun b => (R.static b).castOpen hUV
  recenter_scale := by cases hUV; exact R.recenter_scale
  recenter_mark := by cases hUV; exact R.recenter_mark
  recenter_delta := by cases hUV; exact R.recenter_delta
  recenter_scale_comparison := by cases hUV; exact R.recenter_scale_comparison
  recenter_chart := by cases hUV; exact R.recenter_chart
  recenter_in_buffer := by cases hUV; exact R.recenter_in_buffer
  curvature_preserving := by cases hUV; exact R.curvature_preserving
  scalar_preserving := by cases hUV; exact R.scalar_preserving

private theorem TerminalCutoffFields.castOpen_fields
    {P Q D₀ N₀ : OrientedThreeStage.{u}} {X : SmoothCutCapTransition P Q D₀ N₀}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {g : Q.Metric}
    {p : CutoffParameters} {s : ℝ} (R : TerminalCutoffFields X U h g p s) :
    (R.castOpen hUV).nominalRadius = R.nominalRadius ∧
    (R.castOpen hUV).delta = R.delta ∧ (R.castOpen hUV).order = R.order ∧
    HEq (R.castOpen hUV).neck R.neck ∧
    ∀ b, (R.castOpen hUV).static b = (R.static b).castOpen hUV := by
  cases hUV
  exact ⟨rfl, rfl, rfl, HEq.rfl, fun _ => rfl⟩

private theorem TerminalCutoffFields.castOpen_neck_heq
    {P Q D₀ N₀ : OrientedThreeStage.{u}} {X : SmoothCutCapTransition P Q D₀ N₀}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {g : Q.Metric}
    {p : CutoffParameters} {s : ℝ} (R : TerminalCutoffFields X U h g p s)
    (α : X.trace.tubes.Index) : HEq ((R.castOpen hUV).neck α) (R.neck α) := by
  cases hUV
  exact HEq.rfl

private def translate_cutoff_fields
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : RetainedCoreEvent P Q a s)
    (c : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    {F : {δ : ℝ} → {k : ℕ} → NormalizedNeck E.terminal.metric δ k → ℝ → Type u}
    {F' : {δ : ℝ} → {k : ℕ} →
      NormalizedNeck (translate_retained_event E c).terminal.metric δ k → ℝ → Type u}
    (hF : ∀ {δ r : ℝ} {k : ℕ}
      {N : NormalizedNeck E.terminal.metric δ k}
      {N' : NormalizedNeck (translate_retained_event E c).terminal.metric δ k},
      HEq N' N → F N r → F' N' r)
    {p : CutoffParameters} (R : CutoffFields E.toMetricCutCapEvent F p) :
    CutoffFields (translate_retained_event E c).toMetricCutCapEvent F'
      (translate_cutoff_parameters p c) := by
  let R₀ := TerminalCutoffFields.ofCutoffFields R
  let hU := (translated_terminal_open E.incoming c).symm
  let R' := R₀.castOpen hU
  have hfields := R₀.castOpen_fields hU
  have hd := (translate_cutoff_parameters_eval p c s hs).1
  have hr := (translate_cutoff_parameters_eval p c s hs).2.1
  have hp := (translate_cutoff_parameters_eval p c s hs).2.2
  refine CutoffFields.mk
    (singular := (translated_event_singular E c).mpr
      ((show E.toMetricCutCapEvent.incoming = E.incoming from rfl) ▸ CutoffFields.singular R))
    (nominalRadius := R'.nominalRadius)
    (nominal_pos := R'.nominal_pos)
    (nominal_small := ?_)
    (nominal_time := ?_)
    (delta := R'.delta)
    (delta_pos := R'.delta_pos)
    (delta_le := ?_)
    (order := R'.order)
    (order_lower := R'.order_lower)
    (neck := R'.neck)
    (scale_eq := R'.scale_eq)
    (buffer_disjoint := R'.buffer_disjoint)
    (tube_eq := R'.tube_eq)
    (tube_in_buffer := R'.tube_in_buffer)
    (backward := ?_)
    (retained_terminal := R'.retained_terminal)
    (protected_interior := ?_)
    (retained_meets_protected := ?_)
    (one_retained_side := R'.one_retained_side)
    (no_cuts_discard := R'.no_cuts_discard)
    (static := fun b => TerminalStaticPresentation.toPresented (R'.static b))
    (recenter_scale := R'.recenter_scale)
    (recenter_mark := R'.recenter_mark)
    (recenter_delta := R'.recenter_delta)
    (recenter_scale_comparison := R'.recenter_scale_comparison)
    (recenter_chart := R'.recenter_chart)
    (recenter_in_buffer := R'.recenter_in_buffer)
    (old_eq_retained := rfl)
    (curvature_preserving := R'.curvature_preserving)
    (scalar_preserving := R'.scalar_preserving)
  · intro h
    have h' := R'.nominal_small h
    simpa only [hd, hr] using h'
  · intro h
    rw [hfields.1]
    exact (CutoffFields.nominal_time R h).trans (le_add_of_nonneg_right hc)
  · intro α
    have h' := R'.delta_le α
    simpa only [hd] using h'
  · intro α
    exact hF (R₀.castOpen_neck_heq hU α) (CutoffFields.backward R α)
  · intro x hx
    rw [hp] at hx
    exact R'.protected_interior x hx
  · intro c₁ hc₁
    obtain ⟨x, hx, h1, h2⟩ := R'.retained_meets_protected c₁ hc₁
    exact ⟨x, hx, h1, by rw [hp]; exact h2⟩

private theorem metric_event_heq_of_retained_event_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : RetainedCoreEvent P Q a s} {E' : RetainedCoreEvent P' Q' a' s'}
    (hE : HEq E E') : HEq E.toMetricCutCapEvent E'.toMetricCutCapEvent := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact HEq.rfl

private def AffineEventPrefix.tailBackwardFamily
    {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount)) (i : Fin K.eventCount)
    {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck (translate_retained_event (K.coreEvent i) c).terminal.metric δ k)
    (r : ℝ) : Type u :=
  (N' : NormalizedNeck (J.coreEvent (A.eventIndex i)).terminal.metric δ k) →
    HEq N' N → IncomingBackwardNeck J.toHistory (A.eventIndex i) N' r

/-- Transport the selected record to the actual translated tail event. Its
backward charts are constructed above, including every crossing since their
left endpoint. The parameter values are the actual affine translations. -/
def AffineEventPrefix.translateRecord
    {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount)) (hc : 0 ≤ c)
    {i : Fin K.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord K.toHistory i p) :
    GeometricCutoffRecord J.toHistory (A.eventIndex i) (translate_cutoff_parameters p c) :=
  let R' := translate_cutoff_fields (K.coreEvent i) c hc
    (ObservedHistory.time_nonneg K.toHistory i.succ)
    (F' := A.tailBackwardFamily i)
    (fun hN B N' hN' => A.translateBackwardNeck hc (hN'.trans hN) B)
    (CutoffFields.ofRecord R)
  CutoffFields.toRecord (CutoffFields.transport
    (F := A.tailBackwardFamily i)
    (F' := fun {δ} {k} N r => @IncomingBackwardNeck J.toHistory (A.eventIndex i) δ k N r)
    (A.stage_eq i.castSucc) (A.stage_eq i.succ)
    (A.time_eq i.castSucc) (A.time_eq i.succ)
    (metric_event_heq_of_retained_event_heq
      (A.stage_eq i.castSucc) (A.stage_eq i.succ)
      (A.time_eq i.castSucc) (A.time_eq i.succ) (A.event_heq i))
    (fun hN B => B _ hN) R')

theorem AffineEventPrefix.translateRecord_nominalRadius_heq
    {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount)) (hc : 0 ≤ c)
    {i : Fin K.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord K.toHistory i p) :
    HEq (A.translateRecord hc R).nominalRadius R.nominalRadius := by
  exact transport_nominalRadius_heq _ _ _ _ _ _ _

theorem AffineEventPrefix.translateRecord_delta_heq
    {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount)) (hc : 0 ≤ c)
    {i : Fin K.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord K.toHistory i p) :
    HEq (A.translateRecord hc R).delta R.delta := by
  exact CutoffFields.transport_delta_heq _ _ _ _ _ _ _

theorem AffineEventPrefix.translateRecord_order_heq
    {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount)) (hc : 0 ≤ c)
    {i : Fin K.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord K.toHistory i p) :
    HEq (A.translateRecord hc R).order R.order := by
  exact CutoffFields.transport_order_heq _ _ _ _ _ _ _

theorem AffineEventPrefix.translateRecord_neck_heq
    {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount)) (hc : 0 ≤ c)
    {i : Fin K.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord K.toHistory i p) :
    HEq (A.translateRecord hc R).neck R.neck := by
  refine (CutoffFields.transport_neck_heq _ _ _ _ _ _ _).trans ?_
  exact ((TerminalCutoffFields.ofCutoffFields (CutoffFields.ofRecord R)).castOpen_fields
    (translated_terminal_open (K.coreEvent i).incoming c).symm).2.2.2.1

/-- Full-static HEq is asserted only against the explicitly translated view. -/
theorem AffineEventPrefix.translateRecord_static_heq
    {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount)) (hc : 0 ≤ c)
    {i : Fin K.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord K.toHistory i p) :
    HEq (A.translateRecord hc R).static
      (fun b => translate_presented_static_cap (K.coreEvent i) c (R.static b)) := by
  exact CutoffFields.transport_static_heq _ _ _ _ _ _ _

theorem AffineEventPrefix.translateRecord_canonical
    {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (A : AffineEventPrefix K J c offset (Fin.last K.eventCount)) (hc : 0 ≤ c)
    {i : Fin K.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord K.toHistory i p)
    (hR : ∀ b, (R.static b).hasCanonicalWindow) :
    ∀ b, ((A.translateRecord hc R).static b).hasCanonicalWindow := by
  exact MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
    (A.stage_eq i.castSucc) (A.stage_eq i.succ)
    (A.time_eq i.castSucc) (A.time_eq i.succ)
    (metric_event_heq_of_retained_event_heq
      (A.stage_eq i.castSucc) (A.stage_eq i.succ)
      (A.time_eq i.castSucc) (A.time_eq i.succ) (A.event_heq i))
    rfl rfl rfl rfl
    (fun b => translate_presented_static_cap (K.coreEvent i) c (R.static b))
    (A.translateRecord hc R).static (A.translateRecord_static_heq hc R)
    (fun b => translate_presented_static_cap_canonical (K.coreEvent i) c (R.static b) (hR b))

def RawInitialPrefix.transportRecord
    {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p) :
    GeometricCutoffRecord J.toHistory (i.castLE I.count_le) p :=
  CutoffFields.toRecord (CutoffFields.transport
    (F := fun {δ} {k} N r => @IncomingBackwardNeck H.toHistory i δ k N r)
    (F' := fun {δ} {k} N r => @IncomingBackwardNeck J.toHistory (i.castLE I.count_le) δ k N r)
    (I.stage_eq i.castSucc) (I.stage_eq i.succ)
    (I.time_eq i.castSucc) (I.time_eq i.succ)
    (metric_event_heq_of_retained_event_heq
      (I.stage_eq i.castSucc) (I.stage_eq i.succ)
      (I.time_eq i.castSucc) (I.time_eq i.succ) (I.event_heq i))
    (fun hN B => IncomingBackwardNeck.ofInitialEmbedding I.count_le
      I.time_eq I.stage_eq
      (fun j => metric_event_heq_of_retained_event_heq
        (I.stage_eq j.castSucc) (I.stage_eq j.succ)
        (I.time_eq j.castSucc) (I.time_eq j.succ) (I.event_heq j)) hN B)
    (CutoffFields.ofRecord R))

theorem RawInitialPrefix.transportRecord_preserves
    {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p) :
    HEq (I.transportRecord R).nominalRadius R.nominalRadius ∧
    HEq (I.transportRecord R).delta R.delta ∧
    HEq (I.transportRecord R).order R.order ∧
    HEq (I.transportRecord R).neck R.neck ∧
    HEq (I.transportRecord R).static R.static := by
  exact ⟨transport_nominalRadius_heq _ _ _ _ _ _ _,
    CutoffFields.transport_delta_heq _ _ _ _ _ _ _,
    CutoffFields.transport_order_heq _ _ _ _ _ _ _,
    CutoffFields.transport_neck_heq _ _ _ _ _ _ _,
    CutoffFields.transport_static_heq _ _ _ _ _ _ _⟩

theorem RawInitialPrefix.transportRecord_canonical
    {H J : RetainedCoreHistory.{u}} (I : RawInitialPrefix H J)
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p)
    (hR : ∀ b, (R.static b).hasCanonicalWindow) :
    ∀ b, ((I.transportRecord R).static b).hasCanonicalWindow := by
  exact MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
    (I.stage_eq i.castSucc) (I.stage_eq i.succ)
    (I.time_eq i.castSucc) (I.time_eq i.succ)
    (metric_event_heq_of_retained_event_heq
      (I.stage_eq i.castSucc) (I.stage_eq i.succ)
      (I.time_eq i.castSucc) (I.time_eq i.succ) (I.event_heq i))
    rfl rfl rfl rfl R.static (I.transportRecord R).static
    (I.transportRecord_preserves R).2.2.2.2 hR

private theorem concatenation_event_time_gt_horizon
    (H K : RetainedCoreHistory.{u}) (hH : HistoryEventControl H) (hK : HistoryEventControl K)
    (hs : K.stage 0 = H.stage (Fin.last H.eventCount))
    (hm : HEq (K.initialMetric 0) (H.initialMetric (Fin.last H.eventCount)))
    (i : Fin K.eventCount) : H.horizon < K.time i.succ + H.time (Fin.last H.eventCount) := by
  let L := Classical.choice (concatenation_layers H K hH hK hs hm i.castSucc)
  let c := H.time (Fin.last H.eventCount)
  let E₀ := translate_retained_event (K.coreEvent i) c
  let E := RetainedCoreEvent.transport L.stage_eq.symm rfl L.time_eq.symm rfl E₀
  have hinit : E.incoming.flow.base.metric
      (L.history.time (Fin.last L.history.eventCount)) =
      L.history.initialMetric (Fin.last L.history.eventCount) := by
    apply eq_of_heq
    exact (RetainedCoreEvent.transport_incoming_metric_heq L.stage_eq.symm rfl
      L.time_eq.symm rfl E₀ (L.history.time (Fin.last L.history.eventCount))).trans
      ((heq_of_eq (congrArg (fun t => E₀.incoming.flow.base.metric t) L.time_eq)).trans
      ((heq_of_eq (translated_event_initial (K.coreEvent i) c)).trans
      ((heq_of_eq (K.event_initial i)).trans L.metric_heq.symm)))
  have hE : SurgeryEventControl E := event_control_transport _ _ _ _ E₀
    (event_control_translate (K.coreEvent i) (hK i) c)
  exact L.isPrefix.horizon_le.trans_lt
    (actual_singular_event_after_horizon L.history E hinit hE.1)

/-- Concatenate the two actual histories and the two supplied cutoff families.
The old family keeps all five raw data HEqs. The tail family keeps its nominal
radii, finite orders and terminal necks; its static family is compared with the
explicit translated view, whose original output geometry is preserved above.
All three old parameter functions remain unchanged through the old horizon. -/
theorem finite_history_concatenation_with_cutoff_records_and_raw_prefix
    (H K : RetainedCoreHistory.{u}) (hH : HistoryEventControl H) (hK : HistoryEventControl K)
    (hs : K.stage 0 = H.stage (Fin.last H.eventCount))
    (hm : HEq (K.initialMetric 0) (H.initialMetric (Fin.last H.eventCount)))
    (hB : H.horizon ≤ K.horizon + H.time (Fin.last H.eventCount))
    {pH pK : CutoffParameters}
    (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i pH)
    (tail : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pK)
    (hstatic : pK.fixed = pH.fixed ∧ pK.modelRadius = pH.modelRadius ∧
      pK.modelOrder = pH.modelOrder ∧ pK.modelAccuracy = pH.modelAccuracy ∧
      pK.recenterConstant = pH.recenterConstant)
    (hold : ∀ i b, ((old i).static b).hasCanonicalWindow)
    (htail : ∀ i b, ((tail i).static b).hasCanonicalWindow) :
    let c := H.time (Fin.last H.eventCount)
    let q := pH.spliceAfter (translate_cutoff_parameters pK c) H.horizon
    ∃ (J : RetainedCoreHistory.{u})
      (A : AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount))
      (I0 : RawInitialPrefix H J)
      (hn : H.eventCount ≤ J.eventCount)
      (records : ∀ j : Fin J.eventCount, GeometricCutoffRecord J.toHistory j q),
      H.toHistory.IsPrefixOf J.toHistory ∧ J.horizon = K.horizon + c ∧ HistoryEventControl J ∧
      (∀ t : ℝ, HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t)) ∧
      (∀ t : ℝ, t ≤ H.horizon → q.delta t = pH.delta t ∧
        q.neckRadius t = pH.neckRadius t ∧ q.protectedRadius t = pH.protectedRadius t) ∧
      (∀ j b, ((records j).static b).hasCanonicalWindow) ∧
      (∀ i : Fin H.eventCount,
        HEq (records (i.castLE hn)).nominalRadius (old i).nominalRadius ∧
        HEq (records (i.castLE hn)).delta (old i).delta ∧
        HEq (records (i.castLE hn)).order (old i).order ∧
        HEq (records (i.castLE hn)).neck (old i).neck ∧
        HEq (records (i.castLE hn)).static (old i).static) ∧
      ∀ i : Fin K.eventCount,
        HEq (records (A.eventIndex i)).nominalRadius (tail i).nominalRadius ∧
        HEq (records (A.eventIndex i)).delta (tail i).delta ∧
        HEq (records (A.eventIndex i)).order (tail i).order ∧
        HEq (records (A.eventIndex i)).neck (tail i).neck ∧
        HEq (records (A.eventIndex i)).static
          (fun b => translate_presented_static_cap (K.coreEvent i) c ((tail i).static b)) := by
  dsimp only
  let c := H.time (Fin.last H.eventCount)
  let pT := translate_cutoff_parameters pK c
  let q := pH.spliceAfter pT H.horizon
  have hc : 0 ≤ c := ObservedHistory.time_nonneg H.toHistory (Fin.last H.eventCount)
  obtain ⟨J, ⟨A⟩, ⟨I⟩, hp, hhor, hJ, hmetric⟩ :=
    finite_history_concatenation_with_presentations H K hH hK hs hm hB
  have hcount := A.count_eq
  have hOldTime (i : Fin H.eventCount) : J.time (i.castLE I.count_le).succ ≤ H.horizon := by
    rw [show J.time (i.castLE I.count_le).succ = H.time i.succ from I.time_eq i.succ]
    exact (H.time_strictMono.monotone (Fin.le_last i.succ)).trans H.time_le_horizon
  have hTailTime (i : Fin K.eventCount) : H.horizon < J.time (A.eventIndex i).succ := by
    rw [show J.time (A.eventIndex i).succ = K.time i.succ + c from A.time_eq i.succ]
    exact concatenation_event_time_gt_horizon H K hH hK hs hm i
  let Rold (i : Fin H.eventCount) : GeometricCutoffRecord J.toHistory (i.castLE I.count_le) q :=
    (I.transportRecord (old i)).spliceAfterParametersOfLE (q := pT) (hOldTime i)
  let Rtail (i : Fin K.eventCount) : GeometricCutoffRecord J.toHistory (A.eventIndex i) q :=
    (A.translateRecord hc (tail i)).spliceAfterParametersOfLT hstatic (hTailTime i)
  let Rsum (j : Fin (H.eventCount + K.eventCount)) :
      GeometricCutoffRecord J.toHistory ⟨j.val, by omega_fin⟩ q :=
    Fin.addCases Rold Rtail j
  let records (j : Fin J.eventCount) : GeometricCutoffRecord J.toHistory j q :=
    Rsum (Fin.cast hcount j)
  have hOld (i : Fin H.eventCount) : records (i.castLE I.count_le) = Rold i :=
    Fin.addCases_left i
  have hTail (i : Fin K.eventCount) : records (A.eventIndex i) = Rtail i :=
    Fin.addCases_right i
  have hOldWin (i : Fin H.eventCount) : ∀ b, ((Rold i).static b).hasCanonicalWindow := by
    exact MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
      rfl rfl rfl rfl HEq.rfl rfl rfl rfl rfl
      (I.transportRecord (old i)).static (Rold i).static
      ((I.transportRecord (old i)).spliceAfterParametersOfLE_preserves
        (q := pT) (hOldTime i)).2.2.2.2
      (I.transportRecord_canonical (old i) (hold i))
  have hTailWin (i : Fin K.eventCount) : ∀ b, ((Rtail i).static b).hasCanonicalWindow := by
    exact MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
      rfl rfl rfl rfl HEq.rfl hstatic.1.symm hstatic.2.1.symm
      hstatic.2.2.1.symm hstatic.2.2.2.1.symm
      (A.translateRecord hc (tail i)).static (Rtail i).static
      ((A.translateRecord hc (tail i)).spliceAfterParametersOfLT_preserves
        hstatic (hTailTime i)).2.2.2.2
      (A.translateRecord_canonical hc (tail i) (htail i))
  refine ⟨J, A, I, I.count_le, records, hp, hhor, hJ, hmetric,
    (fun t ht => pH.spliceAfter_eval_of_le pT ht), ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < H.eventCount
    · let i : Fin H.eventCount := ⟨j.val, hj⟩
      have hji : i.castLE I.count_le = j := Fin.ext rfl
      rw [← hji, hOld]
      exact hOldWin i
    · let i : Fin K.eventCount := ⟨j.val - H.eventCount, by omega⟩
      have hji : A.eventIndex i = j := by
        apply Fin.ext
        change H.eventCount + (j.val - H.eventCount) = j.val
        omega
      rw [← hji, hTail]
      exact hTailWin i
  · intro i
    rw [hOld]
    have h₁ := (I.transportRecord (old i)).spliceAfterParametersOfLE_preserves
      (q := pT) (hOldTime i)
    have h₂ := I.transportRecord_preserves (old i)
    exact ⟨(heq_of_eq h₁.1).trans h₂.1, (heq_of_eq h₁.2.1).trans h₂.2.1,
      (heq_of_eq h₁.2.2.1).trans h₂.2.2.1, h₁.2.2.2.1.trans h₂.2.2.2.1,
      h₁.2.2.2.2.trans h₂.2.2.2.2⟩
  · intro i
    rw [hTail]
    have h₁ := (A.translateRecord hc (tail i)).spliceAfterParametersOfLT_preserves
      hstatic (hTailTime i)
    exact ⟨(heq_of_eq h₁.1).trans (A.translateRecord_nominalRadius_heq hc (tail i)),
      (heq_of_eq h₁.2.1).trans (A.translateRecord_delta_heq hc (tail i)),
      (heq_of_eq h₁.2.2.1).trans (A.translateRecord_order_heq hc (tail i)),
      h₁.2.2.2.1.trans (A.translateRecord_neck_heq hc (tail i)),
      h₁.2.2.2.2.trans (A.translateRecord_static_heq hc (tail i))⟩

/-- The original API, obtained by one call to the stronger concatenation and
forgetting only its already constructed raw-prefix witness. -/
theorem finite_history_concatenation_with_cutoff_records
    (H K : RetainedCoreHistory.{u}) (hH : HistoryEventControl H) (hK : HistoryEventControl K)
    (hs : K.stage 0 = H.stage (Fin.last H.eventCount))
    (hm : HEq (K.initialMetric 0) (H.initialMetric (Fin.last H.eventCount)))
    (hB : H.horizon ≤ K.horizon + H.time (Fin.last H.eventCount))
    {pH pK : CutoffParameters}
    (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i pH)
    (tail : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pK)
    (hstatic : pK.fixed = pH.fixed ∧ pK.modelRadius = pH.modelRadius ∧
      pK.modelOrder = pH.modelOrder ∧ pK.modelAccuracy = pH.modelAccuracy ∧
      pK.recenterConstant = pH.recenterConstant)
    (hold : ∀ i b, ((old i).static b).hasCanonicalWindow)
    (htail : ∀ i b, ((tail i).static b).hasCanonicalWindow) :
    let c := H.time (Fin.last H.eventCount)
    let q := pH.spliceAfter (translate_cutoff_parameters pK c) H.horizon
    ∃ (J : RetainedCoreHistory.{u})
      (A : AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount))
      (hn : H.eventCount ≤ J.eventCount)
      (records : ∀ j : Fin J.eventCount, GeometricCutoffRecord J.toHistory j q),
      H.toHistory.IsPrefixOf J.toHistory ∧ J.horizon = K.horizon + c ∧ HistoryEventControl J ∧
      (∀ t : ℝ, HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t)) ∧
      (∀ t : ℝ, t ≤ H.horizon → q.delta t = pH.delta t ∧
        q.neckRadius t = pH.neckRadius t ∧ q.protectedRadius t = pH.protectedRadius t) ∧
      (∀ j b, ((records j).static b).hasCanonicalWindow) ∧
      (∀ i : Fin H.eventCount,
        HEq (records (i.castLE hn)).nominalRadius (old i).nominalRadius ∧
        HEq (records (i.castLE hn)).delta (old i).delta ∧
        HEq (records (i.castLE hn)).order (old i).order ∧
        HEq (records (i.castLE hn)).neck (old i).neck ∧
        HEq (records (i.castLE hn)).static (old i).static) ∧
      ∀ i : Fin K.eventCount,
        HEq (records (A.eventIndex i)).nominalRadius (tail i).nominalRadius ∧
        HEq (records (A.eventIndex i)).delta (tail i).delta ∧
        HEq (records (A.eventIndex i)).order (tail i).order ∧
        HEq (records (A.eventIndex i)).neck (tail i).neck ∧
        HEq (records (A.eventIndex i)).static
          (fun b => translate_presented_static_cap (K.coreEvent i) c ((tail i).static b)) := by
  dsimp only
  obtain ⟨J, A, _, hn, records, hresult⟩ :=
    finite_history_concatenation_with_cutoff_records_and_raw_prefix
      H K hH hK hs hm hB old tail hstatic hold htail
  exact ⟨J, A, hn, records, hresult⟩

end GC.GeneralFlow
