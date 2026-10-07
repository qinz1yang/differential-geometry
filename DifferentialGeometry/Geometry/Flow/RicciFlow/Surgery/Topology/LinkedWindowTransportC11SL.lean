import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LinkedCanonicalWindowC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapRestrictionPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordModelRestriction.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation

/-!
# Linked-window transport mirrors (C11SL, S10 step 4 helper)

Mirrors of the `hasCanonicalWindow` transport lemmas for
`hasLinkedCanonicalWindow_C12X` (the link `δ' ≤ S.delta ∧ 2⌊δ'⁻¹⌋₊ ≤ k` rides along the same
`(x₀, δ', k, d, w)` witness, so every transport is the original proof plus two trailing facts):

* `hasLinkedCanonicalWindow_of_family_heq_C11SL`  (mirror of `hasCanonicalWindow_of_family_heq`);
* `hasLinkedCanonicalWindow_restrictCanonicalWindow_C11SL`, `…_restrictModelWindow_C11SL`;
* `translate_presented_static_cap_linked_C11SL` (private `TerminalStaticPresentation` through
  `open private`);
* `cover_events_C11SL`, `joined_static_linked_C11SL`: all events of a concatenated history are
  old-prefix or translated-tail events.
-/

open private TerminalStaticPresentation TerminalStaticPresentation.ofPresented
  TerminalStaticPresentation.toPresented TerminalStaticPresentation.castOpen
  TerminalStaticPresentation.delta TerminalStaticPresentation.order TerminalStaticPresentation.neck
  TerminalStaticPresentation.witness TerminalStaticPresentation.inclusion
  metric_event_heq_of_retained_event_heq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation

set_option autoImplicit false
noncomputable section

open Set Function Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent.PresentedStaticCap

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D D' ε ε' : ℝ} {m m' : ℕ} {b : E.RetainedBoundaryIndex}

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

/-- Mirror of `hasCanonicalWindow_of_family_heq`. -/
theorem hasLinkedCanonicalWindow_of_family_heq_C11SL
    {P' Q' : OrientedThreeStage.{u}} {a' s' : ℝ} {E' : MetricCutCapEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    {fixed' : StaticCapScaffold} {D' ε' : ℝ} {m' : ℕ}
    (hf : fixed' = fixed) (hD : D' = D) (hm : m' = m) (hε : ε' = ε)
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b)
    (S' : ∀ b : E'.RetainedBoundaryIndex, E'.PresentedStaticCap fixed' D' m' ε' b)
    (hS : HEq S' S) (hlinked : ∀ b, (S b).hasLinkedCanonicalWindow_C12X) :
    ∀ b, (S' b).hasLinkedCanonicalWindow_C12X := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  cases hf
  cases hD
  cases hm
  cases hε
  cases eq_of_heq hS
  exact hlinked

/-- Mirror of `hasCanonicalWindow_restrictCanonicalWindow`. -/
theorem hasLinkedCanonicalWindow_restrictCanonicalWindow_C11SL
    (S : E.PresentedStaticCap fixed D m ε b) (hS : S.hasCanonicalWindow)
    (hl : S.hasLinkedCanonicalWindow_C12X)
    (hD' : 0 < D') (hD'D : D' ≤ D) (hm : m' ≤ m) (hε : ε ≤ ε')
    (hcap : StandardCap.transitionEnd < D' + 1) :
    (S.restrictCanonicalWindow hS hD' hD'D hm hε).hasLinkedCanonicalWindow_C12X := by
  obtain ⟨x₀, δ, k, d, w, hscale, hmetric, hcover, hδS, hk⟩ := hl
  let w' := (w.weakenOrderAccuracy hm hε).restrictWindow hD' hD'D
  have heq : w.windowMetric = S.witness.windowMetric :=
    SmoothRiemannianMetric.ext_inner fun x v z =>
      (hmetric x v z).trans (S.window_inner x v z).symm
  have heq' : w'.windowMetric =
      (S.restrictCanonicalWindow hS hD' hD'D hm hε).witness.windowMetric := by
    rw [restrictCanonicalWindow_windowMetric]
    dsimp only [w']
    rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric,
      StandardCap.CanonicalStaticInsertionWitness.weakenOrderAccuracy_windowMetric, heq]
  refine ⟨x₀, δ, k, d, w', hscale, ?_, ?_, hδS, hk⟩
  · intro x v z
    rw [heq']
    exact (S.restrictCanonicalWindow hS hD' hD'D hm hε).window_inner x v z
  · intro z
    obtain ⟨x, hx, hpoint⟩ := hcover z
    let y : standardCapWindow D' := ⟨x.val, hx.trans_lt hcap⟩
    refine ⟨y, hx, ?_⟩
    change S.window
      ⟨x.val, (hx.trans_lt hcap).trans_le (add_le_add hD'D (le_refl 1))⟩ =
        S.inclusion (S.witness.cap z)
    exact hpoint

end MetricCutCapEvent.PresentedStaticCap

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
  {D ε : ℝ} {m : ℕ}

/-- Mirror of `hasCanonicalWindow_restrictModelWindow`. -/
theorem hasLinkedCanonicalWindow_restrictModelWindow_C11SL (R : GeometricCutoffRecord H i p)
    (hR : ∀ b, (R.static b).hasCanonicalWindow)
    (hl : ∀ b, (R.static b).hasLinkedCanonicalWindow_C12X)
    (hD : 0 < D) (hDp : D ≤ p.modelRadius) (hm : m ≤ p.modelOrder)
    (hε : p.modelAccuracy ≤ ε) (hcap : StandardCap.transitionEnd < D + 1)
    (b : (H.event i).RetainedBoundaryIndex) :
    ((R.restrictModelWindow hR hD hDp hm hε).static b).hasLinkedCanonicalWindow_C12X :=
  MetricCutCapEvent.PresentedStaticCap.hasLinkedCanonicalWindow_restrictCanonicalWindow_C11SL
    (R.static b) (hR b) (hl b) hD hDp hm hε hcap

end GeometricCutoffRecord

/-- Linked windows transfer along `HEq` of the static families of two records of the same event
(parameters equal on the static model fields). -/
theorem linked_of_record_static_heq_C11SL {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p p' : CutoffParameters} (R : GeometricCutoffRecord H i p) (R' : GeometricCutoffRecord H i p')
    (hf : p'.fixed = p.fixed) (hD : p'.modelRadius = p.modelRadius)
    (hm : p'.modelOrder = p.modelOrder) (hε : p'.modelAccuracy = p.modelAccuracy)
    (hS : HEq R'.static R.static) (h : ∀ b, (R.static b).hasLinkedCanonicalWindow_C12X) :
    ∀ b, (R'.static b).hasLinkedCanonicalWindow_C12X :=
  MetricCutCapEvent.PresentedStaticCap.hasLinkedCanonicalWindow_of_family_heq_C11SL
    rfl rfl rfl rfl HEq.rfl hf hD hm hε R.static R'.static hS h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.GeneralFlow

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe v

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

private def TerminalStaticPresentation.Linked
    {P Q D₀ N₀ : OrientedThreeStage.{v}} {X : SmoothCutCapTransition P Q D₀ N₀}
    {U : TopologicalSpace.Opens P.Carrier} {h : SmoothRiemannianMetric ThreeModel U}
    {g : Q.Metric} {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {b : {b : X.trace.tubes.Boundary //
      ∀ y, X.trace.tubes.coreBoundarySphere b y ∈ X.trace.retainedCore}}
    (S : TerminalStaticPresentation X U h g fixed D m ε b) : Prop :=
  ∃ (x₀ : U) (δ : ℝ) (k : ℕ) (d : normalizedDatum h x₀ δ k)
    (w : DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness
      d fixed.collarLength fixed.collar_pos D m ε),
    metricScalarAt h x₀ = (TerminalStaticPresentation.neck S).scale ∧
    (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
      (TerminalStaticPresentation.neck S).scale *
        g.inner (((TerminalStaticPresentation.inclusion S).comp
            (TerminalStaticPresentation.witness S).window) x)
        (mfderiv ThreeModel ThreeModel ((TerminalStaticPresentation.inclusion S).comp
          (TerminalStaticPresentation.witness S).window) x v)
        (mfderiv ThreeModel ThreeModel ((TerminalStaticPresentation.inclusion S).comp
          (TerminalStaticPresentation.witness S).window) x z)) ∧
    (∀ z : ThreeBall, ∃ x : standardCapWindow D,
      ‖x.val‖ ≤ DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd ∧
      ((TerminalStaticPresentation.inclusion S).comp
        (TerminalStaticPresentation.witness S).window) x =
        TerminalStaticPresentation.inclusion S ((TerminalStaticPresentation.witness S).cap z)) ∧
    δ ≤ TerminalStaticPresentation.delta S ∧ 2 * ⌊δ⁻¹⌋₊ ≤ k

private theorem TerminalStaticPresentation.castOpen_linked
    {P Q D₀ N₀ : OrientedThreeStage.{v}} {X : SmoothCutCapTransition P Q D₀ N₀}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {g : Q.Metric}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {b : {b : X.trace.tubes.Boundary //
      ∀ y, X.trace.tubes.coreBoundarySphere b y ∈ X.trace.retainedCore}}
    (S : TerminalStaticPresentation X U h g fixed D m ε b) (hS : S.Linked) :
    (TerminalStaticPresentation.castOpen hUV S).Linked := by
  cases hUV
  exact hS

private theorem TerminalStaticPresentation.ofPresented_linked
    {P Q : OrientedThreeStage.{v}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b) (hS : S.hasLinkedCanonicalWindow_C12X) :
    (TerminalStaticPresentation.ofPresented S).Linked := hS

private theorem TerminalStaticPresentation.toPresented_linked
    {P Q : OrientedThreeStage.{v}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : TerminalStaticPresentation E.transition E.incoming.terminalRegularOpen
      E.terminal.metric E.outputMetric fixed D m ε b) (hS : S.Linked) :
    (TerminalStaticPresentation.toPresented S).hasLinkedCanonicalWindow_C12X := hS

/-- Mirror of `translate_presented_static_cap_canonical`. -/
theorem translate_presented_static_cap_linked_C11SL
    {P Q : OrientedThreeStage.{v}} {a s : ℝ} (E : RetainedCoreEvent P Q a s) (c : ℝ)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {b : E.toMetricCutCapEvent.RetainedBoundaryIndex}
    (S : E.toMetricCutCapEvent.PresentedStaticCap fixed D m ε b)
    (hS : S.hasLinkedCanonicalWindow_C12X) :
    (translate_presented_static_cap E c S).hasLinkedCanonicalWindow_C12X := by
  unfold translate_presented_static_cap
  have h1 := TerminalStaticPresentation.ofPresented_linked S hS
  have h2 := TerminalStaticPresentation.castOpen_linked
    (U := E.toMetricCutCapEvent.incoming.terminalRegularOpen)
    (translated_terminal_open E.incoming c).symm
    (TerminalStaticPresentation.ofPresented S) h1
  exact TerminalStaticPresentation.toPresented_linked _ h2

/-- Every event of a concatenated history is an old-prefix or a translated-tail event. -/
theorem cover_events_C11SL {K J : RetainedCoreHistory.{v}} {c : ℝ} {n : ℕ}
    (A : AffineEventPrefix K J c n (Fin.last K.eventCount)) (hn : n ≤ J.eventCount)
    {P : Fin J.eventCount → Prop} (hold : ∀ i : Fin n, P (i.castLE hn))
    (htail : ∀ i : Fin K.eventCount, P (A.eventIndex i)) (j : Fin J.eventCount) : P j := by
  by_cases hj : j.val < n
  · have hji : (⟨j.val, hj⟩ : Fin n).castLE hn = j := Fin.ext rfl
    rw [← hji]
    exact hold _
  · have hc := A.count_eq
    have hl : (Fin.last K.eventCount).val = K.eventCount := rfl
    let i : Fin K.eventCount := ⟨j.val - n, by omega⟩
    have hji : A.eventIndex i = j := by
      apply Fin.ext
      change n + (j.val - n) = j.val
      omega
    rw [← hji]
    exact htail i

/-- Linked windows of a concatenated record family from the old prefix and the translated,
model-restricted tail, given the `HEq` facts exposed by the overlap extensions. -/
theorem joined_static_linked_C11SL
    {H K J : RetainedCoreHistory.{v}} {c : ℝ} (I : RawInitialPrefix H J)
    (A : AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount))
    {pH pC q : CutoffParameters}
    (hqH : q.fixed = pH.fixed ∧ q.modelRadius = pH.modelRadius ∧ q.modelOrder = pH.modelOrder ∧
      q.modelAccuracy = pH.modelAccuracy)
    (hqC : q.fixed = pC.fixed ∧ q.modelRadius = pC.modelRadius ∧ q.modelOrder = pC.modelOrder ∧
      q.modelAccuracy = pC.modelAccuracy)
    (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i pH)
    (coarse : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pC)
    (records : ∀ j : Fin J.eventCount, GeometricCutoffRecord J.toHistory j q)
    (hOld : ∀ i : Fin H.eventCount,
      HEq (records (i.castLE I.count_le)).static (old i).static)
    (hTail : ∀ i : Fin K.eventCount, HEq (records (A.eventIndex i)).static
      (fun b => translate_presented_static_cap (K.coreEvent i) c ((coarse i).static b)))
    (hlinkOld : ∀ i b, ((old i).static b).hasLinkedCanonicalWindow_C12X)
    (hlinkCoarse : ∀ i b, ((coarse i).static b).hasLinkedCanonicalWindow_C12X) :
    ∀ j b, ((records j).static b).hasLinkedCanonicalWindow_C12X := by
  refine cover_events_C11SL A I.count_le
    (P := fun j => ∀ b, ((records j).static b).hasLinkedCanonicalWindow_C12X) ?_ ?_
  · intro i
    exact MetricCutCapEvent.PresentedStaticCap.hasLinkedCanonicalWindow_of_family_heq_C11SL
      (I.stage_eq i.castSucc) (I.stage_eq i.succ)
      (I.time_eq i.castSucc) (I.time_eq i.succ)
      (metric_event_heq_of_retained_event_heq
        (I.stage_eq i.castSucc) (I.stage_eq i.succ)
        (I.time_eq i.castSucc) (I.time_eq i.succ) (I.event_heq i))
      hqH.1 hqH.2.1 hqH.2.2.1 hqH.2.2.2 (old i).static (records (i.castLE I.count_le)).static
      (hOld i) (hlinkOld i)
  · intro i
    exact MetricCutCapEvent.PresentedStaticCap.hasLinkedCanonicalWindow_of_family_heq_C11SL
      (A.stage_eq i.castSucc) (A.stage_eq i.succ)
      (A.time_eq i.castSucc) (A.time_eq i.succ)
      (metric_event_heq_of_retained_event_heq
        (A.stage_eq i.castSucc) (A.stage_eq i.succ)
        (A.time_eq i.castSucc) (A.time_eq i.succ) (A.event_heq i))
      hqC.1 hqC.2.1 hqC.2.2.1 hqC.2.2.2
      (fun b => translate_presented_static_cap (K.coreEvent i) c ((coarse i).static b))
      (records (A.eventIndex i)).static (hTail i)
      (fun b => translate_presented_static_cap_linked_C11SL (K.coreEvent i) c
        ((coarse i).static b) (hlinkCoarse i b))

end GC.GeneralFlow
