import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.RecordHypFarC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapRadialCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapRestrictionPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordModelRestriction.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation

/-!
# Radial windows: transports for the native record family (C12X, S16 round 3, O-C12X-S16K G4)

New-file lemmas L1–L4 of the G2b RADIAL-DIFF (DELIVERIES), mirrors of S10HORN2's linked-window
transports (`LinkedWindowTransportC11SL`) for `StaticCapWitness.HasRadialCoordinates`:

* L1 `hasRadialCoordinates_restrictCanonicalWindow_C12X`,
  `GeometricCutoffRecord.radial_restrictModelWindow_C12X`, `radialWindows_restrictModelWindow_C12X`
  (the reserved native records of the step are a model-window restriction);
* L2 `translate_presented_static_cap_radial_C12X` (translated tail of a joined history; private
  `TerminalStaticPresentation` through `open private`);
* L3 `radial_of_record_static_heq_C12X` (two records of the same event with `HEq` statics);
* L4 `cover_events_C12X`, `joined_static_radial_C12X`, `radialWindows_joined_C12X`: radial windows
  of a concatenated record family from the old prefix and the translated, model-restricted tail,
  given the `HEq` facts exposed by the class extension.

The radial identities only involve the static witness (`window`, `capChart`, `retained`), which
these operations keep (restriction precomposes the window with the inclusion; translation is an
open-set cast).
-/

open private TerminalStaticPresentation TerminalStaticPresentation.ofPresented
  TerminalStaticPresentation.toPresented TerminalStaticPresentation.castOpen
  TerminalStaticPresentation.witness metric_event_heq_of_retained_event_heq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation

set_option autoImplicit false

noncomputable section

open Set Function Manifold DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent.PresentedStaticCap

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D D' ε ε' : ℝ} {m m' : ℕ}
  {b : E.RetainedBoundaryIndex}

/-- L1 (static form): restricting the canonical window keeps the radial identities. -/
theorem hasRadialCoordinates_restrictCanonicalWindow_C12X
    (S : E.PresentedStaticCap fixed D m ε b) (hS : S.hasCanonicalWindow)
    (hD' : 0 < D') (hD'D : D' ≤ D) (hm : m' ≤ m) (hε : ε ≤ ε')
    (h : S.witness.HasRadialCoordinates) :
    (S.restrictCanonicalWindow hS hD' hD'D hm hε).witness.HasRadialCoordinates := by
  have hsub : standardCapWindow D' ≤ standardCapWindow D :=
    fun _ hx => hx.trans_le (add_le_add hD'D (le_refl 1))
  exact ⟨fun x hx hc => h.1 x (hsub hx) hc, fun x hx => h.2 x (hsub hx)⟩

end MetricCutCapEvent.PresentedStaticCap

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
  {D ε : ℝ} {m : ℕ}

/-- L1 (record form). -/
theorem radial_restrictModelWindow_C12X (R : GeometricCutoffRecord H i p)
    (hR : ∀ b, (R.static b).hasCanonicalWindow)
    (hD : 0 < D) (hDp : D ≤ p.modelRadius) (hm : m ≤ p.modelOrder)
    (hε : p.modelAccuracy ≤ ε) (h : ∀ b, (R.static b).witness.HasRadialCoordinates)
    (b : (H.event i).RetainedBoundaryIndex) :
    ((R.restrictModelWindow hR hD hDp hm hε).static b).witness.HasRadialCoordinates :=
  MetricCutCapEvent.PresentedStaticCap.hasRadialCoordinates_restrictCanonicalWindow_C12X
    (R.static b) (hR b) hD hDp hm hε (h b)

end GeometricCutoffRecord

/-- L1 (family form, `RadialWindows_C12X`): the reserved native records of the step. -/
theorem radialWindows_restrictModelWindow_C12X {H : RetainedCoreHistory.{u}}
    {p : CutoffParameters} {D ε : ℝ} {m : ℕ}
    (R : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hR : ∀ i b, ((R i).static b).hasCanonicalWindow)
    (hD : 0 < D) (hDp : D ≤ p.modelRadius) (hm : m ≤ p.modelOrder)
    (hε : p.modelAccuracy ≤ ε) (h : RadialWindows_C12X H R) :
    RadialWindows_C12X H (fun i => (R i).restrictModelWindow (hR i) hD hDp hm hε) :=
  fun i b => (R i).radial_restrictModelWindow_C12X (hR i) hD hDp hm hε (h i) b

/-- L3: radial windows transfer along `HEq` of the static families of two records of the same
event (parameters equal on the static model fields). -/
theorem radial_of_record_static_heq_C12X {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p p' : CutoffParameters} (R : GeometricCutoffRecord H i p) (R' : GeometricCutoffRecord H i p')
    (hf : p'.fixed = p.fixed) (hD : p'.modelRadius = p.modelRadius)
    (hm : p'.modelOrder = p.modelOrder) (hε : p'.modelAccuracy = p.modelAccuracy)
    (hS : HEq R'.static R.static) (h : ∀ b, (R.static b).witness.HasRadialCoordinates) :
    ∀ b, (R'.static b).witness.HasRadialCoordinates :=
  MetricCutCapEvent.PresentedStaticCap.hasRadialCoordinates_of_family_heq
    rfl rfl rfl rfl HEq.rfl hf hD hm hε R.static R'.static hS h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.GeneralFlow

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe v

private theorem TerminalStaticPresentation.castOpen_radial_C12X
    {P Q D₀ N₀ : OrientedThreeStage.{v}} {X : SmoothCutCapTransition P Q D₀ N₀}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    {h : SmoothRiemannianMetric ThreeModel U} {g : Q.Metric}
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {b : {b : X.trace.tubes.Boundary //
      ∀ y, X.trace.tubes.coreBoundarySphere b y ∈ X.trace.retainedCore}}
    (S : TerminalStaticPresentation X U h g fixed D m ε b)
    (hS : (TerminalStaticPresentation.witness S).HasRadialCoordinates) :
    (TerminalStaticPresentation.witness
      (TerminalStaticPresentation.castOpen hUV S)).HasRadialCoordinates := by
  cases hUV
  exact hS

/-- L2: translating a presented static cap to a shifted event keeps the radial identities. -/
theorem translate_presented_static_cap_radial_C12X
    {P Q : OrientedThreeStage.{v}} {a s : ℝ} (E : RetainedCoreEvent P Q a s) (c : ℝ)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {b : E.toMetricCutCapEvent.RetainedBoundaryIndex}
    (S : E.toMetricCutCapEvent.PresentedStaticCap fixed D m ε b)
    (hS : S.witness.HasRadialCoordinates) :
    (translate_presented_static_cap E c S).witness.HasRadialCoordinates := by
  unfold translate_presented_static_cap
  exact TerminalStaticPresentation.castOpen_radial_C12X
    (U := E.toMetricCutCapEvent.incoming.terminalRegularOpen)
    (translated_terminal_open E.incoming c).symm
    (TerminalStaticPresentation.ofPresented S) hS

/-- Every event of a concatenated history is an old-prefix or a translated-tail event. -/
theorem cover_events_C12X {K J : RetainedCoreHistory.{v}} {c : ℝ} {n : ℕ}
    (A : AffineEventPrefix K J c n (Fin.last K.eventCount)) (hn : n ≤ J.eventCount)
    {Pr : Fin J.eventCount → Prop} (hold : ∀ i : Fin n, Pr (i.castLE hn))
    (htail : ∀ i : Fin K.eventCount, Pr (A.eventIndex i)) (j : Fin J.eventCount) : Pr j := by
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

/-- L4: radial windows of a concatenated record family from the old prefix and the translated,
model-restricted tail, given the `HEq` facts exposed by the class extension. -/
theorem joined_static_radial_C12X
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
    (hradOld : RadialWindows_C12X H old) (hradCoarse : RadialWindows_C12X K coarse) :
    RadialWindows_C12X J records := by
  refine cover_events_C12X A I.count_le
    (Pr := fun j => ∀ b, ((records j).static b).witness.HasRadialCoordinates) ?_ ?_
  · intro i
    exact MetricCutCapEvent.PresentedStaticCap.hasRadialCoordinates_of_family_heq
      (I.stage_eq i.castSucc) (I.stage_eq i.succ)
      (I.time_eq i.castSucc) (I.time_eq i.succ)
      (metric_event_heq_of_retained_event_heq
        (I.stage_eq i.castSucc) (I.stage_eq i.succ)
        (I.time_eq i.castSucc) (I.time_eq i.succ) (I.event_heq i))
      hqH.1 hqH.2.1 hqH.2.2.1 hqH.2.2.2 (old i).static (records (i.castLE I.count_le)).static
      (hOld i) (hradOld i)
  · intro i
    exact MetricCutCapEvent.PresentedStaticCap.hasRadialCoordinates_of_family_heq
      (A.stage_eq i.castSucc) (A.stage_eq i.succ)
      (A.time_eq i.castSucc) (A.time_eq i.succ)
      (metric_event_heq_of_retained_event_heq
        (A.stage_eq i.castSucc) (A.stage_eq i.succ)
        (A.time_eq i.castSucc) (A.time_eq i.succ) (A.event_heq i))
      hqC.1 hqC.2.1 hqC.2.2.1 hqC.2.2.2
      (fun b => translate_presented_static_cap (K.coreEvent i) c ((coarse i).static b))
      (records (A.eventIndex i)).static (hTail i)
      (fun b => translate_presented_static_cap_radial_C12X (K.coreEvent i) c
        ((coarse i).static b) (hradCoarse i b))

end GC.GeneralFlow

end
