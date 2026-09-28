import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordEventExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordHorizonExtension

noncomputable section
open Set Function Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent.PresentedStaticCap

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

def hasCanonicalWindow (S : E.PresentedStaticCap fixed D m ε b) : Prop :=
  ∃ (x₀ : E.incoming.terminalRegularOpen) (δ : ℝ) (k : ℕ)
    (d : normalizedDatum E.terminal.metric x₀ δ k)
    (w : StandardCap.CanonicalStaticInsertionWitness d fixed.collarLength fixed.collar_pos D m ε),
    metricScalarAt E.terminal.metric x₀ = S.neck.scale ∧
    (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
      S.neck.scale * E.outputMetric.inner (S.window x)
        (mfderiv ThreeModel ThreeModel S.window x v)
        (mfderiv ThreeModel ThreeModel S.window x z)) ∧
    ∀ z : ThreeBall, ∃ x : standardCapWindow D, ‖x.val‖ ≤ StandardCap.transitionEnd ∧
      S.window x = S.inclusion (S.witness.cap z)

theorem hasCanonicalWindow_of_family_heq
    {P' Q' : OrientedThreeStage.{u}} {a' s' : ℝ} {E' : MetricCutCapEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    {fixed' : StaticCapScaffold} {D' ε' : ℝ} {m' : ℕ}
    (hf : fixed' = fixed) (hD : D' = D) (hm : m' = m) (hε : ε' = ε)
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b)
    (S' : ∀ b : E'.RetainedBoundaryIndex, E'.PresentedStaticCap fixed' D' m' ε' b)
    (hS : HEq S' S) (hcanonical : ∀ b, (S b).hasCanonicalWindow) :
    ∀ b, (S' b).hasCanonicalWindow := by
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
  exact hcanonical

end MetricCutCapEvent.PresentedStaticCap


theorem RetainedCoreHistory.exists_canonical_cutoff_records_at_appendEvent
    {Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u}) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {p q : CutoffParameters}
    (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (new : GeometricCutoffRecord (H.appendEvent hs E hinit).toHistory
      (Fin.last H.eventCount) q)
    (hfixed : q.fixed = p.fixed) (hradius : q.modelRadius = p.modelRadius)
    (horder : q.modelOrder = p.modelOrder) (haccuracy : q.modelAccuracy = p.modelAccuracy)
    (hrecenter : q.recenterConstant = p.recenterConstant)
    (hold : ∀ i b, ((old i).static b).hasCanonicalWindow)
    (hnew : ∀ b, (new.static b).hasCanonicalWindow) :
    ∃ R : ∀ i : Fin (H.appendEvent hs E hinit).eventCount,
        GeometricCutoffRecord (H.appendEvent hs E hinit).toHistory i (p.spliceAt q s),
      ∀ i b, ((R i).static b).hasCanonicalWindow := by
  obtain ⟨R, hOld, _, hNew, _⟩ := H.exists_cutoff_records_at_appendEvent hs E hinit
    old new hfixed hradius horder haccuracy hrecenter
  refine ⟨R, ?_⟩
  intro i
  cases i using Fin.lastCases with
  | last =>
    exact MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
      rfl rfl rfl rfl HEq.rfl hfixed.symm hradius.symm horder.symm haccuracy.symm
      new.static (R (Fin.last H.eventCount)).static hNew hnew
  | cast i =>
    have hE : HEq ((H.appendEvent hs E hinit).toHistory.event i.castSucc)
        (H.toHistory.event i) := by
      change HEq ((H.extendCoreEventFamily E i.castSucc).toMetricCutCapEvent) (H.toHistory.event i)
      rw [H.extendCoreEventFamily_toMetricCutCapEvent]
      exact H.toHistory.appendEvent_event_castSucc_heq hs E.toMetricCutCapEvent hinit i
    exact MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
      (H.appendEvent_stage_castSucc hs E hinit i.castSucc)
      (H.appendEvent_stage_castSucc hs E hinit i.succ)
      (H.appendEvent_time_castSucc hs E hinit i.castSucc)
      (H.appendEvent_time_castSucc hs E hinit i.succ)
      hE
      rfl rfl rfl rfl (old i).static (R i.castSucc).static (hOld i) (hold i)


namespace RetainedCoreHistory

def hasCanonicalCutoffRecords (H : RetainedCoreHistory.{u})
    (p₀ : CutoffParameters) (δ₀ ρ₀ : ℝ) : Prop :=
  ∃ p : CutoffParameters,
    p.fixed = p₀.fixed ∧ p.modelRadius = p₀.modelRadius ∧ p.modelOrder = p₀.modelOrder ∧
    p.modelAccuracy = p₀.modelAccuracy ∧ p.recenterConstant = p₀.recenterConstant ∧
    ∃ records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p,
      (∀ i b, ((records i).static b).hasCanonicalWindow) ∧
      (∀ i : Fin H.eventCount, p.delta (H.time i.succ) ≤ δ₀) ∧
      ∀ i : Fin H.eventCount, p.neckRadius (H.time i.succ) ≤ ρ₀

theorem hasCanonicalCutoffRecords_atZero (P : OrientedThreeStage.{u}) (g : P.Metric)
    (p₀ : CutoffParameters) (δ₀ ρ₀ : ℝ) :
    (RetainedCoreHistory.atZero P g).hasCanonicalCutoffRecords p₀ δ₀ ρ₀ := by
  refine ⟨p₀, rfl, rfl, rfl, rfl, rfl, (fun i => Fin.elim0 i), ?_, ?_, ?_⟩
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i

theorem hasCanonicalCutoffRecords_extendHorizon
    {H : RetainedCoreHistory.{u}}
    {p₀ : CutoffParameters} {δ₀ ρ₀ : ℝ}
    (hH : H.hasCanonicalCutoffRecords p₀ δ₀ ρ₀)
    (T : ℝ) (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount)) :
    (H.extendHorizon T hT S hS).hasCanonicalCutoffRecords p₀ δ₀ ρ₀ := by
  obtain ⟨p, hfixed, hradius, horder, haccuracy, hrecenter, records, hcanonical, hdelta, hneck⟩ := hH
  refine ⟨p, hfixed, hradius, horder, haccuracy, hrecenter,
    fun i => (records i).extendHorizon T hT S hS, ?_, hdelta, hneck⟩
  intro i b
  exact hcanonical i b

theorem hasCanonicalCutoffRecords_appendEvent
    {Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u}) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {p₀ q : CutoffParameters} {δ₀ ρ₀ : ℝ}
    (hH : H.hasCanonicalCutoffRecords p₀ δ₀ ρ₀)
    (new : GeometricCutoffRecord (H.appendEvent hs E hinit).toHistory
      (Fin.last H.eventCount) q)
    (hfixed : q.fixed = p₀.fixed) (hradius : q.modelRadius = p₀.modelRadius)
    (horder : q.modelOrder = p₀.modelOrder) (haccuracy : q.modelAccuracy = p₀.modelAccuracy)
    (hrecenter : q.recenterConstant = p₀.recenterConstant)
    (hnew : ∀ b, (new.static b).hasCanonicalWindow)
    (hδnew : q.delta s ≤ δ₀) (hρnew : q.neckRadius s ≤ ρ₀) :
    (H.appendEvent hs E hinit).hasCanonicalCutoffRecords p₀ δ₀ ρ₀ := by
  obtain ⟨p, hpf, hpD, hpm, hpε, hpc, old, hold, hδold, hρold⟩ := hH
  obtain ⟨records, hcanonical⟩ := H.exists_canonical_cutoff_records_at_appendEvent hs E hinit
    old new (hfixed.trans hpf.symm) (hradius.trans hpD.symm) (horder.trans hpm.symm)
    (haccuracy.trans hpε.symm) (hrecenter.trans hpc.symm) hold hnew
  refine ⟨p.spliceAt q s, hpf, hpD, hpm, hpε, hpc, records, hcanonical, ?_, ?_⟩
  · intro i
    cases i using Fin.lastCases with
    | last =>
      have ht : (H.appendEvent hs E hinit).time (Fin.last H.eventCount).succ = s :=
        H.appendEvent_time_last hs E hinit
      erw [ht, CutoffParameters.spliceAt_delta_self]
      exact hδnew
    | cast i =>
      have ht : (H.appendEvent hs E hinit).time i.castSucc.succ = H.time i.succ :=
        H.appendEvent_time_castSucc hs E hinit i.succ
      have hne : H.time i.succ ≠ s :=
        ne_of_lt ((H.time_strictMono.monotone (Fin.le_last i.succ)).trans_lt hs)
      erw [ht, CutoffParameters.spliceAt_delta_of_ne p q hne]
      exact hδold i
  · intro i
    cases i using Fin.lastCases with
    | last =>
      have ht : (H.appendEvent hs E hinit).time (Fin.last H.eventCount).succ = s :=
        H.appendEvent_time_last hs E hinit
      erw [ht, CutoffParameters.spliceAt_neckRadius_self]
      exact hρnew
    | cast i =>
      have ht : (H.appendEvent hs E hinit).time i.castSucc.succ = H.time i.succ :=
        H.appendEvent_time_castSucc hs E hinit i.succ
      have hne : H.time i.succ ≠ s :=
        ne_of_lt ((H.time_strictMono.monotone (Fin.le_last i.succ)).trans_lt hs)
      erw [ht, CutoffParameters.spliceAt_neckRadius_of_ne p q hne]
      exact hρold i

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
