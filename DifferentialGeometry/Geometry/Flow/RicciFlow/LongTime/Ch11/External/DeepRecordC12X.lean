import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.DeepTransportHistoryC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordHorizonExtension

/-!
# Deep cut necks of one cutoff record (C12X, S16 round 3 G2c, O-C12X-S16L G1a)

Statement vocabulary and record-level transports for threading the deep backward-neck certificate
(`IncomingBackwardNeckDeep_C12X`, depth factor `θ`) through the record construction.  Tracked
files that state the certificate import only this file (light: record definitions plus the
history transports of S16K G1c).

* `GeometricCutoffRecord.DeepNecks_C12X θ G`: every cut neck of the single record `G` carries a
  deep backward neck at the record's nominal radius; the family form is the first conjunct of
  `RecordHypFar_C12X` (`recordHypFar_iff_deepNecks_C12X`, `Iff.rfl`).
* `GeometricCutoffRecord.deepNecks_of_neck_heq_C12X`: the record produced by the Horn construction
  (`G.delta`, `G.order` constant, `HEq G.neck Nrecord`, neck scale `Q`) is deep once the necks
  `Nrecord` carry deep backward necks at radius `√Q⁻¹` (the nominal radius is `√Q⁻¹`).
* `RecordHypFar_C12X.appendEvent_family_C12X`: the family obtained by appending one event (old
  records identified by `HEq` at `castSucc`, the new record at `Fin.last`) keeps the hypothesis.
* `RecordHypFar_C12X.extendHorizon_C12X`: extending the horizon by a closed slab keeps it.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- Every cut neck of one cutoff record carries a deep backward neck of depth factor `θ` at the
record's nominal radius. -/
def GeometricCutoffRecord.DeepNecks_C12X {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (θ : ℝ) (G : GeometricCutoffRecord H i p) : Prop :=
  ∀ α : (H.event i).transition.trace.tubes.Index,
    Nonempty (IncomingBackwardNeckDeep_C12X H i (G.neck α) (G.nominalRadius ⟨α⟩) θ)

/-- The route β′ record hypothesis is per-record deep necks together with radial windows. -/
theorem recordHypFar_iff_deepNecks_C12X {θ : ℝ} {H : RetainedCoreHistory.{u}}
    {p : CutoffParameters}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p} :
    RecordHypFar_C12X θ H records ↔
      (∀ i, (records i).DeepNecks_C12X θ) ∧ RadialWindows_C12X H records :=
  Iff.rfl

/-- The nominal radius of a record whose cut neck has scale `Q` is `√Q⁻¹`. -/
theorem GeometricCutoffRecord.nominalRadius_eq_of_scale_C12X {H : ObservedHistory.{u}}
    {i : Fin H.eventCount} {p : CutoffParameters} (G : GeometricCutoffRecord H i p) {Q : ℝ}
    (α : (H.event i).transition.trace.tubes.Index) (hscale : (G.neck α).scale = Q) :
    G.nominalRadius ⟨α⟩ = Real.sqrt Q⁻¹ := by
  have h := G.scale_eq α
  rw [hscale] at h
  rw [h, inv_inv, Real.sqrt_sq (G.nominal_pos _).le]

private theorem deep_of_neck_heq_aux_C12X {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {θ r δ : ℝ} {k : ℕ} {d : (H.event i).transition.trace.tubes.Index → ℝ}
    {o : (H.event i).transition.trace.tubes.Index → ℕ}
    (F : ∀ α, NormalizedNeck (H.event i).terminal.metric (d α) (o α))
    (N : (H.event i).transition.trace.tubes.Index →
      NormalizedNeck (H.event i).terminal.metric δ k)
    (hd : d = fun _ => δ) (ho : o = fun _ => k) (hF : HEq F N)
    (α : (H.event i).transition.trace.tubes.Index)
    (hD : Nonempty (IncomingBackwardNeckDeep_C12X H i (N α) r θ)) :
    Nonempty (IncomingBackwardNeckDeep_C12X H i (F α) r θ) := by
  subst hd ho
  cases eq_of_heq hF
  exact hD

/-- A record of the Horn construction (constant precision and order, cut necks `HEq` to `Nrecord`,
neck scale `Q`) is deep once every `Nrecord α` has a deep backward neck at radius `√Q⁻¹`. -/
theorem GeometricCutoffRecord.deepNecks_of_neck_heq_C12X {H : ObservedHistory.{u}}
    {i : Fin H.eventCount} {p : CutoffParameters} {θ δ Q : ℝ} {k : ℕ}
    (G : GeometricCutoffRecord H i p)
    (Nrecord : (H.event i).transition.trace.tubes.Index →
      NormalizedNeck (H.event i).terminal.metric δ k)
    (hδ : G.delta = fun _ => δ) (hk : G.order = fun _ => k) (hN : HEq G.neck Nrecord)
    (hscale : ∀ α, (G.neck α).scale = Q)
    (hD : ∀ α, Nonempty (IncomingBackwardNeckDeep_C12X H i (Nrecord α) (Real.sqrt Q⁻¹) θ)) :
    G.DeepNecks_C12X θ := by
  intro α
  rw [G.nominalRadius_eq_of_scale_C12X α (hscale α)]
  exact deep_of_neck_heq_aux_C12X G.neck Nrecord hδ hk hN α (hD α)

private theorem deep_of_family_heq_aux_C12X
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {E' : MetricCutCapEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    {d : E.transition.trace.tubes.Index → ℝ} {o : E.transition.trace.tubes.Index → ℕ}
    {d' : E'.transition.trace.tubes.Index → ℝ} {o' : E'.transition.trace.tubes.Index → ℕ}
    (nom : Nonempty E.transition.trace.tubes.Index → ℝ)
    (nom' : Nonempty E'.transition.trace.tubes.Index → ℝ)
    (F : ∀ α, NormalizedNeck E.terminal.metric (d α) (o α))
    (F' : ∀ α, NormalizedNeck E'.terminal.metric (d' α) (o' α))
    (hnom : HEq nom' nom) (hd : HEq d' d) (ho : HEq o' o) (hF : HEq F' F)
    (M : ∀ {δ : ℝ} {k : ℕ}, NormalizedNeck E.terminal.metric δ k → ℝ → Prop)
    (M' : ∀ {δ : ℝ} {k : ℕ}, NormalizedNeck E'.terminal.metric δ k → ℝ → Prop)
    (T : ∀ {δ : ℝ} {k : ℕ} (N : NormalizedNeck E.terminal.metric δ k)
      (N' : NormalizedNeck E'.terminal.metric δ k) (r : ℝ), HEq N' N → M N r → M' N' r)
    (h : ∀ α, M (F α) (nom ⟨α⟩)) : ∀ α', M' (F' α') (nom' ⟨α'⟩) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  cases eq_of_heq hd
  cases eq_of_heq ho
  cases eq_of_heq hF
  cases eq_of_heq hnom
  exact fun α => T (F α) (F α) _ HEq.rfl (h α)

/-- Deep necks pass between two records of the same event identified by `HEq` (different cutoff
parameters allowed). -/
theorem GeometricCutoffRecord.deepNecks_of_heq_C12X {H : ObservedHistory.{u}}
    {i : Fin H.eventCount} {θ : ℝ} {p p' : CutoffParameters}
    (G : GeometricCutoffRecord H i p) (R : GeometricCutoffRecord H i p')
    (hnom : HEq R.nominalRadius G.nominalRadius) (hd : HEq R.delta G.delta)
    (ho : HEq R.order G.order) (hN : HEq R.neck G.neck) (h : G.DeepNecks_C12X θ) :
    R.DeepNecks_C12X θ :=
  deep_of_family_heq_aux_C12X rfl rfl rfl rfl HEq.rfl G.nominalRadius R.nominalRadius G.neck
    R.neck hnom hd ho hN (fun N r => Nonempty (IncomingBackwardNeckDeep_C12X H i N r θ))
    (fun N r => Nonempty (IncomingBackwardNeckDeep_C12X H i N r θ))
    (fun N N' _ hN' hD => by cases eq_of_heq hN'; exact hD) h

/-- An old record of `H` and the record of the same event after appending an event (identified by
`HEq` at `i.castSucc`): deep necks pass from the old record to the new one. -/
theorem GeometricCutoffRecord.deepNecks_appendEvent_castSucc_C12X
    {Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u}) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {θ : ℝ} {p p' : CutoffParameters} (i : Fin H.eventCount)
    (old : GeometricCutoffRecord H.toHistory i p)
    (R : GeometricCutoffRecord (H.appendEvent hs E hinit).toHistory i.castSucc p')
    (hnom : HEq R.nominalRadius old.nominalRadius) (hd : HEq R.delta old.delta)
    (ho : HEq R.order old.order) (hN : HEq R.neck old.neck)
    (h : old.DeepNecks_C12X θ) : R.DeepNecks_C12X θ := by
  have hE : HEq ((H.appendEvent hs E hinit).toHistory.event i.castSucc)
      (H.toHistory.event i) := by
    change HEq ((H.extendCoreEventFamily E i.castSucc).toMetricCutCapEvent)
      (H.toHistory.event i)
    exact (heq_of_eq (H.extendCoreEventFamily_toMetricCutCapEvent E i.castSucc)).trans
      (H.toHistory.appendEvent_event_castSucc_heq hs E.toMetricCutCapEvent hinit i)
  exact deep_of_family_heq_aux_C12X
    (H.appendEvent_stage_castSucc hs E hinit i.castSucc)
    (H.appendEvent_stage_castSucc hs E hinit i.succ)
    (H.appendEvent_time_castSucc hs E hinit i.castSucc)
    (H.appendEvent_time_castSucc hs E hinit i.succ) hE
    old.nominalRadius R.nominalRadius old.neck R.neck hnom hd ho hN
    (fun N r => Nonempty (IncomingBackwardNeckDeep_C12X H.toHistory i N r θ))
    (fun N' r => Nonempty (IncomingBackwardNeckDeep_C12X (H.appendEvent hs E hinit).toHistory
      i.castSucc N' r θ))
    (fun _ _ _ hN' hD => hD.map (IncomingBackwardNeckDeep_C12X.appendEvent_C12X H hs E hinit hN'))
    h

/-- Appending one event: old records (identified at `castSucc`) and the new record (at
`Fin.last`) keep deep necks, so the appended family satisfies the route β′ hypothesis. -/
theorem RecordHypFar_C12X.appendEvent_family_C12X
    {Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u}) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {θ : ℝ} {p q p' : CutoffParameters}
    (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (new : GeometricCutoffRecord (H.appendEvent hs E hinit).toHistory (Fin.last H.eventCount) q)
    (records : ∀ i : Fin (H.appendEvent hs E hinit).eventCount,
      GeometricCutoffRecord (H.appendEvent hs E hinit).toHistory i p')
    (hOld : ∀ i : Fin H.eventCount,
      HEq (records i.castSucc).nominalRadius (old i).nominalRadius ∧
      HEq (records i.castSucc).delta (old i).delta ∧
      HEq (records i.castSucc).order (old i).order ∧
      HEq (records i.castSucc).neck (old i).neck ∧
      HEq (records i.castSucc).static (old i).static)
    (hNewNominal : HEq (records (Fin.last H.eventCount)).nominalRadius new.nominalRadius)
    (hNewDelta : HEq (records (Fin.last H.eventCount)).delta new.delta)
    (hNewOrder : HEq (records (Fin.last H.eventCount)).order new.order)
    (hNewNeck : HEq (records (Fin.last H.eventCount)).neck new.neck)
    (hold : ∀ i, (old i).DeepNecks_C12X θ) (hnew : new.DeepNecks_C12X θ)
    (hradial : RadialWindows_C12X (H.appendEvent hs E hinit) records) :
    RecordHypFar_C12X θ (H.appendEvent hs E hinit) records := by
  refine ⟨fun i => ?_, hradial⟩
  cases i using Fin.lastCases with
  | last =>
    exact new.deepNecks_of_heq_C12X _ hNewNominal hNewDelta hNewOrder hNewNeck hnew
  | cast i =>
    exact GeometricCutoffRecord.deepNecks_appendEvent_castSucc_C12X H hs E hinit i (old i) _
      (hOld i).1 (hOld i).2.1 (hOld i).2.2.1 (hOld i).2.2.2.1 (hold i)

/-- Extending the horizon by a closed slab keeps deep necks of a record. -/
theorem GeometricCutoffRecord.deepNecks_extendHorizon_C12X {H : RetainedCoreHistory.{u}}
    (T : ℝ) (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {i : Fin H.eventCount} {p : CutoffParameters} {θ : ℝ}
    (R : GeometricCutoffRecord H.toHistory i p) (h : R.DeepNecks_C12X θ) :
    (GeometricCutoffRecord.extendHorizon T hT S hS R).DeepNecks_C12X θ := by
  intro α
  obtain ⟨D⟩ := h α
  exact ⟨IncomingBackwardNeckDeep_C12X.ofInitialEmbedding_C12X
    (H := H.toHistory) (J := (H.extendHorizon T hT S hS).toHistory) le_rfl (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => HEq.rfl) HEq.rfl D⟩

/-- Extending the horizon by a closed slab keeps the route β′ record hypothesis. -/
theorem RecordHypFar_C12X.extendHorizon_C12X {H : RetainedCoreHistory.{u}}
    (T : ℝ) (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {p : CutoffParameters} {θ : ℝ}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (h : RecordHypFar_C12X θ H records) :
    RecordHypFar_C12X θ (H.extendHorizon T hT S hS)
      (fun i => GeometricCutoffRecord.extendHorizon T hT S hS (records i)) :=
  ⟨fun i => (records i).deepNecks_extendHorizon_C12X T hT S hS (h.1 i), h.2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
