import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PreparedHistoryCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.DeepProducerUniformC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.DeepTransportC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.DeepRecordC12X

/-!
# Deep record certificate at the Poincaré layer (C12X, S16 round 3 G2c, O-C12X-S16L G1b)

The record backward necks of the main chain are a *premise* of the Horn record construction
(CT/HornCutoffRecord); the caller CT/PoincareHornCutoffRecordOfFineCutNecksDistanceC11X discharges
it with the depth-one producer of CT/PreparedHistoryCutoff (`…:156`, private) and the record-neck
transfer (`…:38`, private).  This file gives the deep twins (depth factor `θ`, `1 < θ < 3/2`, main
instance `θ = 5/4`), built on the S16K producer and transports:

* `nonempty_incomingBackwardNeckDeep_record_of_selected_restrictions_C12X` (twin of `…:38`):
  `oriented ∘ rotatedDatum` of the deep neck of the restricted selected neck;
* `nonempty_selected_restriction_retained_appendDeep_C12X` (twin of `…:117`): from the observed
  append to the retained-core append (`ofInitialEmbedding_C12X`);
* `exists_uniform_selected_neck_retained_append_backwardDeep_C12X` (twin of `…:156`): same
  hypotheses and quantifier order, conclusion `IncomingBackwardNeckDeep_C12X … θ`; its
  `toIncomingBackwardNeck` is the depth-one neck of the original;
* `GeometricCutoffRecord.deepNecks_of_selected_restrictions_C12X`: the Horn record
  (`HEq G.neck Nrecord`, neck scale `Q`) has deep cut necks (`G.DeepNecks_C12X θ`).

No tracked file is changed; the private helpers are reused via `open private`.
-/

open private exists_selected_neck_of_event_heq NormalizedNeck.lowerOrder_oriented_rotatedDatum from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PreparedHistoryCutoff

set_option autoImplicit false

noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section Record

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}

private local instance deepCutoffSigmaCompact_C12X :
    SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.event i).incoming.terminalRegularOpen.isOpen)

/-- Deep twin of the record-neck transfer of CT/PreparedHistoryCutoff: record necks
`(oriented ∘ rotatedDatum ∘ lowerOrder ∘ monoDelta)` of the selected necks are deep. -/
theorem nonempty_incomingBackwardNeckDeep_record_of_selected_restrictions_C12X
    {δ r θ : ℝ} {m n : ℕ} {eps : Fin n → ℝ} {order : Fin n → ℕ}
    (O : ∀ j, NormalizedNeck (H.event i).terminal.metric (eps j) (order j))
    (hδ : ∀ j, eps j ≤ δ) (hδ1 : δ < 1) (hm : ∀ j, m ≤ order j)
    (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
      spherePoint = (O j).sphereMark)
    (side : Fin n → Bool)
    (Nrecord : (H.event i).transition.trace.tubes.Index →
      NormalizedNeck (H.event i).terminal.metric δ m)
    (e : Fin n ≃ (H.event i).transition.trace.tubes.Index)
    (hN : ∀ j, Nrecord (e j) =
      (((O j).monoDelta (hδ j) hδ1).rotatedDatum (rotation j) (hmark j)
        (side j)).oriented.toNormalizedNeck.lowerOrder (hm j))
    (hB : ∀ j, Nonempty (IncomingBackwardNeckDeep_C12X H i
      (((O j).monoDelta (hδ j) hδ1).lowerOrder (hm j)) r θ)) :
    ∀ j, Nonempty (IncomingBackwardNeckDeep_C12X H i (Nrecord j) r θ) := by
  intro j
  obtain ⟨B⟩ := hB (e.symm j)
  have he := hN (e.symm j)
  rw [e.apply_symm_apply] at he
  rw [he, ← NormalizedNeck.lowerOrder_oriented_rotatedDatum]
  exact ⟨IncomingBackwardNeckDeep_C12X.oriented_C12X _
    (B.rotatedDatum_C12X (rotation (e.symm j)) (hmark (e.symm j)) (side (e.symm j)))⟩

/-- The record of the Horn construction has deep cut necks once the restricted selected necks
carry deep backward necks at radius `√Q⁻¹` (`Nrecord` and the record identified by `HEq`, neck
scale `Q`). -/
theorem GeometricCutoffRecord.deepNecks_of_selected_restrictions_C12X {p : CutoffParameters}
    {θ δ Q : ℝ} {m n : ℕ} {eps : Fin n → ℝ} {order : Fin n → ℕ}
    (O : ∀ j, NormalizedNeck (H.event i).terminal.metric (eps j) (order j))
    (hδ : ∀ j, eps j ≤ δ) (hδ1 : δ < 1) (hm : ∀ j, m ≤ order j)
    (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
      spherePoint = (O j).sphereMark)
    (side : Fin n → Bool)
    (Nrecord : (H.event i).transition.trace.tubes.Index →
      NormalizedNeck (H.event i).terminal.metric δ m)
    (e : Fin n ≃ (H.event i).transition.trace.tubes.Index)
    (hN : ∀ j, Nrecord (e j) =
      (((O j).monoDelta (hδ j) hδ1).rotatedDatum (rotation j) (hmark j)
        (side j)).oriented.toNormalizedNeck.lowerOrder (hm j))
    (hB : ∀ j, Nonempty (IncomingBackwardNeckDeep_C12X H i
      (((O j).monoDelta (hδ j) hδ1).lowerOrder (hm j)) (Real.sqrt Q⁻¹) θ))
    (G : GeometricCutoffRecord H i p) (hGδ : G.delta = fun _ => δ) (hGm : G.order = fun _ => m)
    (hGN : HEq G.neck Nrecord) (hGscale : ∀ α, (G.neck α).scale = Q) :
    G.DeepNecks_C12X θ :=
  G.deepNecks_of_neck_heq_C12X Nrecord hGδ hGm hGN hGscale
    (nonempty_incomingBackwardNeckDeep_record_of_selected_restrictions_C12X O hδ hδ1 hm rotation
      hmark side Nrecord e hN hB)

end Record

section Append

private local instance deepCutoffSlabSigmaCompact_C12X {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- Deep twin of the retained-append step of CT/PreparedHistoryCutoff: a deep backward neck on the
observed append becomes one on the retained-core append. -/
theorem nonempty_selected_restriction_retained_appendDeep_C12X
    {Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u}) {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s) (hOld : E.old = E.transition.trace.retainedCore)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {η δ θ : ℝ} {m k : ℕ}
    (O : NormalizedNeck
      (((H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit).toHistory).event
        (Fin.last H.eventCount)).terminal.metric η m)
    (hprec : η ≤ δ) (hδ : δ < 1) (horder : k ≤ m)
    (hback : ∀ O0 : NormalizedNeck E.terminal.metric η m, HEq O0 O → O0.scale = O.scale →
      ∃ N0 : NormalizedNeck ((H.toHistory.appendEvent E.incoming.lt
          (E.toRetainedCoreEvent hOld).toMetricCutCapEvent hinit).event
        (Fin.last H.eventCount)).terminal.metric δ k,
        HEq N0 ((O0.monoDelta hprec hδ).lowerOrder horder) ∧
        Nonempty (IncomingBackwardNeckDeep_C12X (H.toHistory.appendEvent E.incoming.lt
          (E.toRetainedCoreEvent hOld).toMetricCutCapEvent hinit)
          (Fin.last H.eventCount) N0 (Real.sqrt O0.scale⁻¹) θ)) :
    Nonempty (IncomingBackwardNeckDeep_C12X
      (H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit).toHistory
      (Fin.last H.eventCount) ((O.monoDelta hprec hδ).lowerOrder horder)
      (Real.sqrt O.scale⁻¹) θ) := by
  let Er := E.toRetainedCoreEvent hOld
  let K := H.appendEvent E.incoming.lt Er hinit
  let J := H.toHistory.appendEvent E.incoming.lt Er.toMetricCutCapEvent hinit
  have heq (j : Fin (H.eventCount + 1)) : HEq (K.toHistory.event j) (J.event j) := by
    change HEq (H.extendCoreEventFamily Er j).toMetricCutCapEvent
      (H.toHistory.extendEventFamily Er.toMetricCutCapEvent j)
    exact heq_of_eq (H.extendCoreEventFamily_toMetricCutCapEvent Er j)
  have hE : HEq (K.toHistory.event (Fin.last H.eventCount)) Er.toMetricCutCapEvent :=
    (heq _).trans
      (H.toHistory.appendEvent_event_last_heq E.incoming.lt Er.toMetricCutCapEvent hinit)
  obtain ⟨O0, hO0, hscale, htarget⟩ := exists_selected_neck_of_event_heq
    (H.appendEvent_stage_castSucc E.incoming.lt Er hinit (Fin.last H.eventCount))
    (H.appendEvent_stage_last E.incoming.lt Er hinit)
    (H.appendEvent_time_castSucc E.incoming.lt Er hinit (Fin.last H.eventCount))
    (H.appendEvent_time_last E.incoming.lt Er hinit) hE O hprec hδ horder
  obtain ⟨N0, hN0, ⟨B⟩⟩ := hback O0 hO0 hscale
  have hneck : HEq ((O.monoDelta hprec hδ).lowerOrder horder) N0 :=
    htarget.symm.trans hN0.symm
  have B' := IncomingBackwardNeckDeep_C12X.ofInitialEmbedding_C12X (H := J) (J := K.toHistory)
    le_rfl (fun _ => rfl) (fun _ => rfl) heq hneck B
  rw [hscale] at B'
  exact ⟨B'⟩

/-- **Deep twin of the uniform retained-append producer** (CT/PreparedHistoryCutoff `…:156`,
private).  Same hypotheses and quantifier order; for `1 < θ < 3/2` the restricted selected neck
carries a deep backward neck of depth factor `θ` on the retained-core append. -/
theorem exists_uniform_selected_neck_retained_append_backwardDeep_C12X
    (D r tol a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D)
    {θ : ℝ} (hθ : 1 < θ) (hθ' : θ < 3 / 2) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∀ a : ℝ, 0 < a →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    ∃ (ηstar : ℝ) (mstar : ℕ) (Λq : ℝ)
      (hηδ : ηstar ≤ δ) (hkm : k ≤ mstar),
      0 < ηstar ∧ 0 < Λq ∧
    ∀ q₀ : ℝ, 0 < q₀ →
    ∀ (H : RetainedCoreHistory.{u}) (s : ℝ) (Qstage : OrientedThreeStage.{u})
      (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qstage
        (H.time (Fin.last H.eventCount)) s)
      (hOld : E.old = E.transition.trace.retainedCore)
      (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)),
    a ≤ s →
    ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount,
      GeometricCutoffRecord H.toHistory j parameters),
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    (∀ j b, (records j).delta b ≤ δ₀) → parameters.modelAccuracy ≤ ε₀ →
    D + 1 ≤ parameters.modelRadius → ⌈tol⁻¹⌉₊ + 2 ≤ parameters.modelOrder →
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q₀ < E.incoming.flow.scalar t y →
      |derivWithin (fun v => E.incoming.flow.scalar v y) (Iic t) t| ≤
        Ctime * E.incoming.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
      (Ico (H.time j.castSucc) (H.time j.succ)) phi) →
    Perelman.PhiAlmostNonnegative E.incoming.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
    (∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
      ((records j).static b).neck.scale / 2 ≤ metricScalarAt ((records j).static b).witness.metric
        (((records j).static b).witness.cap z)) →
    ∀ (center : ∀ j : Fin H.eventCount, (H.toHistory.event j).RetainedBoundaryIndex →
        (H.toHistory.event j).incoming.terminalRegularOpen)
      (precision : ∀ j : Fin H.eventCount, (H.toHistory.event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ j : Fin H.eventCount, (H.toHistory.event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
        normalizedDatum (H.toHistory.event j).terminal.metric (center j b) (precision j b)
          (order j b))
      (w : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d j b)
          parameters.fixed.collarLength parameters.fixed.collar_pos parameters.modelRadius
          parameters.modelOrder parameters.modelAccuracy)
      (Jbig : ∀ j : Fin H.eventCount, (H.toHistory.event j).RetainedBoundaryIndex →
        standardCapWindow parameters.modelRadius → (H.stage j.succ).Carrier),
    (∀ j b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig j b)) →
    (∀ j b y (v z : TangentSpace ThreeModel y), (w j b).windowMetric.inner y v z =
      ((records j).static b).neck.scale * (H.initialMetric j.succ).inner (Jbig j b y)
        (mfderiv ThreeModel ThreeModel (Jbig j b) y v)
        (mfderiv ThreeModel ThreeModel (Jbig j b) y z)) →
    (∀ j b z, ∃ u : standardCapWindow parameters.modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig j b u = ((records j).static b).inclusion (((records j).static b).witness.cap z)) →
    ∀ (η : ℝ) (m : ℕ) (O : NormalizedNeck
      (((H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit).toHistory).event
        (Fin.last H.eventCount)).terminal.metric η m),
    ∀ (hη : η ≤ ηstar) (hm : mstar ≤ m), Λq * max q₀ 1 ≤ O.scale →
    let N := (O.monoDelta (hη.trans hηδ) hδ1).lowerOrder (hkm.trans hm)
    Nonempty (IncomingBackwardNeckDeep_C12X
      (H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit).toHistory
      (Fin.last H.eventCount) N (Real.sqrt N.scale⁻¹) θ) := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hthreshold⟩ :=
    exists_threshold_uniform_selected_neck_append_backwardDeep_C12X D r tol a₀ Ctime ha₀ htol
      htolsmall hr hfit hθ hθ'
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro δ hδ hδ1 k a ha phi hphi
  obtain ⟨ηstar, mstar, Λq, hηδ, hkm, hηstar, hΛq, hmain⟩ :=
    hthreshold hδ hδ1 k a ha phi hphi
  refine ⟨ηstar, mstar, Λq, hηδ, hkm, hηstar, hΛq, ?_⟩
  intro q0 hq0 H s Qstage E hOld hinit hsa parameters records hfixed hlower hdelta haccuracy
    hmargin horder hderiv hfinal hpinch hpinchFinal hcap center precision order d w Jbig hJbig
    hzero hmark η m O hη hm hscale
  apply nonempty_selected_restriction_retained_appendDeep_C12X H E hOld hinit O (hη.trans hηδ)
    hδ1 (hkm.trans hm)
  intro O0 hO0 hOscale
  have hlarge : Λq * max q0 1 ≤ O0.scale := by rw [hOscale]; exact hscale
  exact hmain q0 hq0 H.toHistory s Qstage (E.toRetainedCoreEvent hOld).toMetricCutCapEvent hinit
    hsa parameters records hfixed hlower hdelta haccuracy hmargin horder hderiv hfinal hpinch
    hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark η m O0 hη hm hlarge

end Append

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
