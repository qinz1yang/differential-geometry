import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCutoffRecord
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardNeckIsometries
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ProspectiveNeckSurvival
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordEventExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardNeckAppend
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardNeckRestriction

set_option autoImplicit false

noncomputable section
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}

private local instance : SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.event i).incoming.terminalRegularOpen.isOpen)

private theorem NormalizedNeck.lowerOrder_oriented_rotatedDatum
    {eps δ : ℝ} {k m : ℕ} (N : NormalizedNeck (H.event i).terminal.metric eps k)
    (hδ : eps ≤ δ) (hδ1 : δ < 1) (hm : m ≤ k)
    (rotation : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (hmark : Geometry.sphereDiffeo (n := 2) rotation spherePoint = N.sphereMark)
    (side : Bool) :
    ((((N.monoDelta hδ hδ1).lowerOrder hm).rotatedDatum rotation hmark side).oriented.toNormalizedNeck) =
      (((N.monoDelta hδ hδ1).rotatedDatum rotation hmark side).oriented.toNormalizedNeck.lowerOrder hm) := by
  rfl

private theorem nonempty_incomingBackwardNeck_record_of_selected_restrictions
    {δ r : ℝ} {m n : ℕ} {eps : Fin n → ℝ} {order : Fin n → ℕ}
    (O : ∀ j, NormalizedNeck (H.event i).terminal.metric (eps j) (order j))
    (hδ : ∀ j, eps j ≤ δ) (hδ1 : δ < 1) (hm : ∀ j, m ≤ order j)
    (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (hmark : ∀ j, Geometry.sphereDiffeo (n := 2) (rotation j) spherePoint = (O j).sphereMark)
    (side : Fin n → Bool)
    (Nrecord : (H.event i).transition.trace.tubes.Index → NormalizedNeck (H.event i).terminal.metric δ m)
    (e : Fin n ≃ (H.event i).transition.trace.tubes.Index)
    (hN : ∀ j, Nrecord (e j) =
      (((O j).monoDelta (hδ j) hδ1).rotatedDatum (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (hm j))
    (hB : ∀ j, Nonempty (IncomingBackwardNeck H i
      (((O j).monoDelta (hδ j) hδ1).lowerOrder (hm j)) r)) :
    ∀ j, Nonempty (IncomingBackwardNeck H i (Nrecord j) r) := by
  intro j
  obtain ⟨B⟩ := hB (e.symm j)
  have he := hN (e.symm j)
  rw [e.apply_symm_apply] at he
  rw [he,← NormalizedNeck.lowerOrder_oriented_rotatedDatum]
  exact ⟨IncomingBackwardNeck.oriented _
    (B.rotatedDatum (rotation (e.symm j)) (hmark (e.symm j)) (side (e.symm j)))⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)


private theorem exists_selected_neck_of_event_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : MetricCutCapEvent P Q a s} {E' : MetricCutCapEvent P' Q' a' s'}
    (hE : HEq E E') {η δ : ℝ} {m k : ℕ}
    (O : NormalizedNeck E.terminal.metric η m) (hprec : η ≤ δ) (hδ : δ < 1) (horder : k ≤ m) :
    ∃ O' : NormalizedNeck E'.terminal.metric η m,
      HEq O' O ∧ O'.scale = O.scale ∧
      HEq ((O'.monoDelta hprec hδ).lowerOrder horder) ((O.monoDelta hprec hδ).lowerOrder horder) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact ⟨O, HEq.rfl, rfl, HEq.rfl⟩

private def incomingBackwardNeck_retained_append_of_observed_append
    {P Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {i : Fin (H.eventCount + 1)} {δ r : ℝ} {k : ℕ}
    {N : NormalizedNeck ((H.toHistory.appendEvent hs E.toMetricCutCapEvent hinit).event i).terminal.metric δ k}
    {N' : NormalizedNeck ((H.appendEvent hs E hinit).toHistory.event i).terminal.metric δ k}
    (hneck : HEq N' N)
    (B : IncomingBackwardNeck (H.toHistory.appendEvent hs E.toMetricCutCapEvent hinit) i N r) :
    IncomingBackwardNeck (H.appendEvent hs E hinit).toHistory i N' r := by
  have hevent (j : Fin (H.eventCount + 1)) :
      HEq ((H.appendEvent hs E hinit).toHistory.event j)
        ((H.toHistory.appendEvent hs E.toMetricCutCapEvent hinit).event j) := by
    change HEq (H.extendCoreEventFamily E j).toMetricCutCapEvent (H.toHistory.extendEventFamily E.toMetricCutCapEvent j)
    exact heq_of_eq (H.extendCoreEventFamily_toMetricCutCapEvent E j)
  exact IncomingBackwardNeck.ofInitialEmbedding (H := H.toHistory.appendEvent hs E.toMetricCutCapEvent hinit)
    (J := (H.appendEvent hs E hinit).toHistory) le_rfl
    (fun _ => rfl) (fun _ => rfl) hevent hneck B

private theorem nonempty_selected_restriction_retained_append
    {P Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s) (hOld : E.old = E.transition.trace.retainedCore)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {η δ : ℝ} {m k : ℕ}
    (O : NormalizedNeck
      (((H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit).toHistory).event
        (Fin.last H.eventCount)).terminal.metric η m)
    (hprec : η ≤ δ) (hδ : δ < 1) (horder : k ≤ m)
    (hback : ∀ O0 : NormalizedNeck E.terminal.metric η m, HEq O0 O → O0.scale = O.scale →
      ∃ N0 : NormalizedNeck ((H.toHistory.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld).toMetricCutCapEvent hinit).event
        (Fin.last H.eventCount)).terminal.metric δ k,
        HEq N0 ((O0.monoDelta hprec hδ).lowerOrder horder) ∧
        Nonempty (IncomingBackwardNeck (H.toHistory.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld).toMetricCutCapEvent hinit)
          (Fin.last H.eventCount) N0 (Real.sqrt O0.scale⁻¹))) :
    Nonempty (IncomingBackwardNeck
      (H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit).toHistory
      (Fin.last H.eventCount) ((O.monoDelta hprec hδ).lowerOrder horder) (Real.sqrt O.scale⁻¹)) := by
  let Er := E.toRetainedCoreEvent hOld
  let K := H.appendEvent E.incoming.lt Er hinit
  let J := H.toHistory.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld).toMetricCutCapEvent hinit
  have heq (j : Fin (H.eventCount + 1)) : HEq (K.toHistory.event j) (J.event j) := by
    change HEq (H.extendCoreEventFamily Er j).toMetricCutCapEvent (H.toHistory.extendEventFamily Er.toMetricCutCapEvent j)
    exact heq_of_eq (H.extendCoreEventFamily_toMetricCutCapEvent Er j)
  have hE : HEq (K.toHistory.event (Fin.last H.eventCount)) Er.toMetricCutCapEvent :=
    (heq _).trans (H.toHistory.appendEvent_event_last_heq E.incoming.lt Er.toMetricCutCapEvent hinit)
  obtain ⟨O0, hO0, hscale, htarget⟩ := exists_selected_neck_of_event_heq
    (H.appendEvent_stage_castSucc E.incoming.lt Er hinit (Fin.last H.eventCount))
    (H.appendEvent_stage_last E.incoming.lt Er hinit)
    (H.appendEvent_time_castSucc E.incoming.lt Er hinit (Fin.last H.eventCount))
    (H.appendEvent_time_last E.incoming.lt Er hinit) hE O hprec hδ horder
  obtain ⟨N0, hN0, ⟨B⟩⟩ := hback O0 hO0 hscale
  have hneck : HEq ((O.monoDelta hprec hδ).lowerOrder horder) N0 := htarget.symm.trans hN0.symm
  have B' := incomingBackwardNeck_retained_append_of_observed_append H E.incoming.lt Er hinit hneck B
  rw [hscale] at B'
  exact ⟨B'⟩

private theorem exists_uniform_selected_neck_retained_append_backward
    (D r tol a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < D) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ {δ : ℝ}, 0 < δ → ∀ hδ1 : δ < 1, ∀ k : ℕ,
    ∀ (a q₀ : ℝ), 0 < a → 0 < q₀ →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    ∃ (ηstar : ℝ) (mstar : ℕ) (Qmin : ℝ)
      (hηδ : ηstar ≤ δ) (hkm : k ≤ mstar),
      0 < ηstar ∧ 0 < Qmin ∧
    ∀ {Pbase : OrientedThreeStage.{u}} (H : RetainedCoreHistory Pbase) (s : ℝ) (Qstage : OrientedThreeStage.{u})
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
      |derivWithin (fun v => E.incoming.flow.scalar v y) (Iic t) t| ≤ Ctime * E.incoming.flow.scalar t y ^ 2) →
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
        normalizedDatum (H.toHistory.event j).terminal.metric (center j b) (precision j b) (order j b))
      (w : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d j b)
          parameters.fixed.collarLength parameters.fixed.collar_pos parameters.modelRadius
          parameters.modelOrder parameters.modelAccuracy)
      (Jbig : ∀ j : Fin H.eventCount, (H.toHistory.event j).RetainedBoundaryIndex →
        standardCapWindow parameters.modelRadius → (H.stage j.succ).Carrier),
    (∀ j b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig j b)) →
    (∀ j b y (v z : TangentSpace ThreeModel y), (w j b).windowMetric.inner y v z =
      ((records j).static b).neck.scale * (H.initialMetric j.succ).inner (Jbig j b y)
        (mfderiv ThreeModel ThreeModel (Jbig j b) y v) (mfderiv ThreeModel ThreeModel (Jbig j b) y z)) →
    (∀ j b z, ∃ u : standardCapWindow parameters.modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig j b u = ((records j).static b).inclusion (((records j).static b).witness.cap z)) →
    ∀ (η : ℝ) (m : ℕ) (O : NormalizedNeck (((H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit).toHistory).event
      (Fin.last H.eventCount)).terminal.metric η m),
    ∀ (hη : η ≤ ηstar) (hm : mstar ≤ m), Qmin ≤ O.scale →
    let N := (O.monoDelta (hη.trans hηδ) hδ1).lowerOrder (hkm.trans hm)
    Nonempty (IncomingBackwardNeck
      (H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit).toHistory
      (Fin.last H.eventCount) N (Real.sqrt N.scale⁻¹)) := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hthreshold⟩ :=
    exists_uniform_selected_neck_append_backward D r tol a₀ Ctime ha₀ htol htolsmall hr hfit
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro δ hδ hδ1 k a q0 ha hq0 phi hphi
  obtain ⟨ηstar, mstar, Qmin, hηδ, hkm, hηstar, hQmin, hmain⟩ := hthreshold hδ hδ1 k a q0 ha hq0 phi hphi
  refine ⟨ηstar, mstar, Qmin, hηδ, hkm, hηstar, hQmin, ?_⟩
  intro Pbase H s Qstage E hOld hinit hsa parameters records hfixed hlower hdelta haccuracy hmargin horder
    hderiv hfinal hpinch hpinchFinal hcap center precision order d w Jbig hJbig hzero hmark
    η m O hη hm hscale
  apply nonempty_selected_restriction_retained_append H E hOld hinit O (hη.trans hηδ) hδ1 (hkm.trans hm)
  intro O0 hO0 hOscale
  have hlarge : Qmin ≤ O0.scale := by rw [hOscale]; exact hscale
  exact hmain H.toHistory s Qstage (E.toRetainedCoreEvent hOld).toMetricCutCapEvent hinit hsa
    parameters records hfixed hlower hdelta haccuracy hmargin horder hderiv hfinal hpinch hpinchFinal
    hcap center precision order d w Jbig hJbig hzero hmark η m O0 hη hm hlarge


theorem exists_horn_cutoff_record_at_scale_of_prepared_history
    (Dtrace r tol a₀ : ℝ) (Ctime : ℝ≥0) (ha₀ : 0 < a₀)
    (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < Dtrace) :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∃ εold δold : ℝ, 0 < εold ∧ 0 < δold ∧
    ∀ Dcap : ℝ, 0 < Dcap → StandardCap.transitionEnd < Dcap + 1 → ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
    ∀ ηrecord : ℝ, 0 < ηrecord →
    ∀ (a q0 : ℝ), 0 < a → 0 < q0 →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    ∃ δ ε₀ Qmin : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧ 0 < ε₀ ∧ 0 < Qmin ∧
    ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
      (H : RetainedCoreHistory P₀) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
    ∀ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint)
      (stepParameters : CutoffParameters)
      (_ : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount)),
    a ≤ s →
    let D : OneStepIncoming := {
      stage := H.stage (Fin.last H.eventCount)
      startTime := H.time (Fin.last H.eventCount)
      endTime := s
      startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
      startTime_lt_endTime := G.lt
      slab := G
      terminal := L
      singular := hsing
      parameters := stepParameters }
    ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount,
      GeometricCutoffRecord H.toHistory j parameters),
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    (∀ j b, (records j).delta b ≤ δold) → parameters.modelAccuracy ≤ εold →
    Dtrace + 1 ≤ parameters.modelRadius → ⌈tol⁻¹⌉₊ + 2 ≤ parameters.modelOrder →
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q0 < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q0 < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
      (Ico (H.time j.castSucc) (H.time j.succ)) phi) →
    Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
    (∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
      ((records j).static b).neck.scale / 2 ≤ metricScalarAt ((records j).static b).witness.metric
        (((records j).static b).witness.cap z)) →
    ∀ (center : ∀ j : Fin H.eventCount, (H.toHistory.event j).RetainedBoundaryIndex →
        (H.toHistory.event j).incoming.terminalRegularOpen)
      (precision : ∀ j : Fin H.eventCount, (H.toHistory.event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ j : Fin H.eventCount, (H.toHistory.event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
        normalizedDatum (H.toHistory.event j).terminal.metric (center j b) (precision j b) (order j b))
      (w : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d j b)
          parameters.fixed.collarLength parameters.fixed.collar_pos parameters.modelRadius
          parameters.modelOrder parameters.modelAccuracy)
      (Jbig : ∀ j : Fin H.eventCount, (H.toHistory.event j).RetainedBoundaryIndex →
        standardCapWindow parameters.modelRadius → (H.stage j.succ).Carrier),
    (∀ j b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig j b)) →
    (∀ j b y (v z : TangentSpace ThreeModel y), (w j b).windowMetric.inner y v z =
      ((records j).static b).neck.scale * (H.initialMetric j.succ).inner (Jbig j b y)
        (mfderiv ThreeModel ThreeModel (Jbig j b) y v) (mfderiv ThreeModel ThreeModel (Jbig j b) y z)) →
    (∀ j b z, ∃ u : standardCapWindow parameters.modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig j b u = ((records j).static b).inclusion (((records j).static b).witness.cap z)) →
      ∀ {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ ε₀ →
      ∀ Q : ℝ, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q →
      (((δ ^ 2 * D.parameters.neckRadius D.endTime) ^ 2)⁻¹) < Q → Qmin ≤ Q →
      ∃ (Qout : OrientedThreeStage.{u}) (E : MetricCutCapEvent D.stage Qout D.startTime D.endTime)
        (hOld : E.old = E.transition.trace.retainedCore)
        (K : RetainedCoreHistory P₀) (initialK : InitialIdentification P₀ g₀ K.toHistory)
        (i : Fin K.eventCount) (parameters : CutoffParameters)
        (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
        (NOriginal : ∀ j, NormalizedNeck (K.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j))
        (hδOriginal : ∀ j, δOriginal j ≤ δ)
        (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NOriginal j).sphereMark)
        (side : Fin n → Bool)
        (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
        (hδ1 : δ < 1)
        (Nrecord : (K.toHistory.event i).transition.trace.tubes.Index →
          NormalizedNeck (K.toHistory.event i).terminal.metric δ
            (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)))
        (eOriginal : Fin n ≃ (K.toHistory.event i).transition.trace.tubes.Index),
        0 < Q ∧ E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.transition.boundaryFrameReversing ∧
        initial.IsPrefixOf initialK ∧ K.horizon = D.endTime ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D.stage ∧ K.time i.castSucc = D.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        (∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial) ∧
        parameters.delta = (fun _ => δ) ∧ parameters.protectedRadius = (fun _ => P.coreRadius) ∧
        parameters.neckRadius = (fun _ => D.parameters.neckRadius D.endTime) ∧
        parameters.fixed = fixed ∧ parameters.recenterConstant = recenterConstant ∧
        parameters.modelOrder = m ∧ parameters.modelRadius = Dcap ∧ parameters.modelAccuracy = accuracy ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius D.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ x : E.transition.trace.tubes.core,
            ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤
                ((parameters.protectedRadius D.endTime) ^ 2)⁻¹) ∧
        (∀ j, (NOriginal j).scale = Q) ∧
        (∀ j, δOriginal j ≤ 2 * ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
        (∀ j, Nrecord (eOriginal j) =
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
            (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (horder j)) ∧
        (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
          (K.toHistory.event i).transition.trace.tubes.tube j z =
            ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
        (∃ Record : GeometricCutoffRecord K.toHistory i parameters,
          Record.delta = (fun _ => δ) ∧
          Record.order = (fun _ => max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)) ∧
          HEq Record.neck Nrecord ∧ (∀ j, (Record.neck j).scale = Q) ∧
          (∀ b, (Record.static b).hasCanonicalWindow)) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) := by
  obtain ⟨fixed, c, hc, hfactory⟩ :=
    exists_uniform_horn_cutoff_history_extension_at_scale_with_original_neck_bounds_and_canonical_windows.{u}
  obtain ⟨εold, δold, hεold, hδold, hthreshold⟩ :=
    exists_uniform_selected_neck_retained_append_backward Dtrace r tol a₀ Ctime ha₀ htol htolsmall hr hfit
  refine ⟨fixed, c, hc, εold, δold, hεold, hδold, ?_⟩
  intro Dcap hDcap hDfit m accuracy haccuracy ηrecord hηrecord a q0 ha hq0 phi hphi
  obtain ⟨δ, εfactory, hδ, hδ1, hδη, hεfactory, hmake⟩ := hfactory Dcap hDcap hDfit m accuracy haccuracy ηrecord hηrecord
  let k := max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)
  obtain ⟨ηstar, mstar, Qmin, hηδ, hkm, hηstar, hQmin, hback⟩ :=
    hthreshold hδ hδ1 k a q0 ha hq0 phi hphi
  let ε₀ := min εfactory (min (ηstar / 2) (((mstar : ℝ) + 1)⁻¹))
  have hε₀ : 0 < ε₀ := lt_min hεfactory (lt_min (half_pos hηstar) (by positivity))
  refine ⟨δ, ε₀, Qmin, hδ, hδ1, hδη, hε₀, hQmin, ?_⟩
  intro P₀ g₀ H initial htime s G L hsing stepParameters hinit hsa D
    pold records hfixed hlower hdelta hacc hmargin hm hderiv hfinal hpinch hpinchFinal hcap
    center precision order d w Jbig hJbig hzero hmark ε Λ P hε Q hQscale hQnominal hQlarge
  have hεfactory' : ε ≤ εfactory := hε.trans (min_le_left _ _)
  have hεη : 2 * ε ≤ ηstar := by
    have hh := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hεm : (mstar : ℝ) + 1 ≤ ε⁻¹ := by
    have hh : ε ≤ ((mstar : ℝ) + 1)⁻¹ := hε.trans ((min_le_right _ _).trans (min_le_right _ _))
    simpa only [inv_inv] using inv_anti₀ P.epsilon_pos hh
  have hmFloor : mstar ≤ ⌊ε⁻¹⌋₊ + 1 := (Nat.le_floor (by linarith : (mstar : ℝ) ≤ ε⁻¹)).trans (Nat.le_succ _)
  obtain ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmarkN, side, horderN, hδ1', Nrecord, eOriginal,
    hQ, hG, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC, hpM, hpD, hpAcc,
    hprotected, hretained, hscale, hsource, hNrecord, hTube, hrecord, hvol, hcapNew⟩ :=
    hmake H initial htime D rfl rfl (heq_of_eq hinit) P hεfactory' Q hQscale hQnominal
  have hB : ∀ j, Nonempty (IncomingBackwardNeck K.toHistory i
      (((NOriginal j).monoDelta (hδOriginal j) hδ1').lowerOrder (horderN j)) (Real.sqrt Q⁻¹)) := by
    obtain ⟨Eappend, hOldAppend, hInitial, hEappend, hK⟩ := happend
    have hEqE : Eappend = E := eq_of_heq hEappend
    subst Eappend
    subst K
    have hlasti : i = Fin.last H.eventCount := Fin.ext hi
    subst i
    intro j
    have hηj : δOriginal j ≤ ηstar := (hsource j).1.trans hεη
    have hmj : mstar ≤ kOriginal j := hmFloor.trans (hsource j).2
    have hQj : Qmin ≤ (NOriginal j).scale := hQlarge.trans_eq (hscale j).symm
    have hfinalE : ∀ y, ∀ t ∈ Set.Ioo (H.time (Fin.last H.eventCount)) s,
        q0 < E.incoming.flow.scalar t y →
        |derivWithin (fun v => E.incoming.flow.scalar v y) (Set.Iic t) t| ≤
          Ctime * E.incoming.flow.scalar t y ^ 2 := by
      have hGE : E.incoming = G := hG
      rw [hGE]
      exact hfinal
    have hpinchE : Perelman.PhiAlmostNonnegative E.incoming.flow
        (Set.Ico (H.time (Fin.last H.eventCount)) s) phi := by
      have hGE : E.incoming = G := hG
      rw [hGE]
      exact hpinchFinal
    have hb := hback H s Qout E hOldAppend hInitial hsa pold records hfixed hlower hdelta hacc hmargin hm
      hderiv hfinalE hpinch hpinchE hcap center precision order d w Jbig hJbig hzero hmark
      (δOriginal j) (kOriginal j) (NOriginal j) hηj hmj hQj
    have hsc : (((NOriginal j).monoDelta (hδOriginal j) hδ1').lowerOrder (horderN j)).scale = Q := hscale j
    simpa only [hsc] using hb
  have hBrecord := nonempty_incomingBackwardNeck_record_of_selected_restrictions
    NOriginal hδOriginal hδ1' horderN rotation hmarkN side Nrecord eOriginal hNrecord hB
  obtain ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows⟩ := hrecord hBrecord
  exact ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmarkN, side, horderN, hδ1', Nrecord, eOriginal,
    hQ, hG, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC, hpM, hpD, hpAcc,
    hprotected, hretained, hscale, hsource, hNrecord, hTube,
    ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows⟩, hvol, hcapNew⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
