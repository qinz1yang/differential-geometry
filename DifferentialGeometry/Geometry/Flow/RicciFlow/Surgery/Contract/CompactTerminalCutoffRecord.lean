import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.CompactTerminalHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffGeometryReduction

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)


def CutoffParameters.withCoreProtectedRadius (p : CutoffParameters) : CutoffParameters :=
  { p with protectedRadius := fun t => p.delta t * p.neckRadius t
           protectedRadius_pos := fun t ht => mul_pos (p.delta_pos t ht) (p.neckRadius_pos t ht) }

namespace GeometricCutoffRecord

private theorem nonempty_of_coreEvent_heq
    {P : OrientedThreeStage.{u}} {H : RetainedCoreHistory.{u}} {i : Fin H.eventCount}
    {Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s)
    (hP : H.stage i.castSucc = P) (hQ : H.stage i.succ = Q)
    (ha : H.time i.castSucc = a) (hs : H.time i.succ = s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hE : HEq (H.coreEvent i) (E.toRetainedCoreEvent hOld))
    (p : CutoffParameters) (hindex : IsEmpty E.transition.trace.tubes.Index)
    (hsingular : E.incoming.SingularEndpoint)
    (hprotected : ∀ x : E.incoming.terminalRegularOpen,
      metricScalarAt E.terminal.metric x ≤ ((p.protectedRadius s) ^ 2)⁻¹ →
      x.val ∈ interior (Subtype.val '' E.transition.trace.retainedCore))
    (hmeets : ∀ c : ConnectedComponents E.transition.trace.tubes.core,
      (∃ x : E.transition.trace.tubes.core,
        ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
      ∃ x : E.incoming.terminalRegularOpen,
        ∃ hx : x.val ∈ E.transition.trace.tubes.core,
          ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧
            metricScalarAt E.terminal.metric x ≤ ((p.protectedRadius s) ^ 2)⁻¹)
    (hcurvature : ∀ a : ℝ, 0 < a →
      (∀ x : (H.coreEvent i).incoming.terminalRegularOpen,
        InFixedHamiltonIveyRegion (H.coreEvent i).terminal.metric a x) →
      ∀ x : (H.stage i.succ).Carrier,
        InFixedHamiltonIveyRegion (H.coreEvent i).outputMetric a x)
    (hscalar : ∀ L : ℝ, L ≤ 0 →
      (∀ x : (H.coreEvent i).incoming.terminalRegularOpen,
        L ≤ metricScalarAt (H.coreEvent i).terminal.metric x) →
      ∀ x : (H.stage i.succ).Carrier,
        L ≤ metricScalarAt (H.coreEvent i).outputMetric x) :
    Nonempty (GeometricCutoffRecord H.toHistory i p) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  have heq := eq_of_heq hE
  have hi : IsEmpty (H.toHistory.event i).transition.trace.tubes.Index := by
    change IsEmpty (H.coreEvent i).transition.trace.tubes.Index
    rw [heq]
    exact hindex
  let _ := hi
  refine ⟨ofEmptyIndex ?_ ?_ ?_ ?_ ?_⟩
  · change (H.coreEvent i).incoming.SingularEndpoint
    rw [heq]
    exact hsingular
  · change ∀ x : (H.coreEvent i).incoming.terminalRegularOpen,
      metricScalarAt (H.coreEvent i).terminal.metric x ≤
        ((p.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
      x.val ∈ interior (Subtype.val '' (H.coreEvent i).transition.trace.retainedCore)
    rw [heq]
    exact hprotected
  · change ∀ c : ConnectedComponents (H.coreEvent i).transition.trace.tubes.core,
      (∃ x : (H.coreEvent i).transition.trace.tubes.core,
        ConnectedComponents.mk x = c ∧ x ∈ (H.coreEvent i).transition.trace.retainedCore) →
      ∃ x : (H.coreEvent i).incoming.terminalRegularOpen,
        ∃ hx : x.val ∈ (H.coreEvent i).transition.trace.tubes.core,
          ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧
            metricScalarAt (H.coreEvent i).terminal.metric x ≤
              ((p.protectedRadius (H.time i.succ)) ^ 2)⁻¹
    rw [heq]
    exact hmeets
  · exact hcurvature
  · exact hscalar

end GeometricCutoffRecord

private theorem terminal_scalar_fields_of_eq
    {P Q : OrientedThreeStage.{u}} {a s r : ℝ}
    (E : MetricCutCapEvent P Q a s) (G : P.IncomingSlab a s)
    (L : G.TerminalLimitMetric) (hG : E.incoming = G) (hL : HEq E.terminal L)
    (hprotected : ∀ x : G.terminalRegularOpen, metricScalarAt L.metric x ≤ (r ^ 2)⁻¹ →
      x.val ∈ interior (Subtype.val '' E.transition.trace.retainedCore))
    (hmeets : ∀ c : ConnectedComponents E.transition.trace.tubes.core,
      (∃ x : E.transition.trace.tubes.core,
        ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
      ∃ x : G.terminalRegularOpen, ∃ hx : x.val ∈ E.transition.trace.tubes.core,
        ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt L.metric x ≤ (r ^ 2)⁻¹) :
    (∀ x : E.incoming.terminalRegularOpen,
      metricScalarAt E.terminal.metric x ≤ (r ^ 2)⁻¹ →
      x.val ∈ interior (Subtype.val '' E.transition.trace.retainedCore)) ∧
    (∀ c : ConnectedComponents E.transition.trace.tubes.core,
      (∃ x : E.transition.trace.tubes.core,
        ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
      ∃ x : E.incoming.terminalRegularOpen, ∃ hx : x.val ∈ E.transition.trace.tubes.core,
        ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧
          metricScalarAt E.terminal.metric x ≤ (r ^ 2)⁻¹) := by
  cases hG
  cases eq_of_heq hL
  exact ⟨hprotected, hmeets⟩

namespace RetainedCoreHistory

theorem exists_extension_geometricCutoffRecord_of_compact_low_components
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (H : RetainedCoreHistory.{u}) (A : InitialIdentification P g H.toHistory)
    (htime : H.time (Fin.last H.eventCount) = H.horizon)
    (D : OneStepIncoming.{u})
    (hstage : H.stage (Fin.last H.eventCount) = D.stage)
    (hstart : H.time (Fin.last H.eventCount) = D.startTime)
    (hinit : HEq (D.slab.flow.base.metric D.startTime)
      (H.initialMetric (Fin.last H.eventCount)))
    (hcompact : ∀ x : D.slab.terminalRegularOpen,
      metricScalarAt D.terminal.metric x ≤
        ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime) ^ 2)⁻¹ →
      IsCompact (connectedComponent x)) :
    ∃ (Q : OrientedThreeStage.{u}) (E : MetricCutCapEvent D.stage Q D.startTime D.endTime)
      (hOld : E.old = E.transition.trace.retainedCore),
      E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
      IsEmpty E.transition.trace.tubes.Index ∧ E.transition.boundaryFrameReversing ∧
      ∃ (K : RetainedCoreHistory.{u}) (B : InitialIdentification P g K.toHistory)
        (i : Fin K.eventCount),
        A.IsPrefixOf B ∧ D.endTime < K.horizon ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D.endTime ∧
        K.stage (Fin.last K.eventCount) = Q ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D.stage ∧
        K.time i.castSucc = D.startTime ∧ K.stage i.succ = Q ∧
        K.time i.succ = D.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        HEq (K.initialMetric i.castSucc) (D.slab.flow.base.metric D.startTime) ∧
        HEq (K.initialMetric i.succ) E.outputMetric ∧
        Nonempty (GeometricCutoffRecord K.toHistory i D.parameters.withCoreProtectedRadius) ∧
        ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
              (K.coreEvent i).outputMetric univ ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F := by
  obtain ⟨Q, E, hOld, hG, hL, hindex, hbfr, hprotected, hmeets,
    K, B, i, hprefix, hhorizon, hcount, hlastTime, hlastStage, hlastMetric,
    hi, hsource, hsourceTime, htarget, htargetTime, hE, hmetricIn, hmetricOut,
    F, hF, hvol, hcurvature, hscalar⟩ :=
    H.exists_extension_of_compact_low_components A htime D hstage hstart hinit hcompact
  refine ⟨Q, E, hOld, hG, hL, hindex, hbfr, K, B, i, hprefix, hhorizon, hcount,
    hlastTime, hlastStage, hlastMetric, hi, hsource, hsourceTime, htarget, htargetTime,
    hE, hmetricIn, hmetricOut, ?_, F, hF, hvol⟩
  have hfields := terminal_scalar_fields_of_eq E D.slab D.terminal hG hL
    (by simpa only [hOld] using hprotected) hmeets
  apply GeometricCutoffRecord.nonempty_of_coreEvent_heq E hsource htarget
    hsourceTime htargetTime hOld hE D.parameters.withCoreProtectedRadius hindex
  · rw [hG]
    exact D.singular
  · exact hfields.1
  · exact hfields.2
  · exact hcurvature
  · exact hscalar

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
