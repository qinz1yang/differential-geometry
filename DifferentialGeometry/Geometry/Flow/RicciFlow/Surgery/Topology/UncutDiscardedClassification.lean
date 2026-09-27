import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalComponentClassification
import DifferentialGeometry.Topology.ThreeManifold.CutCapUncutCappingRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticNeckChildCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

theorem MetricCutCapEvent.exists_isPoincareStandard_discardedComponent_threshold_of_uncut
    (E : MetricCutCapEvent P Q a s) :
    ∃ L : ℝ, 0 < L ∧ ∀ (hc : SmoothCutCapCompletion E.transition),
      let X := SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc
      ∀ (C : ConnectedComponents P.Carrier), X.cutIndices C = ∅ →
        ∀ (x : E.transition.trace.tubes.core), x ∈ X.coreComponentSet C →
          ∀ d : E.discarded.Carrier,
            E.transition.trace.presentation (E.transition.trace.capping.coreInclusion x) = Sum.inr d →
            (∀ y : E.incoming.terminalRegularOpen, ConnectedComponents.mk y.val = C →
              metricScalarAt E.terminal.metric y ≤ L →
              y.val ∈ Subtype.val '' E.transition.trace.retainedCore) →
            DifferentialGeometry.Topology.isPoincareStandard
              (E.discarded.toClosedOrientedManifold.component (ConnectedComponents.mk d)).Carrier := by
  obtain ⟨L, hL, hclass⟩ := E.terminal.exists_component_poincareStandard_threshold E.incoming
  refine ⟨L, hL, ?_⟩
  intro hc X C hC x hx d hxd hretain
  have hxd' : X.presentation (X.capping.coreInclusion x) = Sum.inr d := by
    exact (congrArg E.transition.presentation
      (SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion E.transition hc x)).trans
        ((congrFun E.transition.presentation_eq _).trans hxd)
  have hxnot : x ∉ E.transition.trace.retainedCore := by
    rintro ⟨q, hq⟩
    exact Sum.inr_ne_inl (hxd.symm.trans hq)
  have hstd := hclass C (by
    intro y hy
    have hyC : y.val ∈ P.toClosedOrientedManifold.componentSet C :=
      (DifferentialGeometry.Topology.ClosedOrientedManifold.mem_componentSet _ _ _).mpr hy
    have hycore : y.val ∈ E.transition.trace.tubes.core :=
      X.componentSet_subset_core_of_cutIndices_eq_empty C hC hyC
    let z : E.transition.trace.tubes.core := ⟨y.val, hycore⟩
    have hz : z ∈ X.coreComponentSet C := hyC
    have hn : z ∉ E.transition.trace.retainedCore :=
      E.transition.trace.connectedComponent_subset_compl_retainedCore x hxnot
        ((X.isPreconnected_coreComponentSet C hC).subset_connectedComponent hx hz)
    apply lt_of_not_ge
    intro hlow
    obtain ⟨w, hw, hwy⟩ := hretain y hy hlow
    exact hn ((Subtype.ext hwy : w = z) ▸ hw))
  exact X.isPoincareStandard_discardedComponent_of_cutIndices_eq_empty C hC x hx d hxd' hstd

theorem MetricCutCapEvent.exists_poincareStandardDiscarded_threshold_of_isEmpty_index
    (E : MetricCutCapEvent P Q a s) [IsEmpty E.transition.trace.tubes.Index] :
    ∃ L : ℝ, 0 < L ∧
      ((∀ x : E.incoming.terminalRegularOpen, metricScalarAt E.terminal.metric x ≤ L →
        x.val ∈ Subtype.val '' E.transition.trace.retainedCore) →
      E.poincareStandardDiscarded) := by
  obtain ⟨L, hL, hclass⟩ := E.exists_isPoincareStandard_discardedComponent_threshold_of_uncut
  refine ⟨L, hL, ?_⟩
  intro hretain c
  have hboundary : E.transition.boundaryFrameReversing := by
    intro b
    exact False.elim ((inferInstance : IsEmpty E.transition.trace.tubes.Index).false b.1)
  let hc := E.transition.toSmoothCutCapCompletion hboundary
  let X := SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc
  let _ : IsEmpty X.tubes.Index := inferInstanceAs (IsEmpty E.transition.trace.tubes.Index)
  obtain ⟨x, d, hd, hxd, hx, hcut⟩ :=
    X.exists_core_presentation_eq_inr_component_of_isEmpty_index c
  have hxd' : E.transition.trace.presentation (E.transition.trace.capping.coreInclusion x) =
      Sum.inr d := by
    exact (congrFun E.transition.presentation_eq _).symm.trans
      ((congrArg E.transition.presentation
        (SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion E.transition hc x)).symm.trans hxd)
  have hout := hclass hc (ConnectedComponents.mk x.val) hcut x hx d hxd' (fun y _ => hretain y)
  change ConnectedComponents.mk (α := E.discarded.Carrier) d = c at hd
  exact (congrArg (fun K : ConnectedComponents E.discarded.Carrier =>
    DifferentialGeometry.Topology.isPoincareStandard
      (E.discarded.toClosedOrientedManifold.component K).Carrier) hd).mp hout

theorem GeometricCutoffRecord.exists_isPoincareStandard_discardedComponent_threshold_of_uncut
    {H : ObservedHistory.{u}} (i : Fin H.eventCount) :
    ∃ L : ℝ, 0 < L ∧ ∀ (parameters : CutoffParameters),
      GeometricCutoffRecord H i parameters →
      ∀ (hc : SmoothCutCapCompletion (H.event i).transition),
        let X := SphericalCutCapTransition.ofSmoothCutCapTransition (H.event i).transition hc
        ∀ (C : ConnectedComponents (H.stage i.castSucc).Carrier), X.cutIndices C = ∅ →
          ∀ (x : (H.event i).transition.trace.tubes.core), x ∈ X.coreComponentSet C →
            ∀ d : (H.event i).discarded.Carrier,
              (H.event i).transition.trace.presentation
                ((H.event i).transition.trace.capping.coreInclusion x) = Sum.inr d →
              L ≤ ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
              DifferentialGeometry.Topology.isPoincareStandard
                ((H.event i).discarded.toClosedOrientedManifold.component
                  (ConnectedComponents.mk d)).Carrier := by
  obtain ⟨L, hL, hstd⟩ :=
    (H.event i).exists_isPoincareStandard_discardedComponent_threshold_of_uncut
  refine ⟨L, hL, ?_⟩
  intro parameters R hc X C hC x hx d hd hscale
  apply hstd hc C hC x hx d hd
  intro y _ hy
  exact interior_subset (R.protected_interior y (hy.trans hscale))

theorem GeometricCutoffRecord.exists_poincareStandardDiscarded_threshold_of_isEmpty_index
    {H : ObservedHistory.{u}} (i : Fin H.eventCount)
    [IsEmpty (H.event i).transition.trace.tubes.Index] :
    ∃ L : ℝ, 0 < L ∧ ∀ parameters : CutoffParameters,
      GeometricCutoffRecord H i parameters →
      L ≤ ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
      (H.event i).poincareStandardDiscarded := by
  obtain ⟨L, hL, hstd⟩ :=
    (H.event i).exists_poincareStandardDiscarded_threshold_of_isEmpty_index
  refine ⟨L, hL, ?_⟩
  intro parameters R hscale
  apply hstd
  intro x hx
  exact interior_subset (R.protected_interior x (hx.trans hscale))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
