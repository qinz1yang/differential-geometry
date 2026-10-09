import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.InitialCompactTerminalRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornMetricEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteProtectedCoreEvent

open private retained_image_eq_of_trace_heq retained_image_of_buffered_finite_caps from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteProtectedCoreEvent

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Contract

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

private local instance {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      D.slab.terminalRegularOpen.isOpen)

theorem exists_metricCutCapEvent_of_compact_low_components
    (D : OneStepIncoming.{u})
    (hcompact : ∀ x : D.slab.terminalRegularOpen,
      metricScalarAt D.terminal.metric x ≤
        ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime) ^ 2)⁻¹ →
      IsCompact (connectedComponent x)) :
    ∃ (Q : OrientedThreeStage.{u})
      (E : Topology.MetricCutCapEvent D.stage Q D.startTime D.endTime),
      E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
      IsEmpty E.transition.trace.tubes.Index ∧
      E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
      (∀ a : ℝ, 0 < a →
        (∀ x : E.incoming.terminalRegularOpen, InFixedHamiltonIveyRegion E.terminal.metric a x) →
        ∀ x : Q.Carrier, InFixedHamiltonIveyRegion E.outputMetric a x) ∧
      (∀ L : ℝ, L ≤ 0 →
        (∀ x : E.incoming.terminalRegularOpen, L ≤ metricScalarAt E.terminal.metric x) →
        ∀ x : Q.Carrier, L ≤ metricScalarAt E.outputMetric x) ∧
      (∀ x : D.slab.terminalRegularOpen,
        metricScalarAt D.terminal.metric x ≤
          ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime) ^ 2)⁻¹ →
        x.val ∈ interior ((Subtype.val : E.transition.trace.tubes.core → D.stage.Carrier)
          '' E.old)) ∧
      (∀ c : ConnectedComponents E.transition.trace.tubes.core,
        (∃ y : E.transition.trace.tubes.core,
          ConnectedComponents.mk y = c ∧ y ∈ E.transition.trace.retainedCore) →
        ∃ x : D.slab.terminalRegularOpen, ∃ hx : x.val ∈ E.transition.trace.tubes.core,
          ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧
            metricScalarAt D.terminal.metric x ≤
              ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime) ^ 2)⁻¹) ∧
      ∃ K : Set D.slab.terminalRegularOpen, IsCompact K ∧
        riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric K := by
  classical
  obtain ⟨c, hc, C, hC, A, hA, hsmall, hfamily⟩ :=
    exists_uniform_horn_cut_metricCutCapEvent_volume_debit.{u}
  obtain ⟨δ, hδ, hquarter, ε, hε, hmake⟩ := hfamily 1 zero_lt_one 0 1 zero_lt_one
  have ht : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  have hr : 0 < D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime :=
    mul_pos (D.parameters.delta_pos _ ht) (D.parameters.neckRadius_pos _ ht)
  obtain ⟨P, hP⟩ := exists_terminalCorePresentation_of_compact_low_components D hε
    (le_refl 1) hr rfl (fun _ x _ hx => hcompact x hx)
  obtain ⟨S, hS, hmake⟩ := hmake P le_rfl
  obtain ⟨F, K, hK, hfix, hF, hcore, e, t, a, ν, x₀, d, hcenter, ha, hside,
    hmap, hf, hd, hlocal, hRet, hfaces, oQ, oRet, oDisc, B, aCap, hboundary,
    E, hdisc, hcap, htrace, htubes, hincoming, hterminal, hold, hbfr, hpinch,
    hscalar, hvol, hrest⟩ := hmake (S + 1) (lt_add_one S) spherePoint
  let P' := P.reparametrizeHornsOfCompactSupport F hfix K hK hF
  have hemptyj : IsEmpty (Fin (Nat.card P'.HornCutIndex)) := by
    refine ⟨fun j => ?_⟩
    let k := e j
    exact (hP k.1.val).false k.2
  let _ := hemptyj
  have hempty : IsEmpty E.transition.trace.tubes.Index := by
    rw [htubes]
    exact hemptyj
  let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
  let R := scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
      (P'.coreRadius ^ 2)⁻¹
  let hnontrivial := D.slab.nonempty_cut_or_discardedCore_of_singularEndpoint
      D.singular f R hRet
  have htraceImage := retained_image_eq_of_trace_heq hdisc hcap htrace
  have himage := htraceImage.trans (retained_image_of_buffered_finite_caps
      StandardCap.transitionEnd_pos (fun j => (d j).precision_pos)
      (fun j => (d j).precision_lt_one) f hf hd R hnontrivial)
  refine ⟨_, E, hincoming, hterminal, hempty, hold, hbfr, hpinch, hscalar, ?_, ?_, ?_⟩
  · intro x hx
    rw [hold, himage]
    have hp := scalarSublevelComponents_protected D.slab.terminalRegularOpen D.terminal.metric
      x₀ (fun _ => 0 + 6) d (fun j => isEmptyElim j) (fun j => isEmptyElim j)
      hd (P'.coreRadius ^ 2)⁻¹ (fun j => isEmptyElim j)
    apply hp.1 x
    simpa only [P'.coreRadius_eq] using hx
  · have hcores : E.transition.trace.tubes.core = cutCore f := by
      rw [htubes]
      exact TubeSystem.ofBufferedCharts_core (fun j => (d j).precision_pos)
        (fun j => (d j).precision_lt_one) f hf hd
    have hmeets := retainedCore_component_meets_scalar_sublevel_of_image_subset
      D.slab.terminalRegularOpen D.terminal.metric f (P'.coreRadius ^ 2)⁻¹
      E.transition.trace.retainedCore hcores.symm.subset himage.subset
    simpa only [P'.coreRadius_eq] using hmeets
  · obtain ⟨Kvol, hKvol, hvol⟩ := hvol
    let _ := hempty
    exact ⟨Kvol, hKvol, by simpa using hvol⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Contract
