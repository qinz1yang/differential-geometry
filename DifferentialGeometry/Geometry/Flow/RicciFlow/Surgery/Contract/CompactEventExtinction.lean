import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreMetricEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffGeometryReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapWithoutCuts
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PositiveComponentSpaceForm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctionCutCapEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionAssembly

noncomputable section
open Set
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

theorem MetricCutCapEvent.isEmpty_output_of_preconnected_of_isEmpty_index
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) [PreconnectedSpace P.Carrier]
    [hIndex : IsEmpty E.transition.trace.tubes.Index] : IsEmpty Q.Carrier := by
  have hboundary : E.transition.boundaryFrameReversing := by
    intro b
    exact (hIndex.false b.1).elim
  let X := SphericalCutCapTransition.ofSmoothCutCapTransition E.transition
    (E.transition.toSmoothCutCapCompletion hboundary)
  let hX : IsEmpty X.tubes.Index := inferInstanceAs (IsEmpty E.transition.trace.tubes.Index)
  exact @DifferentialGeometry.Topology.SphericalCutCapTransition.isEmpty_output_of_preconnected_of_isEmpty_index
    _ _ X hX (inferInstanceAs (PreconnectedSpace P.Carrier))

theorem MetricCutCapEvent.exists_poincare_controlled_extinction_of_isEmpty_index_of_positive_or_round_components
    {P Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : MetricCutCapEvent P Q 0 s) [PreconnectedSpace P.Carrier]
    [hIndex : IsEmpty E.transition.trace.tubes.Index]
    (hmodels : ∀ C : ConnectedComponents E.discarded.Carrier,
      Nonempty (PositiveComponent
        (M := (E.discarded.toClosedOrientedManifold.component C).Carrier) Set.univ) ∨
      ∃ (D' : RealTimeInterval)
        (S : SolutionOn (I := ThreeModel)
          (M := (E.discarded.toClosedOrientedManifold.component C).Carrier) D')
        (ε : ℝ) (x : (E.discarded.toClosedOrientedManifold.component C).Carrier) (t : ℝ),
        Nonempty (RoundComponent S ε x t Set.univ)) :
    Nonempty (PoincareControlledExtinction P.toClosedOrientedManifold
      (E.incoming.flow.base.metric 0)) := by
  have hboundary : E.transition.boundaryFrameReversing := by
    intro b
    exact (hIndex.false b.1).elim
  have hOld := E.old_eq_retained_of_isEmpty_index
  have hcontrol := E.poincareStandardDiscarded_of_componentwisePositiveOrRoundComponent hmodels
  have hQ := E.isEmpty_output_of_preconnected_of_isEmpty_index
  obtain ⟨H, A, _, hbfr, hctrl, hempty⟩ :=
    (E.toRetainedCoreEvent hOld).exists_extinctHistory E.incoming.lt hQ rfl hboundary hcontrol
  let _ : Nonempty P.Carrier := E.transition.source_nonempty
  exact exists_poincare_controlled_extinction_of_observedHistory P
    (E.incoming.flow.base.metric 0) H.toHistory A
    (fun i => ((H.coreEvent i).toMetricCutCapEvent_hasCutCapCompletion (hbfr i)).some)
    (fun i => (H.coreEvent i).toMetricCutCapEvent_coreInclusionIsSmoothEmbedding)
    hctrl hempty

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
