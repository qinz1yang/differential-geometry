import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.DiscardedSideDecompositionFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardComponentwise

set_option autoImplicit false
noncomputable section
open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

def DiscardedSideStandardRealization (D : ClosedOrientedManifold.{u} 3) : Prop :=
  ∃ P : RelativeDiscardPresentation D.Carrier,
    ∀ c : ConnectedComponents D.Carrier, ∃ i : Fin P.vertexCount,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (D.component c).toClosedOrientedManifold (P.vertex i).toClosedOrientedManifold)

theorem componentwiseStandardFactorOrProjectiveThreeSpaceSum_of_discardedSideStandardRealization
    {D : ClosedOrientedManifold.{u} 3} (h : DiscardedSideStandardRealization D) :
    D.componentwiseStandardFactorOrProjectiveThreeSpaceSum :=
  h.elim fun P hP =>
    componentwiseStandardFactorOrProjectiveThreeSpaceSum_of_discardPresentation P hP

theorem discardedComponent_isPoincareStandard_of_discardedSideStandardRealization
    {D : ClosedOrientedManifold.{u} 3} (h : DiscardedSideStandardRealization D)
    (c : ConnectedComponents D.Carrier) :
    isPoincareStandard (D.component c).Carrier := by
  obtain ⟨P, hP⟩ := h
  obtain ⟨i, he⟩ := hP c
  exact isPoincareStandard_of_standard_factor (D.component c)
    (isStandardFactor_component_of_discardPresentation P c i (Classical.choice he))

theorem MetricCutCapEvent.poincareStandardDiscarded_of_discardedSideStandardRealization
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (h : DiscardedSideStandardRealization E.discarded.toClosedOrientedManifold) :
    E.poincareStandardDiscarded :=
  fun c =>
    discardedComponent_isPoincareStandard_of_discardedSideStandardRealization h c

theorem exists_poincare_controlled_extinction_of_observedHistory_of_discardedSide
    (P : OrientedThreeStage.{u}) (g : P.Metric) (H : ObservedHistory.{u})
    (A : InitialIdentification P g H) [Nonempty P.Carrier]
    (hc : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (hout : (i : Fin H.eventCount) →
      letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : (H.event i).old => (H.event i).transition.trace.capping.coreInclusion x.1))
    (hside : ∀ i : Fin H.eventCount,
      DiscardedSideStandardRealization (H.event i).discarded.toClosedOrientedManifold)
    (hempty : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier) :
    Nonempty (PoincareControlledExtinction P.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_observedHistory P g H A hc hout
    (fun i =>
      MetricCutCapEvent.poincareStandardDiscarded_of_discardedSideStandardRealization
        (H.event i) (hside i))
    hempty

theorem discardedSideStandardRealization_uliftStandardFactorCarrier
    (G : SphericalSpaceFormGroup) :
    DiscardedSideStandardRealization (uliftStandardFactor.{u} G).toClosedOrientedManifold := by
  let D : ClosedOrientedManifold.{u} 3 := (uliftStandardFactor.{u} G).toClosedOrientedManifold
  let P : RelativeDiscardPresentation D.Carrier :=
    relativeDiscardPresentationOfVertex D.Carrier (uliftStandardFactor.{u} G)
      (isStandardFactor_uliftStandardFactor G)
  refine ⟨P, ?_⟩
  intro c
  exact ⟨⟨0, by simp [P, relativeDiscardPresentationOfVertex]⟩,
    ⟨D.componentOrientedDiffeomorph c⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
