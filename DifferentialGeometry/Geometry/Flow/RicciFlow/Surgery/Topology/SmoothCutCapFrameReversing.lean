import DifferentialGeometry.Topology.ThreeManifold.Surgery.Capping.BoundaryOrientation
import DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.SmoothTransition
import DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.Orientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u



theorem MetricCutCapEvent.hasCutCapCompletion_of_attaching_eq_refl
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (h : ∀ b, E.transition.attaching b = Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hout : (SphericalTubeSystem.ofSmoothCutCapTransition E.transition)
      |>.outwardNormalFirstIsStandardSphereOrientation) :
    E.hasCutCapCompletion :=
  E.transition.nonempty_smoothCutCapCompletion_of_attaching_eq_refl h hout

theorem RetainedCoreEvent.toMetricCutCapEvent_hasCutCapCompletion_of_attaching_eq_refl
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : RetainedCoreEvent P Q a s)
    (h : ∀ b, E.transition.attaching b = Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hout : (SphericalTubeSystem.ofSmoothCutCapTransition E.transition)
      |>.outwardNormalFirstIsStandardSphereOrientation) :
    E.toMetricCutCapEvent.hasCutCapCompletion :=
  E.transition.nonempty_smoothCutCapCompletion_of_attaching_eq_refl h hout

theorem RetainedCoreHistory.boundaryFrameReversing_of_attaching_eq_refl
    (H : RetainedCoreHistory.{u})
    (h : ∀ (i : Fin H.eventCount) (b : (H.coreEvent i).transition.trace.tubes.Boundary),
      (H.coreEvent i).transition.attaching b = Diffeomorph.refl (𝓡 2)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hout : ∀ i : Fin H.eventCount,
      (SphericalTubeSystem.ofSmoothCutCapTransition (H.coreEvent i).transition)
        |>.outwardNormalFirstIsStandardSphereOrientation) :
    ∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing :=
  fun i => (H.coreEvent i).transition.boundaryFrameReversing_of_attaching_eq_refl (h i) (hout i)


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
