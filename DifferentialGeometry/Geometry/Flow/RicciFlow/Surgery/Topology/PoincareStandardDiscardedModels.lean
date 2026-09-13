import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PoincareStandardDiscarded
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscardedModels

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace FiniteCutCapTrace

theorem poincareControlled_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
    (T : FiniteCutCapTrace.{u})
    (h : ∀ i : Fin T.eventCount,
      (T.transition i).discarded.componentwiseStandardFactorOrProjectiveThreeSpaceSum) :
    T.poincareControlled :=
  fun i =>
    (T.transition i).poincareControlled_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum (h i)

end FiniteCutCapTrace

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

theorem poincareStandardDiscarded_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
    (E : MetricCutCapEvent P Q a s)
    (h : E.discarded.toClosedOrientedManifold.componentwiseStandardFactorOrProjectiveThreeSpaceSum) :
    E.poincareStandardDiscarded :=
  fun q =>
    DifferentialGeometry.Topology.componentwise_isPoincareStandard_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
      E.discarded.toClosedOrientedManifold h q

end MetricCutCapEvent

namespace RetainedCoreObservationTower

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem hasPoincareStandardDiscarded_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
    (T : RetainedCoreObservationTower P g)
    (h : ∀ (n : ℕ) (j : Fin (T.history n).eventCount),
      ((T.history n).coreEvent j).toMetricCutCapEvent.discarded.toClosedOrientedManifold
        |>.componentwiseStandardFactorOrProjectiveThreeSpaceSum) :
    T.hasPoincareStandardDiscarded :=
  fun n j =>
    MetricCutCapEvent.poincareStandardDiscarded_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
      ((T.history n).coreEvent j).toMetricCutCapEvent (h n j)

end RetainedCoreObservationTower

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace FiniteSurgeryHistory

theorem poincareControlled_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
    (H : FiniteSurgeryHistory.{u})
    (h : ∀ i : Fin H.eventCount,
      (H.event i).transition.discarded.componentwiseStandardFactorOrProjectiveThreeSpaceSum) :
    H.poincareControlled :=
  fun i C =>
    DifferentialGeometry.Topology.componentwise_isPoincareStandard_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
      (H.event i).transition.discarded (h i) C

end FiniteSurgeryHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery
