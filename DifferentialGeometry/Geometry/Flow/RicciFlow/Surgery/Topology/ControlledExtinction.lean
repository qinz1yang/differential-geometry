import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PoincareControl
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

noncomputable section

open Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

structure PoincareControlledExtinction (M : ClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) where
  history : FiniteSurgeryHistory.{u}
  time : ℝ
  time_pos : 0 < time
  initial : history.InitialIdentification M g
  controlled : history.poincareControlled
  extinct : history.extinctAt time

namespace PoincareControlledExtinction

variable {M : ClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
  (W : PoincareControlledExtinction M g)

theorem time_eq : W.time = W.history.terminalTime := W.extinct.1

theorem terminal_isEmpty : IsEmpty (W.history.stage (Fin.last W.history.eventCount)).Carrier :=
  W.extinct.2

def initialCutCapIdentification : W.history.cutCapTrace.InitialIdentification M :=
  W.initial.cutCapIdentification

theorem initialCutCapIdentification_map :
    W.initialCutCapIdentification.1 = W.initial.diffeomorph := rfl

theorem initial_metric_eq (x : M.Carrier) (v w : TangentSpace (𝓡 3) x) :
    (W.history.initialMetric 0).inner (W.initial.diffeomorph x)
      (mfderiv (𝓡 3) (𝓡 3) W.initial.diffeomorph x v)
      (mfderiv (𝓡 3) (𝓡 3) W.initial.diffeomorph x w) = g.inner x v w :=
  W.initial.metric_eq x v w

theorem controlled_extinct_trace :
    W.history.cutCapTrace.poincareControlled ∧ W.history.cutCapTrace.extinct :=
  W.history.extinct_poincareControlled_trace W.controlled W.extinct

end PoincareControlledExtinction

theorem exists_poincare_controlled_extinction (M : ConnectedClosedOrientedManifold.{u} 3)
    [SimplyConnectedSpace M.Carrier] (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) := by
  sorry

theorem exists_poincare_controlled_extinction_on (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (g : SmoothRiemannianMetric (𝓡 3) M) (o : ManifoldOrientation (𝓡 3) M 3) :
    Nonempty (PoincareControlledExtinction
      ({ Carrier := M, orientation := o } : ClosedOrientedManifold 3) g) :=
  exists_poincare_controlled_extinction
    ({ Carrier := M, orientation := o } : ConnectedClosedOrientedManifold 3) g

end DifferentialGeometry.PDE.RicciFlow.Surgery
