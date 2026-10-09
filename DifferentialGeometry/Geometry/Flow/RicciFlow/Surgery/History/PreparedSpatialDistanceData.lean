import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedDistanceData

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal
namespace GC.GeneralFlow
universe u

/-- The stronger callback on this exact selected native class. -/
def ClosedBirthPreparedClass.HasDistanceExtension
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {B : ℝ}
    (K : ClosedBirthPreparedClass pBase C P g B) (Cdist : ℝ≥0) : Prop :=
    PreparedGeometricObservationExtensionWithDistance Cdist P g B
      K.epsilonClass K.kappaClass K.parameters K.deltaBound K.radiusBound

/-- Distance certificates for this state's actual full and native histories and class. -/
structure PreparedSpatialState.DistanceData
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {E B : ℝ}
    (S : PreparedSpatialState pBase C P g E B) (Cdist : ℝ≥0) : Prop where
  full : ∀ i : Fin S.history.eventCount,
    (S.history.toHistory.event i).HasUniformDistanceScalar Cdist
  native : ∀ i : Fin S.native.eventCount,
    (S.native.toHistory.event i).HasUniformDistanceScalar Cdist
  extension : S.prepared.HasDistanceExtension Cdist

end GC.GeneralFlow
