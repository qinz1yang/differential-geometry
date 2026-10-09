import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDistanceData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalarTransport

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal
namespace GC.GeneralFlow
universe u

/-- Restrict the same selected full history at the actual integer observation. -/
theorem PreparedSpatialChain.observation_hasUniformDistanceScalar
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0}
    (S : PreparedSpatialChain pBase C P g)
    (hS : ∀ n, (S.state n).DistanceData Cdist) (n : ℕ) :
    ∀ i : Fin (S.observation n).history.eventCount,
      ((S.observation n).history.toHistory.event i).HasUniformDistanceScalar Cdist
 := by
  exact (S.state (n + 1)).history.hasUniformDistanceScalar_restrict
    (S.observationTime n) (hS (n + 1)).full

/-- The actual tower is made from these same certified observations. -/
theorem PreparedSpatialChain.tower_hasUniformDistanceScalar
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0}
    (S : PreparedSpatialChain pBase C P g)
    (hS : ∀ n, (S.state n).DistanceData Cdist) (n : ℕ) :
    ∀ i : Fin (S.tower.history n).eventCount,
      ((S.tower.history n).toHistory.event i).HasUniformDistanceScalar Cdist := by
  exact S.observation_hasUniformDistanceScalar hS n

end GC.GeneralFlow
