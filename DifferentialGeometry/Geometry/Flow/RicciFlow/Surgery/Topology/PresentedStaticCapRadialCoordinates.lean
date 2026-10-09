import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapCoordinates

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- Transport the radial identities of the supplied cap family through the same
identified event and static parameters. No new cap presentation is selected. -/
theorem MetricCutCapEvent.PresentedStaticCap.hasRadialCoordinates_of_family_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {E' : MetricCutCapEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    {fixed fixed' : StaticCapScaffold} {D D' ε ε' : ℝ} {m m' : ℕ}
    (hf : fixed' = fixed) (hD : D' = D) (hm : m' = m) (hε : ε' = ε)
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b)
    (S' : ∀ b : E'.RetainedBoundaryIndex, E'.PresentedStaticCap fixed' D' m' ε' b)
    (hS : HEq S' S) (hcoordinates : ∀ b, (S b).witness.HasRadialCoordinates) :
    ∀ b, (S' b).witness.HasRadialCoordinates := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  cases hf
  cases hD
  cases hm
  cases hε
  cases eq_of_heq hS
  exact hcoordinates

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
