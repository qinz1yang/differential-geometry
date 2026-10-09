import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteIndecomposable
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialFundamentalGroup
set_option autoImplicit false
noncomputable section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.GeneralFlow
universe u

theorem initial_finiteIndecomposablePresentation
    (P : OrientedThreeStage.{u}) (p : P.Carrier) :
    GC.Group.HasFiniteIndecomposablePresentation (FundamentalGroup P.Carrier p) := by
  let : Group.FG (FundamentalGroup P.Carrier p) := initial_fundamentalGroup_fg P p
  exact GC.Group.finiteIndecomposablePresentation_of_fg (FundamentalGroup P.Carrier p)

end GC.GeneralFlow
