import DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.CompactFundamentalGroup
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteFreeFactors
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapFreeFactor
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold
namespace GC.GeneralFlow
universe u

theorem initial_fundamentalGroup_fg (P : OrientedThreeStage.{u}) (p : P.Carrier) :
    Group.FG (FundamentalGroup P.Carrier p) := by
  let M := P.toClosedOrientedManifold
  let c := ConnectedComponents.mk (show M.Carrier from p)
  let x : (M.component c).Carrier := ⟨p, rfl⟩
  let : Group.FG (FundamentalGroup (M.component c).Carrier x) :=
    GC.Topology.compact_normed_charts_fundamentalGroup_fg ThreeSpace (M.component c).Carrier x
  let e := GC.Surgery.componentFundamentalGroupEquiv M c x
  exact Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

theorem initial_freeFactor_fg_complement (P : OrientedThreeStage.{u}) (p : P.Carrier)
    (G : Type u) [Group G]
    (h : GC.Group.IsFreeFactor G (FundamentalGroup P.Carrier p)) :
    Group.FG G ∧ ∃ (K : Type u) (_ : Group K), Group.FG K ∧
      Nonempty (FundamentalGroup P.Carrier p ≃* Monoid.Coprod G K) := by
  let : Group.FG (FundamentalGroup P.Carrier p) := initial_fundamentalGroup_fg P p
  exact GC.Group.freeFactor_fg_complement h

end GC.GeneralFlow
