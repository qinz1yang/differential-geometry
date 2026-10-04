import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumFreeProduct
import DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.CompactFundamentalGroup
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.RankAdditivity

/-!
# Fundamental group rank of closed oriented 3-manifolds

The fundamental group of a closed connected oriented 3-manifold is finitely generated, so it has
a rank. For a connected sum with two non-simply-connected summands, van Kampen and Grushko show
that the rank of each summand is strictly smaller than the rank of the sum.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
universe u

namespace DifferentialGeometry.Topology

instance fundamentalGroup_chosenPoint_fg (M : ConnectedClosedOrientedManifold.{u} 3) :
    Group.FG (FundamentalGroup M.Carrier (chosenPoint M)) :=
  GC.Topology.compact_normed_charts_fundamentalGroup_fg (EuclideanSpace ℝ (Fin 3))
    M.Carrier (chosenPoint M)

def fundamentalGroupRank (M : ConnectedClosedOrientedManifold.{u} 3) : ℕ :=
  Group.rank (FundamentalGroup M.Carrier (chosenPoint M))

theorem fundamentalGroupRank_lt_of_connectedSum
    (A B M : ConnectedClosedOrientedManifold.{u} 3)
    (e : ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum A B).toClosedOrientedManifold M.toClosedOrientedManifold)
    (hA : Nontrivial (FundamentalGroup A.Carrier (chosenPoint A)))
    (hB : Nontrivial (FundamentalGroup B.Carrier (chosenPoint B))) :
    fundamentalGroupRank A < fundamentalGroupRank M ∧
      fundamentalGroupRank B < fundamentalGroupRank M := by
  let d := e.1.symm
  let f := (fundamentalGroupMulEquivOfHomotopyEquiv d.toHomeomorph.toHomotopyEquiv
    (chosenPoint M) (d (chosenPoint M)) rfl).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      (d (chosenPoint M)) (chosenPoint (connectedSum A B))).trans
        (fundamentalGroup_connectedSum_freeProduct A B).some)
  exact GC.Group.rank_lt_of_mulEquiv_coprod f

end DifferentialGeometry.Topology
