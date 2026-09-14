import DifferentialGeometry.Topology.VanKampen.Pi1FiniteConnectedSum
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem simplyConnectedSpace_finiteConnectedSum_of_factors
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : ∀ (F : ConnectedClosedOrientedManifold.{u} 3) (p : F.Carrier),
      F ∈ L → Subsingleton (FundamentalGroup F.Carrier p))
    (y : (finiteConnectedSum L).Carrier) :
    SimplyConnectedSpace (finiteConnectedSum L).Carrier :=
  (VanKampen.simplyConnectedSpace_iff_fundamentalGroup_subsingleton
      (finiteConnectedSum L).Carrier y).mpr
    (subsingleton_of_finiteConnectedSum_factors L h
      (fun i => Classical.choice (inferInstance : Nonempty (L.get i).Carrier)) y)

theorem simplyConnectedSpace_finiteConnectedSum_of_simplyConnected
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : ∀ (F : ConnectedClosedOrientedManifold.{u} 3),
      F ∈ L → SimplyConnectedSpace F.Carrier)
    (y : (finiteConnectedSum L).Carrier) :
    SimplyConnectedSpace (finiteConnectedSum L).Carrier :=
  simplyConnectedSpace_finiteConnectedSum_of_factors L
    (fun F p hF =>
      (VanKampen.simplyConnectedSpace_iff_fundamentalGroup_subsingleton F.Carrier p).mp
        (h F hF)) y

end DifferentialGeometry.Topology
