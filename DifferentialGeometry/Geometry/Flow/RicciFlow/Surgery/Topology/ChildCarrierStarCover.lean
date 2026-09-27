import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedStarCover

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Topology.VanKampen in
theorem child_simplyConnected_of_starCover {P Q D N : OrientedThreeStage.{u}}
    (E : SmoothCutCapTransition P Q D N) (c : ConnectedComponents Q.Carrier)
    (U : Set (E.ChildCarrier c)) (V : E.ChildCapBoundary c → Set (E.ChildCarrier c))
    (hU : IsOpen U) (hV : ∀ b, IsOpen (V b))
    (hcover : U ∪ ⋃ b, V b = univ)
    (hdisj : Pairwise fun b b' => Disjoint (V b) (V b'))
    [hUsc : SimplyConnectedSpace ↥U] [hVsc : ∀ b, SimplyConnectedSpace ↥(V b)]
    [hInt : ∀ b, SimplyConnectedSpace ↥(U ∩ V b)] :
    SimplyConnectedSpace (Q.component c).Carrier :=
  @simplyConnectedSpace_of_open_cover_of_pairwise_disjoint_of_fintype
    (E.ChildCarrier c) _ (E.ChildCapBoundary c) _ U V hU hV hcover hdisj
    hUsc hVsc hInt

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
