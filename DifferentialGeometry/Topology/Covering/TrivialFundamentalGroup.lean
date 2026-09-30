import DifferentialGeometry.Topology.FundamentalGroup.SimplyConnected

namespace DifferentialGeometry.Topology

theorem simplyConnectedSpace_of_subsingleton_fundamentalGroup
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X)
    [Subsingleton (FundamentalGroup X x₀)] : SimplyConnectedSpace X :=
  (simplyConnectedSpace_iff_fundamentalGroup_eq_one x₀).mpr
    (fun g => Subsingleton.elim g 1)

end DifferentialGeometry.Topology
