import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.Moise252Producer
import DifferentialGeometry.Topology.PiecewiseLinear.Section32PseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.Section33Approximation
import DifferentialGeometry.Topology.PiecewiseLinear.Section33TubeApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Compact

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem moise331OnTube : Moise331OnTube :=
  moise331OnTube_of_moise323_of_moise324_of_moise264Orientable moise323 moise324
    moise264Orientable

theorem moise331 : Moise331 :=
  Moise331OnTube.moise331 moise331OnTube

theorem moise341 : Moise341 :=
  moise341_of_onNeighborhood moise331OnTube

end DifferentialGeometry.Topology.PiecewiseLinear
