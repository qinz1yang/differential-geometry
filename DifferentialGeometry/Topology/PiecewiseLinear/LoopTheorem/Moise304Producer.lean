import DifferentialGeometry.Topology.PiecewiseLinear.SphericalShellCompression
import DifferentialGeometry.Topology.PiecewiseLinear.TameNestedCells
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.Orientable

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem moise304 : Moise304 :=
  moise304_of_moise252 loop_theorem

theorem moise305Tame : Moise305Tame :=
  moise305_tame_of_moise304 moise304

end DifferentialGeometry.Topology.PiecewiseLinear
