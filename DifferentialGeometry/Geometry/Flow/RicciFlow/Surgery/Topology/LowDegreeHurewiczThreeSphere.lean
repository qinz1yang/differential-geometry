import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopClass
import DifferentialGeometry.Topology.Homology.LowDegreeHurewiczNonvacuity
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere

noncomputable section

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem subsingleton_integralHomology_two_standardThreeSphereLift :
    Subsingleton
      (IntegralHomology DifferentialGeometry.Topology.standardThreeSphereLift.{u}.Carrier 2) :=
  DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_liftedHomotopySphere_two.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
