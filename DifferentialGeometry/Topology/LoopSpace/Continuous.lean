import DifferentialGeometry.Topology.ThreeManifold.Model
import DifferentialGeometry.Topology.Homotopy.FreeHomotopyClass
import DifferentialGeometry.Topology.LoopSpace.FreeAdjunction

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

abbrev Circle := DifferentialGeometry.Topology.loopCircle

abbrev SphereFamily (Q : Type*) [TopologicalSpace Q] :=
  C(Sphere 2, DifferentialGeometry.Topology.freeLoop Q)

abbrev ContractibleSphereFamily (Q : Type*) [TopologicalSpace Q] :=
  C(Sphere 2, DifferentialGeometry.Topology.contractibleLoop Q)

abbrev FreeSphereClass (Q : Type*) [TopologicalSpace Q] :=
  DifferentialGeometry.Topology.FreeHomotopyClass (Sphere 2) (DifferentialGeometry.Topology.freeLoop Q)

abbrev FreeContractibleSphereClass (Q : Type*) [TopologicalSpace Q] :=
  DifferentialGeometry.Topology.FreeHomotopyClass (Sphere 2) (DifferentialGeometry.Topology.contractibleLoop Q)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
