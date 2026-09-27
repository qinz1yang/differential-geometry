import DifferentialGeometry.Topology.LoopSpace.Family



noncomputable section

namespace DifferentialGeometry.Topology


def familySphereBasepoint : familySphere :=
  ⟨EuclideanSpace.single (0 : Fin 3) 1, by simp⟩

instance familySphere_nonempty : Nonempty familySphere := ⟨familySphereBasepoint⟩

end DifferentialGeometry.Topology
