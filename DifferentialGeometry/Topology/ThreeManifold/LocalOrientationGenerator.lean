import DifferentialGeometry.Topology.Homology.EuclideanSimplexGenerator
import DifferentialGeometry.Topology.ThreeManifold.LocalOrientation

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

theorem localOrientationClass_generator (o : TangentOrientationSection M) (x : M) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) :=
  localOrientationClass_generator_of_euclideanStandardSimplex o x
    DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
