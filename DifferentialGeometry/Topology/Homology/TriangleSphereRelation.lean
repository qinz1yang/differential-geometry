import DifferentialGeometry.Topology.Homology.TriangleSpherePairing
import DifferentialGeometry.Topology.Homology.TerminalTetrahedronFaces
import DifferentialGeometry.Topology.Simplex.TetrahedronHomotopyRelation

noncomputable section
namespace DifferentialGeometry.Topology
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem integralSingularTriangleSphereClass_face_relation
    (x : X) (tau : integralSingularSimplex 3 X) :
    integralSingularTriangleSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 tau) *
      integralSingularTriangleSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 tau) =
    integralSingularTriangleSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 tau) *
      integralSingularTriangleSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 tau) := by
  obtain ⟨G, hG, hfaces⟩ := exists_terminal_tetrahedron_faces x tau
  have heq (i : Fin 4) := integralSingularTriangleSphereClass_eq_triangleGenLoop x
    ((TopCat.toSSet.obj (TopCat.of X)).δ i tau)
    (G.comp ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩)
    (fun p hp => hG (Simplex.faceBoundaryIntoTetrahedronOneSkeleton i ⟨p, hp⟩))
    (hfaces i)
  rw [heq 0, heq 2, heq 1, heq 3]
  exact triangleGenLoop_tetrahedron_face_relation G hG

end DifferentialGeometry.Topology
