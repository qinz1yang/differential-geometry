import DifferentialGeometry.Topology.Homology.TetrahedronSpherePairing
import DifferentialGeometry.Topology.Homology.FourSimplexTerminalFaces
import DifferentialGeometry.Topology.Simplex.FourSimplexHomotopyRelation

noncomputable section

namespace DifferentialGeometry.Topology

open CategoryTheory AlgebraicTopology
open scoped Simplicial

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem integralSingularTetrahedronSphereClass_face_relation
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]
    (τ : integralSingularSimplex 4 X) :
    integralSingularTetrahedronSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) *
      integralSingularTetrahedronSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) *
      integralSingularTetrahedronSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 4 τ) =
    integralSingularTetrahedronSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) *
      integralSingularTetrahedronSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 τ) := by
  obtain ⟨g, _, hskel, hfaces⟩ := exists_fourSimplex_cone_terminal_faces x τ
  have hg : ∀ p ∈ Simplex.skeleton (Fin 5) 2, g p = x := fun p hp => hskel ⟨p, hp⟩
  have heq (i : Fin 5) := integralSingularTetrahedronSphereClass_eq_tetrahedronGenLoop x
    ((TopCat.toSSet.obj (TopCat.of X)).δ i τ)
    (g.comp ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩)
    (fun p hp => hg _ (Simplex.map_succAbove_mem_skeleton_of_mem_boundary i hp))
    (hfaces i).choose_spec
  rw [heq 0, heq 2, heq 4, heq 1, heq 3]
  exact tetrahedronGenLoop_fourSimplex_face_relation g hg

end DifferentialGeometry.Topology
