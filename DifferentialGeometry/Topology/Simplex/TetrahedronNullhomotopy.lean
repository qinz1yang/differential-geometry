import DifferentialGeometry.Topology.Simplex.TetrahedronFill
import DifferentialGeometry.Topology.Simplex.BoundarySphereFilling

noncomputable section

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem boundarySphereDesc_nullhomotopic_of_triangleGenLoop_relation
    (g : Fin 4 → C(stdSimplex ℝ (Fin 3), X))
    (hg : ∀ i, ∀ p ∈ Simplex.boundary (Fin 3), g i p = x)
    (hcompat : ∀ (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)),
      g i (stdSimplex.map j.succAbove p) =
        g (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p))
    (h : let q : Fin 4 → HomotopyGroup (Fin 2) X x := fun i =>
      ⟦Simplex.triangleGenLoop (g i) x (hg i)⟧
      q 0 * q 2 = q 1 * q 3) :
    (Simplex.boundarySphereDesc g hcompat).Nullhomotopic := by
  obtain ⟨F, hF⟩ := exists_tetrahedron_extension_of_triangleGenLoop_relation g hg h
  exact Simplex.boundarySphereDesc_nullhomotopic_of_extension g hcompat F hF

end DifferentialGeometry.Topology
