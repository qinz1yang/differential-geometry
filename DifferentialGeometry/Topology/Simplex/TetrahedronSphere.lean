import DifferentialGeometry.Topology.Simplex.Sphere

noncomputable section

namespace DifferentialGeometry.Simplex

variable {X : Type*} [TopologicalSpace X]

def tetrahedronSphereFaces (g : C(stdSimplex ℝ (Fin 4), X)) (x : X) :
    Fin 5 → C(stdSimplex ℝ (Fin 4), X) :=
  simplexSphereFaces g x

theorem tetrahedronSphereFaces_compatible (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x)
    (i : Fin 5) (j : Fin 4) (p : stdSimplex ℝ (Fin 3)) :
    tetrahedronSphereFaces g x i (stdSimplex.map j.succAbove p) =
      tetrahedronSphereFaces g x (i.succAbove j)
        (stdSimplex.map (j.predAbove i).succAbove p) :=
  simplexSphereFaces_compatible g x hg i j p

def tetrahedronSphereMap (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X) :=
  simplexSphereMap g x hg

theorem tetrahedronSphereMap_face (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x)
    (i : Fin 5) (p : stdSimplex ℝ (Fin 4)) :
    tetrahedronSphereMap g x hg
      (stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 4) ℝ).symm
        ⟨stdSimplex.map i.succAbove p, ⟨i, map_succAbove_apply_pivot i p⟩⟩) =
      tetrahedronSphereFaces g x i p :=
  simplexSphereMap_face g x hg i p

end DifferentialGeometry.Simplex
