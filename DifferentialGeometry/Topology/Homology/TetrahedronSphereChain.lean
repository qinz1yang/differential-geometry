import DifferentialGeometry.Topology.Homology.SimplexSphereChain
import DifferentialGeometry.Topology.Homology.CycleClassMaps
import DifferentialGeometry.Topology.Simplex.TetrahedronSphere
import DifferentialGeometry.Topology.Homology.SphereHurewicz

noncomputable section
open CategoryTheory AlgebraicTopology ContinuousMap
open scoped Simplicial
namespace DifferentialGeometry.Topology
universe u
variable {X : Type u} [TopologicalSpace X]

theorem integralSingularChainMap_tetrahedronSphereMap_simplexBoundarySphereChain
    (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x) :
    (integralSingularChainMap
      ((Simplex.tetrahedronSphereMap g x hg).comp ⟨ULift.down, continuous_uliftDown⟩)).f 3
      (simplexBoundarySphereChain.{u} 2) =
        integralSimplexChain 3 ((integralSingularSimplexEquiv 3 X).symm g) :=
  integralSingularChainMap_simplexSphereMap_simplexBoundarySphereChain_of_even 2 (by decide) g x hg

theorem integralSimplexChain_three_boundary_eq_zero
    (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x) :
    (integralSingularChains X).d 3 2
      (integralSimplexChain 3 ((integralSingularSimplexEquiv 3 X).symm g)) = 0 :=
  integralSimplexChain_boundary_eq_zero_of_even 2 (by decide) g x hg

def integralSingularTetrahedronCycle (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x) : integralSingularCycles 2 X :=
  ⟨integralSimplexChain 3 ((integralSingularSimplexEquiv 3 X).symm g),
    integralSimplexChain_three_boundary_eq_zero g x hg⟩

theorem integralSingularTetrahedronCycle_val (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x) :
    (integralSingularTetrahedronCycle g x hg).val =
      integralSimplexChain 3 ((integralSingularSimplexEquiv 3 X).symm g) := rfl

theorem tetrahedronSphereMap_simplexBoundarySphereClass
    (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x) :
    freeSphereHomologyImage 2 (simplexBoundarySphereClass.{u} 2)
      (ZerothHomotopy.mk (Simplex.tetrahedronSphereMap g x hg)) =
        integralSingularCycleClass 2 X (integralSingularTetrahedronCycle g x hg) := by
  rw [freeSphereHomologyImage_mk, simplexBoundarySphereClass,
    integralSingularCycleClass_map]
  congr 1
  apply Subtype.ext
  rw [integralSingularCycleMap_val, integralSingularTetrahedronCycle_val]
  exact integralSingularChainMap_tetrahedronSphereMap_simplexBoundarySphereChain g x hg

end DifferentialGeometry.Topology
