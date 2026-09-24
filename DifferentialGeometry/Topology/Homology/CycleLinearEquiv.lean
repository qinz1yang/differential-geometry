import DifferentialGeometry.Topology.Homology.Cochains
import DifferentialGeometry.Topology.Homology.Cycles

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Module
open scoped Simplicial Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

abbrev integralSingularCocycles (n : ℕ) (X : Type u) [TopologicalSpace X] :=
  LinearMap.ker ((integralSingularCochains X).d (n + 1) (n + 2)).hom

def integralSingularCoboundaryToCycles (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularCochain n X →ₗ[ℤ] integralSingularCocycles n X :=
  ((integralSingularCochains X).sc' n (n + 1) (n + 2)).moduleCatToCycles

def integralSingularHomologyCycleLinearEquiv (n : ℕ) (X : Type u) [TopologicalSpace X] :
    ↑(integralSingularHomology (n + 1) X) ≃ₗ[ℤ]
      (integralSingularCycles n X ⧸ LinearMap.range (integralSingularBoundaryToCycles n X)) :=
  AddEquiv.toIntLinearEquiv (integralSingularHomologyCycleEquiv n X)

def integralSingularCohomologyCycleLinearEquiv (n : ℕ) (X : Type u) [TopologicalSpace X] :
    ↑(integralSingularCohomology (n + 1) X) ≃ₗ[ℤ]
      (integralSingularCocycles n X ⧸
        LinearMap.range (integralSingularCoboundaryToCycles n X)) :=
  let iso := ShortComplex.homologyMapIso ((integralSingularCochains X).isoSc'
    n (n + 1) (n + 2) (by simp) (by simp)) ≪≫
    ((integralSingularCochains X).sc' n (n + 1) (n + 2)).moduleCatHomologyIso
  iso.toLinearEquiv.toAddEquiv.toIntLinearEquiv

end DifferentialGeometry.Topology
