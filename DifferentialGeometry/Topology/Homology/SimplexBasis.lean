import DifferentialGeometry.Topology.Homology.Relative.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.FreeModule.Basic



noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Module
open scoped Simplicial

universe u

namespace DifferentialGeometry.Topology


abbrev integralSingularSimplex (n : ℕ) (X : Type u) [TopologicalSpace X] :=
  (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋n⦌)


def integralSingularSimplexEquiv (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularSimplex n X ≃ C(stdSimplex ℝ (Fin (n + 1)), X) :=
  (TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)



def integralSingularChainFinsuppIso (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (integralSingularChains X).X n ≅
      ModuleCat.of ℤ (integralSingularSimplex n X →₀ ULift.{u} ℤ) :=
  ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan
    integralSingularCoefficients n).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ) (integralSingularSimplex n X))



def integralSingularChainRepr (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (integralSingularChains X).X n ≃ₗ[ℤ] (integralSingularSimplex n X →₀ ℤ) :=
  (integralSingularChainFinsuppIso n X).toLinearEquiv.trans
    (Finsupp.mapRange.linearEquiv ULift.moduleEquiv)



def integralSingularChainBasis (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Basis (integralSingularSimplex n X) ℤ ((integralSingularChains X).X n) :=
  Basis.ofRepr (integralSingularChainRepr n X)


instance integralSingularChain_free (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Module.Free ℤ ((integralSingularChains X).X n) :=
  Module.Free.of_basis (integralSingularChainBasis n X)



instance integralSingularChain_projective (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Projective ((integralSingularChains X).X n) :=
  ModuleCat.projective_of_free (integralSingularChainBasis n X)

end DifferentialGeometry.Topology
