import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift








noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology


abbrev integralSingularCoefficients : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)



abbrev integralSingularChains (X : Type u) [TopologicalSpace X] : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).obj (TopCat.of X)


abbrev integralSingularHomology (n : ℕ) (X : Type u) [TopologicalSpace X] : ModuleCat.{u} ℤ :=
  (integralSingularChains X).homology n

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]


def integralSingularHomologyMap (n : ℕ) (f : C(X, Y)) :
    integralSingularHomology n X →ₗ[ℤ] integralSingularHomology n Y :=
  (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj integralSingularCoefficients).map
    (TopCat.ofHom f)).hom


theorem integralSingularHomologyMap_id (n : ℕ) :
    integralSingularHomologyMap n (.id X) = LinearMap.id :=
  congrArg ModuleCat.Hom.hom
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj integralSingularCoefficients).map_id
      (TopCat.of X))


theorem integralSingularHomologyMap_comp (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    integralSingularHomologyMap n (g.comp f) =
      (integralSingularHomologyMap n g).comp (integralSingularHomologyMap n f) :=
  congrArg ModuleCat.Hom.hom
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj integralSingularCoefficients).map_comp
      (TopCat.ofHom f) (TopCat.ofHom g))



theorem integralSingularHomologyMap_homotopic (n : ℕ) {f g : C(X, Y)} (h : f.Homotopic g) :
    integralSingularHomologyMap n f = integralSingularHomologyMap n g := by
  obtain ⟨H⟩ := h
  exact congrArg ModuleCat.Hom.hom
    (@TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (ModuleCat.{u} ℤ)
      _ _ _ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f) (TopCat.ofHom g) _ H
        integralSingularCoefficients n)



def integralSingularHomologyZeroEquiv [PathConnectedSpace X] :
    integralSingularHomology 0 X ≃ₗ[ℤ] ℤ :=
  (asIso ((TopCat.of X).singularHomology₀ε integralSingularCoefficients)).toLinearEquiv.trans
    ULift.moduleEquiv

end DifferentialGeometry.Topology
