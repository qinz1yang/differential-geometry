import DifferentialGeometry.Topology.Category.TopCat.SingularCoproduct
import DifferentialGeometry.Topology.SimplicialSet.ChainColimits
import DifferentialGeometry.Topology.Homology.EulerCharacteristic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
namespace Poincare.Homology
universe u
variable {ι : Type u} (X : ι → TopCat.{u}) {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def singularChainSigmaCofan : Cofan (fun i => ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj (X i)) :=
  Cofan.mk (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj (TopCat.of (Σ i, X i)))
    (fun i => ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map (TopCat.sigmaι X i))


def singularChainSigmaCofanIsColimit : IsColimit (singularChainSigmaCofan X R) :=
  (Cofan.isColimitMapCoconeEquiv ((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R)
    _ (Poincare.TopCat.singularSigmaCofan X))
    (isColimitOfPreserves _ (Poincare.TopCat.singularSigmaCofanIsColimit X))


def singularHomologySigmaCofan (n : ℕ) : Cofan (fun i =>
    (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).obj (X i))) :=
  Cofan.mk (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).obj (TopCat.of (Σ i, X i)))
    (fun i => ((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).map (TopCat.sigmaι X i))


def singularHomologySigmaCofanIsColimit [Finite ι] (n : ℕ) : IsColimit (singularHomologySigmaCofan X R n) :=
  (Cofan.isColimitMapCoconeEquiv (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n)
    _ (singularChainSigmaCofan X R)) (isColimitOfPreserves _ (singularChainSigmaCofanIsColimit X R))


def singularHomologySigmaIso [Finite ι] (n : ℕ) :
    (∐ fun i => ((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).obj (X i)) ≅
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).obj (TopCat.of (Σ i, X i)) :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso (singularHomologySigmaCofanIsColimit X R n)


@[reassoc (attr := simp)]
theorem singularHomologySigmaIso_ι_hom [Finite ι] (n : ℕ) (i : ι) :
    Sigma.ι (fun i => ((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).obj (X i)) i ≫
      (singularHomologySigmaIso X R n).hom =
        ((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).map (TopCat.sigmaι X i) :=
  (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom (singularHomologySigmaCofanIsColimit X R n) ⟨i⟩

end Poincare.Homology
