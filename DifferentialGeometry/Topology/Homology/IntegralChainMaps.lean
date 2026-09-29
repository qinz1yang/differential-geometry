import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def integralCoefficients : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)

def integralChainsFunctor : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralCoefficients

def integralHomologyFunctor (n : ℕ) : TopCat.{u} ⥤ ModuleCat.{u} ℤ :=
  (singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj integralCoefficients

variable (X : Type u) [TopologicalSpace X]

abbrev IntegralChains := integralChainsFunctor.obj (TopCat.of X)

abbrev IntegralHomology (n : ℕ) := (integralHomologyFunctor n).obj (TopCat.of X)

variable {X} {Y : Type u} [TopologicalSpace Y]

def integralHomologyMap (n : ℕ) (f : C(X, Y)) :
    IntegralHomology X n ⟶ IntegralHomology Y n :=
  (integralHomologyFunctor n).map (TopCat.ofHom f)

def singularSimplexChain {n : ℕ} (f : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    integralCoefficients ⟶ (IntegralChains X).X n :=
  (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌)).symm f)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
