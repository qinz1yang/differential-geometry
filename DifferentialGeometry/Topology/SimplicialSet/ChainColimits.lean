import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.MonoCoprod

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
noncomputable section
universe u
namespace Poincare.SSet
variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


instance chainComplexFunctor_preservesColimits :
    PreservesColimitsOfSize.{u, u} ((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R) where
  preservesColimitsOfShape {J _} := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    change PreservesColimitsOfShape J
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n⦌) ⋙ sigmaConst.obj R)
    infer_instance


instance chainComplexFunctor_preservesMonomorphisms :
    ((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).PreservesMonomorphisms where
  preserves f _ := by
    dsimp [_root_.SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
    apply +allowSynthFailures Functor.map_mono
    dsimp [_root_.SSet, SimplicialObject.whiskering, SimplicialObject]
    infer_instance

end Poincare.SSet
