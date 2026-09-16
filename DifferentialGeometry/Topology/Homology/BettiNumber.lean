import DifferentialGeometry.Topology.Homology.HomotopyEquivalence
import Mathlib.LinearAlgebra.Dimension.Constructions

open CategoryTheory AlgebraicTopology

namespace DifferentialGeometry.Homology

universe u

noncomputable def bettiNumber (k : Type u) [Field k] (X : TopCat.{u}) (n : ℕ) : ℕ :=
  Module.finrank k (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X)

theorem bettiNumber_eq_of_isIso (k : Type u) [Field k] {X Y : TopCat.{u}}
    (n : ℕ) (f : X ⟶ Y)
    [IsIso (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map f)] :
    bettiNumber k X n = bettiNumber k Y n :=
  (asIso (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map f)).toLinearEquiv.finrank_eq

theorem bettiNumber_eq_of_homotopyEquiv (k : Type u) [Field k] {X Y : TopCat.{u}}
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) : bettiNumber k X n = bettiNumber k Y n := by
  let _ := isIso_singularHomologyMap_of_homotopyEquiv (ModuleCat.of k k) e n
  exact bettiNumber_eq_of_isIso k n (TopCat.ofHom e.toFun)

noncomputable def bettiOne (X : Type) [TopologicalSpace X] : ℕ :=
  bettiNumber ℚ (TopCat.of X) 1

end DifferentialGeometry.Homology
