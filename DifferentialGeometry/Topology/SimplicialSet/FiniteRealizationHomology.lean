import DifferentialGeometry.Topology.SimplicialSet.FiniteCellInduction
import DifferentialGeometry.Topology.SimplicialSet.RealizationCellInduction

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u

namespace Poincare.SSet

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

theorem quasiIso_realizationChainMap_of_finite (X : _root_.SSet.{u}) [X.Finite] :
    QuasiIso (realizationChainMap X R) := by
  apply finite_cell_induction (fun Y ↦ QuasiIso (realizationChainMap Y R)) ?_ ?_ X
  · intro Y hY
    let e : _root_.SSet.toTop.obj Y ≅ TopCat.of PEmpty.{u + 1} :=
      (hY.isInitialObj _root_.SSet.toTop Y).uniqueUpToIso TopCat.isInitialPEmpty
    have : IsEmpty (_root_.SSet.toTop.obj Y) := ⟨fun y ↦ isEmptyElim (e.hom y)⟩
    have : IsIso (realizationChainMap Y R) := isIso_realizationChainMap_of_isEmpty R Y
    infer_instance
  · intro n A B g r b h hBoundary hA
    exact quasiIso_realizationChainMap_of_cell R h hBoundary hA


def realizationHomologyIso (X : _root_.SSet.{u}) [X.Finite] (n : ℕ) :
    X.homology R n ≅
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).obj (_root_.SSet.toTop.obj X) := by
  have : QuasiIso (realizationChainMap X R) := quasiIso_realizationChainMap_of_finite R X
  exact isoOfQuasiIsoAt (realizationChainMap X R) n


@[simp]
theorem realizationHomologyIso_hom (X : _root_.SSet.{u}) [X.Finite] (n : ℕ) :
    (realizationHomologyIso R X n).hom =
      _root_.HomologicalComplex.homologyMap (realizationChainMap X R) n := rfl

@[reassoc]
theorem realizationHomologyIso_naturality {X Y : _root_.SSet.{u}} [X.Finite] [Y.Finite]
    (f : X ⟶ Y) (n : ℕ) :
    _root_.SSet.homologyMap f R n ≫ (realizationHomologyIso R Y n).hom =
      (realizationHomologyIso R X n).hom ≫
        ((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).map (_root_.SSet.toTop.map f) := by
  simp only [realizationHomologyIso_hom]
  change _root_.HomologicalComplex.homologyMap (_root_.SSet.chainComplexMap f R) n ≫
    _root_.HomologicalComplex.homologyMap (realizationChainMap Y R) n =
      _root_.HomologicalComplex.homologyMap (realizationChainMap X R) n ≫
        _root_.HomologicalComplex.homologyMap
          (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map (_root_.SSet.toTop.map f)) n
  simpa only [_root_.HomologicalComplex.homologyMap_comp] using
    congrArg (fun v ↦ _root_.HomologicalComplex.homologyMap v n)
      (realizationChainMap_naturality f R)

end Poincare.SSet
