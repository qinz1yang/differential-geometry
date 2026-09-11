import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Homology.Opposite

noncomputable section

open CategoryTheory Opposite

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u


abbrev IntegralCochains (X : Type u) [TopologicalSpace X] :
    CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  (IntegralChains X).linearYonedaObj ℤ integralCoefficients


abbrev IntegralCohomology (X : Type u) [TopologicalSpace X] (n : ℕ) : ModuleCat.{u} ℤ :=
  (IntegralCochains X).homology n


def integralCochainsFunctor : TopCat.{u}ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  (integralChainsFunctor ⋙
    (((linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralCoefficients).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ))).op ⋙
    HomologicalComplex.unopFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ)

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]


def integralCochainMap (f : C(X, Y)) : IntegralCochains Y ⟶ IntegralCochains X :=
  integralCochainsFunctor.map (TopCat.ofHom f).op


theorem integralCochainMap_apply (f : C(X, Y)) (n : ℕ)
    (a : (IntegralCochains Y).X n) :
    (integralCochainMap f).f n a = (integralChainsFunctor.map (TopCat.ofHom f)).f n ≫ a := rfl

@[simp] theorem integralCochainMap_id :
    integralCochainMap (ContinuousMap.id X) = 𝟙 (IntegralCochains X) := by
  exact integralCochainsFunctor.map_id (op (TopCat.of X))


theorem integralCochainMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    integralCochainMap (g.comp f) = integralCochainMap g ≫ integralCochainMap f := by
  exact integralCochainsFunctor.map_comp (TopCat.ofHom g).op (TopCat.ofHom f).op


def integralCohomologyMap (n : ℕ) (f : C(X, Y)) :
    IntegralCohomology Y n ⟶ IntegralCohomology X n :=
  HomologicalComplex.homologyMap (integralCochainMap f) n

@[simp] theorem integralCohomologyMap_id (n : ℕ) :
    integralCohomologyMap n (ContinuousMap.id X) = 𝟙 (IntegralCohomology X n) := by
  simp only [integralCohomologyMap, integralCochainMap_id, HomologicalComplex.homologyMap_id]

theorem integralCohomologyMap_comp (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    integralCohomologyMap n (g.comp f) =
      integralCohomologyMap n g ≫ integralCohomologyMap n f := by
  simp only [integralCohomologyMap, integralCochainMap_comp, HomologicalComplex.homologyMap_comp]


def integralCochainHomotopy {f g : C(X, Y)} (h : ContinuousMap.Homotopy f g) :
    Homotopy (integralCochainMap f) (integralCochainMap g) :=
  ((((linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralCoefficients).rightOp).mapHomotopy
    ((show TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) from h).singularChainComplexFunctorObjMap
      integralCoefficients)).unop


theorem integralCohomologyMap_homotopic (n : ℕ) {f g : C(X, Y)}
    (h : ContinuousMap.Homotopic f g) :
    integralCohomologyMap n f = integralCohomologyMap n g := by
  obtain ⟨h⟩ := h
  exact (integralCochainHomotopy h).homologyMap_eq n

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
