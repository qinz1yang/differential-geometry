import DifferentialGeometry.Topology.LocalDegree.SphereGenerator

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace Poincare.LocalDegree
open Poincare.Homology
variable {d : ℕ}


def euclideanSphereDegree (f : C(EuclideanSphere d, EuclideanSphere d)) : ℤ :=
  euclideanSphereTopReducedHomologyEquiv d
    (reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) d
      (euclideanSphereTopGenerator d))


theorem euclideanSphereDegree_generator (f : C(EuclideanSphere d, EuclideanSphere d)) :
    reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) d
        (euclideanSphereTopGenerator d) =
      euclideanSphereDegree f • euclideanSphereTopGenerator d :=
  (euclideanSphereTopReducedHomologyEquiv_smul_generator d _).symm


theorem euclideanSphereDegree_action (f : C(EuclideanSphere d, EuclideanSphere d))
    (c : reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere d)) d) :
    euclideanSphereTopReducedHomologyEquiv d
        (reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) d c) =
      euclideanSphereDegree f * euclideanSphereTopReducedHomologyEquiv d c := by
  rw [← euclideanSphereTopReducedHomologyEquiv_smul_generator d c]
  simp only [map_zsmul, euclideanSphereDegree, smul_eq_mul,
    euclideanSphereTopReducedHomologyEquiv_generator, mul_one]
  ring


@[simp]
theorem euclideanSphereDegree_id :
    euclideanSphereDegree (ContinuousMap.id (EuclideanSphere d)) = 1 := by
  unfold euclideanSphereDegree
  rw [show TopCat.ofHom (ContinuousMap.id (EuclideanSphere d)) = 𝟙 _ from rfl,
    reducedSingularHomologyMap_id]
  exact euclideanSphereTopReducedHomologyEquiv_generator d


theorem euclideanSphereDegree_comp (f g : C(EuclideanSphere d, EuclideanSphere d)) :
    euclideanSphereDegree (g.comp f) = euclideanSphereDegree g * euclideanSphereDegree f := by
  unfold euclideanSphereDegree
  rw [show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g from rfl,
    reducedSingularHomologyMap_comp]
  exact euclideanSphereDegree_action g _


theorem euclideanSphereDegree_eq_of_homotopy
    {f g : C(EuclideanSphere d, EuclideanSphere d)} (H : f.Homotopy g) :
    euclideanSphereDegree f = euclideanSphereDegree g := by
  unfold euclideanSphereDegree
  rw [reducedSingularHomologyMap_eq_of_homotopy (ModuleCat.of ℤ ℤ) H]
  rfl


@[simp]
theorem euclideanSphereDegree_const (y : EuclideanSphere d) :
    euclideanSphereDegree (ContinuousMap.const (EuclideanSphere d) y) = 0 := by
  let p : TopCat.of (EuclideanSphere d) ⟶ TopCat.of PUnit := TopCat.ofHom (ContinuousMap.const _ PUnit.unit)
  let q : TopCat.of PUnit ⟶ TopCat.of (EuclideanSphere d) := TopCat.ofHom (ContinuousMap.const _ y)
  have hz := isZero_reducedSingularHomology_of_contractible (ModuleCat.of ℤ ℤ) (TopCat.of PUnit) d
  have hp : reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) p d = 0 := hz.eq_of_tgt _ _
  unfold euclideanSphereDegree
  rw [show TopCat.ofHom (ContinuousMap.const (EuclideanSphere d) y) = p ≫ q from rfl,
    reducedSingularHomologyMap_comp, hp, zero_comp]
  exact map_zero _


theorem euclideanSphereDegree_isUnit
    (e : ContinuousMap.HomotopyEquiv (EuclideanSphere d) (EuclideanSphere d)) :
    IsUnit (euclideanSphereDegree e.toFun) := by
  obtain ⟨H⟩ := e.left_inv
  have he := euclideanSphereDegree_eq_of_homotopy H
  rw [euclideanSphereDegree_comp, euclideanSphereDegree_id] at he
  exact isUnit_of_dvd_one ⟨euclideanSphereDegree e.invFun, by rw [mul_comm]; exact he.symm⟩

end Poincare.LocalDegree
