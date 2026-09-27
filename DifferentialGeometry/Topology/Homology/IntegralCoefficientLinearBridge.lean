import DifferentialGeometry.Topology.Homology.IntegralReducedCoefficientBridge

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology

namespace DifferentialGeometry.Topology

universe u

private noncomputable def moduleCatIsoAddEquivOfIso {A B : ModuleCat.{u} ℤ} (e : A ≅ B) :
    A ≃+ B where
  toFun := fun x => e.hom x
  invFun := fun y => e.inv y
  left_inv := fun x => by
    change e.inv (e.hom x) = x
    rw [Iso.hom_inv_id_apply]
  right_inv := fun y => by
    change e.hom (e.inv y) = y
    rw [Iso.inv_hom_id_apply]
  map_add' := fun x y => map_add (ConcreteCategory.hom e.hom) x y

noncomputable def moduleCatIsoLinearEquiv {A B : ModuleCat.{u} ℤ} (e : A ≅ B) :
    A ≃ₗ[ℤ] B :=
  AddEquiv.toIntLinearEquiv (moduleCatIsoAddEquivOfIso e)

theorem moduleCatIsoLinearEquiv_apply {A B : ModuleCat.{u} ℤ} (e : A ≅ B) (x : A) :
    moduleCatIsoLinearEquiv e x = e.hom x := rfl

theorem moduleCatIsoLinearEquiv_symm_apply {A B : ModuleCat.{u} ℤ} (e : A ≅ B) (y : B) :
    (moduleCatIsoLinearEquiv e).symm y = e.inv y := rfl

theorem subsingleton_module_int (M : Type u) [AddCommGroup M] : Subsingleton (Module ℤ M) :=
  inferInstance

noncomputable def integralSingularCoefficientsLinearEquiv :
    integralSingularCoefficients ≃ₗ[ℤ] ModuleCat.of ℤ ℤ :=
  moduleCatIsoLinearEquiv integralSingularCoefficientsIso

end DifferentialGeometry.Topology
