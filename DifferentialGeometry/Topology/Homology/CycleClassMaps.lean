import DifferentialGeometry.Topology.Homology.ModuleHomologyMaps
import DifferentialGeometry.Topology.Homology.UniversalCoefficientsOne

noncomputable section

open CategoryTheory

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def integralSingularCycleMap (n : ℕ) (f : C(X, Y)) :
    integralSingularCycles n X →ₗ[ℤ] integralSingularCycles n Y :=
  moduleCycleMap ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} ℤ)
    (ComplexShape.down ℕ) (n + 2) (n + 1) n).map (integralSingularChainMap f))

@[simp]
theorem integralSingularCycleMap_val (n : ℕ) (f : C(X, Y))
    (z : integralSingularCycles n X) :
    (integralSingularCycleMap n f z).val = (integralSingularChainMap f).f (n + 1) z.val :=
  rfl

private theorem integralSingularCycleClass_eq (n : ℕ) (z : integralSingularCycles n X) :
    integralSingularCycleClass n X z =
      ((integralSingularChains X).homologyIsoSc' (n + 2) (n + 1) n
        (by simp) (by simp)).inv
        (moduleHomologyClass ((integralSingularChains X).sc' (n + 2) (n + 1) n) z) := by
  apply (integralSingularHomologyCycleEquiv n X).injective
  rw [integralSingularCycleClass, AddEquiv.apply_symm_apply]
  change _ = ((integralSingularChains X).sc' (n + 2) (n + 1) n).moduleCatHomologyIso.hom
    (((integralSingularChains X).homologyIsoSc' (n + 2) (n + 1) n
      (by simp) (by simp)).hom
      (((integralSingularChains X).homologyIsoSc' (n + 2) (n + 1) n
        (by simp) (by simp)).inv _))
  rw [Iso.inv_hom_id_apply]
  exact (moduleHomologyClass_quotient
    ((integralSingularChains X).sc' (n + 2) (n + 1) n) z).symm

theorem integralSingularCycleClass_map (n : ℕ) (f : C(X, Y))
    (z : integralSingularCycles n X) :
    integralSingularHomologyMap (n + 1) f (integralSingularCycleClass n X z) =
      integralSingularCycleClass n Y (integralSingularCycleMap n f z) := by
  rw [integralSingularCycleClass_eq, integralSingularCycleClass_eq]
  let e := HomologicalComplex.homologyFunctorIso' (ModuleCat.{u} ℤ)
    (ComplexShape.down ℕ) (n + 2) (n + 1) n (by simp) (by simp)
  have h := congrArg (fun g => g
    (moduleHomologyClass ((integralSingularChains X).sc' (n + 2) (n + 1) n) z))
    (e.inv.naturality (integralSingularChainMap f))
  change ((integralSingularChains Y).homologyIsoSc' (n + 2) (n + 1) n
    (by simp) (by simp)).inv
      (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} ℤ)
          (ComplexShape.down ℕ) (n + 2) (n + 1) n).map (integralSingularChainMap f))
        (moduleHomologyClass ((integralSingularChains X).sc' (n + 2) (n + 1) n) z)) =
    integralSingularHomologyMap (n + 1) f
      (((integralSingularChains X).homologyIsoSc' (n + 2) (n + 1) n
        (by simp) (by simp)).inv
        (moduleHomologyClass ((integralSingularChains X).sc' (n + 2) (n + 1) n) z)) at h
  exact h.symm.trans (congrArg
    ((integralSingularChains Y).homologyIsoSc' (n + 2) (n + 1) n
      (by simp) (by simp)).inv
    (moduleHomologyClass_map
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} ℤ)
        (ComplexShape.down ℕ) (n + 2) (n + 1) n).map (integralSingularChainMap f)) z))

end DifferentialGeometry.Topology
