import Mathlib.Topology.Homotopy.Basic

namespace Poincare.Topology.Homotopy

open scoped unitInterval

def cylinderBoundaryHomotopy {X : Type*} [TopologicalSpace X]
    (δ : C(X, X)) (Ψ : C(X × unitInterval, X × unitInterval))
    (hzero : ∀ x, Ψ (x, 0) = (x, 0))
    (hone : ∀ x, Ψ (x, 1) = (δ x, 1)) :
    ContinuousMap.Homotopy (ContinuousMap.id X) δ where
  toFun p := (Ψ (p.2, p.1)).1
  continuous_toFun := continuous_fst.comp (Ψ.continuous.comp continuous_swap)
  map_zero_left x := by simp only [hzero, ContinuousMap.id_apply]
  map_one_left x := by simp only [hone]

theorem not_exists_cylinder_map_of_not_homotopic {X : Type*} [TopologicalSpace X]
    (δ : C(X, X)) (hδ : ¬ ContinuousMap.Homotopic (ContinuousMap.id X) δ) :
    ¬ ∃ Ψ : C(X × unitInterval, X × unitInterval),
      (∀ x, Ψ (x, 0) = (x, 0)) ∧ (∀ x, Ψ (x, 1) = (δ x, 1)) := by
  rintro ⟨Ψ, hzero, hone⟩
  exact hδ ⟨cylinderBoundaryHomotopy δ Ψ hzero hone⟩

def productBoundaryHomotopy {X W : Type*} [TopologicalSpace X] [TopologicalSpace W]
    (Hprod : X × unitInterval ≃ₜ W) (δ : C(X, X)) (Ψ : C(X × unitInterval, W))
    (hzero : ∀ x, Ψ (x, 0) = Hprod (x, 0))
    (hone : ∀ x, Ψ (x, 1) = Hprod (δ x, 1)) :
    ContinuousMap.Homotopy (ContinuousMap.id X) δ :=
  cylinderBoundaryHomotopy δ
    ⟨fun p ↦ Hprod.symm (Ψ p), Hprod.symm.continuous.comp Ψ.continuous⟩
    (fun x ↦ by simp only [ContinuousMap.coe_mk, hzero, Hprod.symm_apply_apply])
    (fun x ↦ by simp only [ContinuousMap.coe_mk, hone, Hprod.symm_apply_apply])

end Poincare.Topology.Homotopy
