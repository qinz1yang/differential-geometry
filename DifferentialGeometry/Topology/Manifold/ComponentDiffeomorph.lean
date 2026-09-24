import DifferentialGeometry.Topology.Manifold.Components
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.ClosedOrientedManifold

universe u v
variable {n : ℕ} {M : ClosedOrientedManifold.{u} n} {N : ClosedOrientedManifold.{v} n}

private theorem componentMap_cancel
    (e : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier)
    (C : ConnectedComponents M.Carrier) :
    e.symm.continuous.connectedComponentsMap (e.continuous.connectedComponentsMap C) = C := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [Continuous.connectedComponentsMap_mk e.continuous x,
    Continuous.connectedComponentsMap_mk e.symm.continuous (e x), e.symm_apply_apply]

private theorem componentMap_mem
    (e : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier)
    (C : ConnectedComponents M.Carrier) (x : M.componentOpen C) :
    ConnectedComponents.mk (e x.val) = e.continuous.connectedComponentsMap C :=
  congrArg e.continuous.connectedComponentsMap x.property

private theorem componentMap_inv_mem
    (e : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier)
    (C : ConnectedComponents M.Carrier)
    (y : N.componentOpen (e.continuous.connectedComponentsMap C)) :
    ConnectedComponents.mk (e.symm y.val) = C :=
  (congrArg e.symm.continuous.connectedComponentsMap y.property).trans (componentMap_cancel e C)

def diffeomorphComponent
    (e : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier)
    (C : ConnectedComponents M.Carrier) :
    M.componentOpen C ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      N.componentOpen (e.continuous.connectedComponentsMap C) where
  toEquiv :=
    { toFun := fun x => ⟨e x.val, componentMap_mem e C x⟩
      invFun := fun y => ⟨e.symm y.val, componentMap_inv_mem e C y⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.val) }
  contMDiff_toFun := by
    intro x
    exact DifferentialGeometry.codRestr_contMDiffAt
      (V := N.componentOpen (e.continuous.connectedComponentsMap C)) (componentMap_mem e C)
      ((e.contMDiff.comp contMDiff_subtype_val).contMDiffAt)
  contMDiff_invFun := by
    intro y
    exact DifferentialGeometry.codRestr_contMDiffAt (V := M.componentOpen C)
      (componentMap_inv_mem e C) ((e.symm.contMDiff.comp contMDiff_subtype_val).contMDiffAt)

@[simp] theorem diffeomorphComponent_apply
    (e : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier)
    (C : ConnectedComponents M.Carrier) (x : M.componentOpen C) :
    (diffeomorphComponent e C x).val = e x.val := rfl

@[simp] theorem diffeomorphComponent_symm_apply
    (e : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier)
    (C : ConnectedComponents M.Carrier)
    (y : N.componentOpen (e.continuous.connectedComponentsMap C)) :
    ((diffeomorphComponent e C).symm y).val = e.symm y.val := rfl

theorem diffeomorphComponent_mfderiv
    (e : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier)
    (C : ConnectedComponents M.Carrier) (x : M.componentOpen C) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (diffeomorphComponent e C) x =
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x.val := by
  rw [← DifferentialGeometry.mfderiv_subtypeVal_comp
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))]
  exact DifferentialGeometry.mfderiv_restrict_open e (M.componentOpen C) x

end DifferentialGeometry.Topology.ClosedOrientedManifold
