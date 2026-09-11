import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false
noncomputable section
open Set ContinuousMap
namespace DifferentialGeometry.HomotopyEquiv
variable (X : Type*) [TopologicalSpace X]
  {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E] {s : Set E}


def productConvex (hs : Convex ℝ s) (c : s) : (X × s) ≃ₕ X where
  toFun := ⟨Prod.fst, continuous_fst⟩
  invFun := (ContinuousMap.id X).prodMk (ContinuousMap.const X c)
  left_inv := ⟨{
    toFun := fun p => (p.2.1, ⟨(1 - (p.1 : ℝ)) • c.val + (p.1 : ℝ) • p.2.2.val,
      hs c.property p.2.2.property (sub_nonneg.mpr p.1.property.2)
        p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ))⟩)
    continuous_toFun := by fun_prop
    map_zero_left := by intro p; ext <;> simp
    map_one_left := by intro p; ext <;> simp }⟩
  right_inv := ContinuousMap.Homotopic.refl _


@[simp]
theorem productConvex_apply (hs : Convex ℝ s) (c : s) (p : X × s) :
    productConvex X hs c p = p.1 := rfl


@[simp]
theorem productConvex_symm_apply (hs : Convex ℝ s) (c : s) (x : X) :
    (productConvex X hs c).symm x = (x, c) := rfl

end DifferentialGeometry.HomotopyEquiv
