import Mathlib.LinearAlgebra.Determinant

namespace AlternatingMap

theorem map_linearMap_eq_det_mul {R E ι : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [Finite ι] (b : Module.Basis ι R E) (α : E [⋀^ι]→ₗ[R] R)
    (f : E →ₗ[R] E) (v : ι → E) : α (f ∘ v) = LinearMap.det f * α v := by
  classical
  let _ := Fintype.ofFinite ι
  rw [α.eq_smul_basis_det b]
  simp only [smul_apply, smul_eq_mul, Module.Basis.det_comp]
  exact mul_left_comm _ _ _

end AlternatingMap
