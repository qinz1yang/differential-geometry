import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open scoped Matrix

def dotProductLinearMap3 (a : Fin 3 → ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun x => a ⬝ᵥ x
    map_add' := by
      intro x y
      exact dotProduct_add a x y
    map_smul' := by
      intro c x
      exact dotProduct_smul c a x }

theorem crossProduct_contraction_kernel_eq_span
    {a : Fin 3 → ℝ} (ha : a ≠ 0) :
    (crossProduct a).ker = Submodule.span ℝ {a} := by
  apply le_antisymm
  · intro x hx
    have hax : a ⨯₃ x = 0 := LinearMap.mem_ker.mp hx
    have hxa : x ⨯₃ a = 0 := by
      rw [← cross_anticomm]
      simp [hax]
    have htriple := cross_cross_eq_smul_sub_smul a x a
    have hzero : (a ⬝ᵥ a) • x - (x ⬝ᵥ a) • a = 0 := by
      simpa [hax, hxa] using htriple.symm
    have hEq : (a ⬝ᵥ a) • x = (x ⬝ᵥ a) • a := sub_eq_zero.mp hzero
    have haa : a ⬝ᵥ a ≠ 0 := by
      intro haa
      exact ha (dotProduct_self_eq_zero.mp haa)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨(a ⬝ᵥ a)⁻¹ * (x ⬝ᵥ a), ?_⟩
    have hscaled : x = (a ⬝ᵥ a)⁻¹ • ((x ⬝ᵥ a) • a) := by
      calc
        x = (a ⬝ᵥ a)⁻¹ • ((a ⬝ᵥ a) • x) := (inv_smul_smul₀ haa x).symm
        _ = (a ⬝ᵥ a)⁻¹ • ((x ⬝ᵥ a) • a) := by rw [hEq]
    simpa [smul_smul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hscaled.symm
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (LinearMap.mem_ker.mpr (by
      simp [cross_self]))

theorem crossProduct_contraction_kernel_finrank
    {a : Fin 3 → ℝ} (ha : a ≠ 0) :
    Module.finrank ℝ (crossProduct a).ker = 1 := by
  rw [crossProduct_contraction_kernel_eq_span ha, finrank_span_singleton]
  exact ha

theorem crossProduct_contraction_range_le_dotProduct_kernel
    (a : Fin 3 → ℝ) :
    (crossProduct a).range ≤ (dotProductLinearMap3 a).ker := by
  rintro _ ⟨x, rfl⟩
  apply LinearMap.mem_ker.mpr
  exact dot_self_cross a x

theorem crossProduct_contraction_range_finrank
    {a : Fin 3 → ℝ} (ha : a ≠ 0) :
    Module.finrank ℝ (crossProduct a).range = 2 := by
  have hdim := (crossProduct a).finrank_range_add_finrank_ker
  rw [crossProduct_contraction_kernel_finrank ha] at hdim
  have hsource : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by
    simp
  rw [hsource] at hdim
  omega

end DifferentialGeometry.Geometry.Curvature.DimensionThree
