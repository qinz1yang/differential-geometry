import DifferentialGeometry.Tensor.LinearAlgebra.RankOneKernelProjection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Symmetric


set_option autoImplicit false
noncomputable section

namespace LinearMap

open scoped RealInnerProductSpace

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]


section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]


theorem trace_ne_zero_of_symmetric_rank_one (A : E →ₗ[ℝ] E)
    (hA : A.IsSymmetric) (hr : Module.finrank ℝ (LinearMap.range A) = 1) :
    LinearMap.trace ℝ E A ≠ 0 := by
  intro hτ
  have hsq : A.comp A = 0 := by
    rw [comp_self_eq_trace_smul_of_rank_one A hr, hτ, zero_smul]
  have hzero : A = 0 := by
    ext v
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [hA v (A v)]
    have hv := congrArg (fun F : E →ₗ[ℝ] E => F v) hsq
    change A (A v) = 0 at hv
    rw [hv, inner_zero_right]
  subst A
  have hbottom : LinearMap.range (0 : E →ₗ[ℝ] E) = ⊥ := LinearMap.range_zero
  rw [hbottom, finrank_bot] at hr
  exact Nat.zero_ne_one hr


theorem rankOneKernelProjection_eq_starProjection (A : E →ₗ[ℝ] E)
    (hA : A.IsSymmetric) (hr : Module.finrank ℝ (LinearMap.range A) = 1) :
    rankOneKernelProjection A = (LinearMap.ker A).starProjection.toLinearMap := by
  ext v
  symm
  have hmem : rankOneKernelProjection A v ∈ LinearMap.ker A := by
    rw [← (rankOneKernelProjection_idempotent_range A hr
      (trace_ne_zero_of_symmetric_rank_one A hA hr)).2]
    exact ⟨v, rfl⟩
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
  intro w hw
  change ⟪v - (v - (LinearMap.trace ℝ E A)⁻¹ • A v), w⟫ = 0
  rw [sub_sub_cancel, real_inner_smul_left, hA v w, LinearMap.mem_ker.mp hw,
    inner_zero_right, mul_zero]

end InnerProduct
end LinearMap
