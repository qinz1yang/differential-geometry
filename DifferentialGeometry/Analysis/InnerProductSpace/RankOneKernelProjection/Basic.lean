import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Symmetric


set_option autoImplicit false
noncomputable section

namespace LinearMap

open scoped RealInnerProductSpace

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]


theorem comp_self_eq_trace_smul_of_rank_one (A : V →ₗ[ℝ] V)
    (hr : Module.finrank ℝ (LinearMap.range A) = 1) :
    A.comp A = LinearMap.trace ℝ V A • A := by
  let R := LinearMap.range A
  let B : R →ₗ[ℝ] R := A.rangeRestrict.comp R.subtype
  obtain ⟨c, hc, _⟩ := B.existsUnique_eq_smul_id_of_finrank_eq_one hr
  have htrace : LinearMap.trace ℝ V A = c := by
    have hcyclic := LinearMap.trace_comp_comm' A.rangeRestrict R.subtype
    have hfactor : R.subtype.comp A.rangeRestrict = A := rfl
    rw [hfactor] at hcyclic
    change LinearMap.trace ℝ V A = LinearMap.trace ℝ R B at hcyclic
    rw [hcyclic, hc, _root_.map_smul, LinearMap.trace_id, hr, Nat.cast_one, smul_eq_mul, mul_one]
  rw [htrace]
  ext v
  have hv := congrArg (fun F : R →ₗ[ℝ] R => (F (A.rangeRestrict v) : V)) hc
  exact hv


def rankOneKernelProjection (A : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  LinearMap.id - (LinearMap.trace ℝ V A)⁻¹ • A

private theorem projection_mem_ker (A : V →ₗ[ℝ] V)
    (hr : Module.finrank ℝ (LinearMap.range A) = 1)
    (hτ : LinearMap.trace ℝ V A ≠ 0) (v : V) :
    rankOneKernelProjection A v ∈ LinearMap.ker A := by
  have hsq := congrArg (fun F : V →ₗ[ℝ] V => F v)
    (comp_self_eq_trace_smul_of_rank_one A hr)
  change A (A v) = LinearMap.trace ℝ V A • A v at hsq
  change A (v - (LinearMap.trace ℝ V A)⁻¹ • A v) = 0
  rw [_root_.map_sub, _root_.map_smul, hsq, smul_smul, inv_mul_cancel₀ hτ, one_smul, sub_self]

omit [FiniteDimensional ℝ V] in
private theorem projection_eq_self (A : V →ₗ[ℝ] V) {v : V}
    (hv : v ∈ LinearMap.ker A) : rankOneKernelProjection A v = v := by
  change v - (LinearMap.trace ℝ V A)⁻¹ • A v = v
  rw [LinearMap.mem_ker.mp hv, smul_zero, sub_zero]


theorem rankOneKernelProjection_idempotent_range (A : V →ₗ[ℝ] V)
    (hr : Module.finrank ℝ (LinearMap.range A) = 1)
    (hτ : LinearMap.trace ℝ V A ≠ 0) :
    (rankOneKernelProjection A).comp (rankOneKernelProjection A) =
        rankOneKernelProjection A ∧
      LinearMap.range (rankOneKernelProjection A) = LinearMap.ker A := by
  constructor
  · ext v
    exact projection_eq_self A (projection_mem_ker A hr hτ v)
  · apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact projection_mem_ker A hr hτ v
    · intro v hv
      exact ⟨v, projection_eq_self A hv⟩

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
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (projection_mem_ker A hr (trace_ne_zero_of_symmetric_rank_one A hA hr) v)
  intro w hw
  change ⟪v - (v - (LinearMap.trace ℝ E A)⁻¹ • A v), w⟫ = 0
  rw [sub_sub_cancel, real_inner_smul_left, hA v w, LinearMap.mem_ker.mp hw,
    inner_zero_right, mul_zero]

end InnerProduct
end LinearMap
