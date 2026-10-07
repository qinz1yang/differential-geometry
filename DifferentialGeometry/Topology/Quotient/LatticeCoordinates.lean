import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Topology.Instances.AddCircle.Defs

namespace Module.Basis

theorem sub_mem_span_int_iff_coe_repr_eq {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (b : Basis ι ℝ E) (x y : E) :
    x - y ∈ Submodule.span ℤ (Set.range b) ↔
      (fun i => (b.repr x i : AddCircle (1 : ℝ))) =
        (fun i => (b.repr y i : AddCircle (1 : ℝ))) := by
  rw [b.mem_span_iff_repr_mem ℤ, funext_iff]
  apply forall_congr'
  intro i
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  simp only [map_sub, Finsupp.sub_apply, Set.mem_range, zsmul_eq_mul, mul_one, eq_intCast]

end Module.Basis
