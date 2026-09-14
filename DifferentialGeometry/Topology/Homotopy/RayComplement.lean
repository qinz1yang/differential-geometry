import Mathlib.Analysis.Convex.Contractible

noncomputable section
open Set

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

theorem mem_compl_nonpositive_ray (v : E) (hv : v ≠ 0) :
    v ∈ {x : E | ¬ ∃ c : ℝ, 0 ≤ c ∧ x = -c • v} := by
  rintro ⟨c, hc, hcv⟩
  have heq : (1 + c) • v = 0 := by
    rw [add_smul, one_smul]
    conv_lhs => lhs; rw [hcv]
    rw [neg_smul, neg_add_cancel]
  have hcoef := (smul_eq_zero.mp heq).resolve_right hv
  linarith

theorem starConvex_compl_nonpositive_ray (v : E) (hv : v ≠ 0) :
    StarConvex ℝ v {x : E | ¬ ∃ c : ℝ, 0 ≤ c ∧ x = -c • v} := by
  intro y hy a b ha hb hab hbad
  apply hy
  obtain ⟨c, hc, hcy⟩ := hbad
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by simpa only [hb0, add_zero] using hab
    have hy' : v = -c • v := by simpa only [ha1, hb0, one_smul, zero_smul, add_zero] using hcy
    exact (mem_compl_nonpositive_ray v hv ⟨c, hc, hy'⟩).elim
  · refine ⟨(c + a) / b, div_nonneg (add_nonneg hc ha) hb, ?_⟩
    apply (smul_right_injective E hb0)
    have hscalar : b * (-((c + a) / b)) = -(c + a) := by field_simp
    change b • y = b • (-((c + a) / b) • v)
    rw [smul_smul, hscalar]
    apply add_left_cancel (a := a • v)
    rw [hcy, ← add_smul]
    congr 1
    ring

variable [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

theorem contractibleSpace_compl_nonpositive_ray (v : E) (hv : v ≠ 0) :
    ContractibleSpace {x : E | ¬ ∃ c : ℝ, 0 ≤ c ∧ x = -c • v} :=
  (starConvex_compl_nonpositive_ray v hv).contractibleSpace
    ⟨v, mem_compl_nonpositive_ray v hv⟩

end DifferentialGeometry.Topology
