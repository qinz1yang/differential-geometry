import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Order.Compact

noncomputable section

open Set

namespace DifferentialGeometry

theorem exists_pos_mul_norm_sq_le_bilinear_of_isCompact
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set X} (hK : IsCompact K) (A : X → E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ContinuousOn A K)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < A x v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : E, c * ‖v‖ ^ 2 ≤ A x v v := by
  have hQ : ContinuousOn (fun p : X × E => A p.1 p.2 p.2)
      (K ×ˢ Metric.sphere (0 : E) 1) := by
    have hAf : ContinuousOn (fun p : X × E => A p.1)
        (K ×ˢ Metric.sphere (0 : E) 1) :=
      hA.comp continuousOn_fst (fun _ hp => hp.1)
    exact (hAf.clm_apply continuousOn_snd).clm_apply continuousOn_snd
  obtain ⟨c, hc, hbound⟩ :=
    (hK.prod (isCompact_sphere (0 : E) 1)).exists_forall_le' hQ (fun p hp => by
      apply hpos p.1 hp.1 p.2
      intro hv
      simpa [hv] using hp.2)
  refine ⟨c, hc, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · subst v
    simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hunit : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
      Real.norm_eq_abs, abs_of_pos hvpos, inv_mul_cancel₀ hvpos.ne']
  have hle := hbound (x, ‖v‖⁻¹ • v) ⟨hx, hunit⟩
  have hscale : A x v v = ‖v‖ ^ 2 * A x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    field_simp
  rw [hscale, mul_comm]
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg ‖v‖)

end DifferentialGeometry
