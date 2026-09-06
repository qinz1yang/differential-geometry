import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

open Set

section

variable {Z F : Type*} [TopologicalSpace Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Z → F →L[ℝ] F →L[ℝ] ℝ} {K : Set Z}

theorem ContinuousOn.exists_uniform_bilin_quadratic_lower_bound
    (hB : ContinuousOn (fun p : Z × F => B p.1 p.2 p.2) (K ×ˢ (univ : Set F)))
    (hK : IsCompact K) (hpos : ∀ x ∈ K, ∀ v : F, v ≠ 0 → 0 < B x v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : F, c * ‖v‖ ^ 2 ≤ B x v v := by
  have hcpt := hK.prod (isCompact_sphere (0 : F) 1)
  have hc : ContinuousOn (fun p : Z × F => B p.1 p.2 p.2)
      (K ×ˢ Metric.sphere (0 : F) 1) :=
    hB.mono (prod_mono Subset.rfl (subset_univ _))
  have hp : ∀ p ∈ K ×ˢ Metric.sphere (0 : F) 1, 0 < B p.1 p.2 p.2 := by
    intro p hp
    apply hpos p.1 hp.1 p.2
    intro hzero
    have hn := hp.2
    rw [hzero, Metric.mem_sphere, dist_self] at hn
    exact zero_ne_one hn
  obtain ⟨c, hcpos, hcbound⟩ := hcpt.exists_forall_le' hc hp
  refine ⟨c, hcpos, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · subst v
    simp
  · have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : F) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_norm, inv_mul_cancel₀ hvnorm]
    have hbound := hcbound (x, ‖v‖⁻¹ • v) ⟨hx, hu⟩
    calc
      c * ‖v‖ ^ 2 ≤ B x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hbound (sq_nonneg ‖v‖)
      _ = B x v v := by
        simp only [map_smul, smul_apply, smul_eq_mul]
        field_simp

omit [TopologicalSpace Z] in
theorem ContinuousLinearMap.isCoercive_of_posDef
    (B : F →L[ℝ] F →L[ℝ] ℝ) (hpos : ∀ v : F, v ≠ 0 → 0 < B v v) :
    IsCoercive B := by
  have hc : ContinuousOn (fun p : Unit × F => B p.2 p.2)
      ((univ : Set Unit) ×ˢ (univ : Set F)) :=
    ((B.continuous.comp continuous_snd).clm_apply continuous_snd).continuousOn
  obtain ⟨c, hcpos, hbound⟩ := hc.exists_uniform_bilin_quadratic_lower_bound
    isCompact_univ (fun _ _ v hv => hpos v hv)
  refine ⟨c, hcpos, ?_⟩
  intro v
  simpa only [pow_two, mul_assoc] using hbound () (mem_univ _) v

end

theorem IsCoercive.isBounded_le
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hB : IsCoercive B) (r : ℝ) :
    Bornology.IsBounded {v : F | B v v ≤ r} := by
  obtain ⟨c, hcpos, hbound⟩ := hB
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max (r / c) 1 + 1, ?_⟩
  intro v hv
  change B v v ≤ r at hv
  have hn : ‖v‖ ^ 2 ≤ r / c := by
    apply (le_div_iff₀ hcpos).mpr
    nlinarith [hbound v]
  have hr := le_max_left (r / c) 1
  have hone := le_max_right (r / c) 1
  nlinarith [sq_nonneg (‖v‖ - 1)]
