import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Compactness.Compact

noncomputable section

open Filter Set
open scoped Topology

namespace SeminormFamily

variable {𝕜 P E : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace P]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_eventually_le_mul_norm
    (q : P → Seminorm 𝕜 E) {p₀ : P}
    (hq : ContinuousAt (fun p : P × E => q p.1 p.2) (p₀, 0)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ p in 𝓝 p₀, ∀ v, q p v ≤ C * ‖v‖ := by
  have hsmall : ∀ᶠ p : P × E in 𝓝 (p₀, 0), q p.1 p.2 < 1 :=
    hq.eventually_lt_const (by simp)
  rw [nhds_prod_eq, Filter.Eventually, Filter.mem_prod_iff] at hsmall
  obtain ⟨U, hU, V, hV, hUV⟩ := hsmall
  obtain ⟨ε, hεpos, hε⟩ := NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp hV
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hratio : 0 < ‖c‖ / ε := div_pos (zero_lt_one.trans hc) hεpos
  refine ⟨max 1 (‖c‖ / ε), le_max_left _ _, ?_⟩
  filter_upwards [hU] with p hp
  intro v
  have hqp : Continuous (q p) := by
    apply Seminorm.continuous (r := 1)
    filter_upwards [hV] with w hw
    exact (q p).mem_ball_zero.mpr (hUV (show (p, w) ∈ U ×ˢ V from ⟨hp, hw⟩))
  by_cases hvnorm : ‖v‖ = 0
  · rw [hvnorm, mul_zero, (q p).map_eq_zero_of_norm_eq_zero hqp hvnorm]
  have hvnorm' : (normSeminorm 𝕜 E) v ≠ 0 := hvnorm
  have hbound : q p v ≤ (‖c‖ / ε) * ‖v‖ := by
    apply (normSeminorm 𝕜 E).bound_of_shell (q p) hεpos hc (fun w hlower hupper => ?_) hvnorm'
    have hsmallw : q p w < 1 := hUV (show (p, w) ∈ U ×ˢ V from
      ⟨hp, hε (show ‖w‖ < ε from hupper)⟩)
    apply hsmallw.le.trans
    rwa [← div_le_iff₀' hratio, one_div_div]
  exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg v))

theorem exists_le_mul_norm_of_compact [CompactSpace P]
    (q : P → Seminorm 𝕜 E) (hq : Continuous (fun p : P × E => q p.1 p.2)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p v, q p v ≤ C * ‖v‖ := by
  have hsmall : ∀ᶠ v : E in 𝓝 0, ∀ p : P, q p v < 1 := by
    have h := (isCompact_univ : IsCompact (univ : Set P)).eventually_forall_of_forall_eventually
      (x₀ := (0 : E)) (P := fun v p => q p v < 1) (fun p _ => ?_)
    · exact h.mono fun v hv p => hv p (mem_univ p)
    · have hc := (hq.comp continuous_swap).continuousAt (x := (0, p))
      exact hc.eventually_lt_const (by simp)
  obtain ⟨ε, hεpos, hε⟩ := NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp hsmall
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hratio : 0 < ‖c‖ / ε := div_pos (zero_lt_one.trans hc) hεpos
  refine ⟨max 1 (‖c‖ / ε), le_max_left _ _, fun p v => ?_⟩
  have hqp : Continuous (q p) := hq.comp (continuous_const.prodMk continuous_id)
  by_cases hvnorm : ‖v‖ = 0
  · rw [hvnorm, mul_zero, (q p).map_eq_zero_of_norm_eq_zero hqp hvnorm]
  have hvnorm' : (normSeminorm 𝕜 E) v ≠ 0 := hvnorm
  have hbound : q p v ≤ (‖c‖ / ε) * ‖v‖ := by
    apply (normSeminorm 𝕜 E).bound_of_shell (q p) hεpos hc (fun w hlower hupper => ?_) hvnorm'
    apply (hε hupper p).le.trans
    rwa [← div_le_iff₀' hratio, one_div_div]
  exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg v))

end SeminormFamily
