import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology

namespace Metric

theorem exists_norm_sq_sphere_prod_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {U : Set (E × ℝ)} (hU : IsOpen U)
    (hS : sphere (0 : E) 1 ×ˢ {(0 : ℝ)} ⊆ U) :
    ∃ r ∈ Ioo (0 : ℝ) 1,
      {p : E × ℝ | |‖p.1‖ ^ 2 - 1| < r ∧ |p.2| < r} ⊆ U := by
  let S := sphere (0 : E) 1
  let T : (ℝ × ℝ) × E → E × ℝ := fun p => (Real.sqrt (1 + p.1.1) • p.2, p.1.2)
  have hT : Continuous T :=
    ((Real.continuous_sqrt.comp (continuous_const.add continuous_fst.fst)).smul
      continuous_snd).prodMk continuous_fst.snd
  have hnear : ∀ᶠ q : ℝ × ℝ in 𝓝 (0, 0), ∀ x ∈ S, T (q, x) ∈ U := by
    apply (isCompact_sphere (0 : E) 1).eventually_forall_of_forall_eventually
    intro x hx
    apply (hU.preimage hT).mem_nhds
    have hh : (x, (0 : ℝ)) ∈ U := hS ⟨hx, rfl⟩
    change (Real.sqrt (1 + (0 : ℝ)) • x, (0 : ℝ)) ∈ U
    simpa only [add_zero, Real.sqrt_one, one_smul] using hh
  obtain ⟨δ, hδ, hδsub⟩ := eventually_nhds_iff.mp hnear
  let r := min δ 1 / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := by dsimp [r]; have := min_le_left δ 1; linarith
  have hr1 : r < 1 := by dsimp [r]; have := min_le_right δ 1; linarith
  refine ⟨r, ⟨hr, hr1⟩, ?_⟩
  intro p hp
  have hn : 0 < ‖p.1‖ := by
    have hlow := (abs_lt.mp hp.1).1
    have hnonneg := norm_nonneg p.1
    nlinarith
  let x := ‖p.1‖⁻¹ • p.1
  have hx : x ∈ S := by
    rw [mem_sphere_zero_iff_norm]
    simp only [x, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  have hdist : dist (‖p.1‖ ^ 2 - 1, p.2) ((0 : ℝ), 0) < δ := by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
    exact ⟨hp.1.trans hrδ, hp.2.trans hrδ⟩
  have hTx : T ((‖p.1‖ ^ 2 - 1, p.2), x) = p := by
    change (Real.sqrt (1 + (‖p.1‖ ^ 2 - 1)) • (‖p.1‖⁻¹ • p.1), p.2) = p
    rw [show 1 + (‖p.1‖ ^ 2 - 1) = ‖p.1‖ ^ 2 by ring,
      Real.sqrt_sq (norm_nonneg _), smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  exact hTx ▸ hδsub hdist x hx

end Metric
