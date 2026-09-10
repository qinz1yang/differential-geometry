import Mathlib.Analysis.Normed.Module.Connected

open Set Metric

namespace DifferentialGeometry.Topology

theorem isPathConnected_compl_closedBall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hd : 1 < Module.rank ℝ E) (x : E) (r : ℝ) :
    IsPathConnected (closedBall x r)ᶜ := by
  by_cases hr : r < 0
  · rw [closedBall_eq_empty.mpr hr, compl_empty]
    exact isPathConnected_univ
  have hr₀ : 0 ≤ r := le_of_not_gt hr
  let F : E × ℝ → E := fun p ↦ x + p.2 • p.1
  have heq : F '' (sphere (0 : E) 1 ×ˢ Ioi r) = (closedBall x r)ᶜ := by
    apply Subset.antisymm
    · rintro _ ⟨⟨v, t⟩, ⟨hv, ht⟩, rfl⟩
      have ht₀ : 0 < t := hr₀.trans_lt ht
      have hvn : ‖v‖ = 1 := by simpa [mem_sphere_iff_norm] using hv
      simpa [F, mem_closedBall, dist_eq_norm, norm_smul, abs_of_pos ht₀, hvn] using ht
    · intro y hy
      have hnr : r < ‖y - x‖ := by simpa [mem_closedBall, dist_eq_norm] using hy
      have hn : 0 < ‖y - x‖ := hr₀.trans_lt hnr
      refine ⟨(‖y - x‖⁻¹ • (y - x), ‖y - x‖), ⟨?_, hnr⟩, ?_⟩
      · simp [mem_sphere_iff_norm, norm_smul, hn.ne']
      · dsimp only [F]
        rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
        exact add_sub_cancel _ _
  rw [← heq]
  exact ((isPathConnected_sphere hd (0 : E) zero_le_one).prod
    ((convex_Ioi r).isPathConnected ⟨r + 1, by simp⟩)).image (by fun_prop)

end DifferentialGeometry.Topology
