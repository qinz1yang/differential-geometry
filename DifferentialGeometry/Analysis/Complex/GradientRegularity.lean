import DifferentialGeometry.Analysis.Complex.SquareRoot
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

theorem contDiffOn_one_closure_of_sq_gradient_add_eq
    {s : Set ℂ} (hs : Convex ℝ s) (ho : IsOpen s)
    {f : ℂ → ℝ} {a q : ℂ → ℂ}
    (hf : ContinuousOn f (closure s)) (hd : ContDiffOn ℝ 1 f s)
    (ha : ContinuousOn a (closure s)) (hq : ContinuousOn q (closure s))
    (hsq : EqOn (fun y => (gradient f y + a y) ^ 2) q s) :
    ContDiffOn ℝ 1 f (closure s) := by
  have hD : ContinuousOn (fderiv ℝ f) s := by
    intro z hz
    exact ((hd z hz).contDiffAt (ho.mem_nhds hz)).continuousAt_fderiv (by norm_num) |>.continuousWithinAt
  have hg : ContinuousOn (fun y => gradient f y + a y) s :=
    ((toDual ℝ ℂ).symm.continuous.comp_continuousOn hD).add (ha.mono subset_closure)
  obtain ⟨v, hv, he, _⟩ := Complex.exists_continuousOn_extension_of_sq_eq hs hg hq hsq
  let D (z : ℂ) : ℂ →L[ℝ] ℝ := toDual ℝ ℂ (v z - a z)
  have hDc : ContinuousOn D (closure s) := (toDual ℝ ℂ).continuous.comp_continuousOn (hv.sub ha)
  have hDe : EqOn (fderiv ℝ f) D s := by
    intro z hz
    dsimp only [D]
    rw [he hz, add_sub_cancel_right]
    exact ((toDual ℝ ℂ).apply_symm_apply (fderiv ℝ f z)).symm
  have hhas (z : ℂ) (hz : z ∈ closure s) : HasFDerivWithinAt f (D z) (closure s) z := by
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (hd.differentiableOn (by norm_num)) hs ho
      (fun y hy => (hf y hy).mono subset_closure)
    have hh : Tendsto D (𝓝[s] z) (𝓝 (D z)) := (hDc z hz).mono subset_closure
    apply (tendsto_congr' (show fderiv ℝ f =ᶠ[𝓝[s] z] D from ?_)).mpr hh
    filter_upwards [self_mem_nhdsWithin] with y hy using hDe hy
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt (by simp : (0 : ℕ∞ω) ≠ ∞)]
  intro z hz
  refine ⟨closure s, ?_, by simp, D, hhas, contDiffOn_zero.mpr hDc⟩
  simpa only [insert_eq_of_mem hz] using (self_mem_nhdsWithin : closure s ∈ 𝓝[closure s] z)

end DifferentialGeometry.Analysis
