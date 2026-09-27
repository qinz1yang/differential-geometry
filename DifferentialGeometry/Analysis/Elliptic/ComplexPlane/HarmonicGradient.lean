import DifferentialGeometry.Analysis.Complex.LogarithmicGradient
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Shift

section

noncomputable section

open Set Metric InnerProductSpace Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem norm_gradient_le_of_harmonicOnNhd_ball
    {u : ℂ → ℝ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hu : HarmonicOnNhd u (ball c R))
    (hbound : ∀ z ∈ ball c R, |u z| ≤ M) :
    ‖gradient u c‖ ≤ 8 * M / R := by
  have hc : c ∈ ball c R := mem_ball_self hR
  have hM : 0 ≤ M := (abs_nonneg (u c)).trans (hbound c hc)
  rcases eq_or_lt_of_le hM with hMzero | hMpos
  · have hueq : u =ᶠ[𝓝 c] (fun _ => 0) := by
      filter_upwards [ball_mem_nhds c hR] with z hz
      have hh : |u z| ≤ 0 := by simpa [← hMzero] using hbound z hz
      exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    rw [hueq.gradient_eq]
    simp [← hMzero]
  obtain ⟨F, hF, hFu⟩ := hu.exists_analyticOnNhd_ball_re_eq
  let G : ℂ → ℂ := fun z => F (c + z) - F c
  have htranslate (z : ℂ) (hz : z ∈ ball 0 R) : c + z ∈ ball c R := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz
  have hG : DifferentiableOn ℂ G (ball 0 R) := by
    intro z hz
    exact (((hF (c + z) (htranslate z hz)).differentiableAt.comp z
      ((differentiableAt_const c).add differentiableAt_id)).sub_const (F c)).differentiableWithinAt
  have hGre : MapsTo G (ball 0 R) {z : ℂ | z.re ≤ 2 * M} := by
    intro z hz
    change (F (c + z)).re - (F c).re ≤ 2 * M
    have hez : (F (c + z)).re = u (c + z) := hFu (htranslate z hz)
    have hec : (F c).re = u c := hFu hc
    rw [hez, hec]
    have h1 := (abs_le.mp (hbound (c + z) (htranslate z hz))).2
    have h2 := (abs_le.mp (hbound c hc)).1
    linarith
  have hG0 : G 0 = 0 := by simp [G]
  have hGcirc (z : ℂ) (hz : z ∈ sphere 0 (R / 2)) : ‖G z‖ ≤ 4 * M := by
    have hzn : ‖z‖ = R / 2 := by simpa only [mem_sphere, dist_zero_right] using hz
    have hzB : z ∈ ball 0 R := by rw [mem_ball_zero_iff, hzn]; linarith
    have hh := Complex.borelCaratheodory_zero (by positivity : 0 < 2 * M)
      hG hGre hR hzB hG0
    rw [hzn] at hh
    have hconst : 2 * (2 * M) * (R / 2) / (R - R / 2) = 4 * M := by
      field_simp [hR.ne']
      ring
    rwa [hconst] at hh
  have hGderiv := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (half_pos hR) (hG.diffContOnCl_ball (closedBall_subset_ball (by linarith))) hGcirc
  have hdG : deriv G 0 = deriv F c := by
    dsimp only [G]
    rw [deriv_sub_const, deriv_comp_const_add, add_zero]
  rw [hdG] at hGderiv
  have hgrad : gradient u c = gradient (fun z => (F z).re) c :=
    (hFu.eventuallyEq_of_mem (ball_mem_nhds c hR)).gradient_eq.symm
  rw [hgrad, norm_gradient_re_eq_norm_deriv (hF c hc).differentiableAt]
  calc
    _ ≤ 4 * M / (R / 2) := hGderiv
    _ = 8 * M / R := by ring

end DifferentialGeometry.Analysis

end

end
