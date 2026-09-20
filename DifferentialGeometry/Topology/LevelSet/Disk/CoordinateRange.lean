import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

section

noncomputable section
open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem mapsTo_Ioo_of_noncritical_coordinate_boundary
    {R : ℝ} {v : V → ℝ} (hc : ContinuousOn v (Metric.closedBall (0 : V) R)) (j : Fin d)
    (hbd : ∀ x ∈ Metric.sphere (0 : V) R, v x = x j)
    (hn : ∀ x ∈ Metric.ball (0 : V) R, fderiv ℝ v x ≠ 0) :
    MapsTo v (Metric.ball (0 : V) R) (Ioo (-R) R) := by
  have hupper {f : V → ℝ} (hfc : ContinuousOn f (Metric.closedBall (0 : V) R))
      (hfb : ∀ x ∈ Metric.sphere (0 : V) R, f x ≤ R)
      (hfn : ∀ x ∈ Metric.ball (0 : V) R, fderiv ℝ f x ≠ 0) :
      ∀ x ∈ Metric.ball (0 : V) R, f x < R := by
    intro x hx
    obtain ⟨y, hy, hm⟩ := (isCompact_closedBall (0 : V) R).exists_isMaxOn
      ⟨x, Metric.ball_subset_closedBall hx⟩ hfc
    have hyn : y ∉ Metric.ball (0 : V) R := by
      intro hyb
      apply hfn y hyb
      exact (hm.isLocalMax (mem_of_superset (Metric.isOpen_ball.mem_nhds hyb)
        Metric.ball_subset_closedBall)).fderiv_eq_zero
    have hys : y ∈ Metric.sphere (0 : V) R := by
      rw [Metric.mem_sphere]
      exact le_antisymm hy (not_lt.mp hyn)
    have hle : f x ≤ R := (hm (Metric.ball_subset_closedBall hx)).trans (hfb y hys)
    apply lt_of_le_of_ne hle
    intro heq
    apply hfn x hx
    have hlocal : IsLocalMax f x := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
      have hmax := (hm (Metric.ball_subset_closedBall hz)).trans (hfb y hys)
      rwa [← heq] at hmax
    exact hlocal.fderiv_eq_zero
  have hu := hupper hc (fun x hx => by
    rw [hbd x hx]
    have he : ‖x‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
    exact (le_abs_self _).trans ((PiLp.norm_apply_le x j).trans_eq he)) hn
  have hl := hupper hc.neg (fun x hx => by
    change -v x ≤ R
    rw [hbd x hx]
    have he : ‖x‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
    exact (neg_le_abs _).trans ((PiLp.norm_apply_le x j).trans_eq he))
    (fun x hx => by rw [fderiv_neg]; exact neg_ne_zero.mpr (hn x hx))
  exact fun x hx => ⟨by have hh := hl x hx; change -v x < R at hh; linarith, hu x hx⟩

end DifferentialGeometry.Analysis

end

end
