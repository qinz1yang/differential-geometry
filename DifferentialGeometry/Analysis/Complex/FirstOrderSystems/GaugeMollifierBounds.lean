import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory Function
open scoped Topology ContDiff Convolution
namespace DifferentialGeometry.Analysis
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- The actual operator norm near the identity controls the inverse, without
assuming a differentiable gauge. This includes a trivial target space. -/
theorem isUnit_and_norm_inverse_le_of_norm_sub_one_le
    (T : V →L[ℂ] V) {δ : ℝ} (hδ : δ < 1) (hnear : ‖T - 1‖ ≤ δ) :
    IsUnit T ∧ ‖Ring.inverse T‖ ≤ 1 / (1 - δ) := by
  have hu : IsUnit T := by
    have hn : ‖1 - T‖ < 1 := by rw [norm_sub_rev]; exact hnear.trans_lt hδ
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hn
  have hid : Ring.inverse T = 1 + Ring.inverse T * (1 - T) := by
    rw [mul_sub, mul_one, Ring.inverse_mul_cancel _ hu]
    abel
  have hn : ‖Ring.inverse T‖ ≤ 1 + ‖Ring.inverse T‖ * δ := by
    calc
      _ = ‖1 + Ring.inverse T * (1 - T)‖ := congrArg norm hid
      _ ≤ ‖(1 : V →L[ℂ] V)‖ + ‖Ring.inverse T * (1 - T)‖ := norm_add_le _ _
      _ ≤ 1 + ‖Ring.inverse T‖ * δ := by
        apply add_le_add ContinuousLinearMap.norm_id_le
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
          (by simpa only [norm_sub_rev] using hnear) (norm_nonneg _))
  refine ⟨hu, (le_div_iff₀ (by linarith : 0 < 1 - δ)).mpr ?_⟩
  nlinarith

/-- A positive normalized bump preserves the same near-identity bound on a
buffered disk. The convolution uses the original ambient representative. -/
theorem normed_bump_gauge_near_identity
    {P : ℂ → V →L[ℂ] V} (hP : AEStronglyMeasurable P volume)
    {a : ℂ} {R r δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ z ∈ closedBall a R, ‖P z - 1‖ ≤ δ)
    (ρ : ContDiffBump (0 : ℂ)) (hbuffer : r + ρ.rOut ≤ R)
    {z : ℂ} (hz : z ∈ closedBall a r) :
    ‖(ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] P) z - 1‖ ≤ δ := by
  have hlocal : ∀ y ∈ ball z ρ.rOut, dist (P y) 1 ≤ δ := by
    intro y hy
    have hyR : y ∈ closedBall a R := by
      change dist y a ≤ R
      have hyz : dist y z < ρ.rOut := hy
      have hza : dist z a ≤ r := hz
      exact (dist_triangle y z a).trans (by linarith)
    simpa only [dist_eq_norm] using hnear y hyR
  simpa only [dist_eq_norm] using
    dist_convolution_le hδ ρ.support_normed_eq.subset ρ.nonneg_normed
      ρ.integral_normed hP hlocal

end DifferentialGeometry.Analysis
