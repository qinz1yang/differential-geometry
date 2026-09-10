import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def ballRadialFunction (p : E) (R : ℝ) (u : E) : ℝ :=
  -⟪p, u⟫_ℝ + Real.sqrt (⟪p, u⟫_ℝ ^ 2 + (R ^ 2 - ‖p‖ ^ 2))

private theorem positive_quadratic_root {a b : ℝ} (hb : 0 < b) :
    0 < -a + Real.sqrt (a ^ 2 + b) ∧
      0 < a + Real.sqrt (a ^ 2 + b) ∧
      (-a + Real.sqrt (a ^ 2 + b)) ^ 2 +
        2 * a * (-a + Real.sqrt (a ^ 2 + b)) = b := by
  have harg : 0 ≤ a ^ 2 + b := by positivity
  have habs : |a| < Real.sqrt (a ^ 2 + b) := by
    rw [← Real.sqrt_sq_eq_abs a]
    exact Real.sqrt_lt_sqrt (sq_nonneg a) (by linarith)
  refine ⟨by linarith [le_abs_self a], by linarith [neg_le_abs a], ?_⟩
  nlinarith [Real.sq_sqrt harg]

private theorem quadratic_le_iff_le_root {a b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    t ^ 2 + 2 * a * t ≤ b ↔ t ≤ -a + Real.sqrt (a ^ 2 + b) := by
  obtain ⟨_, hplus, heq⟩ := positive_quadratic_root (a := a) hb
  have hfactor : 0 < t + a + Real.sqrt (a ^ 2 + b) := by linarith
  have hid : t ^ 2 + 2 * a * t - b =
      (t - (-a + Real.sqrt (a ^ 2 + b))) * (t + a + Real.sqrt (a ^ 2 + b)) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ a ^ 2 + b by positivity)]
  rw [← sub_nonpos, hid, mul_nonpos_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact False.elim (hfactor.not_ge h)
    · exact sub_nonpos.mp h
  · intro h
    exact Or.inr ⟨sub_nonpos.mpr h, hfactor.le⟩

theorem ballRadialFunction_pos {p : E} {R : ℝ} (hp : ‖p‖ < R) (u : E) :
    0 < ballRadialFunction p R u := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg p) hp
  exact (positive_quadratic_root (a := ⟪p, u⟫_ℝ)
    (show 0 < R ^ 2 - ‖p‖ ^ 2 by nlinarith [norm_nonneg p])).1

theorem contDiff_ballRadialFunction {p : E} {R : ℝ} (hp : ‖p‖ < R) :
    ContDiff ℝ ∞ (ballRadialFunction p R) := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg p) hp
  have hb : 0 < R ^ 2 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  have hi : ContDiff ℝ ∞ (fun u : E ↦ ⟪p, u⟫_ℝ) := contDiff_const.inner ℝ contDiff_id
  exact hi.neg.add (((hi.pow 2).add contDiff_const).sqrt
    (fun u ↦ ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hb)))

theorem smul_add_mem_closedBall_iff {p u : E} {R t : ℝ}
    (hp : ‖p‖ < R) (hu : ‖u‖ = 1) (ht : 0 ≤ t) :
    t • u + p ∈ closedBall 0 R ↔ t ≤ ballRadialFunction p R u := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg p) hp
  have hb : 0 < R ^ 2 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  have heq : ‖t • u + p‖ ^ 2 = t ^ 2 + 2 * ⟪p, u⟫_ℝ * t + ‖p‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hu, mul_one,
      real_inner_smul_left, real_inner_comm u p]
    ring
  rw [mem_closedBall_zero_iff, ← sq_le_sq₀ (norm_nonneg _) hR.le, heq]
  change t ^ 2 + 2 * ⟪p, u⟫_ℝ * t + ‖p‖ ^ 2 ≤ R ^ 2 ↔ _
  rw [← le_sub_iff_add_le]
  exact quadratic_le_iff_le_root hb ht

theorem smul_add_mem_ball_iff {p u : E} {R t : ℝ}
    (hp : ‖p‖ < R) (hu : ‖u‖ = 1) (ht : 0 ≤ t) :
    t • u + p ∈ ball 0 R ↔ t < ballRadialFunction p R u := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg p) hp
  have hb : 0 < R ^ 2 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  obtain ⟨_, hplus, hroot⟩ := positive_quadratic_root (a := ⟪p, u⟫_ℝ) hb
  have hnorm : ‖t • u + p‖ ^ 2 = t ^ 2 + 2 * ⟪p, u⟫_ℝ * t + ‖p‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hu, mul_one,
      real_inner_smul_left, real_inner_comm u p]
    ring
  have hfactor : 0 < t + ⟪p, u⟫_ℝ + Real.sqrt (⟪p, u⟫_ℝ ^ 2 + (R ^ 2 - ‖p‖ ^ 2)) := by
    linarith
  have hid : ‖t • u + p‖ ^ 2 - R ^ 2 =
      (t - ballRadialFunction p R u) *
        (t + ⟪p, u⟫_ℝ + Real.sqrt (⟪p, u⟫_ℝ ^ 2 + (R ^ 2 - ‖p‖ ^ 2))) := by
    dsimp [ballRadialFunction]
    nlinarith [Real.sq_sqrt (show 0 ≤ ⟪p, u⟫_ℝ ^ 2 + (R ^ 2 - ‖p‖ ^ 2) by positivity)]
  rw [mem_ball_zero_iff, ← sq_lt_sq₀ (norm_nonneg _) hR.le, ← sub_neg, hid,
    mul_neg_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact False.elim (hfactor.not_ge h.le)
    · exact sub_neg.mp h
  · intro h
    exact Or.inr ⟨sub_neg.mpr h, hfactor⟩

end DifferentialGeometry.Analysis
