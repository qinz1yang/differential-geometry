# AC63 independent review and compiled shortening tests

Ten public theorems in seven leaves add seventeen owned declarations, including
seven generated declarations. The308-module gate checks1388 owned declarations
in3143 jobs. All transitive axiom closures are standard: propext, Classical.choice,
Quot.sound. Source-copy unusedArguments/simpNF/synTaut lint is silent. The review
compiles without warnings and prints22 standard axiom reports, including all ten
new public theorems. Declaration kinds were inspected; defLemma is unavailable.
Earlier math leaves are unchanged. The inherited AreaUpperBarrier warning lies
outside these closures. Static blueprint audit passes; no full migrated root,
fresh PDF/Overleaf build or human approval is claimed.

Independent source and proof review checked curvature -kappa versus the
blueprint lambda=sqrt(kappa), actual radial/tail distances, degenerate triangles,
logarithmic shifts of either sign, clipping at zero and the order of limits.
The scalar ratio is exact with q>0,B>0. The finite angle theorem derives q<=1
and positive q from its original angle bounds; it does not assume a positive
unclipped expression. The limit theorem imposes no restrictions on early terms.
The liminf conclusion concerns actual shortened model angles and uses their
universal upper bound to supply the required coboundedness.

The independent concrete driver checks real p2,a5,b-1, shortened points3,1,
kappa4,L3,r1; zero-angle/degenerate half-angle formulas; and a nontrivial model
side with angle pi/3 whose permitted shortened side is zero. It proves that
clipping remains valid in this case. The explicit B1/4,q1/2 example has a
negative logarithmic shift and negative unclipped lower bound. A varying-angle
sequence checks convergence to pi/2.

Root added original reciprocal-scale tests sigma_i=(10+pi)/(i+1), C1024.
The first sigma is greater than one and its input angle is negative, yet both
the normalized radius and the actual clipped lower-angle sequence have their
claimed limits. A final test applies the actual liminf theorem to long equal
arms L_i=2(i+1), model side c_i of angle pi/2 in curvature-1, and shortened
side max(0,c_i-2(i+1)) at radius i+1. All side and tail conditions are proved
from the model-side API; the shortened-angle liminf is at least pi/2.

AC63 is complete. The coarse256r<L comparison adapter and supplied original
radial-segment extraction remain separate subsequent milestones. These must
retain the SAME segments, approximation maps and limiting lines for AC65/66.
The sharp8r theorem is not claimed. Blueprint207/migration interfaces remain
unchanged; Chapters3-4 and compatibility are unfinished.

```lean
import Mathlib.Tactic
import DifferentialGeometry.Geometry.Comparison.ModelSide
import DifferentialGeometry.Geometry.Comparison.ModelHalfAngleSine
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.HyperbolicShiftRatio
import DifferentialGeometry.Geometry.Comparison.ModelAngleShortening
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.ShortenedAngleLimit
import DifferentialGeometry.Geometry.Comparison.RadialAngleShortening
import DifferentialGeometry.Analysis.Asymptotics.ReciprocalShortening
import DifferentialGeometry.Geometry.Comparison.ShorteningAngleLimit

namespace GCAC63Review

open DifferentialGeometry.Geometry.Comparison.Toponogov Set Filter
open scoped Topology

private noncomputable def bound (θ B : ℝ) : ℝ := 2 * Real.arcsin
  (max 0 (Real.sin (θ / 2) - ((Real.sin (θ / 2))⁻¹ - Real.sin (θ / 2)) /
    (Real.exp (2 * B) - 1)))

private theorem real_opposite_shortening :
    bound Real.pi 2 ≤ comparisonAngleNegCurvature 4 1 1 2 := by
  have hang : Real.pi ≤ comparisonAngleNegCurvature 4 (dist (2 : ℝ) 5) (dist (2 : ℝ) (-1))
      (dist (5 : ℝ) (-1)) := by
    norm_num [Real.dist_eq]
    simpa only [show (3 : ℝ) + 3 = 6 by norm_num] using
      (comparisonAngleNegCurvature_add (κ := 4) (a := 3) (b := 3)
        (by norm_num) (by norm_num) (by norm_num)).ge
  have hh := comparison_angle_lower_bound_of_radial_shortening
    (p := (2 : ℝ)) (a := 5) (b := -1) (ar := 3) (br := 1) (κ := 4) (L := 3) (r := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
    (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq])
    (by norm_num [Real.dist_eq]) (by norm_num [Real.dist_eq]) Real.pi_pos hang
  norm_num [bound, Real.dist_eq] at hh ⊢
  exact hh

private theorem zero_angle_identity :
    Real.sinh (Real.sqrt 1 * 0 / 2) = Real.sinh (Real.sqrt 1 * 1) *
      Real.sin (comparisonAngleNegCurvature 1 1 1 0 / 2) :=
  sinh_half_eq_mul_sin_comparison_half (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem zero_angle_lower_bound :
    Real.sin (0 / 2) * Real.sinh (Real.sqrt 1 * 1) ≤ Real.sinh (Real.sqrt 1 * 0 / 2) := by
  apply sin_half_mul_sinh_le_of_comparison_angle_lower_bound
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (comparisonAngleNegCurvature_mem_Icc 1 1 1 0).1

private noncomputable def c : ℝ := modelSideNegCurvature 1 1 1 (Real.pi / 3)
private noncomputable def r : ℝ := (2 - c) / 4

private theorem theta_mem : Real.pi / 3 ∈ Icc (0 : ℝ) Real.pi := by
  constructor <;> linarith [Real.pi_pos]

private theorem c_nonneg : 0 ≤ c := modelSideNegCurvature_nonneg (by norm_num) (by norm_num)

private theorem c_angle : comparisonAngleNegCurvature 1 1 1 c = Real.pi / 3 :=
  comparisonAngleNegCurvature_modelSide (by norm_num) (by norm_num) (by norm_num) theta_mem

private theorem c_lt_two : c < 2 := by
  have hc2 : c ≤ 2 := by
    simpa only [c, show (1 : ℝ) + 1 = 2 by norm_num] using
      (modelSideNegCurvature_mem_Icc (κ := 1) (a := 1) (b := 1)
        (by norm_num) (by norm_num) (by norm_num) theta_mem).2
  have hne : c ≠ 2 := by
    intro he
    have hh := c_angle
    rw [he] at hh
    have hpi : comparisonAngleNegCurvature 1 1 1 2 = Real.pi := by
      simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
        comparisonAngleNegCurvature_add (κ := 1) (a := 1) (b := 1)
          (by norm_num) (by norm_num) (by norm_num)
    rw [hpi] at hh
    linarith [Real.pi_pos]
  exact lt_of_le_of_ne hc2 hne

private theorem r_pos : 0 < r := by dsimp [r]; linarith [c_lt_two]
private theorem r_le_one : r ≤ 1 := by dsimp [r]; linarith [c_nonneg]

private theorem model_side_shortened_degenerate :
    Real.sin (Real.pi / 3 / 2) -
      ((Real.sin (Real.pi / 3 / 2))⁻¹ - Real.sin (Real.pi / 3 / 2)) /
        (Real.exp (2 * (Real.sqrt 1 * r)) - 1) ≤
      Real.sin (comparisonAngleNegCurvature 1 r r 0 / 2) := by
  apply sin_half_comparison_angle_lower_bound_of_shortening (κ := 1) (L := 1) (c := c)
    (by norm_num) r_pos r_le_one c_nonneg (by simpa only [mul_one] using c_lt_two.le) (by norm_num) (by linarith [r_pos])
  · dsimp [r]
    linarith [c_lt_two]
  · linarith [Real.pi_pos]
  · exact c_angle.ge

private theorem actual_shortened_angle_zero : comparisonAngleNegCurvature 1 r r 0 = 0 :=
  comparisonAngleNegCurvature_self (by norm_num) r_pos

private theorem model_side_shortened_clamped : bound (Real.pi / 3) (Real.sqrt 1 * r) ≤ 0 := by
  have hh := model_side_shortened_degenerate
  rw [actual_shortened_angle_zero] at hh
  have hzero := Real.two_arcsin_max_le_of_le_sin_half (θ := 0)
    (by norm_num) Real.pi_pos.le hh
  exact hzero

private theorem negative_log_shift : (1 / 4 : ℝ) + Real.log (1 / 2) < 0 := by
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  linarith

private theorem negative_unclamped_bound :
    (1 / 2 : ℝ) - ((1 / 2 : ℝ)⁻¹ - 1 / 2) / (Real.exp (2 * (1 / 4)) - 1) < 0 := by
  rw [← Real.sinh_add_log_div_sinh (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (0 : ℝ) < 1 / 2)]
  exact div_neg_of_neg_of_pos (Real.sinh_neg_iff.mpr negative_log_shift)
    (Real.sinh_pos_iff.mpr (by norm_num))

private theorem fixed_angle_interior : (0 : ℝ) < Real.pi / 3 ∧ Real.pi / 3 < Real.pi := by
  constructor <;> linarith [Real.pi_pos]

private theorem varying_angle_limit :
    Tendsto (fun i : ℕ => bound (Real.pi / 2 - 1 / ((i : ℝ) + 1)) ((i : ℝ) + 1))
      atTop (𝓝 (Real.pi / 2)) := by
  have hθ : Tendsto (fun i : ℕ => Real.pi / 2 - 1 / ((i : ℝ) + 1))
      atTop (𝓝 (Real.pi / 2)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hB : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  exact Real.tendsto_shortened_angle_lower_bound
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hθ hB

#print axioms real_opposite_shortening
#print axioms zero_angle_identity
#print axioms zero_angle_lower_bound
#print axioms model_side_shortened_degenerate
#print axioms model_side_shortened_clamped
#print axioms negative_log_shift
#print axioms negative_unclamped_bound
#print axioms varying_angle_limit

end GCAC63Review


namespace GCAC63ReciprocalReview
open DifferentialGeometry.Geometry.Comparison.Toponogov Set Filter
open scoped Topology
private noncomputable def sigma (i : ℕ) : ℝ := (10 + Real.pi) / ((i : ℝ) + 1)
private theorem sigma_pos (i : ℕ) : 0 < sigma i := by dsimp [sigma]; positivity
private theorem sigma_limit : Tendsto sigma atTop (𝓝 0) := by
  change Tendsto (fun i : ℕ => (10 + Real.pi) / ((i : ℝ) + 1)) atTop (𝓝 0)
  simpa only [mul_one_div, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (10 + Real.pi)
private theorem normalized_radius_limit :
    Tendsto (fun i => Real.sqrt (sigma i) * ((sigma i)⁻¹ / 1024)) atTop atTop :=
  Real.tendsto_sqrt_mul_reciprocal_div_atTop (by norm_num) sigma_pos sigma_limit
private theorem reciprocal_angle_limit :
    Tendsto (fun i => 2 * Real.arcsin (max 0 (Real.sin ((Real.pi / 2 - sigma i) / 2) -
      ((Real.sin ((Real.pi / 2 - sigma i) / 2))⁻¹ - Real.sin ((Real.pi / 2 - sigma i) / 2)) /
        (Real.exp (2 * (Real.sqrt (sigma i) * ((sigma i)⁻¹ / 1024))) - 1))))
      atTop (𝓝 (Real.pi / 2)) :=
  Real.tendsto_reciprocal_shortened_angle_lower_bound (by norm_num) sigma_pos sigma_limit
private theorem initial_angle_negative : 1 < sigma 0 ∧ Real.pi / 2 - sigma 0 < 0 := by
  norm_num only [sigma, Nat.cast_zero, zero_add, div_one]
  constructor <;> linarith [Real.pi_pos]
private def rad (i : ℕ) : ℝ := (i : ℝ) + 1
private noncomputable def longSide (i : ℕ) : ℝ :=
  modelSideNegCurvature 1 (2 * rad i) (2 * rad i) (Real.pi / 2)
private noncomputable def shortSide (i : ℕ) : ℝ := max 0 (longSide i - 2 * rad i)
private theorem rad_pos (i : ℕ) : 0 < rad i := by dsimp [rad]; positivity
private theorem theta_mem : Real.pi / 2 ∈ Icc (0 : ℝ) Real.pi := by
  constructor <;> linarith [Real.pi_pos]
private theorem long_bounds (i : ℕ) : 0 ≤ longSide i ∧ longSide i ≤ 4 * rad i := by
  constructor
  · exact modelSideNegCurvature_nonneg (by linarith [rad_pos i]) (by linarith [rad_pos i])
  · have hh := (modelSideNegCurvature_mem_Icc (κ := 1) (a := 2 * rad i) (b := 2 * rad i)
      (by norm_num) (by linarith [rad_pos i]) (by linarith [rad_pos i]) theta_mem).2
    dsimp [longSide]
    linarith
private theorem actual_shortened_angle_liminf :
    Real.pi / 2 ≤ liminf (fun i => comparisonAngleNegCurvature 1 (rad i) (rad i) (shortSide i)) atTop := by
  apply le_liminf_comparison_angle_of_shortening (L := fun i => 2 * rad i)
    (c := longSide) (θ := fun _ => Real.pi / 2)
  · intro i; norm_num
  · exact rad_pos
  · intro i; linarith [rad_pos i]
  · intro i; exact (long_bounds i).1
  · intro i; linarith [(long_bounds i).2]
  · intro i; exact le_max_left _ _
  · intro i; apply max_le (by linarith [rad_pos i]); linarith [(long_bounds i).2]
  · intro i
    have h := le_max_right (0 : ℝ) (longSide i - 2 * rad i)
    dsimp [shortSide]
    linarith
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]
  · exact tendsto_const_nhds
  · simpa only [Real.sqrt_one, one_mul, rad] using
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  · exact Eventually.of_forall fun i =>
      (comparisonAngleNegCurvature_modelSide (κ := 1)
        (by norm_num) (by linarith [rad_pos i]) (by linarith [rad_pos i]) theta_mem).ge
#print axioms normalized_radius_limit
#print axioms reciprocal_angle_limit
#print axioms initial_angle_negative
#print axioms actual_shortened_angle_liminf
end GCAC63ReciprocalReview

#lint- only unusedArguments simpNF synTaut
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.sinh_half_eq_mul_sin_comparison_half
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.sin_half_mul_sinh_le_of_comparison_angle_lower_bound
#print axioms Real.sinh_add_log_div_sinh
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.sin_half_comparison_angle_lower_bound_of_shortening
#print axioms Real.two_arcsin_max_le_of_le_sin_half
#print axioms Real.tendsto_shortened_angle_lower_bound
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_angle_lower_bound_of_radial_shortening
#print axioms Real.tendsto_sqrt_mul_reciprocal_div_atTop
#print axioms Real.tendsto_reciprocal_shortened_angle_lower_bound
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.le_liminf_comparison_angle_of_shortening
```
