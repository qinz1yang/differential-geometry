# Independent buffered comparison and target-angle review

Four public theorems in three leaves add four owned declarations. The311-module
gate checks1392 owned declarations in3146 jobs. Every transitive closure uses
only propext, Classical.choice and Quot.sound. Source-copy unusedArguments,
simpNF and synTaut lint is silent; the accepted-import review prints14 standard
axiom reports and otherwise compiles silently. All four public theorem closures
are included. Declaration kinds were inspected; defLemma is unavailable. Earlier
mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is
outside these closures. Static audit passes. No full migrated root, new PDF or
Overleaf build, or human approval is claimed.

The buffered adapter was implemented by one agent and independently inspected
and tested by another. Both radial segments remain the exact supplied maps,
including unequal total lengths, through the IccExtend proof; the public statement
contains only their actual interval values. Only prefix points<=r enter the2r
comparison ball. The256r<L strict source buffer is retained. The target helper
was independently checked for absence of a splitting dependency: its accepted
crossing-line identities require only nonnegative comparison and the actual lines.
Root's finite bridge was independently inspected and tested by a different agent.

The concrete source test is the real line, with proved short affine curves,
actual comparison and ambientdim<=1. Original L=1024, r=1, forward segment
length2 and backward segment length3 test kappa4 and0 at times1/2 and3/4,
and endpoint times1,1. The target test uses the translated plane p=(3,-2),
the downward line and the rightward line. Its two actual comparison angles at
T=2 are proved from squared distances, then fed to the target theorem to obtain
germ angle pi/2 and Pythagoras for all signed times. A numeric consequence is
d(down(-3),right(4)) squared=25. Coincident lines fail the positive bound.

The bridge tests again prove all original real-line geometry. They apply the
full bridge with actual length1024 segments, kappa4, r1, T1/2, theta=pi.
A second case chooses r=log(2)/4, T=log(2)/8 and theta=pi/3. Its raw lower
expression is proved EXACTLY -1 and its logarithmic shift is proved negative.
The full bridge still yields the valid clipped lower bound0. No positivity of
the un-clipped expression or of the logarithmic shift is silently assumed.

These close the coarse-buffer and fixed-target comparison components of AC65.
The full same-original-radial-family extraction and limit passage remain to be
assembled. The old sharp8r AC64 statement is not claimed. Blueprint207 and PC
migration interfaces are unchanged; Chapters3-4 remain unfinished.

```lean
import DifferentialGeometry.Geometry.Comparison.RadialAngleShortening
import Mathlib.Tactic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.Normed.Affine.AddTorsor
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening
import Mathlib.Analysis.InnerProductSpace.PiL2
import DifferentialGeometry.Geometry.Comparison.VaryingLocalGeometry
import DifferentialGeometry.Geometry.Comparison.GermAngle
import DifferentialGeometry.Topology.MetricSpace.SegmentExtension
import DifferentialGeometry.Geometry.Comparison.CrossingLineCoordinates
import DifferentialGeometry.Geometry.Comparison.BufferedRadialComparison
import DifferentialGeometry.Geometry.Comparison.OppositeCrossAngles
import DifferentialGeometry.Geometry.Comparison.BufferedAngleShortening

open Set Metric Filter Topology
set_option autoImplicit false

namespace GCBufferedCrossAnglesReview

open Set Metric Filter Topology

open DifferentialGeometry.Geometry.Comparison.Toponogov
open InnerProductGeometry

private theorem comparison_eq_angle {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : V) : comparisonAngle ‖x‖ ‖y‖ ‖x - y‖ = angle x y := by
  rw [comparisonAngle, angle, norm_sub_pow_two_real]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem inner_comparison {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    fourPointComparison 0 (univ : Set V) := by
  intro p hp a ha b hb c hc hap hbp hcp
  simp only [comparisonAngleNegCurvature_zero]
  have he (x y : V) : comparisonAngle (dist p x) (dist p y) (dist x y) = angle (x - p) (y - p) := by
    rw [dist_comm p x, dist_comm p y]
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using comparison_eq_angle (x - p) (y - p)
  rw [he a b, he b c, he c a]
  have ht := angle_le_angle_add_angle (a - p) (-(b - p)) (c - p)
  rw [angle_neg_right, angle_neg_left, angle_comm (a - p) (c - p)] at ht
  linarith

private theorem inner_segments {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x y : V) :
    ∃ f : Icc (0 : ℝ) 1 → V,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  refine ⟨fun t => AffineMap.lineMap x y (t : ℝ), by fun_prop, ?_, ?_, ?_⟩
  · exact AffineMap.lineMap_apply_zero x y
  · exact AffineMap.lineMap_apply_one x y
  · intro s t
    rw [dist_lineMap_lineMap]
    exact mul_comm _ _

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def p : Plane := WithLp.toLp 2 ![3, -2]
private def down (t : ℝ) : Plane := WithLp.toLp 2 ![3, -2 - t]
private def right (t : ℝ) : Plane := WithLp.toLp 2 ![3 + t, -2]
private def γ (j : Fin 2) : ℝ → Plane := ![down, right] j

private theorem plane_dist_sq (x y : Plane) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private theorem down_isometry : Isometry down := by
  apply Isometry.of_dist_eq
  intro s t
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [plane_dist_sq]
  simp only [down, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.dist_eq, sq_abs]
  ring

private theorem right_isometry : Isometry right := by
  apply Isometry.of_dist_eq
  intro s t
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [plane_dist_sq]
  simp only [right, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.dist_eq, sq_abs]
  ring


private theorem real_curves : ∀ x y : ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → ℝ, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      eVariationOn c univ < ENNReal.ofReal (dist x y + ε) :=
  Metric.arbitrarily_short_curves_of_metric_segments inner_segments

private def forward : Icc (0 : ℝ) 2 → ℝ := Subtype.val
private def backward : Icc (0 : ℝ) 3 → ℝ := fun t => -t.val

private theorem forward_isometry : Isometry forward := isometry_subtype_coe
private theorem backward_isometry : Isometry backward := by
  apply Isometry.of_dist_eq
  intro s t
  exact dist_neg_neg s.val t.val

private theorem real_dim : dimH (ball (0 : ℝ) 1024) ≤ (1 : ENNReal) :=
  (dimH_mono (subset_univ _)).trans (by rw [Real.dimH_univ])

private theorem real_buffered {κ s t : ℝ} (hκ : 0 ≤ κ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    comparisonAngleNegCurvature κ 1 1 2 ≤ comparisonAngleNegCurvature κ s t (s + t) := by
  have hh := comparisonAngleNegCurvature_le_of_radial_isometries_in_local_buffer
    real_curves (0 : ℝ) (L := 1024) (r := 1) (A := 2) (B := 3) (n := 1)
    hκ (by norm_num) (by norm_num) (by simpa only [Nat.cast_one] using real_dim)
    (fun z _ => ⟨univ, isOpen_univ, inner_comparison.of_zero hκ, mem_univ z⟩)
    (by norm_num) (by norm_num) forward backward forward_isometry backward_isometry
    rfl (by norm_num [backward]) hs ht
  change comparisonAngleNegCurvature κ 1 1 (dist (1 : ℝ) (-1)) ≤
    comparisonAngleNegCurvature κ s t (dist s (-t)) at hh
  simp only [Real.dist_eq, sub_neg_eq_add] at hh
  rw [abs_of_pos (add_pos hs.1 ht.1)] at hh
  norm_num at hh
  exact hh

private theorem buffered_positive :
    comparisonAngleNegCurvature 4 1 1 2 ≤ comparisonAngleNegCurvature 4 (1 / 2) (3 / 4) (5 / 4) := by
  simpa only [show (1 / 2 : ℝ) + 3 / 4 = 5 / 4 by norm_num] using
    real_buffered (κ := 4) (s := 1 / 2) (t := 3 / 4) (by norm_num) (by norm_num) (by norm_num)

private theorem buffered_zero :
    comparisonAngleNegCurvature 0 1 1 2 ≤ comparisonAngleNegCurvature 0 (1 / 2) (3 / 4) (5 / 4) := by
  simpa only [show (1 / 2 : ℝ) + 3 / 4 = 5 / 4 by norm_num] using
    real_buffered (κ := 0) (s := 1 / 2) (t := 3 / 4) (by norm_num) (by norm_num) (by norm_num)

private theorem buffered_endpoints :
    comparisonAngleNegCurvature 1 1 1 2 ≤ comparisonAngleNegCurvature 1 1 1 2 := by
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
    real_buffered (κ := 1) (s := 1) (t := 1) (by norm_num) (by norm_num) (by norm_num)

private theorem plane_plus_bound :
    Real.pi / 2 ≤ comparisonAngle 2 2 (dist (down 2) (right 2)) := by
  rw [comparisonAngle, plane_dist_sq]
  norm_num [down, right]

private theorem plane_minus_bound :
    Real.pi / 2 ≤ comparisonAngle 2 2 (dist (down 2) (right (-2))) := by
  rw [comparisonAngle, plane_dist_sq]
  norm_num [down, right]

private theorem plane_fixed_radius_right_angle : germComparisonAngle 0 down right = Real.pi / 2 :=
  germComparisonAngle_eq_pi_div_two_of_opposite_cross_lower_bounds inner_comparison down_isometry
    right_isometry (by simp [down, right]) (by norm_num : (0 : ℝ) < 2) plane_plus_bound plane_minus_bound

private theorem plane_all_signed_pythagoras (s t : ℝ) :
    dist (down s) (right t) ^ 2 = s ^ 2 + t ^ 2 :=
  sq_dist_crossing_isometries_of_opposite_cross_lower_bounds inner_comparison down_isometry
    right_isometry (by simp [down, right]) (by norm_num : (0 : ℝ) < 2) plane_plus_bound plane_minus_bound s t

private theorem coincident_fails_bound :
    ¬Real.pi / 2 ≤ comparisonAngle 2 2 (dist (down 2) (down 2)) := by
  rw [dist_self, comparisonAngle]
  norm_num
  linarith [Real.pi_pos]

example : dist (down (-3)) (right 4) ^ 2 = 25 := by
  convert plane_all_signed_pythagoras (-3) 4 using 1
  norm_num


end GCBufferedCrossAnglesReview
namespace GCBufferedCrossAnglesReview

open DifferentialGeometry.Geometry.Comparison.Toponogov

private def longForward : Icc (0 : ℝ) 1024 → ℝ := Subtype.val
private def longBackward : Icc (0 : ℝ) 1024 → ℝ := fun t => -t.val

private theorem longForward_isometry : Isometry longForward := isometry_subtype_coe
private theorem longBackward_isometry : Isometry longBackward := by
  apply Isometry.of_dist_eq
  intro s t
  exact dist_neg_neg s.val t.val

private theorem real_opposite_bridge {r T θ : ℝ} (hr : 0 < r)
    (hbuffer : 256 * r < 1024) (hT : T ∈ Ioc (0 : ℝ) r)
    (hθ : 0 < θ) (hθpi : θ ≤ Real.pi) :
    2 * Real.arcsin (max 0 (Real.sin (θ / 2) -
      ((Real.sin (θ / 2))⁻¹ - Real.sin (θ / 2)) /
        (Real.exp (2 * (Real.sqrt 4 * r)) - 1))) ≤
      comparisonAngleNegCurvature 4 T T (2 * T) := by
  have hangle : θ ≤ comparisonAngleNegCurvature 4 1024 1024 (2048 : ℝ) := by
    rw [show (2048 : ℝ) = 1024 + 1024 by norm_num,
      comparisonAngleNegCurvature_add (by norm_num : (0 : ℝ) ≤ 4)
        (by norm_num : (0 : ℝ) < 1024) (by norm_num : (0 : ℝ) < 1024)]
    exact hθpi
  have hh := comparison_angle_lower_bound_at_fixed_time_of_long_radial_isometries
    real_curves (0 : ℝ) (κ := 4) (L := 1024) (r := r) (T := T) (θ := θ) (n := 1)
    (by norm_num) hr hbuffer (by simpa only [Nat.cast_one] using real_dim)
    (fun z _ => ⟨univ, isOpen_univ, inner_comparison.of_zero (by norm_num : (0 : ℝ) ≤ 4), mem_univ z⟩)
    longForward longBackward longForward_isometry longBackward_isometry rfl
    (by norm_num [longBackward]) hT hθ
    (by convert hangle using 1; norm_num [longForward, longBackward, Real.dist_eq])
  change _ ≤ comparisonAngleNegCurvature 4 T T (dist T (-T)) at hh
  rw [Real.dist_eq, sub_neg_eq_add, abs_of_pos (add_pos hT.1 hT.1)] at hh
  simpa only [two_mul] using hh

private theorem bridge_pi_at_half :
    Real.pi ≤ comparisonAngleNegCurvature 4 (1 / 2) (1 / 2) 1 := by
  have hh := real_opposite_bridge (r := 1) (T := 1 / 2) (θ := Real.pi)
    (by norm_num) (by norm_num) (by norm_num) Real.pi_pos le_rfl
  simpa only [Real.sin_pi_div_two, inv_one, sub_self, zero_div, sub_zero,
    max_eq_right zero_le_one, Real.arcsin_one, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    show (2 : ℝ) * (1 / 2) = 1 by norm_num] using hh

private theorem early_raw_bound_negative :
    Real.sin ((Real.pi / 3) / 2) -
      ((Real.sin ((Real.pi / 3) / 2))⁻¹ - Real.sin ((Real.pi / 3) / 2)) /
        (Real.exp (2 * (Real.sqrt 4 * (Real.log 2 / 4))) - 1) = -1 := by
  have hq : Real.sin ((Real.pi / 3) / 2) = 1 / 2 := by
    rw [show Real.pi / 3 / 2 = Real.pi / 6 by ring, Real.sin_pi_div_six]
  have he : 2 * (Real.sqrt 4 * (Real.log 2 / 4)) = Real.log 2 := by
    norm_num
    ring
  rw [hq, he, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem early_shift_negative :
    Real.sqrt 4 * (Real.log 2 / 4) + Real.log (Real.sin ((Real.pi / 3) / 2)) < 0 := by
  have hq : Real.sin ((Real.pi / 3) / 2) = 1 / 2 := by
    rw [show Real.pi / 3 / 2 = Real.pi / 6 by ring, Real.sin_pi_div_six]
  rw [hq, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
  norm_num
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

private theorem bridge_early_negative_expression :
    0 ≤ comparisonAngleNegCurvature 4 (Real.log 2 / 8) (Real.log 2 / 8) (Real.log 2 / 4) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlogle : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hh := real_opposite_bridge (r := Real.log 2 / 4) (T := Real.log 2 / 8) (θ := Real.pi / 3)
    (by positivity) (by linarith) (by constructor <;> linarith)
    (by positivity) (by linarith [Real.pi_pos])
  rw [early_raw_bound_negative] at hh
  norm_num only [max_eq_left (by norm_num : (-1 : ℝ) ≤ 0), Real.arcsin_zero, mul_zero] at hh
  convert hh using 1
  congr 1
  ring

#print axioms bridge_pi_at_half
#print axioms early_raw_bound_negative
#print axioms early_shift_negative
#print axioms bridge_early_negative_expression

end GCBufferedCrossAnglesReview


namespace GCBufferedCrossAnglesReview
#print axioms buffered_positive
#print axioms buffered_zero
#print axioms buffered_endpoints
#print axioms plane_fixed_radius_right_angle
#print axioms plane_all_signed_pythagoras
#print axioms coincident_fails_bound
end GCBufferedCrossAnglesReview
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngleNegCurvature_le_of_radial_isometries_in_local_buffer
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.germComparisonAngle_eq_pi_div_two_of_opposite_cross_lower_bounds
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.sq_dist_crossing_isometries_of_opposite_cross_lower_bounds
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_angle_lower_bound_at_fixed_time_of_long_radial_isometries

#lint- only unusedArguments simpNF synTaut
```
