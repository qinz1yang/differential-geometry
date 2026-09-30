# Refined comparison and midpoint tools independent acceptance

Thirteen public theorems and one definition in three leaves add16 owned declarations, including two generated declarations. The375-module gate checks1754 declarations in3210 jobs. All new transitive closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import regression lint is silent;25 reports cover all14 public production declarations and eleven concrete regressions. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside these closures. The separate blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

Root independently reviewed the entire refined-kernel diff and exact constants against the accepted11/3 proof, all scalar/bridge bodies and every final test. The independent peer read the full scalar proof and actual AKP function-comparison/model passages; source and geometric roles remain distinct. These are preparatory tools for original8R statements, not completion of those source-geometric contracts.

The actual real hinge at0 with endpoints-1,+2 has arm sum3 and complete bufferL10. Tests prove it lies OUTSIDE the older30/11 bound but INSIDE the new100/33 bound, then invoke both same-hinge model-side and canonical-angle conclusions and the full fixed-endpoint consumer for every kappa>=0. Original short curves and local four-point comparison are proved in the fixture.

Scalar tests supply an actual continuous nonsmooth tent2-abs(t-1), prove an unconditional symmetric-step inequality and choose a positive in-domain step at every interior point. They invoke the full actual-endpoint interpolant consumer and then its quotient corollary; the midpoint conclusion is strict. Mixed-sign endpoints-2/5 at frequency2 and length3 test exact endpoints, all symmetric identities and the upper maximum. Negative endpoints-1/-1 disprove that bound without max-nonnegativity. The zero-frequency formula is shown identically0 and fails to interpolate a nonzero endpoint, testing the positive-frequency guard. No derivative or second-order support premise is assumed.

Angle-bridge tests use actual real opposite and same-ray configurations at kappa4, with endpoint interpolation proved from cosh addition, giving exact anglespi and0. The inclusive a=A boundary is also tested with independent c,C: the bridge is purely algebraic and does not conflate them through an auxiliary endpoint function. All sqrt-curvature and denominator normalizations are retained.

The original8R geometric midpoint producer and its full radial assembly are separate work. The scalar principle makes no source-geometric claims and the refined budget does not by itself deliver the older fixed-domain contracts. Blueprint207 and migration interfaces remain unchanged.

```lean
import DifferentialGeometry.Geometry.Comparison.RefinedBudgetInteriorComparison
import DifferentialGeometry.Geometry.Comparison.HyperbolicInterpolation
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov
namespace GCRefinedBudgetReview

private theorem same_side_zero {κ : ℝ} (hκ : 0 ≤ κ) (x a b : ℝ) (ha : a ≠ x) (hb : b ≠ x)
    (hs : (x ≤ a ∧ x ≤ b) ∨ (a ≤ x ∧ b ≤ x)) :
    comparisonAngleNegCurvature κ (dist x a) (dist x b) (dist a b) = 0 := by
  have heq : dist a b = |dist x a - dist x b| := by
    rcases hs with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonpos (sub_nonpos.mpr ha'), abs_of_nonpos (sub_nonpos.mpr hb')]
      have h : -(x - a) - -(x - b) = a - b := by ring
      rw [h]
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonneg (sub_nonneg.mpr ha'), abs_of_nonneg (sub_nonneg.mpr hb')]
      have h : (x - a) - (x - b) = b - a := by ring
      rw [h, abs_sub_comm]
  rw [heq]
  exact comparisonAngleNegCurvature_abs_sub hκ (dist_pos.mpr ha.symm) (dist_pos.mpr hb.symm)

private theorem real_comparison {κ : ℝ} (hκ : 0 ≤ κ) : fourPointComparison κ (univ : Set ℝ) := by
  intro x _ a _ b _ c _ ha hb hc
  have hab := (comparisonAngleNegCurvature_mem_Icc κ (dist x a) (dist x b) (dist a b)).2
  have hbc := (comparisonAngleNegCurvature_mem_Icc κ (dist x b) (dist x c) (dist b c)).2
  have hca := (comparisonAngleNegCurvature_mem_Icc κ (dist x c) (dist x a) (dist c a)).2
  rcases le_total x a with hxa | hax <;> rcases le_total x b with hxb | hbx <;>
    rcases le_total x c with hxc | hcx
  all_goals first
    | have hz := same_side_zero hκ x a b ha hb (Or.inl ⟨hxa, hxb⟩); linarith
    | have hz := same_side_zero hκ x a b ha hb (Or.inr ⟨hax, hbx⟩); linarith
    | have hz := same_side_zero hκ x b c hb hc (Or.inl ⟨hxb, hxc⟩); linarith
    | have hz := same_side_zero hκ x b c hb hc (Or.inr ⟨hbx, hcx⟩); linarith
    | have hz := same_side_zero hκ x c a hc ha (Or.inl ⟨hxc, hxa⟩); linarith
    | have hz := same_side_zero hκ x c a hc ha (Or.inr ⟨hcx, hax⟩); linarith


private theorem real_segments (x y : ℝ) :
    ∃ f : unitInterval → ℝ, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → ℝ := fun t => (1 - (t : ℝ)) * x + (t : ℝ) * y
  refine ⟨f, by fun_prop, by simp [f], by simp [f], ?_⟩
  intro s t
  change |(1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y)| =
    |x - y| * |(s : ℝ) - t|
  rw [show (1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y) =
    (y - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm y x]

private theorem real_curves : ∀ x y : ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → ℝ, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      eVariationOn c univ < ENNReal.ofReal (dist x y + ε) :=
  arbitrarily_short_curves_of_metric_segments real_segments

private noncomputable def ray (x a t : ℝ) : ℝ := if x ≤ a then x + t else x - t

private theorem ray_isometry (x a : ℝ) : Isometry (ray x a) := by
  apply Isometry.of_dist_eq
  intro s t
  by_cases h : x ≤ a
  · simp only [ray, ite_eq_left h, Real.dist_eq]
    congr 1
    ring
  · simp only [ray, ite_eq_right h, Real.dist_eq]
    rw [show x - s - (x - t) = t - s by ring, abs_sub_comm]

private noncomputable def realHinge (x a y : ℝ) : MinimizingHinge a y where
  center := x
  left t := ray x a t
  right t := ray x y t
  left_isometry := (ray_isometry x a).comp isometry_subtype_coe
  right_isometry := (ray_isometry x y).comp isometry_subtype_coe
  left_zero := by simp [ray]
  right_zero := by simp [ray]
  left_end := by
    by_cases h : x ≤ a
    · simp only [ray, ite_eq_left h, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · simp only [ray, ite_eq_right h, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]
      ring
  right_end := by
    by_cases h : x ≤ y
    · simp only [ray, ite_eq_left h, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · simp only [ray, ite_eq_right h, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]
      ring


theorem strict_improvement_range :
    3 * (10 : ℝ) / 11 ≤ dist (realHinge 0 (-1) 2).center (-1) +
      dist (realHinge 0 (-1) 2).center 2 ∧
    dist (realHinge 0 (-1) 2).center (-1) +
      dist (realHinge 0 (-1) 2).center 2 < 10 * (10 : ℝ) / 33 := by
  norm_num [realHinge, Real.dist_eq]

theorem original_real_hinge_in_new_range {κ : ℝ} (hκ : 0 ≤ κ) :
    dist (-1 : ℝ) 2 ≤ (realHinge 0 (-1) 2).modelSide κ ∧
      comparisonAngleNegCurvature κ 1 2 3 ≤ (realHinge 0 (-1) 2).germAngle κ := by
  have hlocal : ∀ z : ℝ, ∃ Ω : Set ℝ, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω :=
    fun z => ⟨univ, isOpen_univ, real_comparison hκ, mem_univ z⟩
  have hc : IsComplete (closedBall (-1 : ℝ) 10) := isClosed_closedBall.isComplete
  refine ⟨?_, ?_⟩
  · exact MinimizingHinge.modelSide_ge_dist_of_complete_refined_budget_buffer
      hκ real_curves hlocal hc (realHinge 0 (-1) 2) strict_improvement_range.2
  · have hh := MinimizingHinge.comparisonAngle_le_of_complete_refined_budget_buffer
      hκ real_curves hlocal hc (realHinge 0 (-1) 2) strict_improvement_range.2
      (by norm_num [realHinge, Real.dist_eq]) (by norm_num [realHinge, Real.dist_eq])
    norm_num [realHinge, Real.dist_eq] at hh ⊢
    exact hh

theorem original_real_endpoint_comparison_in_new_range {κ : ℝ} (hκ : 0 ≤ κ) :
    endpointHingeComparison κ (-1 : ℝ) (100 / 33) := by
  have hlocal : ∀ z : ℝ, ∃ Ω : Set ℝ, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω :=
    fun z => ⟨univ, isOpen_univ, real_comparison hκ, mem_univ z⟩
  have hc : IsComplete (closedBall (-1 : ℝ) 10) := isClosed_closedBall.isComplete
  have hh := endpointHingeComparison_of_complete_refined_budget_buffer hκ real_curves hlocal hc
  norm_num at hh ⊢
  exact hh

end GCRefinedBudgetReview

namespace GCHyperbolicMidpointReview
open Set
open DifferentialGeometry.Analysis.ODE

private def tent (t : ℝ) : ℝ := 2 - |t - 1|

private theorem tent_midpoint (t h : ℝ) : tent (t-h) + tent (t+h) ≤ 2 * tent t := by
  have hh := abs_add_le (t-h-1) (t+h-1)
  rw [show t-h-1 + (t+h-1) = 2 * (t-1) by ring, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  dsimp only [tent]
  linarith

private theorem tent_step {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 2) :
    ∃ h : ℝ, 0 < h ∧ t-h ∈ Icc (0 : ℝ) 2 ∧ t+h ∈ Icc (0 : ℝ) 2 ∧
      tent (t-h) + tent (t+h) ≤ 2 * Real.cosh h * tent t := by
  let h := min t (2-t) / 2
  have hpos : 0 < h := half_pos (lt_min ht.1 (sub_pos.mpr ht.2))
  have hlo : h ≤ t / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hhi : h ≤ (2-t) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have habs : |t-1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htent : 0 ≤ tent t := by dsimp [tent]; linarith
  refine ⟨h, hpos, ⟨by linarith, by linarith [ht.2]⟩,
    ⟨by linarith [ht.1], by linarith⟩, ?_⟩
  have hm := tent_midpoint t h
  have hc := mul_nonneg (sub_nonneg.mpr (Real.one_le_cosh h)) htent
  nlinarith

theorem actual_tent_dominates_interpolant :
    (∀ t ∈ Icc (0 : ℝ) 2, hyperbolicInterpolate 1 2 1 1 t ≤ tent t) ∧
      hyperbolicInterpolate 1 2 1 1 1 < tent 1 := by
  have hf : ContinuousOn tent (Icc (0 : ℝ) 2) := by unfold tent; fun_prop
  have h := hyperbolicInterpolate_le_of_local_midpoint (k := 1) (A := 2)
    (by norm_num) (by norm_num) hf (fun t ht _ => by
      obtain ⟨h, hh, hl, hr, hm⟩ := tent_step ht
      exact ⟨h, hh, hl, hr, by simpa only [one_mul] using hm⟩)
  have hbound := hyperbolicInterpolate_le_max (k := 1) (A := 2) (u := 1) (v := 1) (t := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · simpa only [tent, zero_sub, abs_neg, abs_one, show (2 : ℝ)-1=1 by norm_num] using h
  · norm_num [tent] at hbound ⊢
    linarith

theorem mixed_sign_interpolant_exact_endpoints_and_midpoints :
    hyperbolicInterpolate 2 3 (-2) 5 0 = -2 ∧
    hyperbolicInterpolate 2 3 (-2) 5 3 = 5 ∧
    (∀ t ∈ Icc (0 : ℝ) 3, hyperbolicInterpolate 2 3 (-2) 5 t ≤ 5) ∧
    ∀ t h : ℝ, hyperbolicInterpolate 2 3 (-2) 5 (t-h) +
      hyperbolicInterpolate 2 3 (-2) 5 (t+h) =
        2 * Real.cosh (2*h) * hyperbolicInterpolate 2 3 (-2) 5 t := by
  refine ⟨hyperbolicInterpolate_zero (by norm_num) (by norm_num) _ _,
    hyperbolicInterpolate_right (by norm_num) (by norm_num) _ _, ?_,
    hyperbolicInterpolate_midpoint _ _ _ _⟩
  intro t ht
  simpa only [max_eq_right (by norm_num : (-2 : ℝ) ≤ 5)] using
    hyperbolicInterpolate_le_max (k := 2) (A := 3) (u := -2) (v := 5)
      (by norm_num) (by norm_num) (by norm_num) ht

theorem nonnegative_endpoint_maximum_is_necessary :
    max (-1 : ℝ) (-1) < hyperbolicInterpolate 1 2 (-1) (-1) 1 := by
  have hs : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr (by norm_num)
  have hc : 1 < Real.cosh 1 := Real.one_lt_cosh.mpr (by norm_num)
  have hden : 0 < Real.sinh 2 := Real.sinh_pos_iff.mpr (by norm_num)
  have htwo : Real.sinh 2 = 2 * Real.sinh 1 * Real.cosh 1 := by
    rw [show (2 : ℝ) = 1+1 by norm_num, Real.sinh_add]
    ring
  norm_num only [hyperbolicInterpolate, one_mul, sub_self, sub_zero, max_self,
    show (2 : ℝ)-1=1 by norm_num]
  apply (lt_div_iff₀ hden).mpr
  rw [htwo]
  nlinarith [mul_pos hs (sub_pos.mpr hc)]

theorem zero_parameter_does_not_interpolate_nonzero_endpoint :
    (∀ t : ℝ, hyperbolicInterpolate 0 2 3 4 t = 0) ∧
      hyperbolicInterpolate 0 2 3 4 0 ≠ 3 := by
  constructor
  · intro t
    simp [hyperbolicInterpolate]
  · norm_num [hyperbolicInterpolate]


theorem actual_tent_quotient_bound {t : ℝ} (ht : 0 < t) (htwo : t ≤ 2) :
    (Real.cosh t - tent t) / Real.sinh t ≤ (Real.cosh 2 - 1) / Real.sinh 2 := by
  have hbound : hyperbolicInterpolate 1 2 (tent 0) (tent 2) t ≤ tent t := by
    simpa only [tent, zero_sub, abs_neg, abs_one, show (2 : ℝ)-1=1 by norm_num] using
      actual_tent_dominates_interpolant.1 t ⟨ht.le, htwo⟩
  have hh := hyperbolic_quotient_le_of_interpolate_le (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 2) ht hbound
  simpa only [one_mul, tent, zero_sub, abs_neg, abs_one,
    show (2 : ℝ)-1=1 by norm_num, mul_one] using hh

end GCHyperbolicMidpointReview

namespace GCHyperbolicInterpolationReview
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem interpolate_cosh_profile {k A : ℝ} (hk : 0 < k) (hA : 0 < A)
    (b t : ℝ) :
    hyperbolicInterpolate k A (Real.cosh (k*b)) (Real.cosh (k*(A+b))) t =
      Real.cosh (k*(t+b)) := by
  have hden : Real.sinh (k*A) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos hk hA)).ne'
  rw [hyperbolicInterpolate_eq_cosh hk hA]
  simp only [mul_add, Real.cosh_add]
  field_simp
  ring

theorem actual_opposite_real_radial_points :
    comparisonAngleNegCurvature 4 (dist (0 : ℝ) 3) (dist (0 : ℝ) (-2)) (dist (3 : ℝ) (-2)) ≤
      comparisonAngleNegCurvature 4 (dist (0 : ℝ) 1) (dist (0 : ℝ) (-2)) (dist (1 : ℝ) (-2)) ∧
    comparisonAngleNegCurvature 4 3 2 5 = Real.pi ∧ comparisonAngleNegCurvature 4 1 2 3 = Real.pi := by
  have hmodel : hyperbolicInterpolate (Real.sqrt 4) 3 (Real.cosh (Real.sqrt 4 * 2))
      (Real.cosh (Real.sqrt 4 * 5)) 1 ≤ Real.cosh (Real.sqrt 4 * 3) := by
    have hh := interpolate_cosh_profile (k := 2) (A := 3) (by norm_num) (by norm_num) 2 1
    norm_num only [show Real.sqrt 4 = 2 by rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]; norm_num, show (3 : ℝ)+2=5 by norm_num,
      show (1 : ℝ)+2=3 by norm_num] at hh ⊢
    exact hh.le
  have h := comparisonAngleNegCurvature_le_of_cosh_interpolate
    (by norm_num : (0 : ℝ) < 4) (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) < 2) hmodel
  refine ⟨by norm_num [Real.dist_eq]; exact h, ?_, ?_⟩
  · convert comparisonAngleNegCurvature_add (κ := 4) (a := 3) (b := 2)
      (by norm_num) (by norm_num) (by norm_num) using 1; norm_num
  · convert comparisonAngleNegCurvature_add (κ := 4) (a := 1) (b := 2)
      (by norm_num) (by norm_num) (by norm_num) using 1; norm_num

theorem actual_same_ray_real_radial_points :
    comparisonAngleNegCurvature 4 (dist (0 : ℝ) 3) (dist (0 : ℝ) 5) (dist (3 : ℝ) 5) ≤
      comparisonAngleNegCurvature 4 (dist (0 : ℝ) 1) (dist (0 : ℝ) 5) (dist (1 : ℝ) 5) ∧
    comparisonAngleNegCurvature 4 3 5 2 = 0 ∧ comparisonAngleNegCurvature 4 1 5 4 = 0 := by
  have hmodel : hyperbolicInterpolate (Real.sqrt 4) 3 (Real.cosh (Real.sqrt 4 * 5))
      (Real.cosh (Real.sqrt 4 * 2)) 1 ≤ Real.cosh (Real.sqrt 4 * 4) := by
    have hh := interpolate_cosh_profile (k := 2) (A := 3) (by norm_num) (by norm_num) (-5) 1
    norm_num only [show Real.sqrt 4 = 2 by rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]; norm_num] at ⊢
    norm_num [Real.cosh_neg] at hh ⊢
    exact hh.le
  have h := comparisonAngleNegCurvature_le_of_cosh_interpolate
    (by norm_num : (0 : ℝ) < 4) (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) < 5) hmodel
  refine ⟨by norm_num [Real.dist_eq] at ⊢; exact h, ?_, ?_⟩
  · convert comparisonAngleNegCurvature_abs_sub (κ := 4) (a := 3) (b := 5)
      (by norm_num) (by norm_num) (by norm_num) using 1; norm_num
  · convert comparisonAngleNegCurvature_abs_sub (κ := 4) (a := 1) (b := 5)
      (by norm_num) (by norm_num) (by norm_num) using 1; norm_num

theorem equal_radial_parameters_keep_opposite_sides_separate :
    comparisonAngleNegCurvature 4 1 2 1 ≤ comparisonAngleNegCurvature 4 1 2 3 := by
  apply comparisonAngleNegCurvature_le_of_cosh_interpolate (by norm_num) (by norm_num)
    le_rfl (by norm_num)
  rw [hyperbolicInterpolate_right (by positivity) (by norm_num)]
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  nlinarith [Real.sqrt_nonneg (4 : ℝ)]

end GCHyperbolicInterpolationReview


#print axioms Metric.MinimizingHinge.modelSide_ge_dist_of_complete_refined_budget_buffer
#print axioms Metric.MinimizingHinge.comparisonAngle_le_of_complete_refined_budget_buffer
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.endpointHingeComparison_of_complete_refined_budget_buffer
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngleNegCurvature_le_of_cosh_interpolate
#print axioms DifferentialGeometry.Analysis.ODE.le_of_local_hyperbolic_midpoint
#print axioms DifferentialGeometry.Analysis.ODE.hyperbolicInterpolate
#print axioms DifferentialGeometry.Analysis.ODE.continuous_hyperbolicInterpolate
#print axioms DifferentialGeometry.Analysis.ODE.hyperbolicInterpolate_zero
#print axioms DifferentialGeometry.Analysis.ODE.hyperbolicInterpolate_right
#print axioms DifferentialGeometry.Analysis.ODE.hyperbolicInterpolate_midpoint
#print axioms DifferentialGeometry.Analysis.ODE.hyperbolicInterpolate_le_max
#print axioms DifferentialGeometry.Analysis.ODE.hyperbolicInterpolate_le_of_local_midpoint
#print axioms DifferentialGeometry.Analysis.ODE.hyperbolicInterpolate_eq_cosh
#print axioms DifferentialGeometry.Analysis.ODE.hyperbolic_quotient_le_of_interpolate_le
#print axioms GCRefinedBudgetReview.strict_improvement_range
#print axioms GCRefinedBudgetReview.original_real_hinge_in_new_range
#print axioms GCRefinedBudgetReview.original_real_endpoint_comparison_in_new_range
#print axioms GCHyperbolicMidpointReview.actual_tent_dominates_interpolant
#print axioms GCHyperbolicMidpointReview.mixed_sign_interpolant_exact_endpoints_and_midpoints
#print axioms GCHyperbolicMidpointReview.nonnegative_endpoint_maximum_is_necessary
#print axioms GCHyperbolicMidpointReview.zero_parameter_does_not_interpolate_nonzero_endpoint
#print axioms GCHyperbolicMidpointReview.actual_tent_quotient_bound
#print axioms GCHyperbolicInterpolationReview.actual_opposite_real_radial_points
#print axioms GCHyperbolicInterpolationReview.actual_same_ray_real_radial_points
#print axioms GCHyperbolicInterpolationReview.equal_radial_parameters_keep_opposite_sides_separate
#lint- only unusedArguments simpNF synTaut
```
