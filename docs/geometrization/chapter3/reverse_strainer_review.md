# Full AC68-70 acceptance and original reverse KL implication

Ten public theorems, two definitions and two private helper theorems in four leaves add19 owned declarations, including5 generated declarations. The326-module gate checks1427 declarations in3161 jobs. Every new transitive closure uses only propext, Classical.choice and Quot.sound. Source-copy and accepted-import review lint is silent; the driver emits21 requested standard axiom reports. Earlier mathematical leaves are unchanged. Declaration kinds were inspected; defLemma is unavailable. The inherited AreaUpperBarrier warning lies outside these closures. Static audit passes. No full migrated root, new PDF/Overleaf build or human approval is claimed.

One agent implemented AC68 scalar and signed-family results; a second independently reviewed their full source contracts/proofs and tests. Another agent implemented AC69 exact tolerance and metric assembly; root read its whole proof. Root implemented AC70 original-global-input wrapper and the AC69 author independently reviewed its proof and built an original-input regression. Root read all three source sections and all proof bodies and concrete drivers. AC68 retains the exact written minimum, both degenerate equal-leg endpoints, all four signed cross angles and strict D<mu. AC69 retains the inclusive epsilon<=epsilon0 and exact written minimum. The strict buffer and chord guards follow with slack from1/8 and60, including equality at epsilon0. AC70 derives properness and actual segments from original source geometry through the accepted global Hopf-Rinow route. The same supplied map and endpoint family are preserved. Only quality is replaced by min(delta,1); the requested radius is always delta inverse.

The AC68 concrete plane configuration has actual radius3, both signed axes, all cross signs and injectivity. The equal-leg formula is tested at c=0 and c=2r. Additional calculations prove exact angle equality at each individual opposite/cross chord threshold, and prove the corresponding STRICT angle assertion fails there. These checks establish why the strict margin is needed; they do not merely instantiate the desired inequality as a hypothesis.

The AC69 test uses an actual identity approximation on Euclidean(Fin2) times the real line, based at(0,5), radius2 and auxiliary quality1. Its approximation parameter is EXACTLY epsilon0, rather than a strict smaller value. It retains all endpoint-radius, same-map14epsilon, pair27epsilon, strict angle and injectivity conclusions and both strict numeric guards. This checks the inclusive bound in the original blueprint.

The AC70 test constructs an actual onto isometric approximation from the complete real line to Euclidean(Fin1) times PUnit. It proves the source short curves, global curvature-zero comparison and Hausdorff dimension1. It applies the original wrapper with requested delta=2 and epsilon exactly epsilon0(1/2,1). The public test requires radius exactly1/2 and signed target coordinates plus/minus1/2, while the quality is2. The same supplied approximation,14epsilon/27epsilon estimates and distinct endpoints remain in the conclusion. This rules out silently changing the requested radius when delta exceeds one.

The quantitative constants are blueprint calculations, not numeric constants attributed to KL. Source scope is recorded in reverse_strainer_sources.json. Full AC67-70 now establish the original reverse KL4.15(1) implication, separately from forward AC55. Compatibility and later Chapters3-4 work remain. Blueprint207 and migration interfaces are unchanged.

```lean
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import DifferentialGeometry.Geometry.Comparison.EqualRadiusStrainerMargin
import DifferentialGeometry.Geometry.Metric.Approximation.EqualRadiusStrainerConfiguration
import DifferentialGeometry.Geometry.Metric.Approximation.QuantitativeReverseStrainer
import DifferentialGeometry.Geometry.Metric.Approximation.OriginalReverseStrainer

open Set Metric

namespace GCAC68Review

open DifferentialGeometry.Geometry.Comparison.Toponogov GC.MetricGeometry

private def axes (v : Fin 2 × Bool) : EuclideanSpace ℝ (Fin 2) :=
  PiLp.single 2 v.1 (if v.2 then 3 else -3)

private theorem plane_configuration :
    (∀ j, Real.pi - 1 < metricComparisonAngle (axes (j, true)) 0 (axes (j, false))) ∧
    (∀ j l, j ≠ l → ∀ b c : Bool,
      Real.pi / 2 - 1 < metricComparisonAngle (axes (j, b)) 0 (axes (l, c))) ∧
    Function.Injective axes ∧ ∀ v, axes v ≠ 0 := by
  have hrad (v : Fin 2 × Bool) : dist 0 (axes v) = 3 := by
    rcases v with ⟨j, b⟩
    cases b <;> simp [axes, dist_zero_left, PiLp.norm_single]
  have heq (v : Fin 2 × Bool) : axes v = (3 : ℝ) •
      (PiLp.single 2 v.1 (if v.2 then (1 : ℝ) else -1) : EuclideanSpace ℝ (Fin 2)) := by
    rcases v with ⟨j, b⟩
    cases b <;> ext l <;> by_cases h : l = j <;> simp [axes, h]
  apply equal_radius_strainer_angles_of_chord_errors (D := 0) (r := 3)
    (by norm_num) (by norm_num) (by norm_num) axes hrad
    (equalRadiusStrainerMargin_pos (by norm_num) (by norm_num) (by norm_num))
  intro v w
  rw [dist_eq_norm, heq v, heq w, ← smul_sub, norm_smul, Real.norm_eq_abs]
  norm_num

private theorem collapsed_formula : comparisonAngle 3 3 0 = 0 := by
  rw [comparisonAngle_eq_two_arcsin_of_equal_legs (by norm_num) (by norm_num) (by norm_num)]
  norm_num

private theorem straight_formula : comparisonAngle 3 3 6 = Real.pi := by
  rw [comparisonAngle_eq_two_arcsin_of_equal_legs (by norm_num) (by norm_num) (by norm_num)]
  norm_num
  ring

private theorem opposite_threshold_exact :
    comparisonAngle 3 3 (6 * Real.cos (1 / 2)) = Real.pi - 1 ∧
      |6 * Real.cos (1 / 2) - 6| = 6 * (1 - Real.cos (1 / 2)) := by
  have hp := Real.one_le_pi_div_two
  have hcos : 0 ≤ Real.cos (1 / 2) :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).le
  have hcosle := Real.cos_le_one (1 / 2)
  constructor
  · rw [comparisonAngle_eq_two_arcsin_of_equal_legs (by norm_num)
      (by positivity) (by nlinarith)]
    have hq : 6 * Real.cos (1 / 2) / (2 * 3) = Real.cos (1 / 2) := by ring
    rw [hq, ← Real.sin_pi_div_two_sub (1 / 2), Real.arcsin_sin (by linarith) (by linarith)]
    ring
  · rw [abs_of_nonpos (by nlinarith)]
    ring

private theorem cross_threshold_exact :
    comparisonAngle 3 3 (6 * Real.sin (Real.pi / 4 - 1 / 2)) = Real.pi / 2 - 1 ∧
      |6 * Real.sin (Real.pi / 4 - 1 / 2) - Real.sqrt 2 * 3| =
        Real.sqrt 2 * 3 - 6 * Real.sin (Real.pi / 4 - 1 / 2) := by
  have hp := Real.one_le_pi_div_two
  have hsin : 0 ≤ Real.sin (Real.pi / 4 - 1 / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsinle := Real.sin_le_one (Real.pi / 4 - 1 / 2)
  have hbound := (equalRadiusStrainerMargin_pos (r := 3) (α := 1)
    (by norm_num) (by norm_num) (by norm_num)).trans_le (min_le_right _ _)
  constructor
  · rw [comparisonAngle_eq_two_arcsin_of_equal_legs (by norm_num)
      (by positivity) (by nlinarith)]
    have hq : 6 * Real.sin (Real.pi / 4 - 1 / 2) / (2 * 3) =
        Real.sin (Real.pi / 4 - 1 / 2) := by ring
    rw [hq, Real.arcsin_sin (by linarith) (by linarith)]
    ring
  · rw [abs_of_nonpos (by linarith)]
    ring

private theorem strict_threshold_counterchecks :
    ¬ Real.pi - 1 < comparisonAngle 3 3 (6 * Real.cos (1 / 2)) ∧
    ¬ Real.pi / 2 - 1 < comparisonAngle 3 3 (6 * Real.sin (Real.pi / 4 - 1 / 2)) := by
  rw [opposite_threshold_exact.1, cross_threshold_exact.1]
  exact ⟨lt_irrefl _, lt_irrefl _⟩

#print axioms opposite_threshold_exact
#print axioms cross_threshold_exact
#print axioms strict_threshold_counterchecks

#print axioms plane_configuration
#print axioms collapsed_formula
#print axioms straight_formula

end GCAC68Review

#lint- only unusedArguments simpNF synTaut

namespace GCQuantitativeReverseStrainerReview

open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem normed_segments {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x y : V) :
    ∃ f : Icc (0 : ℝ) 1 → V,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  refine ⟨fun t => AffineMap.lineMap x y (t : ℝ), by fun_prop, ?_, ?_, ?_⟩
  · exact AffineMap.lineMap_apply_zero x y
  · exact AffineMap.lineMap_apply_one x y
  · intro s t
    rw [dist_lineMap_lineMap]
    exact mul_comm _ _

private def identityApprox {V : Type*} [MetricSpace V] (p : V) {ε : ℝ}
    (hε : 0 < ε) (hεone : ε < 1) : KleinerLottApprox p p ε where
  error_pos := hε
  error_lt_one := hεone
  toFun := id
  basepoint := rfl
  distortion _ _ _ _ := by simpa only [id_eq, sub_self, abs_zero] using hε.le
  coverage q hq := by
    have hmem : q ∈ id '' ball p ε⁻¹ := ⟨q, show dist q p < ε⁻¹ by linarith, rfl⟩
    exact (Metric.infDist_le_dist_of_mem hmem).trans (by simpa using hε.le)

private abbrev Model := WithLp 2 (EuclideanSpace ℝ (Fin 2) × ℝ)
private def p : Model := WithLp.toLp 2 (0, 5)
private noncomputable def eps : ℝ := reverseStrainerTolerance 2 1
private noncomputable def approximation : KleinerLottApprox p p eps :=
  identityApprox p (reverseStrainerTolerance_pos (by norm_num) (by norm_num) (by norm_num))
    (reverseStrainerTolerance_lt_one 2 1)

-- The actual approximation parameter equals epsilon0, exercising the closed upper bound.
-- This is a genuine two-axis example for curvature-zero comparison angles.
theorem two_axes_at_tolerance_endpoint :
    ∃ a : Fin 2 × Bool → Model,
      (∀ j, dist p (a j) = 2) ∧
      (∀ j, dist (a j) (WithLp.toLp 2 (PiLp.single 2 j.1
        (if j.2 then (2 : ℝ) else -2), (5 : ℝ))) < 14 * eps) ∧
      (∀ j l, |dist (a j) (a l) - 2 *
        ‖(PiLp.single 2 j.1 (if j.2 then (1 : ℝ) else -1) : EuclideanSpace ℝ (Fin 2)) -
          PiLp.single 2 l.1 (if l.2 then (1 : ℝ) else -1)‖| < 27 * eps) ∧
      (∀ j, Real.pi - 1 < metricComparisonAngle (a (j, true)) p (a (j, false))) ∧
      (∀ j l, j ≠ l → ∀ b c : Bool,
        Real.pi / 2 - 1 < metricComparisonAngle (a (j, b)) p (a (l, c))) ∧
      Function.Injective a ∧ ∀ j, a j ≠ p := by
  exact approximation.exists_exact_radius_strainer_of_le_reverseStrainerTolerance
    normed_segments (r := 2) (α := 1) (by norm_num) (by norm_num) (by norm_num) le_rfl

theorem tolerance_endpoint_strict_guards :
    0 < eps ∧ eps < 1 ∧ 2 + 5 * eps < eps⁻¹ ∧
      27 * eps < equalRadiusStrainerMargin 2 1 := by
  have hpos : 0 < eps := reverseStrainerTolerance_pos (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hpos, reverseStrainerTolerance_lt_one 2 1,
    radius_buffer_and_chord_error_of_le_reverseStrainerTolerance
      (by norm_num) (by norm_num) (by norm_num) hpos le_rfl⟩

end GCQuantitativeReverseStrainerReview

#print axioms GCQuantitativeReverseStrainerReview.two_axes_at_tolerance_endpoint
#print axioms GCQuantitativeReverseStrainerReview.tolerance_endpoint_strict_guards
#lint- only unusedArguments simpNF synTaut

namespace GCOriginalReverseStrainerReview

open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov

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


private abbrev Factor := PUnit.{1}
private abbrev Target := WithLp 2 (EuclideanSpace ℝ (Fin 1) × Factor)
private def targetBase : Target := WithLp.toLp 2 (0, PUnit.unit)
private def embedding (x : ℝ) : Target := WithLp.toLp 2 (PiLp.single 2 0 x, PUnit.unit)

private theorem embedding_isometry : Isometry embedding := by
  apply Isometry.of_dist_eq
  intro x x'
  dsimp only [embedding]
  rw [(WithLp.isometry_prodMk_right (E := EuclideanSpace ℝ (Fin 1)) (PUnit.unit : Factor)).dist_eq,
    PiLp.dist_single_same]

private theorem embedding_base : embedding 0 = targetBase := by
  simp [embedding, targetBase]

private theorem embedding_onto (q : Target) : embedding (q.fst 0) = q := by
  apply (WithLp.equiv 2 (EuclideanSpace ℝ (Fin 1) × Factor)).injective
  refine Prod.ext ?_ (Subsingleton.elim _ _)
  ext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simp [embedding]

private noncomputable def eps : ℝ := reverseStrainerTolerance ((2 : ℝ)⁻¹) (min 2 1)
private theorem eps_pos : 0 < eps :=
  reverseStrainerTolerance_pos (by norm_num) (by norm_num) (by norm_num)
private theorem eps_lt_one : eps < 1 := reverseStrainerTolerance_lt_one _ _

private noncomputable def approximation : KleinerLottApprox (0 : ℝ) targetBase eps where
  error_pos := eps_pos
  error_lt_one := eps_lt_one
  toFun := embedding
  basepoint := embedding_base
  distortion x _ x' _ := by simpa only [embedding_isometry.dist_eq, sub_self, abs_zero] using eps_pos.le
  coverage q hq := by
    have hrad : dist (q.fst 0) (0 : ℝ) = dist q targetBase := by
      conv_rhs => rw [← embedding_onto q, ← embedding_base, embedding_isometry.dist_eq]
    have hball : q.fst 0 ∈ ball (0 : ℝ) eps⁻¹ := by
      change dist (q.fst 0) 0 < eps⁻¹
      rw [hrad]
      linarith [eps_pos]
    have hmem : q ∈ embedding '' ball (0 : ℝ) eps⁻¹ := ⟨q.fst 0, hball, embedding_onto q⟩
    exact (Metric.infDist_le_dist_of_mem hmem).trans (by simpa using eps_pos.le)

-- Quality delta=2 is clipped to 1 only inside the auxiliary tolerance.
-- The actual source endpoint radius and target model coordinates stay exactly 1/2.
theorem original_real_delta_two :
    ∃ a : Fin 1 × Bool → ℝ,
      (∀ j, dist (0 : ℝ) (a j) = 1 / 2) ∧
      (∀ j, dist (approximation.toFun (a j))
        (WithLp.toLp 2 (PiLp.single 2 j.1
          (if j.2 then (1 / 2 : ℝ) else -(1 / 2)), (PUnit.unit : Factor))) < 14 * eps) ∧
      (∀ j l, |dist (a j) (a l) - (1 / 2 : ℝ) *
        ‖(PiLp.single 2 j.1 (if j.2 then (1 : ℝ) else -1) : EuclideanSpace ℝ (Fin 1)) -
          PiLp.single 2 l.1 (if l.2 then (1 : ℝ) else -1)‖| < 27 * eps) ∧
      (∀ j, Real.pi - 2 < metricComparisonAngle (a (j, true)) (0 : ℝ) (a (j, false))) ∧
      (∀ j l, j ≠ l → ∀ b c : Bool,
        Real.pi / 2 - 2 < metricComparisonAngle (a (j, b)) (0 : ℝ) (a (l, c))) ∧
      Function.Injective a ∧ ∀ j, a j ≠ (0 : ℝ) := by
  simpa only [one_div] using approximation.exists_exact_scale_strainer_of_nonnegative_comparison
    (δ := 2) (n := 1) (by norm_num) le_rfl
    (arbitrarily_short_curves_of_metric_segments real_segments)
    (real_comparison (by norm_num)) (by simpa only [Nat.cast_one] using Real.dimH_univ.le)

end GCOriginalReverseStrainerReview

#print axioms GCOriginalReverseStrainerReview.original_real_delta_two
#lint- only unusedArguments simpNF synTaut

#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.equalRadiusStrainerMargin
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.equalRadiusStrainerMargin_pos
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_eq_two_arcsin_of_equal_legs
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.opposite_angle_of_equal_radius_chord_error
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.cross_angle_of_equal_radius_chord_error
#print axioms GC.MetricGeometry.equal_radius_strainer_angles_of_chord_errors
#print axioms GC.MetricGeometry.reverseStrainerTolerance
#print axioms GC.MetricGeometry.reverseStrainerTolerance_pos
#print axioms GC.MetricGeometry.reverseStrainerTolerance_lt_one
#print axioms GC.MetricGeometry.radius_buffer_and_chord_error_of_le_reverseStrainerTolerance
#print axioms GC.MetricGeometry.KleinerLottApprox.exists_exact_radius_strainer_of_le_reverseStrainerTolerance
#print axioms GC.MetricGeometry.KleinerLottApprox.exists_exact_scale_strainer_of_nonnegative_comparison

#lint- only unusedArguments simpNF synTaut
```
