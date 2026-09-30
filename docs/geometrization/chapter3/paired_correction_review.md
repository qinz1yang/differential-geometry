# AC21: self-review and compiled consumers

This is an assistant self-review, not independent human/agent approval.
The full geometric theorem constructs one point y using AC20. Every later
comparison is on the supplied Omega and uses actual endpoints; all central
noncoincidences are proved from the positive anchor bounds and positive move
length. Both endpoint uses of AC19 retain their anchor bounds. The exact
K and all three coordinate constants are preserved. Other anchors may be
an arbitrary set; the later finite-coordinate consumer can instantiate it.

Both fresh leaves and source-copy declaration linters (unusedArguments,
simpNF, synTaut) pass silently. All five owned source declarations (three
public, two private) are theorems; defLemma is unavailable in this environment.
The combined gate passes for 77 modules / 2865 jobs / 607 owned constants.
All new transitive axiom closures are standard. The inherited AreaUpperBarrier
warning is outside these new dependencies; no full migrated root is built.
Earlier mathematical leaves and blueprint207 are unchanged.

Five compiled examples test the short-cosine inequality at its endpoint,
the near-pi bound, actual four-point comparison on the real line, the whole
geometric move in the packet with anchors +2,-2 and working interval (-1,1),
and existence of a positive move length satisfying its quantitative scale.
The real-line comparison is proved in the consumer driver by same-side
angle zero and a three-point order argument. Thus the example does not
merely assume the main geometric input. Its other-anchor set is empty;
the general nonempty cross-coordinate proof is covered by the theorem and
its full axiom audit rather than claimed as a separate concrete plane test.

```lean
import DifferentialGeometry.Geometry.Comparison.PairedCorrection
import DifferentialGeometry.Topology.MetricSpace.ApproximateMidpoint

open Set Real Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem same_side_zero (x a b : ℝ) (ha : a ≠ x) (hb : b ≠ x)
    (hs : (x ≤ a ∧ x ≤ b) ∨ (a ≤ x ∧ b ≤ x)) :
    comparisonAngleNegCurvature 1 (dist x a) (dist x b) (dist a b) = 0 := by
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
  exact comparisonAngleNegCurvature_abs_sub (by norm_num) (dist_pos.mpr ha.symm) (dist_pos.mpr hb.symm)

private theorem real_comparison : fourPointComparison 1 (univ : Set ℝ) := by
  intro x _ a _ b _ c _ ha hb hc
  have hab := (comparisonAngleNegCurvature_mem_Icc 1 (dist x a) (dist x b) (dist a b)).2
  have hbc := (comparisonAngleNegCurvature_mem_Icc 1 (dist x b) (dist x c) (dist b c)).2
  have hca := (comparisonAngleNegCurvature_mem_Icc 1 (dist x c) (dist x a) (dist c a)).2
  rcases le_total x a with hxa | hax <;> rcases le_total x b with hxb | hbx <;>
    rcases le_total x c with hxc | hcx
  all_goals first
    | have hz := same_side_zero x a b ha hb (Or.inl ⟨hxa, hxb⟩); linarith
    | have hz := same_side_zero x a b ha hb (Or.inr ⟨hax, hbx⟩); linarith
    | have hz := same_side_zero x b c hb hc (Or.inl ⟨hxb, hxc⟩); linarith
    | have hz := same_side_zero x b c hb hc (Or.inr ⟨hbx, hcx⟩); linarith
    | have hz := same_side_zero x c a hc ha (Or.inl ⟨hxc, hxa⟩); linarith
    | have hz := same_side_zero x c a hc ha (Or.inr ⟨hcx, hax⟩); linarith

example : (1 : ℝ) ^ 2 / 4 ≤ 1 - cos 1 := sq_div_four_le_one_sub_cos (by norm_num) le_rfl

example : Real.pi - 4 * (1 / 100 : ℝ) ≤ Real.pi :=
  pi_sub_four_mul_le_of_one_add_cos_le (by norm_num) le_rfl pi_pos.le (by simp)

example : fourPointComparison 1 (univ : Set ℝ) := real_comparison

private theorem real_short_curves (p u : ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ c : unitInterval → ℝ, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
      eVariationOn c univ < ENNReal.ofReal (dist p u + η) := by
  have hmid (a b ε : ℝ) (hε : 0 < ε) :
      ∃ z : ℝ, dist a z ≤ dist a b / 2 + ε ∧ dist b z ≤ dist a b / 2 + ε := by
    refine ⟨(a + b) / 2, ?_, ?_⟩
    · have heq : a - (a + b) / 2 = (a - b) / 2 := by ring
      rw [Real.dist_eq, heq, abs_div]
      norm_num
      rw [Real.dist_eq a b]
      linarith
    · have heq : b - (a + b) / 2 = (b - a) / 2 := by ring
      rw [Real.dist_eq, heq, abs_div, abs_sub_comm b a]
      norm_num
      rw [Real.dist_eq a b]
      linarith
  obtain ⟨c, hc, hc0, hc1, _, hlen⟩ := exists_curve_eVariationOn_lt_of_approximate_midpoints
    hmid p u hη
  exact ⟨c, hc, hc0, hc1, hlen⟩

example {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 2)
    (hscale : t ≤ (1 / 100 : ℝ) ^ 2 / (4 * cosh (3 + 1) / sinh 1)) :
    ∃ y ∈ Ioo (-1 : ℝ) 1, dist 0 y = t ∧
      (1 - (1 / 100 : ℝ) ^ 2) * t ≤ dist (0 : ℝ) 2 - dist y 2 ∧
      dist (0 : ℝ) 2 - dist y 2 ≤ t ∧
      (1 - 3 * (1 / 100 : ℝ) ^ 2) * t ≤ dist y (-2) - dist (0 : ℝ) (-2) ∧
      dist y (-2) - dist (0 : ℝ) (-2) ≤ t := by
  have hbounds (z : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) (c : ℝ)
      (hc : c ∈ insert (2 : ℝ) (insert (-2) (∅ : Set ℝ))) : dist z c ∈ Icc (1 : ℝ) 3 := by
    simp only [mem_insert_iff, mem_empty_iff_false, or_false] at hc
    rcases hc with rfl | rfl
    · rw [Real.dist_eq, abs_of_nonpos (by linarith [hz.2] : z - 2 ≤ 0)]
      constructor <;> linarith [hz.1, hz.2]
    · rw [Real.dist_eq, abs_of_nonneg (by linarith [hz.1] : 0 ≤ z - -2)]
      constructor <;> linarith [hz.1, hz.2]
  have hpair (z : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) : Real.pi - 1 / 100 <
      comparisonAngleNegCurvature 1 (dist z 2) (dist z (-2)) (dist (2 : ℝ) (-2)) := by
    have heq : dist (2 : ℝ) (-2) = dist z 2 + dist z (-2) := by
      rw [Real.dist_eq (2 : ℝ) (-2), Real.dist_eq z 2, Real.dist_eq z (-2),
        abs_of_nonpos (by linarith [hz.2] : z - 2 ≤ 0),
        abs_of_nonneg (by linarith [hz.1] : 0 ≤ z - -2)]
      norm_num
      ring
    rw [heq, comparisonAngleNegCurvature_add (by norm_num)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hbounds z hz 2 (by simp)).1)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hbounds z hz (-2) (by simp)).1)]
    linarith
  obtain ⟨y, hy, hxy, hd, hdu, hv, hvu, _⟩ := exists_paired_geometric_correction
    real_short_curves (Ω := univ) (V := Ioo (-1 : ℝ) 1) (W := ∅)
    (x := 0) (u := 2) (v := -2) (a := 1) (A := 3) (δ := 1 / 100)
    real_comparison (subset_univ _) (subset_univ _) (by norm_num) (by norm_num) le_rfl
    ht (by linarith) ht1 hscale
    (by intro z hz; rw [mem_closedBall, Real.dist_eq, sub_zero] at hz
        obtain ⟨hl, hu⟩ := abs_le.mp hz; constructor <;> linarith)
    hbounds hpair (by simp)
  exact ⟨y, hy, hxy, hd, hdu, hv, hvu⟩

example : ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧
    t ≤ (1 / 100 : ℝ) ^ 2 / (4 * cosh (3 + 1) / sinh 1) := by
  let B := (1 / 100 : ℝ) ^ 2 / (4 * cosh (3 + 1) / sinh 1)
  have hB : 0 < B := by
    apply div_pos (by norm_num)
    exact div_pos (mul_pos (by norm_num) (cosh_pos _)) (sinh_pos_iff.mpr (by norm_num))
  refine ⟨min (1 / 4) (B / 2), lt_min (by norm_num) (half_pos hB), ?_, ?_⟩
  · exact (min_le_left _ _).trans (by norm_num)
  · exact (min_le_right _ _).trans (half_le_self hB.le)

#print axioms Real.sq_div_four_le_one_sub_cos
#print axioms Real.pi_sub_four_mul_le_of_one_add_cos_le
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_paired_geometric_correction
```
