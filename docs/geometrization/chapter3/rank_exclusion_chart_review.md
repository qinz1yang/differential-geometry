# Rank-exclusion chart: compiled self-review

This is assistant self-review, not independent human/agent approval.
The lower bound is obtained by contradiction from AC26 on the same original
anchor coordinates and metric. The 3r buffer supplies containment of the
whole correction ball for every pair of points in B(q,r). Coincident points
are handled directly. A coordinate lower bound is converted to the Euclidean
norm, not the l1 norm. The target is the actual range of the same distance map,
and the returned homeomorphism agrees pointwise with it. Its inverse bound
is proved from the lower bound; it is not an extra assumed embedding.
Openness applies on every open subset through the prior uniform-packet proof.
The dimension ceiling uses AC23 and dimension monotonicity on that same Omega.

The four new leaves and all source-copy unusedArguments, simpNF and synTaut
linters compile silently. defLemma is unavailable; declaration kinds were
inspected manually. The combined gate passes for 99 modules, 2887 jobs and
667 owned constants, checking generated helpers and standard-only transitive
axioms. The inherited AreaUpperBarrier admission warning is outside new
closures. Earlier mathematical leaves are unchanged. The static blueprint
audit passes unchanged, frozen207 is preserved, and no migrated root or PDF
build is claimed.

The concrete real-line test PROVES exclusion of rank two using the new
packet dimension theorem and dimH(R)=1. It supplies proved real-line
comparison, short curves, actual anchors +/-2, and a positive radius obeying
the exact hyperbolic scale. The full chart theorem then returns an open image,
the original distance map, Lipschitz constant one, and the exact inverse
constant. Thus the exclusion hypothesis is not merely assumed in this test.
A separate identity-map example exercises the generic range homeomorphism.
Both examples and axiom queries compile without warnings.

```lean
import DifferentialGeometry.Geometry.Comparison.RankExclusionChart
import DifferentialGeometry.Geometry.Comparison.PairedPacketDimension
import DifferentialGeometry.Geometry.Comparison.PairedRankIncrease
import DifferentialGeometry.Geometry.Comparison.AngleReversal
import DifferentialGeometry.Geometry.Comparison.BalancedMidpoint
import DifferentialGeometry.Geometry.Comparison.PairedDistanceLocalOpenness
import Mathlib.Tactic

open Set Metric Real
open scoped Topology ENNReal NNReal
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

private theorem real_anchor_bounds (z : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) (c : ℝ)
    (hc : c ∈ ({2, -2} : Set ℝ)) : dist z c ∈ Icc (1 : ℝ) 3 := by
  simp only [mem_insert_iff, mem_singleton_iff] at hc
  rcases hc with rfl | rfl
  · rw [Real.dist_eq, abs_of_nonpos (by linarith [hz.2] : z - 2 ≤ 0)]
    constructor <;> linarith [hz.1, hz.2]
  · rw [Real.dist_eq, abs_of_nonneg (by linarith [hz.1] : 0 ≤ z - -2)]
    constructor <;> linarith [hz.1, hz.2]

private theorem real_packet : PairedComparisonPacket (1 / 40000) (Ioo (-1 : ℝ) 1)
    (fun _ : Fin 1 => (2 : ℝ)) (fun _ : Fin 1 => (-2 : ℝ)) := by
  constructor
  · intro z hz i
    have heq : dist (2 : ℝ) (-2) = dist z 2 + dist z (-2) := by
      rw [Real.dist_eq (2 : ℝ) (-2), Real.dist_eq z 2, Real.dist_eq z (-2),
        abs_of_nonpos (by linarith [hz.2] : z - 2 ≤ 0),
        abs_of_nonneg (by linarith [hz.1] : 0 ≤ z - -2)]
      norm_num
      ring
    rw [heq, comparisonAngleNegCurvature_add (by norm_num)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (real_anchor_bounds z hz 2 (by simp)).1)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (real_anchor_bounds z hz (-2) (by simp)).1)]
    linarith
  · intro z hz i j hij
    exact False.elim (hij (Subsingleton.elim _ _))

private theorem real_no_rank_two (z : ℝ) (c d : Option (Fin 1) → ℝ) :
    ¬ PairedComparisonPacket (1/400) {z} c d := by
  intro hp
  have h := hp.card_le_dimH real_short_curves real_comparison
    (Filter.univ_mem) (subset_univ _) (by norm_num) (by norm_num)
    (fun z _ => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩)
  rw [Real.dimH_univ] at h
  norm_num at h

example : ∃ r : ℝ, 0 < r ∧ ∃ U : Set (PiLp 2 (fun _ : Fin 1 => ℝ)), IsOpen U ∧
    ∃ e : ball (0 : ℝ) r ≃ₜ U,
      (∀ z, (e z : PiLp 2 (fun _ : Fin 1 => ℝ)) = distanceCoordinates 2 (fun _ : Fin 1 => (2 : ℝ)) (z : ℝ)) ∧
      LipschitzWith 1 e ∧
      LipschitzWith (⟨((1/400 : ℝ) / (100 * Real.pi))^2, sq_nonneg _⟩ : ℝ≥0)⁻¹ e.symm := by
  let β : ℝ := 1/400
  let ε : ℝ := (β / (100 * Real.pi))^2
  let K : ℝ := 4 * cosh (3+1) / sinh 1
  let r : ℝ := min (1/8) (ε / (2 * K))
  have hK : 0 < K := div_pos (by positivity) (sinh_pos_iff.mpr (by norm_num))
  have hε : 0 < ε := by dsimp [ε, β]; positivity
  have hr : 0 < r := lt_min (by norm_num) (div_pos hε (by positivity))
  have hr8 : r ≤ 1/8 := min_le_left _ _
  have hrK : 2 * r ≤ ε / K := by
    have h := (le_div_iff₀ (show 0 < 2 * K by positivity)).mp (min_le_right (1/8) (ε / (2*K)))
    apply (le_div_iff₀ hK).mpr
    nlinarith
  obtain ⟨U, hU, e, he, _, hLip, hInv⟩ := real_packet.exists_chart_of_rank_exclusion
    real_short_curves real_comparison (subset_univ _) (subset_univ _)
    (a₀ := 1) (A := 3) (β := β) (q := 0) (r := r)
    (by norm_num) (by norm_num [β]) (by norm_num [β]) (by norm_num) (by norm_num [β])
    (fun z hz c hc => real_anchor_bounds z hz c (by simpa [or_comm] using hc))
    (fun z _ => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩)
    (fun z _ c d _ => real_no_rank_two z c d)
    hr (by intro z hz; rw [mem_ball, Real.dist_eq, sub_zero, abs_lt] at hz
           constructor <;> linarith [hz.1, hz.2])
    (by linarith) (by linarith) hrK
  exact ⟨r, hr, U, hU, e, he, by simpa using hLip, hInv⟩

example : ∃ e : ℝ ≃ₜ range (fun x : ℝ => x),
    (∀ x, (e x : ℝ) = x) ∧ LipschitzWith 1 e ∧ LipschitzWith 1 e.symm := by
  obtain ⟨e, he, hL, hI⟩ := exists_homeomorph_range_of_lipschitz_lower_bound
    (LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x)) (by norm_num : (0 : ℝ≥0) < 1)
    (by intro x y; simp)
  exact ⟨e, he, hL, by simpa only [inv_one] using hI⟩

#print axioms PairedComparisonPacket.exists_chart_of_rank_exclusion
#print axioms PairedComparisonPacket.card_le_dimH
#print axioms Metric.exists_homeomorph_range_of_lipschitz_lower_bound
```
