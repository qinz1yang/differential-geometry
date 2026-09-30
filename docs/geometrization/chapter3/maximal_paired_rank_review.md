# Compiled self-review: finite paired rank

All four new leaves build in the scoped gate. The source-copy lint suite
`unusedArguments simpNF synTaut` passes silently. `defLemma` is unavailable in
this Mathlib pin; declaration kinds were checked manually. The review below
checks exact small-n quality values, a nonempty real-line open set yielding
rank exactly one with next-rank exclusion, and the nearby distinct-point
consumer. It compiles with only the displayed standard axiom reports.

The proof uses an actual positive rank seed and a bounded natural maximum;
there is no assumed maximal packet, chart, injectivity or recognition. The
Option-indexed excluded packet is explicitly reindexed before the maximum
argument. New closures contain only propext, Classical.choice and Quot.sound.
The gate still replays the inherited AreaUpperBarrier admission warning,
which is outside these new closures. This is a self-review, not human approval.

```lean
import DifferentialGeometry.Geometry.Comparison.MaximalPairedRank
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

example : pairedChartQuality 1 1 = 1/160000 := by norm_num [pairedChartQuality]
example : pairedChartQuality 1 2 = 1/800 := by norm_num [pairedChartQuality]
example : pairedChartQuality 0 0 = 1/80000 := by norm_num [pairedChartQuality]

example : ∃ m : ℕ, m = 1 ∧ ∃ q ∈ Ioo (-1 : ℝ) 1, ∃ a b : Fin m → ℝ,
    PairedComparisonPacket (pairedChartQuality 1 m) {q} a b ∧
    ∀ z ∈ Ioo (-1 : ℝ) 1, ∀ c d : Option (Fin m) → ℝ,
      ¬ PairedComparisonPacket (pairedChartQuality 1 (m+1)) {z} c d := by
  obtain ⟨m, hm1, hmn, q, hq, a, b, hp, _, hno⟩ := exists_maximal_paired_rank
    real_short_curves real_comparison (subset_univ _) isOpen_Ioo
    (show (Ioo (-1 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩)
    (fun z _ => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩)
    (n := 1) le_rfl (by rw [Nat.cast_one, Real.dimH_univ])
  exact ⟨m, by omega, q, hq, a, b, hp, fun z hz c d => hno z hz c d (subset_univ _)⟩

example (p : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ y : ℝ, 0 < dist p y ∧ dist p y < ε :=
  exists_nearby_point_of_arbitrarily_short_curves real_short_curves p hε

#print axioms exists_maximal_paired_rank
#print axioms exists_rank_one_packet_in_open_set
#print axioms pairedChartQuality_eq_reciprocal

```
