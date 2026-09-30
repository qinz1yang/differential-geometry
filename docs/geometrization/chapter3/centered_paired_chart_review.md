# Compiled self-review: centered paired chart

Five public theorems and one definition in three leaves complete AC28 at the
stated metric scope. The selected rank and anchors are produced from the
geometry; no chart, injectivity or maximal packet is assumed. The centered
map is exactly the selected first-anchor distance vector minus its value at
the selected center. The image is proved open, the map is an actual
homeomorphism, and both estimates use the exact blueprint L_n. No positive
lower bound on the chosen radius is claimed.

The driver checks the explicit L_1=(16000000*pi)^2 value and derives a chart
of rank exactly one inside every real interval (-s,s), s>0, retaining the
centered coordinate formula, zero center, open image and both metric bounds.
This prevents an empty-domain, zero-rank or abstract-replacement consumer.
Source-copy `unusedArguments simpNF synTaut` lint passes silently; `defLemma`
is unavailable in this pin, so declaration kinds were checked manually.
All new dependency closures use only propext, Classical.choice and Quot.sound.
The scoped gate replays the inherited AreaUpperBarrier admission warning;
that declaration is outside the new closures. Earlier math leaves are
unchanged. This is compiled self-review, not human approval. No full migrated
root or new PDF build was run.

```lean
import DifferentialGeometry.Geometry.Comparison.CenteredPairedChart
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

example : pairedChartDistortion 1 = (16000000 * Real.pi) ^ 2 := by
  have ht : pairedChartQuality 1 1 = 1 / 160000 := by norm_num [pairedChartQuality]
  unfold pairedChartDistortion
  rw [ht]
  norm_num
  rw [max_eq_right]
  · congr 1
    ring
  · nlinarith [Real.two_le_pi]

example {s : ℝ} (hs : 0 < s) :
    ∃ m : ℕ, m = 1 ∧ ∃ q ∈ Ioo (-s) s, ∃ a : Fin m → ℝ,
      ∃ r : ℝ, ∃ hr : 0 < r, ball q r ⊆ Ioo (-s) s ∧
      ∃ U : Set (PiLp 2 (fun _ : Fin m => ℝ)), IsOpen U ∧
      ∃ e : ball q r ≃ₜ U,
        (∀ z, (e z : PiLp 2 (fun _ : Fin m => ℝ)) =
          distanceCoordinates 2 a (z : ℝ) - distanceCoordinates 2 a q) ∧
        (e ⟨q, mem_ball_self hr⟩ : PiLp 2 (fun _ : Fin m => ℝ)) = 0 ∧
        (∀ x y, (pairedChartDistortion 1)⁻¹ * dist x y ≤ dist (e x) (e y)) ∧
        (∀ x y, dist (e x) (e y) ≤ pairedChartDistortion 1 * dist x y) := by
  obtain ⟨m, hm1, hmn, q, hq, a, _, r, hr, hB, U, hU, e, he, hzero, hlo, hhi⟩ :=
    exists_centered_distance_chart_in_open_set real_short_curves real_comparison
      (subset_univ _) isOpen_Ioo (show (Ioo (-s) s).Nonempty from ⟨0, by constructor <;> linarith⟩)
      (fun z _ => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩)
      (n := 1) le_rfl (by rw [Nat.cast_one, Real.dimH_univ])
  exact ⟨m, by omega, q, hq, a, r, hr, hB, U, hU, e, he, hzero, hlo, hhi⟩

#print axioms exists_centered_distance_chart_in_open_set
#print axioms exists_distance_chart_in_open_set
#print axioms inverse_pairedChartDistortion_le_quality

```
