# Uniform-packet openness: self-review and compiled consumers

This is an assistant self-review, not independent human/agent approval.
The packet contains actual opposite/cross comparison inequalities. The
finite move proof keeps the original first-anchor coordinates when its
direction is reversed. Exact target coordinates and the same metric are
used in the geometric step, l1 residual, limit, image inclusion and open-map
conclusion. Every move stays in the same comparison domain. The complete
ball is explicit and need not coincide with the whole space.

The final openness proof repeats the quantitative construction inside any
open subset of the working region. It does not infer openness from the
image of just one neighborhood. Norm transport is through the existing
PiLp homeomorphisms; no altered source metric or length structure is asserted.
Pointwise-to-uniform packet localization remains a separate obligation.

All four new leaves and source-copy declaration linters (unusedArguments,
simpNF, synTaut) compile silently. Nine public theorems, one private theorem,
and one explicit proposition structure are checked, including its generated
constructors/projections/recursors. The combined gate passes for 83 modules /
2871 jobs / 635 owned constants. New axiom closures are standard. defLemma is
unavailable; declaration kinds were manually inspected. The inherited
AreaUpperBarrier warning is outside these new dependencies; no full migrated
root is built. Earlier mathematical leaves and blueprint207 are unchanged.

Four compiled examples use a real-line packet whose comparison and curve
inputs are proved in the driver: restriction/weakening/swap, actual Euclidean
open-map assembly, the exact positive target-ball inclusion, and correction
toward a second anchor while preserving the first-anchor coordinate. The
one-dimensional examples are nonvacuous; their finite cross-index condition
is empty, so no separate concrete higher-dimensional packet test is claimed.

```lean
import DifferentialGeometry.Geometry.Comparison.PairedDistanceOpenness
import Mathlib.Tactic

open Set Metric Real
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

private theorem real_packet : PairedComparisonPacket (1 / 100) (Ioo (-1 : ℝ) 1)
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

example : PairedComparisonPacket (1 / 50) (Ioo (-1 / 2 : ℝ) (1 / 2))
    (fun _ : Fin 1 => (-2 : ℝ)) (fun _ : Fin 1 => (2 : ℝ)) := by
  apply (real_packet.swap.weaken (by norm_num)).mono
  intro z hz
  constructor <;> linarith [hz.1, hz.2]

example : IsOpenMap (fun z : Ioo (-1 : ℝ) 1 =>
    distanceCoordinates 2 (fun _ : Fin 1 => (2 : ℝ)) (z : ℝ)) := by
  apply real_packet.isOpenMap_distanceCoordinates real_short_curves
    real_comparison (subset_univ _) isOpen_Ioo (subset_univ _)
    (a₀ := 1) (A := 3) (by norm_num) (by norm_num) (by norm_num)
  · intro q _
    exact ⟨1, by norm_num, isClosed_closedBall.isComplete⟩
  · intro z hz c hc
    apply real_anchor_bounds z hz c
    simpa [or_comm] using hc

example :
    let μ := 1 - 3 * (1 / 100 : ℝ) ^ 2
    let ε := min 1 (min (1 / 2) (min ((1 / 100 : ℝ) ^ 2 / (4 * cosh (3 + 1) / sinh 1)) (μ * (1 / 4) / 2)))
    0 < ε ∧ ball (distanceCoordinates 1 (fun _ : Fin 1 => (2 : ℝ)) 0) ε ⊆
      distanceCoordinates 1 (fun _ : Fin 1 => (2 : ℝ)) '' ball (0 : ℝ) (1 / 4) := by
  have h := real_packet.ball_subset_distanceCoordinates_image real_short_curves real_comparison
    (subset_univ _) (subset_univ _) (q := 0) (a₀ := 1) (A := 3) (r := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) isClosed_closedBall.isComplete
    (by intro z hz; rw [mem_ball, Real.dist_eq, sub_zero, abs_lt] at hz
        constructor <;> linarith [hz.1, hz.2])
    (fun z hz c hc => real_anchor_bounds z hz c (by simpa [or_comm] using hc))
  simpa using h

example {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 2)
    (hscale : t ≤ (1 / 100 : ℝ) ^ 2 / (4 * cosh (3 + 1) / sinh 1)) :
    ∃ y ∈ Ioo (-1 : ℝ) 1, dist 0 y = t ∧
      (1 - 3 * (1 / 100 : ℝ) ^ 2) * t ≤ dist y 2 - dist (0 : ℝ) 2 ∧
      dist y 2 - dist (0 : ℝ) 2 ≤ t := by
  obtain ⟨y, hy, hxy, hdir, _⟩ := real_packet.exists_distance_coordinate_move
    real_short_curves real_comparison (subset_univ _) (subset_univ _)
    (x := 0) (a₀ := 1) (A := 3) (by norm_num) (by norm_num) le_rfl
    ht (by linarith) ht1 hscale
    (by intro z hz; rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hz
        constructor <;> linarith [hz.1, hz.2])
    (fun z hz c hc => real_anchor_bounds z hz c (by simpa [or_comm] using hc)) 0 3
  simp only [Real.dist_eq] at hdir
  norm_num at hdir
  refine ⟨y, hy, hxy, ?_⟩
  norm_num [Real.dist_eq]
  exact hdir

#print axioms PairedComparisonPacket
#print axioms PairedComparisonPacket.exists_distance_coordinate_move
#print axioms PairedComparisonPacket.exists_distance_residual_correction
#print axioms PairedComparisonPacket.exists_preimage_in_complete_buffer
#print axioms PairedComparisonPacket.ball_subset_distanceCoordinates_image
#print axioms PairedComparisonPacket.isOpenMap_distanceCoordinates_one
#print axioms PairedComparisonPacket.isOpenMap_distanceCoordinates
```
