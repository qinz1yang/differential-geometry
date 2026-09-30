# AC26 compiled self-review

This is assistant self-review, not independent human/agent approval.
The near-coordinate hypothesis concerns the actual first anchors only. Equal
radial lengths at the same balanced point allow subtraction of the two AC19
remainders. The four cross-angle bounds use the old opposite pair at x,y,z
and the new near-pi pair at z, all in one Omega. Each positive distance and
scale hypothesis is supplied from the packet or the balanced construction.
The error arithmetic retains epsilon=(beta/(100*pi))^2 and the exact E bound.

The Option-indexed extension preserves the original pairs at `some i` and
adjoins (x,y) at `none`. Both old/new cross-index orders are proved using
actual angle symmetry. The same constructed z is returned with balance,
strict containment and the new packet; every old/new anchor remains in Omega.
The stronger allowed parameter range (beta<=1) contains AC26's range, and
there is no hidden positive-rank requirement on this local construction.

All five new leaves and source-copy unusedArguments, simpNF and synTaut
linters compile silently. defLemma is unavailable and declaration kinds were
inspected manually. The 95-module gate passes (2883 jobs, 662 owned constants),
including generated helpers and transitive axiom closure. New proofs use only
propext, Classical.choice and Quot.sound. The inherited AreaUpperBarrier
warning remains outside those closures. Earlier leaves are preserved; the
migrated root is not built. Blueprint207 is unchanged and its static audit
passes. No chart injectivity or later rank hierarchy is claimed here.

The compiled driver exercises the zero-error four-angle case through the
actual theorem and the complete geometric construction with an empty old
packet on the real line, producing an actual rank-one packet and a positive
balanced distance. Its scale satisfies the exact hyperbolic restriction.
This is a nonvacuous boundary use; a concrete positive-old-rank geometric
example is not claimed. Positive-rank generality is kernel-checked in the
quantified theorem, not inferred from this one-dimensional example.

```lean
import DifferentialGeometry.Geometry.Comparison.PairedRankIncrease
import DifferentialGeometry.Geometry.Comparison.AngleReversal
import DifferentialGeometry.Geometry.Comparison.BalancedMidpoint
import DifferentialGeometry.Geometry.Comparison.PairedDistanceLocalOpenness
import Mathlib.Tactic

open Set Metric Real
open scoped Topology ENNReal
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

private theorem real_packet : PairedComparisonPacket (1 / 200) (Ioo (-1 : ℝ) 1)
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

example : |(Real.pi/2 : ℝ) - Real.pi/2| ≤ 0 ∧
    |(Real.pi/2 : ℝ) - Real.pi/2| ≤ 0 ∧
    |(Real.pi/2 : ℝ) - Real.pi/2| ≤ 0 ∧
    |(Real.pi/2 : ℝ) - Real.pi/2| ≤ 0 := by
  have h := four_cross_angles_near_pi_div_two
    (δ := 0) (τ := 0) (ω := 0) (σ := 0)
    (α := Real.pi/2) (α' := Real.pi/2) (γ := Real.pi/2) (γ' := Real.pi/2)
    (by norm_num) (by norm_num) (by norm_num) (by simp)
    (by linarith) (by linarith) (by linarith) (by linarith)
  simpa only [mul_zero, zero_mul, zero_div, add_zero] using h

example :
    let L := min (1/4) (((1 : ℝ) / (100 * Real.pi))^2 / (4 * cosh (1+1) / sinh 1))
    ∃ z : ℝ, 0 < dist (0 : ℝ) z ∧
      PairedComparisonPacket 1 {z}
        (fun i : Option (Fin 0) => i.elim 0 (fun j => Fin.elim0 j))
        (fun i : Option (Fin 0) => i.elim L (fun j => Fin.elim0 j)) := by
  intro L
  have hK : 0 < 4 * cosh (1+1 : ℝ) / sinh 1 := by
    exact div_pos (by positivity) (sinh_pos_iff.mpr (by norm_num))
  have hL : 0 < L := lt_min (by norm_num) (div_pos (by positivity) hK)
  have hL1 : L ≤ 1/4 := min_le_left _ _
  have hLK : L ≤ ((1 : ℝ) / (100 * Real.pi))^2 / (4 * cosh (1+1) / sinh 1) := min_le_right _ _
  have hd : dist (0 : ℝ) L = L := by rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hL]
  have hp : PairedComparisonPacket 0 (univ : Set ℝ)
      (fun i : Fin 0 => (Fin.elim0 i : ℝ)) (fun i : Fin 0 => (Fin.elim0 i : ℝ)) := by
    constructor <;> intro z hz i <;> exact Fin.elim0 i
  obtain ⟨z, _, _, hslo, _, hpacket, _⟩ := hp.exists_extension_of_near_coordinates
    real_short_curves real_comparison (subset_univ _) (subset_univ _)
    (a₀ := 1) (A := 1) (β := 1) (x := 0) (y := L)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro z hz c hc; simp at hc)
    (by rwa [hd]) (by rw [hd]; linarith) (by rw [hd]; linarith) (by rwa [hd])
    (subset_univ _) (by intro i; exact Fin.elim0 i)
  exact ⟨z, by rw [hd] at hslo; linarith, hpacket⟩

#print axioms PairedComparisonPacket.exists_extension_of_near_coordinates
#print axioms balanced_cross_angles_near_pi_div_two
#print axioms PairedComparisonPacket.extend
```
