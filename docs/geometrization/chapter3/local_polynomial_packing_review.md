# Compiled self-review: local polynomial packing

Four public theorems in three leaves pass the 133-module/778-owned-declaration
gate. Source-copy unusedArguments, simpNF and synTaut linters are silent;
defLemma is unavailable and declaration kinds were inspected manually.
New closures use only propext, Classical.choice and Quot.sound. Earlier
mathematical leaves are unchanged. The inherited AreaUpperBarrier warning
is outside these closures; no migrated full-root or PDF build is claimed.

The driver applies the local theorem at every real p with actual rank bound
n=1. It also applies the exact radial centered-map bound to the nonempty
annulus [2,3], with the real-line chart embedded in Euclidean Fin1 and
q=0, rho=L=1, t=1/4. The supplied centered chart is used in both bounds.
The main theorem selects h,m,C before all positive epsilon; p=q and p!=q
are both proved. Positive annular inner radius prevents a hidden collision
with q. No assumption of finite packing numbers precedes the finite floor
bound. This is self-review, not human approval. Rough-volume asymptotics
and intrinsic adaptation remain separate.

```lean
import DifferentialGeometry.Geometry.Comparison.LocalPolynomialPacking
import DifferentialGeometry.Geometry.Comparison.LocalCompactness
import DifferentialGeometry.Geometry.Comparison.PairedCompactPatch
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

private noncomputable def lineEmbedding (x : ℝ) : PiLp 2 (fun _ : Fin 1 => ℝ) :=
  WithLp.toLp 2 (fun _ => x)

private theorem lineEmbedding_dist (x y : ℝ) : dist (lineEmbedding x) (lineEmbedding y) = dist x y := by
  simp [PiLp.dist_eq_of_L2, lineEmbedding]

private theorem lineEmbedding_norm (x : ℝ) : ‖lineEmbedding x‖ = |x| := by
  simp [PiLp.norm_eq_of_L2, lineEmbedding, Real.sqrt_sq_eq_abs]

example (p : ℝ) : ∃ h : ℝ, 0 < h ∧ ball p h ⊆ (univ : Set ℝ) ∧
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 1 ∧ ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      finitePackingNumber ε (ball p h) ≤ (⌊(1 + C / ε) ^ m⌋₊ : ℕ∞) := by
  exact exists_local_polynomial_packing_of_fourPointComparison real_short_curves
    isOpen_univ real_comparison
    (fun z _ => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩)
    (n := 1) le_rfl (by rw [Nat.cast_one, Real.dimH_univ]) (mem_univ p)

example {ε : ℝ} (hε : 0 < ε) :
    finitePackingNumber ε (Icc (2 : ℝ) 3) ≤
      (⌊1 + 8 / (((1 / 4) * 3 / sinh 3) * ε)⌋₊ : ℕ∞) := by
  let f : ball (0 : ℝ) 1 → PiLp 2 (fun _ : Fin 1 => ℝ) := fun z => lineEmbedding z
  have hf0 : f ⟨0, by norm_num⟩ = 0 := by ext i; simp [f, lineEmbedding]
  have hflo (x y : ball (0 : ℝ) 1) : (1 : ℝ)⁻¹ * dist x y ≤ dist (f x) (f y) := by
    simp [f, lineEmbedding_dist, Subtype.dist_eq]
  have hfhi (x y : ball (0 : ℝ) 1) : dist (f x) (f y) ≤ (1 : ℝ) * dist x y := by
    simp [f, lineEmbedding_dist, Subtype.dist_eq]
  have hrad (x : ℝ) (hx : x ∈ Icc (2 : ℝ) 3) : dist (0 : ℝ) x ∈ Icc (2 : ℝ) 3 := by
    simpa only [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1] : 0 ≤ x)] using hx
  have hb := finitePackingNumber_le_of_radial_centered_dist_bounds real_short_curves real_comparison
    (q := 0) (mem_univ _) (a := 2) (D := 3) (t := 1 / 4) (ρ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε
    (subset_univ _) (subset_univ _) hrad (m := 1) (by norm_num) (by norm_num)
    (L := 1) (by norm_num) hf0 hflo hfhi
  simpa only [Nat.cast_one, Real.sqrt_one, one_pow, pow_one, mul_one] using hb

#print axioms exists_local_polynomial_packing_of_fourPointComparison
#print axioms finitePackingNumber_le_of_radial_centered_dist_bounds
#print axioms finitePackingNumber_le_floor_of_centered_dist_bounds

```
