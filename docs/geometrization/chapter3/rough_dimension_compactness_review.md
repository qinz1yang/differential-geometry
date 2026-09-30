# Compiled self-review: rough-dimension compactness

Four public theorems in two leaves pass the 139-module/801-owned-declaration
gate. Source-copy unusedArguments, simpNF and synTaut linters are silent.
defLemma is unavailable; declaration kinds were inspected manually.
New closures contain only propext, Classical.choice and Quot.sound. Earlier
mathematical leaves are unchanged. The inherited AreaUpperBarrier warning
is outside these closures; no full migrated-root or PDF build is claimed.
The blueprint static audit passes.

The driver produces a compact positive closed-ball neighborhood at every
real point through AC33 and rough dimension. It proves total boundedness
of the incomplete open interval (0,1) from its actual polynomial bound,
checking that completeness is not accidentally required at that step.
It also obtains eventual finite packing for a singleton from positive-
exponent rough volume. The proof uses the actual finite ENat value, and
chooses a smaller packing scale for each requested net radius. Complete
closed-ball restriction is explicit and used only for compactness.
This is self-review, not human approval; intrinsic adaptation remains open.

```lean
import DifferentialGeometry.Geometry.Comparison.RoughLocalCompactness
import DifferentialGeometry.Topology.MetricSpace.EuclideanPacking
import DifferentialGeometry.Geometry.Comparison.LocalRoughDimension
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

example (p : ℝ) : ∃ r : ℝ, 0 < r ∧ closedBall p r ⊆ (univ : Set ℝ) ∧
    IsCompact (closedBall p r) := by
  exact exists_compact_closedBall_of_local_rough_dimension real_short_curves
    isOpen_univ real_comparison
    (fun z _ => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩)
    (n := 1) (by rw [Nat.cast_one, Real.dimH_univ]) (mem_univ p)

example : TotallyBounded (Ioo (0 : ℝ) 1) := by
  let f : Ioo (0 : ℝ) 1 → PiLp 2 (fun _ : Fin 1 => ℝ) := fun x => lineEmbedding x
  have hn (x : Ioo (0 : ℝ) 1) : ‖f x‖ ≤ (1 : ℝ) := by
    rw [show f x = lineEmbedding x from rfl, lineEmbedding_norm, abs_of_pos x.property.1]
    exact x.property.2.le
  have hl (x y : Ioo (0 : ℝ) 1) : (1 : ℝ) * dist x y ≤ dist (f x) (f y) := by
    simp [f, lineEmbedding_dist, Subtype.dist_eq]
  have hpack (ε : ℝ) (hε : 0 < ε) : finitePackingNumber ε (Ioo (0 : ℝ) 1) ≤
      (⌊(1 + (4 : ℝ) / ε) ^ (1 : ℕ)⌋₊ : ℕ∞) := by
    have h := finitePackingNumber_le_floor_of_bounded_lower_dist_map
      (m := 1) (by norm_num) (B := 1) (K := 1) (by norm_num) (by norm_num) hε hn hl
    simpa only [Nat.cast_one, Real.sqrt_one, mul_one, one_mul] using h
  have hd := roughDim_le_of_polynomial_bound (C := 4) (by norm_num) hpack
  exact totallyBounded_of_roughDim_lt_top (hd.trans_lt (by simp))

example (p : ℝ) : ∀ᶠ ε : ℝ in 𝓝[>] 0, finitePackingNumber ε ({p} : Set ℝ) ≠ ⊤ := by
  have hpack (ε : ℝ) (_ : 0 < ε) : finitePackingNumber ε ({p} : Set ℝ) ≤
      (⌊(1 + (0 : ℝ) / ε) ^ (0 : ℕ)⌋₊ : ℕ∞) := by
    simpa using finitePackingNumber_le_one_of_subsingleton subsingleton_singleton ε
  exact eventually_finitePackingNumber_ne_top_of_roughVolume_eq_zero
    (roughVolume_eq_zero_of_polynomial_bound (m := 0) (C := 0) (b := 1)
      le_rfl (by norm_num) hpack)

#print axioms totallyBounded_of_roughDim_lt_top
#print axioms exists_compact_closedBall_of_roughDim_lt_top
#print axioms exists_compact_closedBall_of_local_rough_dimension

```
