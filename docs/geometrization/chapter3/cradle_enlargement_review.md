# Compiled self-review: full ALG02 cradle enlargement

Twenty-one public theorems, three definitions, one actual hinge structure
and its generated declarations add 53 owned declarations. The 173-module gate
passes for 956 owned declarations. All new transitive axiom closures use only
propext, Classical.choice and Quot.sound. Source-copy unusedArguments, simpNF
and synTaut linters are silent; defLemma is unavailable, and declaration
kinds were inspected manually. Earlier mathematical leaves are unchanged.
The inherited AreaUpperBarrier warning is outside these closures. Static
audit passes; no migrated full-root, PDF or Overleaf build is claimed.

The compiled driver proves actual real-line four-point comparison, endpoint
comparison for every radius, and existence of the required minimizing joins
for every center and both endpoints. It applies the full headline to an
ARBITRARY supplied real-line hinge, retaining its segments. A concrete hinge
with center 0 and endpoints 6,8 has total length 14, beyond the short threshold 12
for ell 18, and satisfies the full comparison-angle conclusion at curvature
minus 2. Reversal retains its angle/model side. Further examples check order
reflection at nonendpoint angles and inversion at a zero opposite side.
The tests supply actual geometric data and prove every antecedent.

Statement audit: the headline quantifies over the same supplied hinge. The
local-comparison and join-availability hypotheses range over all centers
of arm sum below ell, exactly where the constructed iteration remains.
No side inequality, sequence, convergence, successor, compactness or dimension
is assumed by the headline. The finite stopping cases are discharged before
entering the failing-state iteration. Zero arms are included in the side
statement; the angle statement explicitly requires positive arms. The source's
adjacent inequality suffices. Intrinsic/restricted metric translation,
production of joins from an accepted PC release, and ALG04 globalization
remain separate. This is a compiled self-review, not human approval.

```lean
import DifferentialGeometry.Geometry.Comparison.CradleEnlargement
import Mathlib.Tactic

open Set Metric Filter Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

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


private theorem real_endpoint_comparison {κ : ℝ} (hκ : 0 ≤ κ) (p r : ℝ) :
    endpointHingeComparison κ p r := by
  intro x R S γ β hR hS hsum hend hγrad hβrad hγmin hβmin
  rw [germComparisonAngle_eq_limitingComparisonAngle hκ hR hS (real_comparison hκ)
    (mem_univ x) hγrad hβrad hγmin hβmin (fun _ _ => mem_univ _) (fun _ _ => mem_univ _), ← hend]
  exact comparisonAngleNegCurvature_le_limitingComparisonAngle γ β ⟨hR, le_rfl⟩ ⟨hS, le_rfl⟩

private theorem real_segment (x y : ℝ) :
    ∃ σ : Icc (0 : ℝ) (dist x y) → ℝ, Isometry σ ∧
      σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
      σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
  by_cases hxy : x ≤ y
  · refine ⟨fun t => x + (t : ℝ), ?_, by simp, ?_⟩
    · apply Isometry.of_dist_eq
      intro s t
      change |x + (s : ℝ) - (x + (t : ℝ))| = |(s : ℝ) - (t : ℝ)|
      congr 1
      ring
    · change x + dist x y = y
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
      ring
  · refine ⟨fun t => x - (t : ℝ), ?_, by simp, ?_⟩
    · apply Isometry.of_dist_eq
      intro s t
      change |x - (s : ℝ) - (x - (t : ℝ))| = |(s : ℝ) - (t : ℝ)|
      rw [show x - (s : ℝ) - (x - (t : ℝ)) = -((s : ℝ) - (t : ℝ)) by ring, abs_neg]
    · change x - dist x y = y
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hxy))]
      ring

private theorem real_joins (p q z : ℝ) : ∃ J : MinimizingHinge p q, J.center = z := by
  obtain ⟨η, hη, hη0, hηp⟩ := real_segment z p
  obtain ⟨σ, hσ, hσ0, hσq⟩ := real_segment z q
  exact ⟨⟨z, η, σ, hη, hσ, hη0, hσ0, hηp, hσq⟩, rfl⟩

example {p q κ ℓ : ℝ} (H : MinimizingHinge p q) (hκ : 0 ≤ κ) (hℓ : 0 < ℓ)
    (hsum : dist H.center p + dist H.center q < ℓ) : dist p q ≤ H.modelSide κ := by
  exact H.modelSide_ge_dist_of_small_hinges hκ hℓ
    (real_endpoint_comparison hκ p (2 * ℓ / 3))
    (real_endpoint_comparison hκ q (2 * ℓ / 3))
    (fun z _ => real_joins p q z)
    (fun z _ => ⟨univ, isOpen_univ, real_comparison hκ, mem_univ z⟩) hsum

private def large_hinge : MinimizingHinge (6 : ℝ) 8 where
  center := 0
  left := fun t => t
  right := fun t => t
  left_isometry := isometry_subtype_coe
  right_isometry := isometry_subtype_coe
  left_zero := rfl
  right_zero := rfl
  left_end := by norm_num [Real.dist_eq]
  right_end := by norm_num [Real.dist_eq]

example : comparisonAngleNegCurvature 2 6 8 2 ≤ large_hinge.germAngle 2 := by
  have h := large_hinge.comparisonAngle_le_of_small_hinges (κ := 2) (ℓ := 18)
    (by norm_num) (by norm_num)
    (real_endpoint_comparison (by norm_num) 6 (2 * 18 / 3))
    (real_endpoint_comparison (by norm_num) 8 (2 * 18 / 3))
    (fun z _ => real_joins 6 8 z)
    (fun z _ => ⟨univ, isOpen_univ, real_comparison (by norm_num), mem_univ z⟩)
    (by norm_num [large_hinge, Real.dist_eq])
    (by norm_num [large_hinge, Real.dist_eq])
    (by norm_num [large_hinge, Real.dist_eq])
  norm_num [large_hinge, Real.dist_eq] at h ⊢
  exact h

example : large_hinge.reverse.germAngle 2 = large_hinge.germAngle 2 :=
  large_hinge.germAngle_reverse 2

example : large_hinge.reverse.modelSide 2 = large_hinge.modelSide 2 :=
  large_hinge.modelSide_reverse 2

example : modelSideNegCurvature 2 2 3 (Real.pi / 3) ≤ modelSideNegCurvature 2 2 3 (Real.pi / 2) ↔
    Real.pi / 3 ≤ Real.pi / 2 := by
  apply modelSideNegCurvature_le_iff_angle_le (by norm_num) (by norm_num) (by norm_num)
  · constructor <;> linarith [Real.pi_pos]
  · constructor <;> linarith [Real.pi_pos]

example : comparisonAngleNegCurvature 2 2 2 0 ≤ 0 ↔
    (0 : ℝ) ≤ modelSideNegCurvature 2 2 2 0 := by
  apply comparisonAngleNegCurvature_le_iff_le_modelSide (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨le_rfl, Real.pi_pos.le⟩

#print axioms MinimizingHinge.modelSide_ge_dist_of_small_hinges
#print axioms MinimizingHinge.comparisonAngle_le_of_small_hinges
#print axioms MinimizingHinge.exists_cradle_successor_of_modelSide_lt
#print axioms MinimizingHinge.exists_hinge_with_forward_right
#print axioms comparisonAngleNegCurvature_le_iff_le_modelSide
```
