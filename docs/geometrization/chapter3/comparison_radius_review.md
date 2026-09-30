# Compiled self-review: actual comparison radii and germ preservation

Ten public theorems, one definition and a generated declaration add 12 owned
declarations. The 177-module gate passes for 968 owned declarations. All new
transitive axiom closures use only propext, Classical.choice and Quot.sound.
Source-copy unusedArguments, simpNF and synTaut linters are silent; defLemma
is unavailable, and declaration kinds were inspected manually. Earlier
mathematical leaves are unchanged. The inherited AreaUpperBarrier warning
is outside these closures. Static audit passes; no migrated full-root, PDF
or Overleaf build is claimed.

The compiled driver proves real-line comparison and actual joins. It computes
the capped radius as exactly 3 when M=3 and exactly 0 when M=0. It constructs
an isometry segment from a germ whose original value at zero is 99 but whose
specified center is 0, checking the actual zero and terminal values. It also
checks the zero-length segment adapter with center 7 and arbitrary original
curve value 99. Finally it derives the full endpoint comparison property at
radius 18 from the radius-12 hypotheses and actual real-line joins.

Statement audit: capped radii are actual suprema of the stated good-radius
set. Strict-below comparison uses a larger admissible witness, not supremum
attainment. Local lower bounds are uniform across a neighborhood. The germ
adapter agrees at every positive parameter, preserves the canonical angle,
and supplies the required closed-interval isometries. The final complete
space contradiction and global four-point conclusions remain separate.

```lean
import DifferentialGeometry.Geometry.Comparison.ComparisonRadius
import DifferentialGeometry.Geometry.Comparison.EndpointEnlargement
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

example : cappedEndpointComparisonRadius 2 (6 : ℝ) 3 = 3 := by
  apply le_antisymm (cappedEndpointComparisonRadius_mem_Icc 2 (6 : ℝ) (by norm_num)).2
  exact le_cappedEndpointComparisonRadius (by norm_num) le_rfl
    (real_endpoint_comparison (by norm_num) 6 3)

example : cappedEndpointComparisonRadius 2 (6 : ℝ) 0 = 0 := by
  have h := cappedEndpointComparisonRadius_mem_Icc 2 (6 : ℝ) (M := 0) le_rfl
  exact le_antisymm h.2 h.1

example : ∃ σ : Icc (0 : ℝ) 2 → ℝ, Isometry σ ∧
    σ ⟨0, by norm_num⟩ = 0 ∧ σ ⟨2, by norm_num⟩ = 2 := by
  let γ : ℝ → ℝ := fun t => if t = 0 then 99 else t
  have hrad : ∀ s ∈ Ioc (0 : ℝ) 2, dist (0 : ℝ) (γ s) = s := by
    intro s hs
    simp [γ, hs.1.ne', Real.dist_eq, abs_of_pos hs.1]
  have hmin : ∀ s ∈ Ioc (0 : ℝ) 2, ∀ t ∈ Ioc (0 : ℝ) 2,
      dist (γ s) (γ t) = |s - t| := by
    intro s hs t ht
    simp [γ, hs.1.ne', ht.1.ne', Real.dist_eq]
  obtain ⟨σ, hσ, hσ0, hσeq⟩ := exists_isometry_segment_of_germ (by norm_num : (0 : ℝ) ≤ 2) hrad hmin
  refine ⟨σ, hσ, hσ0, ?_⟩
  have h := hσeq 2 (by norm_num)
  simpa [γ] using h

example : ∃ σ : Icc (0 : ℝ) 0 → ℝ, Isometry σ ∧ σ ⟨0, by norm_num⟩ = 7 := by
  obtain ⟨σ, hσ, hσ0, hσeq⟩ := exists_isometry_segment_of_germ
    (x := (7 : ℝ)) (γ := fun _ => (99 : ℝ)) (R := 0) le_rfl
    (by intro s hs; have := hs.1; have := hs.2; linarith)
    (by intro s hs t ht; have := hs.1; have := hs.2; linarith)
  exact ⟨σ, hσ, hσ0⟩

example : endpointHingeComparison 2 (6 : ℝ) 18 := by
  apply endpointHingeComparison_enlarge (by norm_num) (by norm_num)
    (real_endpoint_comparison (by norm_num) 6 (2 * 18 / 3))
  · intro q hq
    exact real_endpoint_comparison (by norm_num) q (2 * 18 / 3)
  · intro q hq z hz
    exact real_joins 6 q z
  · intro z hz
    exact ⟨univ, isOpen_univ, real_comparison (by norm_num), mem_univ z⟩

#print axioms cappedEndpointComparisonRadius_mem_Icc
#print axioms endpointHingeComparison_of_lt_cappedRadius
#print axioms exists_uniform_cappedComparisonRadius_lower_bound
#print axioms MinimizingHinge.exists_hinge_of_germs
#print axioms endpointHingeComparison_enlarge
```
