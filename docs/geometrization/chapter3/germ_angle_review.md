# Compiled self-review: local germ angles

Sixteen public theorems and one definition in three leaves pass the
149-module/833-owned-declaration gate. Nineteen owned declarations are
added, including generated proof declarations. The source-copy unusedArguments,
simpNF and synTaut linters are silent. defLemma is unavailable at this pin;
declaration kinds were inspected manually. Closures use only propext,
Classical.choice and Quot.sound. This includes the reused existing joint-limit
helper. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning remains outside the new closures. Static audit passes;
no full migrated-root, PDF or Overleaf build is claimed.

The compiled examples prove actual four-point comparison on the real line
for every nonnegative kappa. At kappa=2 they exercise genuine positive arms,
independent two-parameter convergence for opposite rays to pi, zero self-angle,
and the local existence consumer with no assumed angle or monotonicity input.
The geometric hypotheses in those examples are proved, not assumed. The
public main theorem uses a product of right-neighborhood filters; the
subsequent diagonal specialization is used only to pass the finite three-angle
inequality to the already established joint limits. Radius restriction uses
uniqueness in a nontrivial filter. Local hinge containment is proved before
applying the common-domain comparison theorem. The uniform radius is chosen
before every hinge parameter, including the moving center.

The model parameter kappa means curvature -kappa. Zero and positive kappa
are separate branches of finite shortening; no division by a zero shortened
arm occurs. Opposite-germ input supplies exact distance addition on the
chosen subsegments. Only the adjacent-angle inequality is concluded. This
is self-review, not human approval or a claim that globalization is finished.

```lean
import DifferentialGeometry.Geometry.Comparison.LocalGermAngle
import Mathlib.Tactic
open Set Filter Topology Metric
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


private theorem positive_radial {R : ℝ} (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R) :
    dist (0 : ℝ) s = s := by
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hs.1]

private theorem negative_radial {R : ℝ} (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R) :
    dist (0 : ℝ) (-s) = s := by
  rw [Real.dist_eq, sub_neg_eq_add, zero_add, abs_of_pos hs.1]

private theorem opposite_distance {R S : ℝ} (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) S) : dist s (-t) = s + t := by
  rw [Real.dist_eq, sub_neg_eq_add, abs_of_pos (add_pos hs.1 ht.1)]

example : Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature 2 z.1 z.2
    (dist z.1 (-z.2))) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 Real.pi) := by
  have h := tendsto_limitingComparisonAngle_of_fourPointComparison
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 3) (real_comparison (by norm_num : (0 : ℝ) ≤ 2))
    (mem_univ (0 : ℝ)) (γ := id) (β := fun t : ℝ => -t)
    positive_radial negative_radial
    (fun s _ t _ => Real.dist_eq s t)
    (fun s _ t _ => by rw [dist_neg_neg]; exact Real.dist_eq s t)
    (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
  have heq : limitingComparisonAngle 2 2 3 (id : ℝ → ℝ) (fun t => -t) = Real.pi :=
    limitingComparisonAngle_opposite (γ := id) (β := fun t : ℝ => -t)
      (by norm_num) (by norm_num) (by norm_num) opposite_distance
  rw [heq] at h
  simpa only [id_eq] using h

example : limitingComparisonAngle 2 2 2 (id : ℝ → ℝ) id = 0 := by
  exact limitingComparisonAngle_self (by norm_num) (by norm_num)
    (fun s _ t _ => Real.dist_eq s t)

example : ∃ r ∈ Ioc (0 : ℝ) 2,
    limitingComparisonAngle 2 r r (id : ℝ → ℝ) (fun t => -t) ∈ Icc 0 Real.pi ∧
    Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature 2 z.1 z.2
      (dist z.1 (-z.2))) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝 (limitingComparisonAngle 2 r r (id : ℝ → ℝ) (fun t => -t))) := by
  simpa only [min_self, id_eq] using exists_local_comparisonAngle_limit
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2) isOpen_univ
    (real_comparison (by norm_num : (0 : ℝ) ≤ 2)) (mem_univ (0 : ℝ))
    (γ := id) (β := fun t : ℝ => -t) positive_radial negative_radial
    (fun s _ t _ => Real.dist_eq s t)
    (fun s _ t _ => by rw [dist_neg_neg]; exact Real.dist_eq s t)

#print axioms DifferentialGeometry.Toponogov.tendsto_sSup_positiveRectangle
#print axioms comparisonAngleNegCurvature_le_of_shortening_left
#print axioms limitingComparisonAngle_sum_le_two_pi
#print axioms exists_uniform_hinge_angle_limit

```
