# Compiled self-review: quantitative signed product Busemann limits

Nine public theorems in two leaves add nine owned declarations. The276-module
gate checks1304 owned declarations (3110 jobs), with transitive axiom closures
limited to propext, Classical.choice and Quot.sound. Source-copy unusedArguments,
simpNF and synTaut linters are silent. Declaration kinds were manually inspected;
defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning is outside these closures. Static audit passes. No full
migrated root, fresh blueprint PDF/Overleaf build, human or delegated review is claimed.

The independent compiled driver uses the genuine L2 cylinder R x_2 AddCircle4.
At the actual point(3,1), the transverse distance is independently proved tobe1,
the basepoint distance issqrt(10), and the point lies in the closed4-ball. For
EVERY T>4 it verifies both signed-axis error estimates with the exact constant
16/(2(T-4)); the positive-ray Busemann limit is-3. The uniform theorem is tested
for every fixed cylinder ball and every positive accuracy, not just this point.
The geometric line-splitting consumer is tested on the actual real line with
proved comparison and explicit minimizing segments, for BOTH oriented lines
gamma(t)=t andgamma(t)=-t. It yields limits-x and+x respectively, so a wrong
Busemann sign or silently discarded orientation would fail these tests. The
driver exits zero with nine axiom reports.

Statement audit checks the actual L2 metric and nonzero transverse contribution,
the exact rationalizedB^2/(2(T-B)) error, both nonnegativity bounds and strict
positive denominator, all-point uniformity on fixed balls, finite real limits,
and preservation of the supplied positive orientation. The product statements
assume no geometry of the transverse factor. The one-line geometric consumer
uses the existing actual onto lineSplitting, without assuming finite dimension.
The result identifies the Busemann limit with the negative of its established
lineCoordinate. Long-strainer prefixes/lines, their source calibration and
multi-axis alignment remain separate and are not claimed by this milestone.

```lean
import DifferentialGeometry.Geometry.Comparison.LineBusemann
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Tactic

open Set Metric Filter
open scoped Topology
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


private theorem real_segments (x y : ℝ) :
    ∃ f : unitInterval → ℝ, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → ℝ := fun t => (1 - (t : ℝ)) * x + (t : ℝ) * y
  refine ⟨f, by fun_prop, by simp [f], by simp [f], ?_⟩
  intro s t
  change |(1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y)| =
    |x - y| * |(s : ℝ) - t|
  rw [show (1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y) =
    (y - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm y x]


private abbrev C := AddCircle (4 : ℝ)
private instance : Fact (0 < (4 : ℝ)) := ⟨by norm_num⟩
private def x : WithLp 2 (ℝ × C) := WithLp.toLp 2 (3, ((1 : ℝ) : C))
private theorem circle_distance : dist (((1 : ℝ) : C)) (0 : C) = 1 := by
  rw [dist_zero_right]
  have hh : ‖((1 : ℝ) : C)‖ = |(1 : ℝ)| :=
    (AddCircle.norm_coe_eq_abs_iff 4 (by norm_num)).mpr (by norm_num)
  simpa only [abs_one] using hh
private theorem x_radius : dist x (WithLp.toLp 2 ((0 : ℝ), (0 : C))) = Real.sqrt 10 := by
  rw [WithLp.prod_dist_eq_sqrt_sq_add_sq]
  change Real.sqrt (dist (3 : ℝ) 0 ^ 2 + dist (((1 : ℝ) : C)) 0 ^ 2) = _
  rw [circle_distance]
  norm_num [Real.dist_eq]
private theorem x_ball : dist x (WithLp.toLp 2 ((0 : ℝ), (0 : C))) ≤ 4 := by
  rw [x_radius]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10), Real.sqrt_nonneg 10]

example {T : ℝ} (hT : 4 < T) :
    (0 ≤ dist x (WithLp.toLp 2 (T, (0 : C))) - T + 3 ∧
      dist x (WithLp.toLp 2 (T, (0 : C))) - T + 3 ≤ 16 / (2 * (T - 4))) ∧
    (0 ≤ dist x (WithLp.toLp 2 (-T, (0 : C))) - T - 3 ∧
      dist x (WithLp.toLp 2 (-T, (0 : C))) - T - 3 ≤ 16 / (2 * (T - 4))) := by
  have hp := WithLp.dist_real_axis_sub_bounds x 0 x_ball hT
  have hn := WithLp.dist_negative_real_axis_sub_bounds x 0 x_ball hT
  norm_num [x] at hp hn ⊢
  exact ⟨hp, hn⟩

example : Tendsto (fun T : ℝ => dist x (WithLp.toLp 2 (T, (0 : C))) - T)
    atTop (𝓝 (-3 : ℝ)) := WithLp.tendsto_dist_real_axis_sub x 0

example (B : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ z : WithLp 2 (ℝ × C),
      dist z (WithLp.toLp 2 ((0 : ℝ), (0 : C))) ≤ B →
      |dist z (WithLp.toLp 2 (T, (0 : C))) - T + z.fst| < η ∧
      |dist z (WithLp.toLp 2 (-T, (0 : C))) - T - z.fst| < η :=
  (IsometryEquiv.refl (WithLp 2 (ℝ × C))).eventually_abs_dist_aligned_line_sub_lt
    (γ := fun t => WithLp.toLp 2 (t, (0 : C))) (fun _ => rfl) B hη

example (z : ℝ) : Tendsto (fun T : ℝ => dist z T - T) atTop (𝓝 (-z)) := by
  have hh := tendsto_dist_line_sub_lineCoordinate (real_comparison (le_refl 0))
    (γ := id) isometry_id real_segments z
  have hc : lineCoordinate (id : ℝ → ℝ) z = z := by
    simpa only [id_eq] using lineCoordinate_apply_isometry (γ := (id : ℝ → ℝ)) isometry_id z
  simpa only [id_eq, hc] using hh

example (z : ℝ) : Tendsto (fun T : ℝ => dist z (-T) - T) atTop (𝓝 z) := by
  have hh := tendsto_dist_line_sub_lineCoordinate (real_comparison (le_refl 0))
    isometry_neg real_segments z
  have hcoord : lineCoordinate (fun t : ℝ => -t) z = -z := by
    simpa only [neg_neg] using lineCoordinate_apply_isometry (γ := fun t : ℝ => -t) isometry_neg (-z)
  simpa only [hcoord, neg_neg] using hh

#print axioms Real.sqrt_sq_add_sq_sub_bounds
#print axioms WithLp.dist_real_axis_sub_bounds
#print axioms WithLp.dist_negative_real_axis_sub_bounds
#print axioms WithLp.tendsto_dist_real_axis_sub
#print axioms IsometryEquiv.dist_aligned_line_sub_bounds
#print axioms IsometryEquiv.tendsto_dist_aligned_line_sub
#print axioms IsometryEquiv.eventually_abs_dist_aligned_line_sub_lt
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_dist_line_sub_lineCoordinate
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.eventually_abs_dist_line_sub_lineCoordinate_lt
```
