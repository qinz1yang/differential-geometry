# Compiled self-review: actual finite-length curve prefixes and calibration

Five public theorems in three leaves add seven owned declarations, including
compiler-generated choice auxiliaries. The 280-module gate checks 1314 owned
declarations (3115 jobs), with transitive axiom closures limited to propext,
Classical.choice and Quot.sound. Source-copy unusedArguments, simpNF and synTaut
linters are silent. Declaration kinds were manually inspected; defLemma is
unavailable. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning is outside these closures. Static audit passes. No full
migrated root, fresh blueprint PDF/Overleaf build, human or delegated review is claimed.

The independent compiled driver uses the genuine curve c(t)=max(2t-1,0), which
pauses on its first half. It proves continuity, monotonicity and actual metric
variation equal to one, verifies the pause at t=0 and1/4, and then consumes the
constructed parametrization with actual endpoints and EXACT variation on every
subinterval. It also applies the single-curve prefix theorem to this supplied
paused curve and verifies its actual tail bound. Thus the construction does not
assume an injective or strictly increasing original parameter.

The original-input opposite-prefix producer is tested on the open positive real
ray. The driver constructs actual linear segments and short curves in that
subspace and separately PROVES it is not complete (its image is not closed in R).
For basepoint2 and endpoints3 and1 at distance1, it consumes both actual prefixes,
the zero-excess cross-branch estimate, all four signed calibration inequalities,
and containment in every closed initial-radius ball. All five theorem axiom
reports are standard and the review compiles without diagnostics.

Statement audit checks actual finite metric variation, continuity and monotone
surjectivity of the length parameter, choice within the original curve image,
exact subpath variation and absence of a strict-monotonicity assumption. The
prefix proof uses only 1-Lipschitz parametrization and remaining-length bounds;
it never imports a minimizing source segment or completes the source. Exact
AC58 constants E and2eta, both orientation signs and closed-ball containment are
retained. The consumer assumes the original arbitrarily-short-curves condition.
AC59 whole-line extraction and finite-family subsequence synchronization remain
separate, as do multi-axis geometry and strainer-to-splitting production.

```lean
import DifferentialGeometry.Topology.MetricSpace.OppositePrefixes
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Tactic

open Set Metric Filter
open scoped Topology

private def paused (t : unitInterval) : ℝ := max (2 * (t : ℝ) - 1) 0
private theorem paused_cont : Continuous paused := by
  change Continuous (fun t : unitInterval => max (2 * t.val - 1) 0)
  fun_prop
private theorem paused_mono : Monotone paused := by
  intro s t hst
  exact max_le_max (by linarith [show (s : ℝ) ≤ t from hst]) le_rfl
private theorem paused_length : eVariationOn paused univ = 1 := by
  have hall : Icc (0 : unitInterval) 1 = univ := by
    ext t
    simp only [mem_Icc, mem_univ, iff_true]
    exact ⟨unitInterval.nonneg', unitInterval.le_one'⟩
  have hh := (paused_mono.monotoneOn univ).eVariationOn_eq
    (mem_univ (0 : unitInterval)) (mem_univ 1)
  norm_num [hall, paused] at hh
  exact hh

example : paused 0 = paused ⟨1 / 4, by norm_num⟩ ∧ paused 1 = 1 := by
  norm_num [paused]

example : ∃ q : Icc (0 : ℝ) 1 → ℝ, LipschitzWith 1 q ∧
    q ⟨0, by norm_num⟩ = 0 ∧ q ⟨1, by norm_num⟩ = 1 ∧
    ∀ s t, s ≤ t → eVariationOn q (Icc s t) = ENNReal.ofReal (t.val - s.val) := by
  have hv : BoundedVariationOn paused univ := by rw [BoundedVariationOn, paused_length]; norm_num
  obtain ⟨φ, hφc, hφm, hφ0, hφ1, q, hq, hq0, hq1, hfactor, hlen⟩ :=
    exists_lipschitz_parametrization_of_finite_variation paused paused_cont hv
  have he : (eVariationOn paused univ).toReal = 1 := by rw [paused_length]; norm_num
  let incl : Icc (0 : ℝ) 1 → Icc (0 : ℝ) (eVariationOn paused univ).toReal :=
    fun t => ⟨t.val, by simpa only [he] using t.property⟩
  have hi : Isometry incl := Isometry.of_dist_eq (fun _ _ => rfl)
  have hz : incl ⟨0, by norm_num⟩ = ⟨0, ⟨le_rfl, ENNReal.toReal_nonneg⟩⟩ := rfl
  have hone : incl ⟨1, by norm_num⟩ =
      ⟨(eVariationOn paused univ).toReal, ⟨ENNReal.toReal_nonneg, le_rfl⟩⟩ := Subtype.ext he.symm
  refine ⟨q ∘ incl, by simpa using hq.comp hi.lipschitzWith, ?_, ?_, ?_⟩
  · change q (incl ⟨0, by norm_num⟩) = 0
    rw [hz]
    norm_num [paused] at hq0
    exact hq0
  · change q (incl ⟨1, by norm_num⟩) = 1
    rw [hone]
    norm_num [paused] at hq1
    exact hq1
  · intro s t hst
    have hrange : incl '' univ = univ := by
      apply Set.eq_univ_of_forall
      intro t
      exact ⟨⟨t.val, by simpa only [he] using t.property⟩, mem_univ _, rfl⟩
    rw [← univ_inter (Icc s t), eVariationOn.comp_inter_Icc_eq_of_monotoneOn q incl
      (fun _ _ _ _ h => h) (mem_univ s) (mem_univ t), hrange, univ_inter]
    exact hlen (incl s) (incl t) hst

example : ∃ q : Icc (0 : ℝ) (dist (0 : ℝ) 1) → ℝ,
    LipschitzWith 1 q ∧ q ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = 0 ∧
    ∀ t, dist (q t) 1 < 1 + 1 / 100 - t.val := by
  obtain ⟨q, hq, hq0, htail, _, _, _⟩ := exists_short_curve_prefix (p := (0 : ℝ)) (a := 1) (η := 1 / 100)
    (by norm_num) paused paused_cont (by norm_num [paused]) (by norm_num [paused])
    (by rw [paused_length]; norm_num [Real.dist_eq])
  exact ⟨q, hq, hq0, by simpa only [Real.dist_eq, zero_sub, abs_neg, abs_one] using htail⟩

private theorem ray_segments (x y : Ioi (0 : ℝ)) :
    ∃ f : unitInterval → Ioi (0 : ℝ), Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → Ioi (0 : ℝ) := fun t =>
    ⟨(1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ), by
      have hx := x.property
      have hy := y.property
      have ht0 := t.property.1
      have ht1 := t.property.2
      by_cases ht : (t : ℝ) = 0
      · simp [ht]
      · have htp : 0 < (t : ℝ) := lt_of_le_of_ne ht0 (Ne.symm ht)
        exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1) hx.le)
          (mul_pos htp hy)⟩
  have hd (s t : unitInterval) : dist (f s) (f t) = dist x y * dist s t := by
    change |(1 - (s : ℝ)) * (x : ℝ) + (s : ℝ) * (y : ℝ) -
      ((1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ))| =
      |(x : ℝ) - y| * |(s : ℝ) - t|
    rw [show (1 - (s : ℝ)) * (x : ℝ) + (s : ℝ) * (y : ℝ) -
      ((1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ)) =
      ((y : ℝ) - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm (y : ℝ) x]
  have hLip : LipschitzWith (nndist x y) f :=
    LipschitzWith.of_dist_le_mul (fun s t => (hd s t).le)
  refine ⟨f, hLip.continuous, ?_, ?_, hd⟩
  · apply Subtype.ext
    simp [f]
  · apply Subtype.ext
    simp [f]

private theorem ray_curves : ∀ a b : Ioi (0 : ℝ), ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → Ioi (0 : ℝ), Continuous c ∧ c 0 = a ∧ c 1 = b ∧
      eVariationOn c univ < ENNReal.ofReal (dist a b + ε) :=
  arbitrarily_short_curves_of_metric_segments ray_segments


example : ¬ CompleteSpace (Ioi (0 : ℝ)) := by
  intro h
  let := h
  have hi : Isometry (Subtype.val : Ioi (0 : ℝ) → ℝ) := isometry_subtype_coe
  have hc := hi.isUniformInducing.isComplete_range.isClosed
  have hclosed : IsClosed (Ioi (0 : ℝ)) := by simpa only [Subtype.range_val] using hc
  have hz : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by simpa only [closure_Ioi, mem_Ici] using (le_rfl : (0 : ℝ) ≤ 0)
  rw [hclosed.closure_eq] at hz
  exact lt_irrefl (0 : ℝ) hz

private def point (t : ℝ) (ht : 0 < t) : Ioi (0 : ℝ) := ⟨t, ht⟩

example (η : ℝ) (hη : 0 < η) :
    ∃ qPlus qMinus : Icc (0 : ℝ) 1 → Ioi (0 : ℝ),
      LipschitzWith 1 qPlus ∧ LipschitzWith 1 qMinus ∧
      qPlus ⟨0, by norm_num⟩ = point 2 (by norm_num) ∧
      qMinus ⟨0, by norm_num⟩ = point 2 (by norm_num) ∧
      (∀ t u, t.val + u.val - 2 * η ≤ dist (qPlus t) (qMinus u) ∧
        dist (qPlus t) (qMinus u) ≤ t.val + u.val) ∧
      (∀ t, t.val - η ≤ 1 - dist (qPlus t) (point 3 (by norm_num)) ∧
        1 - dist (qPlus t) (point 3 (by norm_num)) ≤ t.val ∧
        -t.val ≤ 1 - dist (qMinus t) (point 3 (by norm_num)) ∧
        1 - dist (qMinus t) (point 3 (by norm_num)) ≤ -t.val + η) ∧
      ∀ T : ℝ, ∀ t, t.val ≤ T →
        qPlus t ∈ closedBall (point 2 (by norm_num)) T ∧
        qMinus t ∈ closedBall (point 2 (by norm_num)) T := by
  obtain ⟨qPlus, qMinus, hp, hm, hp0, hm0, _, _, hcross, hcal, hball⟩ :=
    exists_opposite_calibrated_prefixes ray_curves (point 2 (by norm_num))
      (point 3 (by norm_num)) (point 1 (by norm_num)) (L := 1) (by norm_num) hη
      (by norm_num [point, Subtype.dist_eq, Real.dist_eq])
      (by norm_num [point, Subtype.dist_eq, Real.dist_eq])
  refine ⟨qPlus, qMinus, hp, hm, hp0, hm0, ?_, ?_, hball⟩
  · simpa only [point, Subtype.dist_eq, Real.dist_eq, show |(3 : ℝ) - 1| = 2 by norm_num,
      mul_one, sub_self, sub_zero] using hcross
  · simpa only [point, Subtype.dist_eq, Real.dist_eq, show |(3 : ℝ) - 1| = 2 by norm_num,
      mul_one, sub_self, add_zero] using hcal

#print axioms Metric.dist_le_abs_variationOnFromTo_sub
#print axioms Metric.exists_lipschitz_parametrization_of_finite_variation
#print axioms Metric.exists_short_curve_prefix
#print axioms Metric.opposite_prefix_distance_calibration
#print axioms Metric.exists_opposite_calibrated_prefixes
```
