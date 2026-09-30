# Compiled integration: full AC59 and AC60 on the same constructed data

Two public theorems in two leaves add two owned declarations. The 287-module
gate checks 1322 owned declarations (3122 jobs), with transitive axiom closures
limited to propext, Classical.choice and Quot.sound. Source-copy unusedArguments,
simpNF and synTaut linters are silent. Declaration kinds were manually inspected;
defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning is outside these closures. Static audit passes. No full
migrated root, fresh blueprint PDF/Overleaf build, human or delegated review is claimed.

The independent compiled integration reuses the explicit expanding open-ray
sources X_i=(-3(i+1),infinity), basepoint0, two endpoint scales i+1 and2(i+1),
actual short curves, and positive approximation errors. It proves each source
is incomplete and nonproper, and the farther positive endpoint lies outside
the original approximation domain. It then PROVES PointedGHConverges to the
specified real line by actual restriction with slack and error enlargement.
The new original-input theorem selects its OWN actual maps/radii/errors, signed
prefixes and lines on one common strict source subsequence, retaining convergence
to this SAME real target.

The integration does not assume coordinate convergence or an abstract splitting.
It proves the real target's actual global nonnegative comparison and explicit
minimizing segments, applies the established geometric lineSplitting to EACH
returned line, and verifies exact positive-axis alignment. It then passes the
very same returned maps, prefixes, calibration inequalities and uniform prefix
convergence into the new AC60 theorem. The final compiled conclusion retains
one source subsequence and the actual maps, with uniform signed distance-coordinate
convergence on every fixed source ball for both individual splittings. Thus
replacing the maps, changing target, losing the subsequence or reversing the
Busemann orientation would not satisfy this integration. The two pairs live on
a real line; no distinctness or multi-axis orthogonality is silently assumed.
Both theorem axiom reports are standard, and the driver has no diagnostics.

Statement audit checks the original short-curve and absolute-excess hypotheses,
pair-dependent radii, arbitrary finite families, both subsequence compositions,
actual pointed maps with limits of radius/error, explicit source-domain witnesses,
all-point fixed-ball coordinate uniformity and the supplied aligned splitting
required by AC60. The coordinate proof builds calibration witnesses at fixed
positive and negative T, then uses the accepted quantitative squeeze. The existing
product Busemann theorem supplies the negative-positive-ray sign. AC53 simultaneous
alignment, AC57 angle-to-excess production, long-strainer production and source
compatibility remain separate. Chapters3-4 are not claimed complete.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.PointedEndpointLines
import DifferentialGeometry.Geometry.Metric.Approximation.PrefixCoordinateConvergence
import DifferentialGeometry.Geometry.Comparison.LineBusemann
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Tactic

open Set Metric Filter GC.MetricGeometry
open scoped Topology

private def radius (i : ℕ) : ℝ := (i : ℝ) + 1
private theorem radius_one (i : ℕ) : 1 ≤ radius i := by dsimp [radius]; linarith [Nat.cast_nonneg (α := ℝ) i]
private theorem radius_pos (i : ℕ) : 0 < radius i := lt_of_lt_of_le (by norm_num) (radius_one i)
private theorem radius_top : Tendsto radius atTop atTop :=
  tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
private def lengths (i : ℕ) (j : Fin 2) : ℝ := ((j.val : ℝ) + 1) * radius i
private theorem length_pos (i : ℕ) (j : Fin 2) : 0 < lengths i j := by
  dsimp [lengths]
  exact mul_pos (by positivity) (radius_pos i)
private theorem length_lt (i : ℕ) (j : Fin 2) : lengths i j < 3 * radius i := by
  have hj : (j.val : ℝ) < 2 := by exact_mod_cast j.isLt
  dsimp [lengths]
  nlinarith [radius_pos i]
private theorem lengths_top (j : Fin 2) : Tendsto (fun i => lengths i j) atTop atTop :=
  radius_top.const_mul_atTop (by positivity)
private abbrev Source (i : ℕ) := Ioi (-(3 * radius i))
private def base (i : ℕ) : Source i := ⟨0, by change -(3 * radius i) < 0; linarith [radius_pos i]⟩
private def positiveEnd (i : ℕ) (j : Fin 2) : Source i :=
  ⟨lengths i j, by change -(3 * radius i) < lengths i j; linarith [radius_pos i, length_pos i j]⟩
private def negativeEnd (i : ℕ) (j : Fin 2) : Source i :=
  ⟨-lengths i j, by change -(3 * radius i) < -lengths i j; linarith [length_lt i j]⟩
private noncomputable def errors (i : ℕ) : ℝ := (1 / ((i : ℝ) + 1)) / 100
private theorem errors_pos (i : ℕ) : 0 < errors i := by dsimp [errors]; positivity
private theorem errors_lt (i : ℕ) : errors i < radius i := by
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hh : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  dsimp [errors, radius]
  linarith
private theorem errors_zero : Tendsto errors atTop (𝓝 0) := by
  change Tendsto (fun i : ℕ => (1 / ((i : ℝ) + 1)) / 100) atTop (𝓝 0)
  simpa only [zero_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 100
private def approx (i : ℕ) : PointedBallApprox (base i) (0 : ℝ) (radius i) (errors i) where
  error_pos := errors_pos i
  error_lt_radius := errors_lt i
  toFun x := x.val.val
  basepoint := rfl
  distortion x y := by simpa only [Subtype.dist_eq, sub_self, abs_zero] using errors_pos i
  coverage y hy := by
    have hyabs : |y| ≤ radius i - errors i := by simpa only [Real.dist_eq, sub_zero] using hy
    have hsrc : -(3 * radius i) < y := by linarith [(abs_le.mp hyabs).1, radius_pos i, errors_pos i]
    refine ⟨⟨⟨y, hsrc⟩, ?_⟩, ?_⟩
    · change |y - 0| ≤ radius i
      rw [sub_zero]
      linarith [errors_pos i]
    · simpa only [dist_self] using errors_pos i

private theorem ray_segments (c : ℝ) (x y : Ioi c) :
    ∃ f : unitInterval → Ioi c, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → Ioi c := fun t =>
    ⟨(1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ), by
      change c < (1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ)
      have hx : c < x.val := x.property
      have hy : c < y.val := y.property
      have ht0 := t.property.1
      have ht1 := t.property.2
      by_cases ht : (t : ℝ) = 0
      · simpa only [ht, sub_zero, one_mul, zero_mul, add_zero] using hx
      · have htp : 0 < (t : ℝ) := lt_of_le_of_ne ht0 (Ne.symm ht)
        have hp := mul_pos htp (sub_pos.mpr hy)
        have hn := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hx.le)
        nlinarith⟩
  have hd (s t : unitInterval) : dist (f s) (f t) = dist x y * dist s t := by
    change |(1 - (s : ℝ)) * (x : ℝ) + (s : ℝ) * (y : ℝ) -
      ((1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ))| =
      |(x : ℝ) - y| * |(s : ℝ) - t|
    rw [show (1 - (s : ℝ)) * (x : ℝ) + (s : ℝ) * (y : ℝ) -
      ((1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (y : ℝ)) =
      ((y : ℝ) - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm (y : ℝ) x]
  have hl : LipschitzWith (nndist x y) f := LipschitzWith.of_dist_le_mul (fun s t => (hd s t).le)
  refine ⟨f, hl.continuous, ?_, ?_, hd⟩
  · apply Subtype.ext; simp [f]
  · apply Subtype.ext; simp [f]
private theorem source_curves (i : ℕ) : ∀ a b : Source i, ∀ η : ℝ, 0 < η →
    ∃ c : unitInterval → Source i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
      eVariationOn c univ < ENNReal.ofReal (dist a b + η) :=
  arbitrarily_short_curves_of_metric_segments (ray_segments _)

private theorem source_not_complete (i : ℕ) : ¬ CompleteSpace (Source i) := by
  intro h
  let := h
  have hi : Isometry (Subtype.val : Source i → ℝ) := isometry_subtype_coe
  have hc : IsClosed (Ioi (-(3 * radius i))) := by
    simpa only [Subtype.range_val] using hi.isUniformInducing.isComplete_range.isClosed
  have hz : -(3 * radius i) ∈ closure (Ioi (-(3 * radius i))) := by
    simpa only [closure_Ioi, mem_Ici] using (le_rfl : -(3 * radius i) ≤ -(3 * radius i))
  rw [hc.closure_eq] at hz
  exact lt_irrefl (-(3 * radius i)) hz

example (i : ℕ) : ¬ ProperSpace (Source i) := by
  intro h
  let := h
  exact source_not_complete i inferInstance

example (i : ℕ) : radius i < dist (base i) (positiveEnd i 1) := by
  have hh := radius_pos i
  change radius i < |0 - lengths i 1|
  rw [zero_sub, abs_neg, abs_of_pos (length_pos i 1)]
  norm_num [lengths]
  linarith


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

private theorem source_convergence : PointedGHConverges base (0 : ℝ) := by
  refine ⟨inferInstance, ?_⟩
  intro R ε hε hεR
  filter_upwards [radius_top.eventually (eventually_ge_atTop R),
    errors_zero.eventually (eventually_lt_nhds (by positivity : 0 < ε / 2))] with i hiR hie
  exact ⟨((approx i).restrict (by linarith) hiR).enlargeError (by linarith) hεR⟩

example : ∃ (ψ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono ψ ∧
    PointedGHConverges (fun i => base (ψ i)) (0 : ℝ) ∧
    Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
    ∃ f : ∀ i, PointedBallApprox (base (ψ i)) (0 : ℝ) (R i) (ε i),
    ∃ γ : Fin 2 → ℝ → ℝ, (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = 0) ∧
      ∀ j, ∃ (Z : Type) (m : MetricSpace Z), letI := m
        ∃ (z : Z) (e : ℝ ≃ᵢ WithLp 2 (ℝ × Z)),
          (∀ t, e (γ j t) = WithLp.toLp 2 (t, z)) ∧
          ∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
            S ≤ R i ∧ ∀ x : BallCarrier (base (ψ i)) (R i), dist x.val (base (ψ i)) ≤ S →
              |dist (base (ψ i)) (positiveEnd (ψ i) j) - dist x.val (positiveEnd (ψ i) j) -
                (e ((f i).toFun x)).fst| < ζ := by
  have hp (i : ℕ) (j : Fin 2) : dist (base i) (positiveEnd i j) = lengths i j := by
    simp only [base, positiveEnd, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_pos (length_pos i j)]
  have hm (i : ℕ) (j : Fin 2) : dist (base i) (negativeEnd i j) = lengths i j := by
    simp only [base, negativeEnd, Subtype.dist_eq, Real.dist_eq, zero_sub, neg_neg,
      abs_of_pos (length_pos i j)]
  have hexcess (i : ℕ) (j : Fin 2) : 2 * lengths i j - dist (positiveEnd i j) (negativeEnd i j) = 0 := by
    change 2 * lengths i j - |lengths i j - (-lengths i j)| = 0
    rw [abs_of_nonneg (by linarith [length_pos i j])]
    ring
  have hE (j : Fin 2) : Tendsto
      (fun i => 2 * lengths i j - dist (positiveEnd i j) (negativeEnd i j)) atTop (𝓝 0) := by
    simpa only [hexcess] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  obtain ⟨ψ, R, ε, hψ, hconv, hR, hε, f, σ, hσLip, hσbase, hσcal, γ, hγ, hγ0, hcontrol⟩ :=
    source_convergence.exists_calibrated_lines_of_opposite_endpoints source_curves
      positiveEnd negativeEnd length_pos lengths_top hp hm hE errors_pos errors_zero
  refine ⟨ψ, R, ε, hψ, hconv, hR, hε, f, γ, hγ, hγ0, ?_⟩
  intro j
  let Z := {x : ℝ // lineCoordinate (γ j) x = 0}
  let z : Z := ⟨γ j 0, by rw [lineCoordinate_apply_isometry (hγ j)]⟩
  let e : ℝ ≃ᵢ WithLp 2 (ℝ × Z) := lineSplitting (real_comparison (by norm_num)) (hγ j) real_segments
  have halign (t : ℝ) : e (γ j t) = WithLp.toLp 2 (t, z) :=
    lineSplitting_apply_line (real_comparison (by norm_num)) (hγ j) real_segments t
  refine ⟨Z, inferInstance, z, e, halign, ?_⟩
  apply eventually_distance_coordinate_error_lt_of_converging_prefixes e halign (hγ0 j) f hR hε
    (fun i => positiveEnd (ψ i) j) (fun i => hp (ψ i) j) (fun i => (length_pos (ψ i) j).le)
    (E := fun i => 2 * lengths (ψ i) j - dist (positiveEnd (ψ i) j) (negativeEnd (ψ i) j))
    (fun i => by rw [hexcess]) ((hE j).comp hψ.tendsto_atTop) (errors_zero.comp hψ.tendsto_atTop)
    (fun i => σ i j) (fun i => hσLip i j) (fun i => hσbase i j)
    (fun i t => ⟨(hσcal i j t).1, (hσcal i j t).2.2.2⟩)
  intro S ζ hζ
  filter_upwards [hcontrol S ζ hζ] with i hi
  exact ⟨hi.1, (hi.2 j).1, (hi.2 j).2⟩

#print axioms GC.MetricGeometry.PointedGHConverges.exists_calibrated_lines_of_opposite_endpoints
#print axioms GC.MetricGeometry.eventually_distance_coordinate_error_lt_of_converging_prefixes
```
