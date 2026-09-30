# Compiled self-review: calibrated original-endpoint lines in the same target

Four public theorems in four leaves add five owned declarations. The 285-module
gate checks 1320 owned declarations (3120 jobs), with transitive axiom closures
limited to propext, Classical.choice and Quot.sound. Source-copy unusedArguments,
simpNF and synTaut linters are silent. Declaration kinds were manually inspected;
defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning is outside these closures. Static audit passes. No full
migrated root, fresh blueprint PDF/Overleaf build, human or delegated review is claimed.

The compiled driver uses genuinely varying sources X_i=(-3(i+1),infinity), with
the inherited real metric and basepoint zero. It separately PROVES each source
is neither complete nor proper, using its nonclosed image in R. It constructs
actual short curves by convex linear interpolation. The actual inclusion maps
on source balls of radius i+1 satisfy PointedBallApprox to the specified real
line with positive errors 1/(100(i+1)) tending to zero; coverage witnesses and
distortion are proved directly. The two endpoint pairs have distinct scales
L(i,0)=i+1 and L(i,1)=2(i+1), and zero absolute excess. The second positive endpoint
is independently proved OUTSIDE the approximation domain for every i.

The driver then invokes the original-endpoint producer, retaining actual signed
prefixes, both isometric lines in this SAME real target, one strictly increasing
subsequence, and simultaneous uniform approximation control over every fixed
signed parameter interval. Thus varying-source completeness/properness, common
endpoint radii, or containment of the remote endpoints in approximation domains
cannot have been silently added. All four theorem axiom reports are standard;
the driver compiles without diagnostics. Exact signed calibration and natural
prefix production also have the preceding AC58 independent tests.

Statement audit checks exact positive/negative gluing at zero, 1-Lipschitz
continuity of the joined prefix, the exact E+2eta loss and radial domain control,
absolute excess for each finite family member, and the finite norm bound tending
to zero. The isometric lines and ordinary subsequence control the supplied maps
in the supplied target; no alternate target, completion of sources or per-family
subsequence is substituted. Pair-dependent radii and deficits are supported.
The original PointedGHConverges-only map-selection adapter and the joined AC60
coordinate consumer remain separate obligations.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.OppositeEndpointLines
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

example : ∃ (σ : ∀ i j, Icc (-(lengths i j)) (lengths i j) → Source i)
    (γ : Fin 2 → ℝ → ℝ) (φ : ℕ → ℕ),
    (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = 0) ∧ StrictMono φ ∧
    ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
      S ≤ radius (φ i) ∧ ∀ j, S ≤ lengths (φ i) j ∧
      ∀ t : Icc (-(lengths (φ i) j)) (lengths (φ i) j), |t.val| ≤ S →
        ∀ ht : dist (σ (φ i) j t) (base (φ i)) ≤ radius (φ i),
          dist ((approx (φ i)).toFun ⟨σ (φ i) j t, ht⟩) (γ j t.val) < ζ := by
  have hp (i : ℕ) (j : Fin 2) : dist (base i) (positiveEnd i j) = lengths i j := by
    simp only [base, positiveEnd, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_pos (length_pos i j)]
  have hm (i : ℕ) (j : Fin 2) : dist (base i) (negativeEnd i j) = lengths i j := by
    simp only [base, negativeEnd, Subtype.dist_eq, Real.dist_eq, zero_sub, neg_neg,
      abs_of_pos (length_pos i j)]
  have hE (j : Fin 2) : Tendsto
      (fun i => 2 * lengths i j - dist (positiveEnd i j) (negativeEnd i j)) atTop (𝓝 0) := by
    have hh (i : ℕ) : 2 * lengths i j - dist (positiveEnd i j) (negativeEnd i j) = 0 := by
      change 2 * lengths i j - |lengths i j - (-lengths i j)| = 0
      rw [abs_of_nonneg (by linarith [length_pos i j])]
      ring
    simpa only [hh] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  obtain ⟨σ, _, _, _, γ, φ, hγ, hγ0, hφ, hconv⟩ :=
    exists_calibrated_lines_of_opposite_endpoints approx radius_top errors_zero source_curves
      positiveEnd negativeEnd length_pos lengths_top hp hm hE errors_pos errors_zero
  exact ⟨σ, γ, φ, hγ, hγ0, hφ, hconv⟩

#print axioms Metric.exists_signed_prefix_of_opposite_prefixes
#print axioms Metric.exists_calibrated_signed_prefix
#print axioms GC.MetricGeometry.exists_isometric_lines_of_signed_prefixes
#print axioms GC.MetricGeometry.exists_calibrated_lines_of_opposite_endpoints
```
