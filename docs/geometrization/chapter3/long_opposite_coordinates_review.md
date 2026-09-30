# AC61 independent statement review and compiled integration

Three public theorems in two leaves add three owned declarations. The combined
294-module gate checks 1349 owned declarations in3129 jobs. Every new transitive
axiom closure uses only propext, Classical.choice and Quot.sound. Source-copy
unusedArguments/simpNF/synTaut lint and the compiled integration are silent
apart from the requested three axiom reports. Declaration kinds were checked;
defLemma is unavailable. The inherited AreaUpperBarrier warning remains outside
these closures. No full migrated root, fresh PDF/Overleaf build or human approval
is claimed. Blueprint static audit passes; earlier accepted math is unchanged.

An independent reviewer read the actual theorem and proof bodies, checked the
finite-family/empty-family quantifiers, common target/maps, orientation, original
index sequence, and reciprocal local geometry. It identified that an early draft
omitted the constructed prefixes from its conclusion. The accepted statements
return the prefixes, all calibrations, and simultaneous signed-parameter map
convergence, as well as the coordinate/Busemann conclusions on the same objects.
The reviewer then rechecked the strengthened statements and found no further
contract issue. One agent implemented the generic assembly; root strengthened
its output and implemented/compiled both original-input consumers.

The driver first uses actual varying open half-lines Ioi(-3(i+1)), proves they
are incomplete and nonproper, supplies explicit short curves and inclusion
approximations, and derives the specified pointed convergence to the real line.
The generic endpoint theorem is applied to two pair-dependent endpoint lengths.
The long-angle theorem is then applied to two REPEATED endpoint pairs at the
same exact reciprocal scale; their model comparison angle is pi, and all the
coordinate/Busemann outputs are obtained from the theorem's own selected maps.
The equality of the two positive endpoints is explicitly checked. This is a
non-vacuity and scope check: distinctness is not an assumed or inferred property.

The original-geometric-input theorem is separately instantiated with complete
real-line sources, actual affine segments/short curves, proved global comparison
at each sigma_i, a proved local Hausdorff bound, actual endpoints, and constant
pointed convergence. Thus target geometry and the excess hypothesis are produced,
not postulated. The same complete-source test is run with Fin0, retaining growing
radii and approximation maps despite the empty family. The driver also obtains
fixed-interval radius control from each returned prefix convergence package.
The actual prefix calibration and limit construction are already covered by
AC58/59's retained integration checks; this milestone checks their same-object
assembly with AC57/60 and the geometric producers.

The result is full AC61 in its written scope. Cross-pair orthogonality, simultaneous
higher-rank splitting, and compatibility remain separate unfinished conclusions.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.LongOppositeCoordinates
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

example :
    ∃ (ψ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono ψ ∧
      PointedGHConverges (fun i => base (ψ i)) (0 : ℝ) ∧ Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ f : ∀ i, PointedBallApprox (base (ψ i)) (0 : ℝ) (R i) (ε i),
      ∃ γ : Fin 2 → ℝ → ℝ,
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = (0 : ℝ)) ∧
        (∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, ∀ x : BallCarrier (base (ψ i)) (R i), dist x.val (base (ψ i)) ≤ S →
            |dist (base (ψ i)) (positiveEnd (ψ i) j) - dist x.val (positiveEnd (ψ i) j) -
              lineCoordinate (γ j) ((f i).toFun x)| < ζ) ∧
        ∀ j x, Tendsto (fun T : ℝ => dist x (γ j T) - T) atTop (𝓝 (-lineCoordinate (γ j) x)) := by
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
  obtain ⟨ψ, R, ε, hψ, hconv, hR, hε, f, q, hqLip, hqbase, hqcal, γ, hγ, hγ0, hprefix, hcoord, hbus⟩ :=
    source_convergence.exists_line_coordinates_of_opposite_endpoints
    (real_comparison (by norm_num)) real_segments source_curves
    positiveEnd negativeEnd length_pos lengths_top hp hm hE errors_pos errors_zero
  have hsign (ζ : ℝ) (hζ : 0 < ζ) : ∀ᶠ i in atTop,
      1 ≤ R i := by
    filter_upwards [hprefix 1 ζ hζ] with i hi using hi.1
  have _ := hsign
  exact ⟨ψ, R, ε, hψ, hconv, hR, hε, f, γ, hγ, hγ0, hcoord, hbus⟩

private noncomputable def sig (i : ℕ) : ℝ := 1 / radius i
private theorem sig_pos (i : ℕ) : 0 < sig i := div_pos (by norm_num) (radius_pos i)
private theorem sig_zero : Tendsto sig atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
private theorem sig_inv (i : ℕ) : (sig i)⁻¹ = radius i := by simp [sig]
private def samePositive (i : ℕ) (_ : Fin 2) : Source i := positiveEnd i 0
private def sameNegative (i : ℕ) (_ : Fin 2) : Source i := negativeEnd i 0
private theorem samehp (i : ℕ) (j : Fin 2) : dist (base i) (samePositive i j) = (sig i)⁻¹ := by
  rw [sig_inv]
  change |0 - lengths i 0| = radius i
  simp [lengths, abs_of_pos (radius_pos i)]
private theorem samehm (i : ℕ) (j : Fin 2) : dist (base i) (sameNegative i j) = (sig i)⁻¹ := by
  rw [sig_inv]
  change |0 - (-lengths i 0)| = radius i
  simp [lengths, abs_of_pos (radius_pos i)]
private theorem sameangle (j : Fin 2) : ∀ᶠ i in atTop,
    Real.pi - sig i ≤ comparisonAngleNegCurvature (sig i)
      (dist (base i) (samePositive i j)) (dist (base i) (sameNegative i j))
      (dist (samePositive i j) (sameNegative i j)) := by
  exact Eventually.of_forall fun i => by
    rw [samehp, samehm, sig_inv]
    have hd : dist (samePositive i j) (sameNegative i j) = radius i + radius i := by
      change |lengths i 0 - (-lengths i 0)| = radius i + radius i
      simp only [lengths, Fin.val_zero, Nat.cast_zero, zero_add, one_mul, sub_neg_eq_add]
      exact abs_of_pos (by linarith [radius_pos i])
    rw [hd, comparisonAngleNegCurvature_add (sig_pos i).le (radius_pos i) (radius_pos i)]
    linarith [sig_pos i]

example :
    ∃ (ψ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono ψ ∧
      PointedGHConverges (fun i => base (ψ i)) (0 : ℝ) ∧ Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ f : ∀ i, PointedBallApprox (base (ψ i)) (0 : ℝ) (R i) (ε i),
      ∃ γ : Fin 2 → ℝ → ℝ,
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = (0 : ℝ)) ∧
        (∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, ∀ x : BallCarrier (base (ψ i)) (R i), dist x.val (base (ψ i)) ≤ S →
            |dist (base (ψ i)) (samePositive (ψ i) j) - dist x.val (samePositive (ψ i) j) -
              lineCoordinate (γ j) ((f i).toFun x)| < ζ) ∧
        ∀ j x, Tendsto (fun T : ℝ => dist x (γ j T) - T) atTop (𝓝 (-lineCoordinate (γ j) x)) := by
  obtain ⟨ψ, R, ε, hψ, hconv, hR, hε, f, q, hqLip, hqbase, hqcal, γ, hγ, hγ0, hprefix, hcoord, hbus⟩ :=
    source_convergence.exists_line_coordinates_of_long_opposite_angles
    (real_comparison (by norm_num)) real_segments source_curves
    samePositive sameNegative sig_pos sig_zero samehp samehm sameangle
  have hsign (ζ : ℝ) (hζ : 0 < ζ) : ∀ᶠ i in atTop,
      1 ≤ R i := by
    filter_upwards [hprefix 1 ζ hζ] with i hi using hi.1
  have _ := hsign
  exact ⟨ψ, R, ε, hψ, hconv, hR, hε, f, γ, hγ, hγ0, hcoord, hbus⟩

example :
    ∃ (ψ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono ψ ∧
      PointedGHConverges (fun _ : ℕ => (0 : ℝ)) (0 : ℝ) ∧ Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ f : ∀ i, PointedBallApprox ((0 : ℝ)) (0 : ℝ) (R i) (ε i),
      ∃ γ : Fin 2 → ℝ → ℝ,
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = (0 : ℝ)) ∧
        (∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, ∀ x : BallCarrier ((0 : ℝ)) (R i), dist x.val ((0 : ℝ)) ≤ S →
            |dist ((0 : ℝ)) (radius (ψ i)) - dist x.val (radius (ψ i)) -
              lineCoordinate (γ j) ((f i).toFun x)| < ζ) ∧
        ∀ j x, Tendsto (fun T : ℝ => dist x (γ j T) - T) atTop (𝓝 (-lineCoordinate (γ j) x)) := by
  obtain ⟨ψ, R, ε, hψ, hconv, hR, hε, f, q, hqLip, hqbase, hqcal, γ, hγ, hγ0, hprefix, hcoord, hbus⟩ :=
    (PointedGHConverges.const (0 : ℝ)).exists_line_coordinates_of_reciprocal_local_geometry
    (n := 1) (fun _ => arbitrarily_short_curves_of_metric_segments real_segments)
    (fun i => by simpa only [Nat.cast_one] using (dimH_mono (subset_univ (ball (0 : ℝ) ((sig i)⁻¹)))).trans_eq Real.dimH_univ)
    (fun i z _ => ⟨univ, isOpen_univ, real_comparison (sig_pos i).le, mem_univ z⟩)
    (fun i (_ : Fin 2) => radius i) (fun i _ => -radius i) sig_pos sig_zero
    (fun i _ => by rw [sig_inv, Real.dist_eq, zero_sub, abs_neg, abs_of_pos (radius_pos i)])
    (fun i _ => by rw [sig_inv, Real.dist_eq, zero_sub, neg_neg, abs_of_pos (radius_pos i)]) (by
   intro j
   exact Eventually.of_forall fun i => by
    have hh := comparisonAngleNegCurvature_add (sig_pos i).le (radius_pos i) (radius_pos i)
    rw [Real.dist_eq (0 : ℝ) (radius i), Real.dist_eq (0 : ℝ) (-radius i),
      Real.dist_eq (radius i) (-radius i), zero_sub, abs_neg, abs_of_pos (radius_pos i),
      zero_sub, neg_neg, abs_of_pos (radius_pos i), sub_neg_eq_add,
      abs_of_pos (show 0 < radius i + radius i by linarith [radius_pos i]), hh]
    linarith [sig_pos i])
  have hsign (ζ : ℝ) (hζ : 0 < ζ) : ∀ᶠ i in atTop,
      1 ≤ R i := by
    filter_upwards [hprefix 1 ζ hζ] with i hi using hi.1
  have _ := hsign
  exact ⟨ψ, R, ε, hψ, hconv, hR, hε, f, γ, hγ, hγ0, hcoord, hbus⟩

example :
    ∃ (ψ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono ψ ∧
      PointedGHConverges (fun _ : ℕ => (0 : ℝ)) (0 : ℝ) ∧ Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ f : ∀ i, PointedBallApprox ((0 : ℝ)) (0 : ℝ) (R i) (ε i),
      ∃ γ : Fin 0 → ℝ → ℝ,
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = (0 : ℝ)) ∧
        (∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, ∀ x : BallCarrier ((0 : ℝ)) (R i), dist x.val ((0 : ℝ)) ≤ S →
            |dist ((0 : ℝ)) (radius (ψ i)) - dist x.val (radius (ψ i)) -
              lineCoordinate (γ j) ((f i).toFun x)| < ζ) ∧
        ∀ j x, Tendsto (fun T : ℝ => dist x (γ j T) - T) atTop (𝓝 (-lineCoordinate (γ j) x)) := by
  obtain ⟨ψ, R, ε, hψ, hconv, hR, hε, f, q, hqLip, hqbase, hqcal, γ, hγ, hγ0, hprefix, hcoord, hbus⟩ :=
    (PointedGHConverges.const (0 : ℝ)).exists_line_coordinates_of_reciprocal_local_geometry
    (n := 1) (fun _ => arbitrarily_short_curves_of_metric_segments real_segments)
    (fun i => by simpa only [Nat.cast_one] using (dimH_mono (subset_univ (ball (0 : ℝ) ((sig i)⁻¹)))).trans_eq Real.dimH_univ)
    (fun i z _ => ⟨univ, isOpen_univ, real_comparison (sig_pos i).le, mem_univ z⟩)
    (fun i (_ : Fin 0) => radius i) (fun i _ => -radius i) sig_pos sig_zero
    (fun i _ => by rw [sig_inv, Real.dist_eq, zero_sub, abs_neg, abs_of_pos (radius_pos i)])
    (fun i _ => by rw [sig_inv, Real.dist_eq, zero_sub, neg_neg, abs_of_pos (radius_pos i)]) (by
   intro j
   exact Eventually.of_forall fun i => by
    have hh := comparisonAngleNegCurvature_add (sig_pos i).le (radius_pos i) (radius_pos i)
    rw [Real.dist_eq (0 : ℝ) (radius i), Real.dist_eq (0 : ℝ) (-radius i),
      Real.dist_eq (radius i) (-radius i), zero_sub, abs_neg, abs_of_pos (radius_pos i),
      zero_sub, neg_neg, abs_of_pos (radius_pos i), sub_neg_eq_add,
      abs_of_pos (show 0 < radius i + radius i by linarith [radius_pos i]), hh]
    linarith [sig_pos i])
  have hsign (ζ : ℝ) (hζ : 0 < ζ) : ∀ᶠ i in atTop,
      1 ≤ R i := by
    filter_upwards [hprefix 1 ζ hζ] with i hi using hi.1
  have _ := hsign
  exact ⟨ψ, R, ε, hψ, hconv, hR, hε, f, γ, hγ, hγ0, hcoord, hbus⟩

example (i : ℕ) : samePositive i 0 = samePositive i 1 := rfl

#print axioms GC.MetricGeometry.PointedGHConverges.exists_line_coordinates_of_opposite_endpoints
#print axioms GC.MetricGeometry.PointedGHConverges.exists_line_coordinates_of_long_opposite_angles
#print axioms GC.MetricGeometry.PointedGHConverges.exists_line_coordinates_of_reciprocal_local_geometry
```
