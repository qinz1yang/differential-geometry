# Compiled self-review: coordinate squeeze from actual opposite calibration

Three public theorems in one leaf add three owned declarations. The 277-module
gate checks 1307 owned declarations (3111 jobs), with transitive axiom closures
limited to propext, Classical.choice and Quot.sound. Source-copy unusedArguments,
simpNF and synTaut linters are silent. Declaration kinds were manually inspected;
defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning is outside these closures. Static audit passes. No full
migrated root, fresh blueprint PDF/Overleaf build, human or delegated review is claimed.

The compiled driver uses the actual real line and its onto product isometry with
the zero-dimensional Euclidean factor. The finite estimate is tested on the
coordinate h(x)=x+1/10, giving actual nonzero coordinate error. The sequential
consumer uses actual remote endpoints L_i=i+1, actual identity approximation
maps, radii 10L_i and errors tending to zero. Calibration is proved with the
actual points plus/minus T on a sufficiently late tail. It verifies the full
uniform conclusion for every fixed radius and accuracy. As a negative control,
at the actual points x_i=2L_i inside the growing approximation domains, the
coordinate error equals 2L_i. Thus extending the conclusion to the growing
whole domains would be false. All three theorem axiom reports are standard.

The statement audit checks both signed calibrations, actual map distortion,
fixed positive T chosen before the source-index limit, the exact rationalized
product error, universal control over every point of each fixed source ball,
and the actual signed distance coordinate. The endpoint may be outside the
approximation domain. No geometry of the source or right-hand factor is assumed.
Calibration points and the aligned line remain supplied inputs, not claimed
products of these theorems. Their production remains the next dependency.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.CalibratedCoordinates
import DifferentialGeometry.Geometry.Metric.Approximation.RealBallExamples
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open Set Metric Filter GC.MetricGeometry
open scoped Topology

private abbrev Z0 := EuclideanSpace ℝ (Fin 0)
private noncomputable def split : ℝ ≃ᵢ WithLp 2 (ℝ × Z0) :=
  (IsometryEquiv.withLpProdUnique 2 ℝ Z0).symm
private theorem align (t : ℝ) : split t = WithLp.toLp 2 (t, (0 : Z0)) := by
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext rfl (Subsingleton.elim _ _)

example : |(1 / 10 : ℝ)| ≤ 1 / 10 + 1 / 100 := by
  let f : PointedBallApprox (0 : ℝ) (0 : ℝ) 2 (1 / 100) :=
    identityApprox 0 (by norm_num) (by norm_num)
  have hLip : LipschitzWith 1 (fun x : ℝ => x + 1 / 10) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_add_right, NNReal.coe_one, one_mul, le_refl]
  have hh := abs_coordinate_error_le_of_opposite_calibration (γ := id) split align f
    (fun x : ℝ => x + 1 / 10) hLip
    (⟨1, by norm_num [Real.dist_eq]⟩) (⟨-1, by norm_num [Real.dist_eq]⟩)
    (⟨0, by norm_num⟩) (E := 0) (η := 1 / 10) (ζ := 0) (B := 0) (T := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [f, identityApprox])
    (by norm_num [f, identityApprox]) (by norm_num [f, identityApprox]) (by norm_num)
  have hf0 : f.toFun ⟨0, by norm_num⟩ = 0 := rfl
  rw [hf0, align] at hh
  simpa only [WithLp.fst, WithLp.ofLp_toLp, zero_add, add_zero, sub_zero,
    zero_pow (by omega : (2 : ℕ) ≠ 0), zero_div] using hh


private def L (i : ℕ) : ℝ := (i : ℝ) + 1
private def radii (i : ℕ) : ℝ := 10 * L i
private noncomputable def errors (i : ℕ) : ℝ := (1 / ((i : ℝ) + 1)) / 100
private theorem L_pos (i : ℕ) : 0 < L i := by dsimp [L]; positivity
private theorem errors_bounds (i : ℕ) : 0 < errors i ∧ errors i < 1 := by
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hq : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  dsimp [errors]
  exact ⟨by positivity, by linarith⟩
private theorem L_top : Tendsto L atTop atTop :=
  tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
private theorem radii_top : Tendsto radii atTop atTop := L_top.const_mul_atTop (by norm_num)
private theorem errors_zero : Tendsto errors atTop (𝓝 0) := by
  change Tendsto (fun i : ℕ => (1 / ((i : ℝ) + 1)) / 100) atTop (𝓝 0)
  simpa only [zero_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 100
private noncomputable def approx (i : ℕ) : PointedBallApprox (0 : ℝ) (0 : ℝ) (radii i) (errors i) :=
  identityApprox 0 (errors_bounds i).1 (by
    have hi : 1 ≤ L i := by dsimp [L]; linarith [Nat.cast_nonneg (α := ℝ) i]
    dsimp [radii]
    linarith [(errors_bounds i).2])

private theorem calibration (T : ℝ) (hT : 0 < T) (ζ : ℝ) (hζ : 0 < ζ) :
    ∀ᶠ i in atTop, ∃ aPlus aMinus : BallCarrier (0 : ℝ) (radii i),
      T - 0 ≤ dist (0 : ℝ) (L i) - dist aPlus.val (L i) ∧
      dist (0 : ℝ) (L i) - dist aMinus.val (L i) ≤ -T + 0 + 0 ∧
      dist ((approx i).toFun aPlus) T ≤ ζ ∧ dist ((approx i).toFun aMinus) (-T) ≤ ζ := by
  filter_upwards [L_top.eventually (eventually_ge_atTop T)] with i hi
  have hp : dist T (0 : ℝ) ≤ radii i := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hT]
    dsimp [radii]
    linarith [L_pos i]
  have hm : dist (-T) (0 : ℝ) ≤ radii i := by simpa only [Real.dist_eq, sub_zero, abs_neg] using hp
  refine ⟨⟨T, hp⟩, ⟨-T, hm⟩, ?_, ?_, ?_, ?_⟩
  · simp only [sub_zero, Real.dist_eq, zero_sub, abs_neg, abs_of_pos (L_pos i),
      abs_of_nonpos (sub_nonpos.mpr hi)]
    linarith
  · have hh : -T - L i ≤ 0 := by linarith [L_pos i]
    simp only [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (L_pos i), abs_of_nonpos hh,
      add_zero]
    linarith
  · simpa only [approx, identityApprox, dist_self] using hζ.le
  · simpa only [approx, identityApprox, dist_self] using hζ.le

example : ∀ S : ℝ, 0 < S → ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
    S ≤ radii i ∧ ∀ x : BallCarrier (0 : ℝ) (radii i), dist x.val 0 ≤ S →
      |dist (0 : ℝ) (L i) - dist x.val (L i) - x.val| < η := by
  have hh := eventually_abs_distance_coordinate_error_lt_of_opposite_calibration
    (γ := id) split align approx radii_top errors_zero L (Eseq := fun _ => 0)
    (ηseq := fun _ => 0) (fun _ => le_rfl) tendsto_const_nhds tendsto_const_nhds calibration
  exact hh

example (i : ℕ) : dist (2 * L i) (0 : ℝ) ≤ radii i ∧
    |dist (0 : ℝ) (L i) - dist (2 * L i) (L i) - 2 * L i| = 2 * L i := by
  have hL := L_pos i
  constructor
  · rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    dsimp [radii]
    linarith
  · rw [Real.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hL,
      show 2 * L i - L i = L i by ring, abs_of_pos hL]
    rw [sub_self, zero_sub, abs_neg, abs_of_nonneg (by positivity)]

#print axioms GC.MetricGeometry.abs_coordinate_error_le_of_opposite_calibration
#print axioms GC.MetricGeometry.eventually_abs_coordinate_error_lt_of_opposite_calibration
#print axioms GC.MetricGeometry.eventually_abs_distance_coordinate_error_lt_of_opposite_calibration
```
