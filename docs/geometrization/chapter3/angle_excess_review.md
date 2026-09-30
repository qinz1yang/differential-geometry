# AC57 review and compiled acceptance

Ten public theorems in five leaves add 24 owned declarations including generated
proof declarations. The 292-module gate checks 1346 owned declarations, 3127
build jobs, with transitive closures limited to propext, Classical.choice and
Quot.sound. Source-copy unusedArguments, simpNF and synTaut lint is silent.
Declaration kinds were inspected; defLemma is unavailable. The inherited
AreaUpperBarrier warning is outside the new closures. Earlier accepted math
leaves are unchanged. Blueprint static audit passes; no full migrated root or
fresh PDF/Overleaf build is claimed.

A separate agent independently read the AC57 statement, pinned AKP model
identities, archived PDF and retained erratum. It confirmed the curvature
parameter sigma (not sqrt(sigma)), positive-arm/triangle hypotheses, the exact
constant, the elementary log proof, and the angle-pi boundary. A second agent
implemented the half-angle pair and compiled/linted its draft. Root inspected
the actual proof, proved the remaining estimates and metric/sequence consumers,
and ran the combined build, lint, axiom and review checks. This is agent review,
not human approval.

The compiled review constructs the actual hyperbolic model side with arms one,
curvature -1 and angle pi-1. It proves the side lies strictly between zero and
two, so the tested excess is genuinely POSITIVE, and obtains the exact upper
bound 1/2. Actual real-line opposite endpoints test the degenerate angle-pi
case for every positive arm length and 0<sigma<=1. A varying real-line example
instantiates the sequential metric theorem with sigma_i=1/(i+1) and actual
endpoints +/- (i+1). Finally, a negative control proves that c_i=2L_i-1 has
relative excess tending to zero but absolute excess identically one, which
does not tend to zero. All ten public axiom reports contain only the standard
triple. The source-copy lint and reviewed drivers contain no warnings.

The statement audit checks exact real exponent 3/2, both inequalities of the
modulus, actual metric triangle bounds, eventual angle control, arbitrary early
sigma values, and no curvature/geodesic/completeness requirement. The equal-arm
length is generalized; L=sigma inverse is a direct specialization. The proof
uses an elementary logarithmic inequality instead of the blueprint integral,
without changing the result. AC61 and multi-axis work remain separate.

```lean
import DifferentialGeometry.Geometry.Comparison.OppositeAngleExcess
import DifferentialGeometry.Geometry.Comparison.ModelSide
import Mathlib.Tactic

open Filter Set
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

private noncomputable def c : ℝ := modelSideNegCurvature 1 1 1 (Real.pi - 1)

private theorem hc : 0 < c ∧ c < 2 := by
  have ht : Real.pi - 1 ∈ Icc (0 : ℝ) Real.pi := by constructor <;> linarith [Real.two_le_pi]
  have hb := modelSideNegCurvature_mem_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) ht
  have ha := comparisonAngleNegCurvature_modelSide (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) ht
  change comparisonAngleNegCurvature 1 1 1 c = Real.pi - 1 at ha
  have h0 : c ≠ 0 := by
    intro hh
    rw [hh] at ha
    have hz : comparisonAngleNegCurvature 1 1 1 0 = 0 := by
      simpa only [modelSideNegCurvature_zero_angle (by norm_num : (0 : ℝ) ≤ 1), sub_self, abs_zero] using comparisonAngleNegCurvature_modelSide (κ := 1) (a := 1) (b := 1)
        (by norm_num) (by norm_num) (by norm_num) (θ := 0) ⟨le_rfl, Real.pi_pos.le⟩
    rw [hz] at ha
    linarith [Real.two_le_pi]
  have h2 : c ≠ 2 := by
    intro hh
    rw [hh] at ha
    have he : comparisonAngleNegCurvature 1 1 1 2 = Real.pi := by
      convert comparisonAngleNegCurvature_add (κ := 1) (a := 1) (b := 1)
        (by norm_num) (by norm_num) (by norm_num) using 1
      norm_num
    rw [he] at ha
    linarith
  change |(1 : ℝ) - 1| ≤ c ∧ c ≤ 1 + 1 at hb
  simp only [sub_self, abs_zero] at hb
  exact ⟨lt_of_le_of_ne hb.1 (Ne.symm h0), lt_of_le_of_ne (by linarith [hb.2]) h2⟩

example : 0 < 2 - c ∧ 2 - c ≤ (1 / 2 : ℝ) := by
  have ht : Real.pi - 1 ∈ Icc (0 : ℝ) Real.pi := by constructor <;> linarith [Real.two_le_pi]
  have ha : Real.pi - 1 ≤ comparisonAngleNegCurvature 1 1 1 c := by
    exact (comparisonAngleNegCurvature_modelSide (by norm_num) (by norm_num)
      (by norm_num) ht).ge
  have hh := equal_side_excess_bound_of_angle_lower_bound (σ := 1) (L := 1) (c := c)
    (by norm_num) le_rfl (by norm_num) hc.1.le (by linarith [hc.2]) ha
  constructor
  · linarith [hc.2]
  · simpa using hh.2.1.trans hh.2.2

example (L : ℝ) (hL : 0 < L) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    0 ≤ 2 * L - dist L (-L) ∧
    2 * L - dist L (-L) ≤ -(2 / Real.sqrt σ) * Real.log (Real.cos (σ / 2)) ∧
    -(2 / Real.sqrt σ) * Real.log (Real.cos (σ / 2)) ≤ σ ^ (3 / 2 : ℝ) / 2 := by
  have hp : dist (0 : ℝ) L = L := by simp [Real.dist_eq, abs_of_pos hL]
  have hm : dist (0 : ℝ) (-L) = L := by simp [Real.dist_eq, abs_of_pos hL]
  have hd : dist L (-L) = L + L := by rw [Real.dist_eq, sub_neg_eq_add, abs_of_pos (by linarith)]
  apply opposite_endpoint_excess_bound (p := (0 : ℝ)) hσ hσ1 hL hp hm
  rw [hp, hm, hd, comparisonAngleNegCurvature_add hσ.le hL hL]
  linarith

example : Tendsto (fun i : ℕ => 2 * ((i : ℝ) + 1) - dist ((i : ℝ) + 1) (-((i : ℝ) + 1)))
    atTop (𝓝 0) := by
  let σ : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 1)
  have hs (i : ℕ) : 0 < σ i := by dsimp [σ]; positivity
  apply tendsto_opposite_endpoint_excess_zero (σ := σ) (p := fun _ => (0 : ℝ)) hs
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (fun i => by positivity)
    (fun i => by rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (show 0 < (i : ℝ) + 1 by positivity)])
    (fun i => by rw [Real.dist_eq, zero_sub, neg_neg, abs_of_pos (show 0 < (i : ℝ) + 1 by positivity)])
  exact Eventually.of_forall fun i => by
    have hi : 0 < (i : ℝ) + 1 := by positivity
    simp only [Real.dist_eq, zero_sub, abs_neg, neg_neg]
    rw [abs_of_pos hi, sub_neg_eq_add, abs_of_pos (show 0 < ((i : ℝ) + 1) + ((i : ℝ) + 1) by linarith),
      comparisonAngleNegCurvature_add (hs i).le hi hi]
    linarith [hs i]

example : Tendsto (fun i : ℕ =>
    (2 * ((i : ℝ) + 1) - (2 * ((i : ℝ) + 1) - 1)) / ((i : ℝ) + 1)) atTop (𝓝 0) := by
  simpa only [sub_sub_cancel] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

example : ¬ Tendsto (fun i : ℕ => 2 * ((i : ℝ) + 1) - (2 * ((i : ℝ) + 1) - 1)) atTop (𝓝 0) := by
  simp only [sub_sub_cancel]
  intro h
  have hh : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds h
  norm_num at hh

#print axioms Real.neg_log_cos_le_sq_of_abs_le_one
#print axioms Real.sinh_add_log_le_mul_sinh
#print axioms Real.add_log_le_of_mul_sinh_le
#print axioms sinh_half_sq_eq_of_equal_comparison_sides
#print axioms cos_half_mul_sinh_le_of_comparison_angle_lower_bound
#print axioms equal_side_excess_le_log_cos_of_angle_lower_bound
#print axioms log_cos_excess_modulus_le
#print axioms equal_side_excess_bound_of_angle_lower_bound
#print axioms opposite_endpoint_excess_bound
#print axioms tendsto_opposite_endpoint_excess_zero
```
