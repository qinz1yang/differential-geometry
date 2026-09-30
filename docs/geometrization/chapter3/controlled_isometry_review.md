# Compiled self-review: actual-map controlled isometries

Three public theorems in two leaves add four owned declarations including generated
declarations. The 268-module gate checks1253 owned declarations (3102 jobs), with
transitive axiom closures limited to propext, Classical.choice and Quot.sound.
Source-copy unusedArguments, simpNF and synTaut linters are silent. Declaration
kinds were manually inspected; defLemma is unavailable. Earlier mathematical
leaves are unchanged. The inherited AreaUpperBarrier warning is outside these
closures. Static audit passes. No full migrated root, fresh blueprint PDF/Overleaf
build, human or delegated review is claimed.

The independent compiled driver constructs ACTUAL alternating identity/reflection
approximations on real balls, with increasing radii and positive errors tending
to zero. At the actual point1 their images equal1 on even indices and-1 on odd
indices. It independently proves this full image sequence has NO real limit,
using the two explicit strictly increasing even/odd subsequences and uniqueness
of limits. Both new subsequence theorems apply successfully: the fixed-domain
input-map theorem and the common-source theorem with identity first maps and
alternating second maps. Thus subsequence extraction is materially necessary,
not an unnecessary weakening hidden by an identity-only example. The driver
exits zero with three axiom reports.

Statement audit checks one strictly increasing subsequence for ALL fixed balls,
uniformity over ALL source points in each ball, actual supplied-map values,
onto-ness via compact coverage preimages, basepoint preservation, vanishing errors
and growing radii. The common-source spaces need no properness or completeness;
only the fixed limit spaces are proper. It proves the precise3epsilon forward
comparison using the existing chosen inverse, not a substituted unrelated map.
No continuity of approximations is assumed. The proof selects an actual ordinary
subsequence after uniform ultrafilter estimates; it does not assert that an
arbitrary ultrafilter has a convergent sequence. Full AC51 product assembly remains.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.CommonSourceControl
import Mathlib.Tactic

open GC.MetricGeometry Set Filter Metric
open scoped Topology

private def J (i : ℕ) : ℝ := (i : ℝ) + 1
private noncomputable def errors (i : ℕ) : ℝ := (1 / ((i : ℝ) + 1)) / 100
private theorem J_one (i : ℕ) : 1 ≤ J i := by dsimp [J]; linarith [Nat.cast_nonneg (α := ℝ) i]
private theorem J_top : Tendsto J atTop atTop :=
  tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
private theorem errors_pos (i : ℕ) : 0 < errors i := by dsimp [errors]; positivity
private theorem errors_J (i : ℕ) : 10 * errors i < J i := by
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hq : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  dsimp [errors, J]
  linarith
private theorem errors_zero : Tendsto errors atTop (𝓝 0) := by
  change Tendsto (fun i : ℕ => (1 / ((i : ℝ) + 1)) / 100) atTop (𝓝 0)
  simpa only [zero_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 100

private def negApprox {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    PointedBallApprox (0 : ℝ) (0 : ℝ) R ε where
  error_pos := hε
  error_lt_radius := hεR
  toFun x := -x.val
  basepoint := neg_zero
  distortion x y := by simpa only [dist_neg_neg, sub_self, abs_zero] using hε
  coverage y hy := by
    have hh : dist (-y) (0 : ℝ) ≤ R := by simpa using hy.trans (sub_le_self R hε.le)
    exact ⟨⟨-y, hh⟩, by simpa using hε⟩

private noncomputable def alternating (i : ℕ) :
    PointedBallApprox (0 : ℝ) (0 : ℝ) (4 * J i + 4) (errors i) :=
  if i % 2 = 0 then identityApprox 0 (errors_pos i) (by linarith [errors_J i, J_one i])
  else negApprox (errors_pos i) (by linarith [errors_J i, J_one i])

private def sign (i : ℕ) : ℝ := if i % 2 = 0 then 1 else -1

example (i : ℕ) : (alternating i).toFun
    ⟨1, by simpa using (show (1 : ℝ) ≤ 4 * J i + 4 by linarith [J_one i])⟩ = sign i := by
  simp only [alternating, sign]
  split_ifs <;> rfl

example : ¬ ∃ t : ℝ, Tendsto sign atTop (𝓝 t) := by
  rintro ⟨t, ht⟩
  have he : StrictMono (fun n : ℕ => 2 * n) := by intro a b hab; dsimp; omega
  have ho : StrictMono (fun n : ℕ => 2 * n + 1) := by intro a b hab; dsimp; omega
  have heven : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 t) := by
    simpa [sign, Function.comp_def, Nat.mul_mod] using ht.comp he.tendsto_atTop
  have hodd : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 t) := by
    simpa [sign, Function.comp_def, Nat.mul_mod, Nat.add_mod] using ht.comp ho.tendsto_atTop
  have h1 : t = 1 := tendsto_nhds_unique heven tendsto_const_nhds
  have hm : t = -1 := tendsto_nhds_unique hodd tendsto_const_nhds
  linarith

example : ∃ (e : ℝ ≃ᵢ ℝ) (φ : ℕ → ℕ), e 0 = 0 ∧ StrictMono φ ∧
    ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
      ∀ x : BallCarrier (0 : ℝ) (4 * J (φ i) + 4), dist x.val 0 ≤ S →
        dist ((alternating (φ i)).toFun x) (e x.val) < η := by
  have hR : Tendsto (fun i => 4 * J i + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop 4 (J_top.const_mul_atTop (by norm_num))
  exact exists_isometryEquiv_subsequence_of_pointed_approximations hR errors_zero alternating

example : ∃ (e : ℝ ≃ᵢ ℝ) (φ : ℕ → ℕ), e 0 = 0 ∧ StrictMono φ ∧
    ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
      ∀ x : BallCarrier (0 : ℝ) (4 * J (φ i) + 4), dist x.val 0 ≤ S →
        dist ((alternating (φ i)).toFun x) (e x.val) < η := by
  exact exists_controlled_common_limit_isometry J_one J_top errors_zero errors_J
    (fun i => identityApprox (0 : ℝ) (errors_pos i) (by linarith [errors_J i, J_one i]))
    alternating

#print axioms GC.MetricGeometry.exists_isometryEquiv_subsequence_of_pointed_approximations
#print axioms GC.MetricGeometry.commonSourceComparison_forward_error
#print axioms GC.MetricGeometry.exists_controlled_common_limit_isometry
```
