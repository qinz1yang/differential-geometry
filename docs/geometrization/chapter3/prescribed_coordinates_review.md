# Compiled self-review: full AC52 prescribed coordinates

Three public theorems and four definitions in three leaves add twenty-four owned
declarations including generated declarations. The273-module gate checks1290
owned declarations (3107 jobs), with transitive axiom closures limited to
propext, Classical.choice and Quot.sound. Source-copy unusedArguments, simpNF
and synTaut linters are silent. Declaration kinds were manually inspected;
defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning is outside these closures. Static audit passes. No full
migrated root, fresh blueprint PDF/Overleaf build, human or delegated review is claimed.

The independent compiled driver uses the ACTUAL L2 real plane, its identity
closed-ball approximation, and the prescribed coordinateh_tau(u,v)=0 whenu=0,
otherwiseu+tau. It proves the discrepancy bound<=tau and exact basepoint, and
independently provesh_tau is NOT continuous fortau>0: along(1/(n+1),0) it tends
totau while continuity at the basepoint would forcezero. The finite construction
is applied with original error1/32, coordinate discrepancy1/32, radius3 and
KL tolerance1/2. It preservesh EVERYWHERE. The driver proves(100,7) lies outside
the radius3 domain and verifies its output coordinate is exactly100+1/32.
The sequence theorem is tested with positive tau_i=1/(100(i+1)), actual growing
identity approximations, vanishing errors and uniform discrepancy; for EVERY
fixed0<delta<1 it produces all sufficiently late whole-space KL maps with the
exact prescribed discontinuous coordinates. The driver exits zero with eight
axiom reports, including the independently checked noncontinuity proof.

Statement audit checks the exactepsilon+2rho error, unchanged radius, strict
coverage includingrho=0, both distortion directions, actual L2 slice distance,
basepoint preservation and all-source coordinate equality. The whole-space
constructor proves its coverage witnesses lie in the OPEN reciprocal-radius
source ball and uses infimum coverage without an attainment claim. The eventual
consumer has no hidden continuity, smoothness, properness, completeness or length
hypothesis and requires no additional subsequence. It restores prescribed
coordinates; it does not establish the geometric hypotheses needed to produce
them from long strainers or infer smooth adapted fibrations.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.PrescribedCoordinateConvergence
import DifferentialGeometry.Geometry.Metric.Approximation.RealBallExamples
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open GC.MetricGeometry Set Filter Metric
open scoped Topology

private abbrev P := WithLp 2 (ℝ × ℝ)
private def p : P := WithLp.toLp 2 (0, 0)
private noncomputable def coord (τ : ℝ) (x : P) : ℝ :=
  if x.fst = 0 then 0 else x.fst + τ
private theorem coord_base (τ : ℝ) : coord τ p = 0 := by simp [coord, p]
private theorem coord_bound {τ : ℝ} (hτ : 0 ≤ τ) (x : P) : dist (coord τ x) x.fst ≤ τ := by
  by_cases hx : x.fst = 0
  · simp [coord, hx, hτ]
  · simp only [coord, ite_eq_right hx, Real.dist_eq]
    have he : x.fst + τ - x.fst = τ := by ring
    rw [he, abs_of_nonneg hτ]

private theorem coord_not_continuous {τ : ℝ} (hτ : 0 < τ) : ¬ Continuous (coord τ) := by
  intro hcont
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let c (n : ℕ) : P := WithLp.toLp 2 (1 / ((n : ℝ) + 1), 0)
  have hc : Tendsto c atTop (𝓝 p) :=
    ((WithLp.prod_continuous_toLp 2 ℝ ℝ).tendsto (0, 0)).comp
      (ht.prodMk_nhds tendsto_const_nhds)
  have hzero : Tendsto (fun n => coord τ (c n)) atTop (𝓝 0) := by
    simpa only [coord_base, Function.comp_def] using (hcont.tendsto p).comp hc
  have hval (n : ℕ) : coord τ (c n) = 1 / ((n : ℝ) + 1) + τ := by
    change (if 1 / ((n : ℝ) + 1) = 0 then 0 else 1 / ((n : ℝ) + 1) + τ) = _
    rw [ite_eq_right (ne_of_gt (by positivity : 0 < 1 / ((n : ℝ) + 1)))]
  have hlimit : Tendsto (fun n => coord τ (c n)) atTop (𝓝 τ) := by
    simpa only [hval, zero_add] using ht.add_const τ
  have he : (0 : ℝ) = τ := tendsto_nhds_unique hzero hlimit
  linarith

private noncomputable def original : PointedBallApprox p p 3 (1 / 32) :=
  identityApprox p (by norm_num) (by norm_num)
private noncomputable def restored : KleinerLottApprox p p (1 / 2) :=
  (original.replaceFirstCoordinate (coord (1 / 32)) (coord_base _)
    (fun x => coord_bound (by norm_num) x.val) (by norm_num)).toKleinerLottWithFirstCoordinate
      (coord (1 / 32)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ¬ Continuous (coord (1 / 32)) := coord_not_continuous (by norm_num)
example (x : P) : (restored.toFun x).fst = coord (1 / 32) x :=
  (original.replaceFirstCoordinate (coord (1 / 32)) (coord_base _)
    (fun x => coord_bound (by norm_num) x.val) (by norm_num)).toKleinerLottWithFirstCoordinate_fst (δ := (1 / 2 : ℝ))
      (coord (1 / 32)) (original.replaceFirstCoordinate_fst _ _ _ _)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) x

example : dist (WithLp.toLp 2 ((100 : ℝ), (7 : ℝ))) p > 3 := by
  have hd := WithLp.dist_fst_le (WithLp.toLp 2 ((100 : ℝ), (7 : ℝ))) p
  norm_num [p, Real.dist_eq] at hd
  dsimp only [p]
  linarith

example : (restored.toFun (WithLp.toLp 2 ((100 : ℝ), (7 : ℝ)))).fst = 100 + 1 / 32 := by
  have hh := (original.replaceFirstCoordinate (coord (1 / 32)) (coord_base _)
    (fun x => coord_bound (by norm_num) x.val) (by norm_num)).toKleinerLottWithFirstCoordinate_fst (δ := (1 / 2 : ℝ))
      (coord (1 / 32)) (original.replaceFirstCoordinate_fst _ _ _ _)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (WithLp.toLp 2 ((100 : ℝ), (7 : ℝ)))
  simpa [coord, restored] using hh

private noncomputable def errors (i : ℕ) : ℝ := (1 / ((i : ℝ) + 1)) / 100
private theorem errors_bounds (i : ℕ) : 0 < errors i ∧ errors i < 1 := by
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hq : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  dsimp [errors]
  exact ⟨by positivity, by linarith⟩
private theorem errors_zero : Tendsto errors atTop (𝓝 0) := by
  change Tendsto (fun i : ℕ => (1 / ((i : ℝ) + 1)) / 100) atTop (𝓝 0)
  simpa only [zero_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 100

example {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    ∀ᶠ i in atTop, ∃ ψ : KleinerLottApprox p p δ,
      ∀ x : P, (ψ.toFun x).fst = coord (errors i) x := by
  apply eventually_prescribed_kleinerLott_approximation (IsometryEquiv.refl P)
    (fun i => identityApprox p (R := (i : ℝ) + 2) (errors_bounds i).1
      (by linarith [(errors_bounds i).2, Nat.cast_nonneg (α := ℝ) i]))
    (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    errors_zero (fun i => coord (errors i)) (fun i => coord_base _) ?_ hδ hδone
  intro S η hη
  filter_upwards [errors_zero.eventually (eventually_le_nhds hη)] with i hi
  intro x _
  exact (coord_bound (errors_bounds i).1.le x.val).trans hi

#print axioms GC.MetricGeometry.PointedBallApprox.mapTargetIsometry
#print axioms GC.MetricGeometry.PointedBallApprox.perturb
#print axioms GC.MetricGeometry.PointedBallApprox.replaceFirstCoordinate
#print axioms GC.MetricGeometry.PointedBallApprox.replaceFirstCoordinate_fst
#print axioms GC.MetricGeometry.PointedBallApprox.toKleinerLottWithFirstCoordinate
#print axioms GC.MetricGeometry.PointedBallApprox.toKleinerLottWithFirstCoordinate_fst
#print axioms GC.MetricGeometry.eventually_prescribed_kleinerLott_approximation
#print axioms coord_not_continuous
```
