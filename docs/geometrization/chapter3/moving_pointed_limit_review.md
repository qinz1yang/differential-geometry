# Full AC81 independent acceptance

Five public theorems and one definition in two leaves add seven owned declarations, including one generated declaration. The348-module gate checks1563 declarations in3183 jobs. All new closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import review lint is silent; nine reports check all production declarations and three concrete regressions. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside these closures. The separate blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

Root implemented the marked evaluation, separation, original-map recentering and proper-target extraction proofs. An independent agent read the complete frozen bodies, actual source passages and all hypotheses; it independently compiled the proofs with lint/axiom evidence and implemented the original-input regressions. Root read the complete regression bodies. Final checks import accepted production leaves rather than copying their theorem bodies.

The whole extension changes no value on an original carrier. A bounded marked point eventually belongs to the growing carriers; every radial/error estimate explicitly proves that domain condition. The fallback at the old target basepoint handles only the finite undefined prefix and adds no convergence assumption. For every requested new radius s and error alpha, the ORIGINAL maps are recentered using the original source displacement bound and then repaired at their target with total error3epsilon+2eta. This yields pointed convergence to the SAME specified Y. Only target completeness is used. The proper-target clause extracts a common subsequence from actual marked images in a fixed compact ball of Y, retaining original f values and all target identity information. It returns a universal separation statement for any convergent source distance sequence along that same subsequence.

The regression constructs actual rational-to-real inclusion approximations based at5, on radii i+1/2 with errors1/[4(i+1)]. It proves rational sources incomplete and nonproper and proves coverage by rational density. Alternating source marks6,4 have source distance1. At index0 the mark is outside the carrier and its extension is5, explicitly proved. The production extraction returns y in the SAME real line, an actual strictly increasing subsequence, marked-image convergence, pointed convergence at the original marks, and dist(y,5)=1, hence y differs from5. A negative control proves the FULL marked-image sequence does not converge, using the even/odd subsequences. A separate constant mark6 example proves pointed convergence to the SAME real line based at6 despite the early fallback value5.

Source review covers frozen AC81 and KL4.20's actual proof, with BBI8.1.1 and fixed-radius convention context. Retained BBIerrataPDF9's diameter/fixed-epsilon corrections are respected: no whole-space compact convergence is inferred. AC81 establishes only the marked-point step; it neither produces the first limit nor proves either cone structure or the two-apex line. Full AC81 is complete. Blueprint207 and migration interfaces remain unchanged.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.MovingPointedLimit
import Mathlib.Topology.Instances.Rat
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Filter GC.MetricGeometry
open scoped Topology

namespace GCMovingPointedLimitReview

private noncomputable def rad (i : ℕ) : ℝ := i + 1 / 2
private noncomputable def err (i : ℕ) : ℝ := (1 / (i + 1)) / 4

private theorem err_pos (i : ℕ) : 0 < err i := by unfold err; positivity
private theorem err_lt_rad (i : ℕ) : err i < rad i := by
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hi' : 0 < (i : ℝ) + 1 := by positivity
  have hle : (1 : ℝ) / (i + 1) ≤ 1 := (div_le_iff₀ hi').mpr (by linarith)
  dsimp only [err, rad]
  linarith

private def ratApprox (i : ℕ) : PointedBallApprox (5 : ℚ) (5 : ℝ) (rad i) (err i) where
  error_pos := err_pos i
  error_lt_radius := err_lt_rad i
  toFun x := (x.val : ℝ)
  basepoint := by norm_num
  distortion x y := by
    simp only [Rat.dist_cast, sub_self, abs_zero]
    exact err_pos i
  coverage y hy := by
    obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn (by linarith [err_pos i] : y - err i / 2 < y + err i / 2)
    have hry : dist (r : ℝ) y < err i / 2 := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hrad : dist r (5 : ℚ) ≤ rad i := by
      rw [← Rat.dist_cast]
      norm_num only [Rat.cast_ofNat]
      have ht := dist_triangle (r : ℝ) y 5
      linarith
    refine ⟨⟨r, hrad⟩, ?_⟩
    change dist y (r : ℝ) < err i
    rw [dist_comm]
    linarith [err_pos i]

private theorem rad_tendsto : Tendsto rad atTop atTop :=
  tendsto_atTop_add_const_right atTop (1 / 2 : ℝ) tendsto_natCast_atTop_atTop

private theorem err_tendsto : Tendsto err atTop (𝓝 0) := by
  change Tendsto (fun i : ℕ => (1 / ((i : ℝ) + 1)) / 4) atTop (𝓝 0)
  simpa only [zero_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 4

private def marked (i : ℕ) : ℚ := if i % 2 = 0 then 6 else 4
private theorem marked_dist (i : ℕ) : dist (marked i) (5 : ℚ) = 1 := by
  unfold marked
  split_ifs <;> norm_num [Rat.dist_eq]

private theorem marked_in_ball {i : ℕ} (hi : 1 ≤ i) : dist (marked i) (5 : ℚ) ≤ rad i := by
  rw [marked_dist]
  dsimp only [rad]
  have h : (1 : ℝ) ≤ i := by exact_mod_cast hi
  linarith

private theorem actual_image {i : ℕ} (hi : 1 ≤ i) :
    (ratApprox i).extendToWholeSpace (marked i) = (marked i : ℝ) := by
  rw [(ratApprox i).extendToWholeSpace_apply _ (marked_in_ball hi)]
  rfl

private theorem rat_incomplete : ¬ CompleteSpace ℚ := by
  intro hc
  let := hc
  have hi : Isometry (fun r : ℚ => (r : ℝ)) := Isometry.of_dist_eq (fun _ _ => rfl)
  have hclosed := hi.antilipschitzWith.isClosed_range hi.uniformContinuous
  have hdense : DenseRange (fun r : ℚ => (r : ℝ)) := Rat.denseRange_cast
  have heq : range (fun r : ℚ => (r : ℝ)) = univ := hclosed.closure_eq.symm.trans hdense.closure_range
  exact irrational_sqrt_two (by rw [heq]; exact mem_univ _)

private theorem rat_not_proper : ¬ ProperSpace ℚ := by
  intro hp
  let := hp
  exact rat_incomplete inferInstance

theorem alternating_marks_same_real_limit :
    ¬ CompleteSpace ℚ ∧ ¬ ProperSpace ℚ ∧
    (ratApprox 0).extendToWholeSpace (marked 0) = 5 ∧
    dist (marked 0) (5 : ℚ) > rad 0 ∧
    ∃ (y : ℝ) (χ : ℕ → ℕ), StrictMono χ ∧
      Tendsto (fun i => (ratApprox (χ i)).extendToWholeSpace (marked (χ i))) atTop (𝓝 y) ∧
      PointedGHConverges (fun i => marked (χ i)) y ∧ dist y 5 = 1 ∧ y ≠ 5 := by
  refine ⟨rat_incomplete, rat_not_proper, ?_, ?_, ?_⟩
  · norm_num [PointedBallApprox.extendToWholeSpace, marked, rad, Rat.dist_eq]
  · rw [marked_dist]
    norm_num [rad]
  · obtain ⟨y, χ, hχ, _, hy, hconv, hd⟩ := exists_subsequence_moving_pointed_limit
      ratApprox rad_tendsto err_tendsto (fun i => (marked_dist i).le)
    have hdy : dist y 5 = 1 := hd 1 (by simpa only [marked_dist] using tendsto_const_nhds)
    refine ⟨y, χ, hχ, hy, hconv, hdy, ?_⟩
    intro heq
    rw [heq, dist_self] at hdy
    norm_num at hdy

theorem alternating_images_do_not_converge :
    ¬ ∃ y : ℝ, Tendsto (fun i => (ratApprox i).extendToWholeSpace (marked i)) atTop (𝓝 y) := by
  rintro ⟨y, hy⟩
  have heven : StrictMono (fun i : ℕ => 2 * i + 2) := by intro i j hij; dsimp only; omega
  have hodd : StrictMono (fun i : ℕ => 2 * i + 1) := by intro i j hij; dsimp only; omega
  have he (i : ℕ) : (ratApprox (2 * i + 2)).extendToWholeSpace (marked (2 * i + 2)) = 6 := by
    rw [actual_image (by omega)]
    norm_num [marked, Nat.add_mod, Nat.mul_mod]
  have ho (i : ℕ) : (ratApprox (2 * i + 1)).extendToWholeSpace (marked (2 * i + 1)) = 4 := by
    rw [actual_image (by omega)]
    norm_num [marked, Nat.add_mod, Nat.mul_mod]
  have hy6 : Tendsto (fun _ : ℕ => (6 : ℝ)) atTop (𝓝 y) := by
    exact (hy.comp heven.tendsto_atTop).congr he
  have hy4 : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 y) := by
    exact (hy.comp hodd.tendsto_atTop).congr ho
  have h6 : y = 6 := tendsto_nhds_unique hy6 tendsto_const_nhds
  have h4 : y = 4 := tendsto_nhds_unique hy4 tendsto_const_nhds
  linarith

theorem convergent_marks_recenter_after_undefined_prefix :
    (ratApprox 0).extendToWholeSpace (6 : ℚ) = 5 ∧
    PointedGHConverges (fun _ : ℕ => (6 : ℚ)) (6 : ℝ) := by
  have hb (i : ℕ) : dist (6 : ℚ) 5 ≤ (1 : ℝ) := by norm_num [Rat.dist_eq]
  have he : ∀ᶠ i : ℕ in atTop, (ratApprox i).extendToWholeSpace (6 : ℚ) = (6 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with i hi
    have hrad : dist (6 : ℚ) 5 ≤ rad i := by
      have h : (1 : ℝ) ≤ i := by exact_mod_cast hi
      have hd : dist (6 : ℚ) 5 = 1 := by norm_num [Rat.dist_eq]
      rw [hd]
      dsimp only [rad]
      linarith
    rw [(ratApprox i).extendToWholeSpace_apply _ hrad]
    norm_num [ratApprox]
  refine ⟨?_, pointedGHConverges_of_marked_point_tendsto ratApprox rad_tendsto err_tendsto hb
    (tendsto_const_nhds.congr' (he.mono (fun _ hi => hi.symm)))⟩
  norm_num [PointedBallApprox.extendToWholeSpace, rad, Rat.dist_eq]

end GCMovingPointedLimitReview

#print axioms GC.MetricGeometry.PointedBallApprox.extendToWholeSpace
#print axioms GC.MetricGeometry.PointedBallApprox.extendToWholeSpace_apply
#print axioms GC.MetricGeometry.eventually_marked_point_radial_error
#print axioms GC.MetricGeometry.marked_point_limit_dist
#print axioms GC.MetricGeometry.pointedGHConverges_of_marked_point_tendsto
#print axioms GC.MetricGeometry.exists_subsequence_moving_pointed_limit
#print axioms GCMovingPointedLimitReview.alternating_marks_same_real_limit
#print axioms GCMovingPointedLimitReview.alternating_images_do_not_converge
#print axioms GCMovingPointedLimitReview.convergent_marks_recenter_after_undefined_prefix
#lint- only unusedArguments simpNF synTaut
```
