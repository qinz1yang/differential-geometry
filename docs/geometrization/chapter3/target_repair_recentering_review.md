# Full AC77-78 acceptance

Six public theorems and three definitions in two leaves add45 owned declarations, including36 generated declarations. The343-module gate checks1522 declarations in3178 jobs. All new closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import review lint is silent;15 requested reports check production declarations and concrete tests. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves remain unchanged. The inherited AreaUpperBarrier warning is outside these closures. The separate blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

One agent implemented and tested the proofs. Root independently read all source and proof bodies, including the closed-ball and whole-map coverage bounds. The compatibility consumer's author and reviewer also checked the actual-displacement and self-target APIs in their full integration. The final driver imports the accepted leaves, not copied theorem bodies.

The repair proof changes only the basepoint value and uses actual original coverage. It keeps the SAME closed radius and bounds distortion by e+2eta. Zero eta does not consume the strict error margin. The recentering proof uses the accepted KL conversion with actual strict2e witnesses, then MC10 and repair; this yields errors3e,9e,11e at explicitly padded radii. The exact inclusive tolerance implies22e<delta. Actual target coverage places a source witness strictly inside the required new open ball. The returned whole map retains EVERY noncenter original value. Its public bound uses actual dist(f(a),b), which the later joint-product repair needs; b=f(a) makes the entire map unchanged.

Tests cover eta0 at every controlled point, nonzero repair at the basepoint and unchanged exact radius5 boundary, and global displacement. A real whole-space map is the identity except f(1000)=77, outside its original radius500 control ball. At EXACT epsilon=theta(1/2,1)=1/500 the new center is1, on the closed displacement boundary, and prescribed target501/500 has error exactly epsilon. The returned map retains the remote value77, agrees with the old map at every noncenter point, has the claimed global displacement, and has its own coverage witnesses inside the new radius2 ball. An additional identity example on Ioi0 proves source incompleteness and invokes self-target recentering while preserving every point.

Source reading covers frozen AC77-78 and actual KL4.10 proof/equations4.11-4.13 with retained errata. The original source assumes completeness and an open center ball; the metric proof justifies removing completeness and including the closed boundary. The explicit theta and numeric constants are blueprint bounds, not quotations from KL. Continuity of repaired maps is not asserted. Full AC77-78 are complete; normalized splitting and compatibility transport remain AC79-80's separate acceptance. Blueprint207 and migration interfaces are unchanged.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottRecentering
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import Mathlib.Tactic

set_option autoImplicit false

namespace GCAC7778Review

open GC.MetricGeometry Metric Set

private def identityBall : PointedBallApprox (0 : ℝ) (0 : ℝ) 5 (1 / 100) where
  error_pos := by norm_num
  error_lt_radius := by norm_num
  toFun x := x.val
  basepoint := rfl
  distortion x y := by norm_num
  coverage y hy := by
    refine ⟨⟨y, by linarith⟩, ?_⟩
    change dist y y < (1 / 100 : ℝ)
    norm_num

private theorem zero_repair_all_points :
    ∃ F : PointedBallApprox (0 : ℝ) (0 : ℝ) 5 (1 / 100 + 2 * 0),
      ∀ x : BallCarrier (0 : ℝ) 5, F.toFun x = x.val := by
  let F := identityBall.repairTarget 0 (η := 0) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨F, fun x => ?_⟩
  have hh := identityBall.repairTarget_dist_le 0 (η := 0)
    (by norm_num) (by norm_num) (by norm_num) x
  exact dist_eq_zero.mp (le_antisymm hh dist_nonneg)

private theorem nonzero_repair_at_and_away :
    ∃ F : PointedBallApprox (0 : ℝ) (1 / 10 : ℝ) 5 (1 / 100 + 2 * (1 / 10)),
      F.toFun ⟨0, by norm_num⟩ = 1 / 10 ∧
      F.toFun ⟨5, by norm_num [Real.dist_eq]⟩ = 5 ∧
      ∀ x : BallCarrier (0 : ℝ) 5, dist (F.toFun x) x.val ≤ 1 / 10 := by
  let F := identityBall.repairTarget (1 / 10) (η := 1 / 10)
    (by norm_num) (by norm_num [Real.dist_eq]) (by norm_num)
  refine ⟨F, F.basepoint, ?_, ?_⟩
  · exact identityBall.repairTarget_apply_of_ne (1 / 10) (η := 1 / 10)
      (by norm_num) (by norm_num [Real.dist_eq]) (by norm_num) ⟨5, by norm_num [Real.dist_eq]⟩
      (by norm_num)
  · exact identityBall.repairTarget_dist_le (1 / 10) (η := 1 / 10)
      (by norm_num) (by norm_num [Real.dist_eq]) (by norm_num)

private noncomputable def wild (x : ℝ) : ℝ := if x = 1000 then 77 else x

private theorem wild_eq (x : ℝ) (hx : x ≠ 1000) : wild x = x := by
  simp only [wild, ite_eq_right hx]

private noncomputable def original : KleinerLottApprox (0 : ℝ) (0 : ℝ) (1 / 500) where
  error_pos := by norm_num
  error_lt_one := by norm_num
  toFun := wild
  basepoint := by norm_num [wild]
  distortion x hx y hy := by
    have hx' : x ≠ 1000 := by intro hh; subst x; norm_num [mem_ball, Real.dist_eq] at hx
    have hy' : y ≠ 1000 := by intro hh; subst y; norm_num [mem_ball, Real.dist_eq] at hy
    rw [wild_eq x hx', wild_eq y hy', sub_self, abs_zero]
    norm_num
  coverage y hy := by
    have hy' : y ≠ 1000 := by intro hh; subst y; norm_num [Real.dist_eq] at hy
    have hm : y ∈ wild '' ball 0 (1 / 500 : ℝ)⁻¹ :=
      ⟨y, by change dist y 0 < (1 / 500 : ℝ)⁻¹; linarith, wild_eq y hy'⟩
    exact (Metric.infDist_le_dist_of_mem hm).trans (by norm_num)

private theorem exact_tolerance : recenterTolerance (1 / 2) 1 = 1 / 500 := by
  norm_num [recenterTolerance]

private theorem repaired_recenter_preserves_remote_value :
    ∃ F : KleinerLottApprox (1 : ℝ) (501 / 500 : ℝ) (1 / 2),
      F.toFun 1 = 501 / 500 ∧ F.toFun 1000 = 77 ∧
      (∀ x : ℝ, x ≠ 1 → F.toFun x = wild x) ∧
      (∀ x : ℝ, dist (F.toFun x) (wild x) ≤ 1 / 500) ∧
      ∀ y : ℝ, dist y (501 / 500) < 3 / 2 →
        ∃ x ∈ ball (1 : ℝ) 2, dist y (F.toFun x) < 1 := by
  have hε : (1 / 500 : ℝ) ≤ recenterTolerance (1 / 2) 1 := by rw [exact_tolerance]
  have ha : dist (0 : ℝ) 1 ≤ 1 := by norm_num [Real.dist_eq]
  have hb : dist (original.toFun 1) (501 / 500) ≤ 1 / 500 := by
    norm_num [original, wild, Real.dist_eq]
  let F := original.recenterWithTarget 1 (501 / 500) (δ := 1 / 2) (C := 1)
    (by norm_num) (by norm_num) (by norm_num) hε ha hb
  refine ⟨F, F.basepoint, ?_, ?_, ?_, ?_⟩
  · have hh := original.recenterWithTarget_apply_of_ne 1 (501 / 500) (δ := 1 / 2) (C := 1)
      (by norm_num) (by norm_num) (by norm_num) hε ha hb 1000 (by norm_num)
    change F.toFun 1000 = wild 1000 at hh
    exact hh.trans (by norm_num [wild])
  · intro x hx
    exact original.recenterWithTarget_apply_of_ne 1 (501 / 500) (δ := 1 / 2) (C := 1)
      (by norm_num) (by norm_num) (by norm_num) hε ha hb x hx
  · intro x
    exact (original.recenterWithTarget_dist_le 1 (501 / 500) (δ := 1 / 2) (C := 1)
      (by norm_num) (by norm_num) (by norm_num) hε ha hb x).trans hb
  · intro y hy
    simpa using F.coverage_witness y (by norm_num; exact hy)

private abbrev HalfLine := Ioi (0 : ℝ)
private def oldBase : HalfLine := ⟨1, by norm_num⟩
private def newBase : HalfLine := ⟨2, by norm_num⟩

private theorem half_line_not_complete : ¬ CompleteSpace HalfLine := by
  intro h
  let := h
  have hc : IsClosed (Ioi (0 : ℝ)) := by
    simpa only [Subtype.range_val] using
      (isometry_subtype_coe (s := Ioi (0 : ℝ))).isUniformInducing.isComplete_range.isClosed
  have hm : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact (show (0 : ℝ) ≤ 0 from le_rfl)
  exact (lt_irrefl (0 : ℝ)) (hc.closure_subset hm)

private theorem incomplete_source_actual_map_recenter :
    ∃ F : KleinerLottApprox newBase newBase (1 / 2 : ℝ),
      ∀ x : HalfLine, F.toFun x = x := by
  let f := (IsometryEquiv.refl HalfLine).toKleinerLottApprox (p := oldBase) rfl
    (by norm_num : (0 : ℝ) < 1 / 500) (by norm_num : (1 / 500 : ℝ) < 1)
  have hε : (1 / 500 : ℝ) ≤ recenterTolerance (1 / 2) 1 := by rw [exact_tolerance]
  have ha : dist oldBase newBase ≤ (1 : ℝ) := by norm_num [oldBase, newBase, Subtype.dist_eq, Real.dist_eq]
  refine ⟨f.recenterWithTarget newBase (f.toFun newBase) (δ := 1 / 2) (C := 1)
    (by norm_num) (by norm_num) (by norm_num) hε ha
      (by simpa only [dist_self] using f.error_pos.le), ?_⟩
  exact f.recenterWithTarget_self_apply newBase (δ := 1 / 2) (C := 1)
    (by norm_num) (by norm_num) (by norm_num) hε ha

#print axioms zero_repair_all_points
#print axioms nonzero_repair_at_and_away
#print axioms exact_tolerance
#print axioms repaired_recenter_preserves_remote_value
#print axioms half_line_not_complete
#print axioms incomplete_source_actual_map_recenter

end GCAC7778Review

#lint- only unusedArguments simpNF synTaut

#print axioms GC.MetricGeometry.PointedBallApprox.repairTarget
#print axioms GC.MetricGeometry.PointedBallApprox.repairTarget_apply_of_ne
#print axioms GC.MetricGeometry.PointedBallApprox.repairTarget_dist_le
#print axioms GC.MetricGeometry.recenterTolerance
#print axioms GC.MetricGeometry.recenterTolerance_pos
#print axioms GC.MetricGeometry.KleinerLottApprox.recenterWithTarget
#print axioms GC.MetricGeometry.KleinerLottApprox.recenterWithTarget_apply_of_ne
#print axioms GC.MetricGeometry.KleinerLottApprox.recenterWithTarget_dist_le
#print axioms GC.MetricGeometry.KleinerLottApprox.recenterWithTarget_self_apply
```
