# Full AC67 independent metric review

Two public theorems in one leaf add two owned declarations. The 322-module gate checks 1408 declarations in 3157 jobs. All transitive closures contain only propext, Classical.choice and Quot.sound. Source-copy and accepted-import review lint is silent; the driver emits six requested standard axiom reports. Earlier mathematical leaves are unchanged. Declaration kinds were inspected; defLemma is unavailable. The inherited AreaUpperBarrier warning is outside these closures. Static audit passes. No full migrated root, PDF/Overleaf build or human approval is claimed.

One agent implemented the construction and incomplete-factor test. Another independently inspected the proof and built signed-axis tests. Root read the entire proof, source passage and drivers. Every distortion application has both endpoints in the original OPEN source ball. Coverage uses actual witnesses with 2epsilon slack, not an attained minimum. Radial trimming requires only the supplied source segments; no extension beyond their endpoints occurs. The exact 27epsilon estimate passes through the ORIGINAL lifts: less than14epsilon from the two tails, less than5epsilon from lift-pair distortion, and at most8epsilon from model-scale change. The generic index type is unrestricted; no finite choice hypothesis is needed in Lean. The factor is only metric. True and false agree with the positive and negative explicit singleton coordinates.

The first concrete test uses actual real sources and target factor {0} union (200,201). It proves that factor is incomplete. For epsilon=1/100 the target coverage ball lies entirely in the horizontal slice, giving an actual normalized approximation without any factor completeness assumption. It invokes the generic theorem on both opposite unit vectors at r=2, checking exact radii, same-map14/100 error and pair27/100 error.

A second independent test uses the actual Euclidean-plane identity-slice approximation at epsilon=1/100 and r=999/10, close to the buffer boundary. It invokes the SIGNED specialization, verifies positive and negative labels, exact sphere radii, map14/100, the opposite chord target999/5 and mixed-sign cross chord target(999/10)*sqrt2, with pair27/100. A rank-zero instance checks the empty family. All tests import the accepted new leaf. An omitted affine-distance import in the assembled review driver was restored before the clean successful rerun; no failed elaboration evidence is accepted.

Root removed an unnecessary umbrella Mathlib.Tactic import from the new production leaf after a successful minimal-import compile, then rebuilt and reran the combined gate. The proof bodies are unchanged. AC67 is complete; AC68-70 remain separate acceptance steps. Chapters3-4 are unfinished and blueprint207/migration interfaces are unchanged.

```lean
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Tactic
import DifferentialGeometry.Geometry.Metric.Approximation.ExactRadiusLifts
open Set Metric

namespace GCExactRadiusLiftReview

open GC.MetricGeometry

private def FactorSet : Set ℝ := {0} ∪ Ioo 200 201
private abbrev Factor := FactorSet
private def factorBase : Factor := ⟨0, Or.inl rfl⟩

private theorem real_segments (x y : ℝ) :
    ∃ f : Icc (0 : ℝ) 1 → ℝ, Continuous f ∧
      f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : Icc (0 : ℝ) 1 → ℝ := fun t => (1 - (t : ℝ)) * x + (t : ℝ) * y
  refine ⟨f, by fun_prop, by simp [f], by simp [f], ?_⟩
  intro s t
  change |(1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y)| =
    |x - y| * |(s : ℝ) - t|
  rw [show (1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y) =
    (y - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm y x]

private def approximation : KleinerLottApprox (0 : ℝ)
    (WithLp.toLp 2 ((0 : ℝ), factorBase)) (1 / 100 : ℝ) where
  error_pos := by norm_num
  error_lt_one := by norm_num
  toFun x := WithLp.toLp 2 (x, factorBase)
  basepoint := rfl
  distortion x _ x' _ := by
    rw [(WithLp.isometry_prodMk_right (E := ℝ) factorBase).dist_eq]
    norm_num
  coverage q hq := by
    have hrad := WithLp.dist_snd_le q (WithLp.toLp 2 ((0 : ℝ), factorBase))
    have hfactor : q.snd = factorBase := by
      apply Subtype.ext
      rcases q.snd.property with hh | hh
      · exact hh
      · have hpos : 0 < q.snd.val := by linarith [hh.1]
        change |q.snd.val - 0| ≤ _ at hrad
        rw [sub_zero, abs_of_pos hpos] at hrad
        norm_num at hq
        linarith [hh.1]
    have hfirst := WithLp.dist_fst_le q (WithLp.toLp 2 ((0 : ℝ), factorBase))
    have hball : q.fst ∈ ball (0 : ℝ) ((1 / 100 : ℝ)⁻¹) := by
      change dist q.fst 0 < _
      change dist q.fst 0 ≤ _ at hfirst
      linarith
    have hpoint : WithLp.toLp 2 (q.fst, factorBase) = q := by
      apply (WithLp.equiv 2 (ℝ × Factor)).injective
      exact Prod.ext rfl hfactor.symm
    have hmem : q ∈ (fun x : ℝ => WithLp.toLp 2 (x, factorBase)) ''
        ball (0 : ℝ) ((1 / 100 : ℝ)⁻¹) := ⟨q.fst, hball, hpoint⟩
    exact (Metric.infDist_le_dist_of_mem hmem).trans (by norm_num)

theorem factor_not_complete : ¬ CompleteSpace Factor := by
  intro h
  let := h
  have hi : Isometry (Subtype.val : Factor → ℝ) := isometry_subtype_coe
  have hc : IsClosed FactorSet := by
    simpa only [Subtype.range_val] using hi.isUniformInducing.isComplete_range.isClosed
  have h201 : (201 : ℝ) ∈ closure (Ioo (200 : ℝ) 201) := by
    rw [closure_Ioo (by norm_num)]
    constructor <;> norm_num
  have h201' : (201 : ℝ) ∈ closure FactorSet :=
    closure_mono (show Ioo (200 : ℝ) 201 ⊆ FactorSet from subset_union_right) h201
  rw [hc.closure_eq] at h201'
  rcases h201' with hzero | hint
  · norm_num at hzero
  · exact (lt_irrefl (201 : ℝ)) hint.2

-- The factor contains an isolated basepoint and a distant open interval, hence is
-- incomplete. The entire relevant target coverage ball is the horizontal slice.
theorem opposite_lifts_with_incomplete_factor :
    ∃ x a : Bool → ℝ,
      (∀ j, x j ∈ ball (0 : ℝ) 100) ∧
      (∀ j, dist (0 : ℝ) (a j) = 2) ∧
      (∀ j, dist (approximation.toFun (a j))
        (WithLp.toLp 2 ((if j then (2 : ℝ) else -2), factorBase)) < 14 / 100) ∧
      |dist (a true) (a false) - 4| < 27 / 100 := by
  obtain ⟨x, a, hxmem, _hlift, _hlength, harad, _htail, hamap, hpair⟩ :=
    approximation.exists_exact_radius_unit_vector_lifts real_segments
      (fun j : Bool => if j then (1 : ℝ) else -1)
      (fun j => by cases j <;> norm_num) (r := 2) (by norm_num) (by norm_num)
  refine ⟨x, a, ?_, harad, ?_, ?_⟩
  · intro j
    simpa using hxmem j
  · intro j
    cases j
    · have h := hamap false
      norm_num [smul_eq_mul] at h ⊢
      exact h
    · have h := hamap true
      norm_num [smul_eq_mul] at h ⊢
      exact h
  · have h := hpair true false
    norm_num at h ⊢
    exact h

end GCExactRadiusLiftReview

#print axioms GCExactRadiusLiftReview.factor_not_complete
#print axioms GCExactRadiusLiftReview.opposite_lifts_with_incomplete_factor
#lint- only unusedArguments simpNF synTaut

namespace GCExactRadiusSignedReview

open GC.MetricGeometry

private abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)
private def approximation (k : ℕ) : KleinerLottApprox (0 : E k)
    (WithLp.toLp 2 ((0 : E k), (PUnit.unit : PUnit.{1}))) (1 / 100 : ℝ) where
  error_pos := by norm_num
  error_lt_one := by norm_num
  toFun x := WithLp.toLp 2 (x, (PUnit.unit : PUnit.{1}))
  basepoint := rfl
  distortion x _ y _ := by
    rw [(WithLp.isometry_prodMk_right (E := E k) (PUnit.unit : PUnit.{1})).dist_eq]
    norm_num
  coverage q hq := by
    have hf := WithLp.dist_fst_le q (WithLp.toLp 2 ((0 : E k), (PUnit.unit : PUnit.{1})))
    have hball : q.fst ∈ ball (0 : E k) ((1 / 100 : ℝ)⁻¹) := by
      change dist q.fst 0 < _
      change dist q.fst 0 ≤ _ at hf
      linarith
    have hpoint : WithLp.toLp 2 (q.fst, (PUnit.unit : PUnit.{1})) = q := by
      apply (WithLp.equiv 2 (E k × PUnit.{1})).injective
      exact Prod.ext rfl (Subsingleton.elim _ _)
    have hmem : q ∈ (fun x : E k => WithLp.toLp 2 (x, (PUnit.unit : PUnit.{1}))) ''
        ball (0 : E k) ((1 / 100 : ℝ)⁻¹) := ⟨q.fst, hball, hpoint⟩
    exact (infDist_le_dist_of_mem hmem).trans (by norm_num)
private theorem segments (k : ℕ) (x y : E k) :
    ∃ f : Icc (0 : ℝ) 1 → E k,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  refine ⟨fun t => AffineMap.lineMap x y (t : ℝ), by fun_prop, ?_, ?_, ?_⟩
  · exact AffineMap.lineMap_apply_zero x y
  · exact AffineMap.lineMap_apply_one x y
  · intro s t
    rw [dist_lineMap_lineMap]
    exact mul_comm _ _

theorem signed_plane_near_boundary :
    ∃ x a : Fin 2 × Bool → E 2,
      (∀ j, x j ∈ ball (0 : E 2) 100) ∧
      (∀ j, dist (0 : E 2) (a j) = 999 / 10) ∧
      (∀ j, dist ((approximation 2).toFun (a j))
        (WithLp.toLp 2 (PiLp.single 2 j.1 (if j.2 then (999 / 10 : ℝ) else -(999 / 10)), (PUnit.unit : PUnit.{1}))) < 14 / 100) ∧
      |dist (a (0, true)) (a (0, false)) - 999 / 5| < 27 / 100 ∧
      |dist (a (0, true)) (a (1, false)) - (999 / 10) * Real.sqrt 2| < 27 / 100 := by
  obtain ⟨x, a, hxmem, hlift, hlength, harad, htail, hamap, hpair⟩ :=
    (approximation 2).exists_exact_radius_signed_axis_lifts (segments 2)
      (r := 999 / 10) (by norm_num) (by norm_num)
  have hop : ‖(PiLp.single 2 (0 : Fin 2) (1 : ℝ) : E 2) - PiLp.single 2 (0 : Fin 2) (-1 : ℝ)‖ = 2 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [Fin.sum_univ_two, PiLp.sub_apply]
  have hcross : ‖(PiLp.single 2 (0 : Fin 2) (1 : ℝ) : E 2) - PiLp.single 2 (1 : Fin 2) (-1 : ℝ)‖ = Real.sqrt 2 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [Fin.sum_univ_two, PiLp.sub_apply]
  refine ⟨x, a, ?_, harad, ?_, ?_, ?_⟩
  · intro j
    simpa using hxmem j
  · intro j
    simpa only [show (14 : ℝ) * (1 / 100) = 14 / 100 by norm_num] using hamap j
  · have hh := hpair (0, true) (0, false)
    simp only [ite_true, Bool.false_eq_true, ite_false, hop] at hh
    norm_num at hh ⊢
    exact hh
  · have hh := hpair (0, true) (1, false)
    simp only [ite_true, Bool.false_eq_true, ite_false, hcross] at hh
    norm_num at hh ⊢
    exact hh

theorem rank_zero_near_boundary :
    ∃ x a : Fin 0 × Bool → E 0,
      (∀ j, x j ∈ ball (0 : E 0) 100) ∧
      ∀ j, dist (0 : E 0) (a j) = 999 / 10 := by
  obtain ⟨x, a, hxmem, hlift, hlength, harad, htail, hamap, hpair⟩ :=
    (approximation 0).exists_exact_radius_signed_axis_lifts (segments 0)
      (r := 999 / 10) (by norm_num) (by norm_num)
  refine ⟨x, a, ?_, harad⟩
  intro j
  simpa only [show ((1 / 100 : ℝ)⁻¹) = 100 by norm_num] using hxmem j

#print axioms signed_plane_near_boundary
#print axioms rank_zero_near_boundary

end GCExactRadiusSignedReview

#lint- only unusedArguments simpNF synTaut


#print axioms GC.MetricGeometry.KleinerLottApprox.exists_exact_radius_unit_vector_lifts
#print axioms GC.MetricGeometry.KleinerLottApprox.exists_exact_radius_signed_axis_lifts
#lint- only unusedArguments simpNF synTaut
```
