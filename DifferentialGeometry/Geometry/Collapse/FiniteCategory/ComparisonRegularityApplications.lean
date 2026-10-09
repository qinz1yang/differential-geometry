import DifferentialGeometry.Geometry.Metric.Approximation.BufferedImageContainment
import DifferentialGeometry.Geometry.Metric.Isometry.TransitionSubconvergence
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import DifferentialGeometry.Geometry.Metric.SplittingCoordinate

/-!
# Concrete consumers for the W4-F7b kernels (LFR10 containment, LFR13)

* LFR10: the translations `x ↦ x + i` of `ℝ` (moving basepoint `i`, unbounded) cover
  `B(i, 1)` by the image of `B(0, 2)`, via `eventually_ball_subset_image_of_distortion`, with the
  almost minimizing curves of `ℝ` supplied by its affine segments.
* LFR11 (metric piece): for a rank-one splitting `N ≃ᵢ ℝ × Y` (the case of LFR15–LFR16) the real
  coordinate is the difference of two squared distances divided by `4 s`.
* LFR13: the Euclidean isometries `x ↦ (-1)^i x` of the unit interval, an actual non-constant
  sequence of transition isometries for the constant metric `u v ↦ u v`, have a `C^K`
  convergent subsequence for every `K` (`exists_transition_cK_subseq`).
-/

set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse.FiniteCategory

open DifferentialGeometry.CheegerGromovCompactness

/-- Affine segments of `ℝ`, the length-space input of the LFR10 kernel. -/
theorem real_arbitrarily_short_curves (a b : ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ c : unitInterval → ℝ, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
      eVariationOn c univ < ENNReal.ofReal (dist a b + η) := by
  refine Metric.arbitrarily_short_curves_of_metric_segments (fun x y => ?_) a b η hη
  refine ⟨fun s => x + (s : ℝ) * (y - x), by fun_prop, by simp, by simp, fun s t => ?_⟩
  rw [Real.dist_eq, Real.dist_eq, Subtype.dist_eq, Real.dist_eq,
    show x + (s : ℝ) * (y - x) - (x + (t : ℝ) * (y - x)) = ((s : ℝ) - t) * (y - x) by ring,
    abs_mul, abs_sub_comm y x, mul_comm]

/-- **LFR10 consumer.** Translations with an unbounded moving basepoint. -/
theorem translations_cover_ball :
    ∀ᶠ i : ℕ in atTop, ball (i : ℝ) 1 ⊆ (fun x : ℝ => x + i) '' ball 0 2 := by
  have h := GC.MetricGeometry.eventually_ball_subset_image_of_distortion
    (M := fun _ : ℕ => ℝ) (fun (i : ℕ) (x : ℝ) => x + i) 0 (fun i => (i : ℝ))
    (fun i => by simp) (R := 2)
    (Eventually.of_forall fun i => (continuous_id.add continuous_const).continuousOn)
    (Eventually.of_forall fun i =>
      (Homeomorph.addRight (i : ℝ)).isOpenMap _ isOpen_ball)
    (fun ε hε => Eventually.of_forall fun i x _ y _ => by simpa using hε)
    (fun _ a b η hη => real_arbitrarily_short_curves a b η hη) (r := 1) (by norm_num)
  exact h

/-- **LFR13 consumer.** The reflections `x ↦ (-1)^i x` of the unit interval are isometries of the
constant metric `u v ↦ u v`; for every `K` a subsequence converges in `C^K` on compact subsets. -/
theorem reflections_cK_subseq (K : ℕ) :
    ∃ (φ : ℕ → ℕ) (τinf : ℝ → ℝ), StrictMono φ ∧ ContDiffOn ℝ K τinf (ball 0 1) ∧
      ∀ S : Set ℝ, IsCompact S → S ⊆ ball 0 1 →
        MapCPConvergenceOn S K (fun k => fun x : ℝ => (-1 : ℝ) ^ φ k * x) τinf := by
  have hc : ∀ i : ℕ, ((-1 : ℝ) ^ i) ^ 2 = 1 := fun i => by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hderiv : ∀ (i : ℕ) (x u : ℝ),
      fderiv ℝ (fun y : ℝ => (-1 : ℝ) ^ i * y) x u = u * ((-1 : ℝ) ^ i * 1) := by
    intro i x u
    have h := ((hasDerivAt_id x).const_mul ((-1 : ℝ) ^ i)).hasFDerivAt
    simp only [id] at h
    rw [h.fderiv]
    simp
  exact MetricIsometry.exists_transition_cK_subseq K
    (fun _ _ => ContinuousLinearMap.mul ℝ ℝ) (fun _ _ => ContinuousLinearMap.mul ℝ ℝ)
    (fun i (x : ℝ) => (-1 : ℝ) ^ i * x) isOpen_ball isOpen_ball
    ⟨1, fun y hy => (mem_ball_zero_iff.1 hy).le⟩
    (fun _ => contDiffOn_const) (fun _ => contDiffOn_const)
    (fun _ => (contDiff_const.mul contDiff_id).contDiffOn)
    (fun i x hx => by
      rw [mem_ball_zero_iff] at hx ⊢
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact hx)
    (fun i x _ u v => by
      rw [hderiv, hderiv]
      simp only [ContinuousLinearMap.mul_apply']
      linear_combination (-(u * v)) * hc i)
    (fun _ _ _ a b => by simp only [ContinuousLinearMap.mul_apply']; ring)
    (fun _ _ _ v => by
      simp only [ContinuousLinearMap.mul_apply', Real.norm_eq_abs, sq_abs]
      constructor <;> nlinarith [sq_nonneg v])
    (fun _ _ _ v => by
      simp only [ContinuousLinearMap.mul_apply', Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg v])
    (A := 0)
    (fun _ q hq _ _ _ => by rw [iteratedFDeriv_const_of_ne (by omega)]; simp)
    (fun _ q hq _ _ _ => by rw [iteratedFDeriv_const_of_ne (by omega)]; simp)

/-- **LFR11 consumer.** The real coordinate of a rank-one exact splitting, recovered from two
squared distances. -/
theorem real_splitting_coordinate {N Y : Type*} [MetricSpace N] [MetricSpace Y]
    (I : N ≃ᵢ WithLp 2 (ℝ × Y)) (x : N) (u₀ : ℝ) (y₀ : Y) {s : ℝ} (hs : s ≠ 0) :
    (I x).fst - u₀ =
      (dist x (I.symm (WithLp.toLp 2 (u₀ - s, y₀))) ^ 2 -
        dist x (I.symm (WithLp.toLp 2 (u₀ + s, y₀))) ^ 2) / (4 * s) := by
  have h := GC.MetricGeometry.inner_fst_sub_eq_sq_dist_sub I x u₀ y₀ 1 hs
  simpa using h

end DifferentialGeometry.Geometry.Collapse.FiniteCategory
