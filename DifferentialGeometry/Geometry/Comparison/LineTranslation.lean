import DifferentialGeometry.Geometry.Comparison.ParallelLines

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [ProperSpace X]
variable (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X} (hγ : Isometry γ)
variable (hsegments : ∀ a b : X, ∃ f : Icc (0 : ℝ) 1 → X,
  Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
  ∀ s t, dist (f s) (f t) = dist a b * dist s t)

noncomputable def lineTranslation (t : ℝ) (x : X) : X :=
  (Classical.choose (exists_calibrated_line hs hγ hsegments x)) t

theorem isometry_lineTranslation_time (x : X) :
    Isometry (fun t => lineTranslation hs hγ hsegments t x) :=
  (Classical.choose_spec (exists_calibrated_line hs hγ hsegments x)).1

theorem lineTranslation_zero (x : X) : lineTranslation hs hγ hsegments 0 x = x :=
  (Classical.choose_spec (exists_calibrated_line hs hγ hsegments x)).2.1

theorem lineCoordinate_lineTranslation (t : ℝ) (x : X) :
    lineCoordinate γ (lineTranslation hs hγ hsegments t x) = lineCoordinate γ x + t :=
  (Classical.choose_spec (exists_calibrated_line hs hγ hsegments x)).2.2 t

theorem sq_dist_lineTranslation (s t : ℝ) (x y : X) :
    dist (lineTranslation hs hγ hsegments s x) (lineTranslation hs hγ hsegments t y) ^ 2 =
      (lineCoordinate γ x + s - lineCoordinate γ y - t) ^ 2 +
      dist x y ^ 2 - (lineCoordinate γ x - lineCoordinate γ y) ^ 2 := by
  have h := sq_dist_calibrated_lines hs hγ
    (isometry_lineTranslation_time hs hγ hsegments x)
    (isometry_lineTranslation_time hs hγ hsegments y)
    (fun r => by rw [lineTranslation_zero]; exact lineCoordinate_lineTranslation hs hγ hsegments r x)
    (fun r => by rw [lineTranslation_zero]; exact lineCoordinate_lineTranslation hs hγ hsegments r y) s t
  simpa only [lineTranslation_zero] using h

theorem lineTranslation_add (s t : ℝ) (x : X) :
    lineTranslation hs hγ hsegments s (lineTranslation hs hγ hsegments t x) =
      lineTranslation hs hγ hsegments (s + t) x := by
  apply dist_eq_zero.mp
  have h := sq_dist_lineTranslation hs hγ hsegments s (s + t)
    (lineTranslation hs hγ hsegments t x) x
  have hrad : dist (lineTranslation hs hγ hsegments t x) x = |t| := by
    have hd := (isometry_lineTranslation_time hs hγ hsegments x).dist_eq t 0
    simpa only [lineTranslation_zero, Real.dist_eq, sub_zero] using hd
  rw [lineCoordinate_lineTranslation, hrad, sq_abs] at h
  nlinarith [dist_nonneg (x := lineTranslation hs hγ hsegments s
    (lineTranslation hs hγ hsegments t x)) (y := lineTranslation hs hγ hsegments (s + t) x)]

theorem isometry_lineTranslation (t : ℝ) : Isometry (lineTranslation hs hγ hsegments t) := by
  apply Isometry.of_dist_eq
  intro x y
  have h := sq_dist_lineTranslation hs hγ hsegments t t x y
  nlinarith [dist_nonneg (x := x) (y := y),
    dist_nonneg (x := lineTranslation hs hγ hsegments t x) (y := lineTranslation hs hγ hsegments t y)]

theorem lineTranslation_apply_line (t s : ℝ) :
    lineTranslation hs hγ hsegments t (γ s) = γ (s + t) := by
  have hline : Isometry (fun t : ℝ => γ (s + t)) := by
    apply Isometry.of_dist_eq
    intro a b
    rw [hγ.dist_eq, dist_add_left]
  have heq := calibrated_line_unique hs hγ
    (isometry_lineTranslation_time hs hγ hsegments (γ s)) hline
    (fun t => by rw [lineTranslation_zero]; exact lineCoordinate_lineTranslation hs hγ hsegments t _)
    (fun t => by simp only [lineCoordinate_apply_isometry hγ, add_zero])
    (by simp only [lineTranslation_zero, add_zero])
  exact congrFun heq t

end DifferentialGeometry.Geometry.Comparison.Toponogov
