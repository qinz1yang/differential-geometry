import DifferentialGeometry.Geometry.Comparison.IntrinsicEightHingeComparison
import DifferentialGeometry.Geometry.Comparison.IntrinsicGeodesicDirections
import DifferentialGeometry.Geometry.Comparison.GeodesicDirectionCurvature
import DifferentialGeometry.Geometry.Comparison.HingeOfGerms
import DifferentialGeometry.Geometry.Comparison.EqualSideHalfAngle
import DifferentialGeometry.Analysis.Convex.HyperbolicSine
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem side_le_sinh_mul_comparisonAngle_one {r c : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (hc2r : c ≤ 2 * r) :
    c ≤ Real.sinh r * comparisonAngleNegCurvature 1 r r c := by
  let θ := comparisonAngleNegCurvature 1 r r c
  have hθ : 0 ≤ θ := (comparisonAngleNegCurvature_mem_Icc 1 r r c).1
  have hs : 0 ≤ Real.sinh r := Real.sinh_nonneg_iff.mpr hr.le
  have hh : 0 ≤ Real.sinh (c / 2) := Real.sinh_nonneg_iff.mpr (by positivity)
  have hid := sinh_half_sq_eq_of_equal_comparison_sides (by norm_num : (0 : ℝ) < 1)
    hr hc hc2r
  simp only [Real.sqrt_one, one_mul] at hid
  have hcos := Real.one_sub_sq_div_two_le_cos (x := θ)
  have hmul := mul_le_mul_of_nonneg_left hcos (sq_nonneg (Real.sinh r))
  have hcsmall := Real.self_le_sinh_iff.mpr (show 0 ≤ c / 2 by positivity)
  have hcsq := (sq_le_sq₀ (by positivity : 0 ≤ c / 2) hh).mpr hcsmall
  apply (sq_le_sq₀ hc (mul_nonneg hs hθ)).mp
  change c ^ 2 ≤ (Real.sinh r * θ) ^ 2
  change Real.sinh (c / 2) ^ 2 = Real.sinh r ^ 2 * (1 - Real.cos θ) / 2 at hid
  nlinarith

theorem dist_same_radius_le_mul_dist_direction_of_intrinsic_8_buffer
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {q : X} {R : ℝ} (hR : 0 < R)
    (hq : dist q p < R / 2) [LocallyCompactSpace (ball p (8 * R))]
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)
    (σ τ : GeodesicRepresentative q) {r : ℝ} (hr : 0 < r)
    (hσ : r ≤ σ.length) (hτ : r ≤ τ.length) (hrR : r ≤ R / 2) (hr1 : r ≤ 1) :
    letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
      (by change dist q p < 8 * R; linarith)
    dist (σ.path r) (τ.path r) ≤ Real.sinh 1 * r * dist σ.direction τ.direction := by
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
    (by change dist q p < 8 * R; linarith)
  have hdσ : dist q (σ.path r) = r := σ.dist_base_path ⟨hr.le, hσ⟩
  have hdτ : dist q (τ.path r) = r := τ.dist_base_path ⟨hr.le, hτ⟩
  have hmσ : σ.path r ∈ closedBall p R := by
    have hd := dist_triangle (σ.path r) q p
    rw [dist_comm (σ.path r) q, hdσ] at hd
    change dist (σ.path r) p ≤ R
    linarith
  have hmτ : τ.path r ∈ closedBall p R := by
    have hd := dist_triangle (τ.path r) q p
    rw [dist_comm (τ.path r) q, hdτ] at hd
    change dist (τ.path r) p ≤ R
    linarith
  obtain ⟨H, hc, hang⟩ := Metric.MinimizingHinge.exists_hinge_of_germs (κ := 1) hr hr
    (x := q) (γ := σ.path) (β := τ.path) rfl rfl
    (fun _ hs => σ.dist_base_path ⟨hs.1.le, hs.2.trans hσ⟩)
    (fun _ hs => τ.dist_base_path ⟨hs.1.le, hs.2.trans hτ⟩)
    (fun _ hs _ ht => σ.dist_path ⟨hs.1.le, hs.2.trans hσ⟩ ⟨ht.1.le, ht.2.trans hσ⟩)
    (fun _ hs _ ht => τ.dist_path ⟨hs.1.le, hs.2.trans hτ⟩ ⟨ht.1.le, ht.2.trans hτ⟩)
  have hangle := H.comparisonAngle_le_of_intrinsic_8_buffer hcurves p
    (by norm_num : (0 : ℝ) < 1) hR hlocal (by rw [hc]; exact hq) hmσ hmτ
    (by rw [hc, hdσ]; exact hr) (by rw [hc, hdτ]; exact hr)
  rw [hc, hdσ, hdτ, hang, germComparisonAngle_eq_of_tendsto
    (σ.tendsto_comparisonAngleNegCurvature_dist_direction τ (by norm_num : (0 : ℝ) ≤ 1))] at hangle
  have hc2r : dist (σ.path r) (τ.path r) ≤ 2 * r := by
    have hd := dist_triangle (σ.path r) q (τ.path r)
    rw [dist_comm (σ.path r) q, hdσ, hdτ] at hd
    linarith
  have hsinh : Real.sinh r ≤ r * Real.sinh 1 := by
    simpa only [mul_one] using Real.sinh_mul_le_mul_sinh ⟨hr.le, hr1⟩ (by norm_num : (0 : ℝ) ≤ 1)
  calc
    dist (σ.path r) (τ.path r) ≤
        Real.sinh r * comparisonAngleNegCurvature 1 r r (dist (σ.path r) (τ.path r)) :=
      side_le_sinh_mul_comparisonAngle_one hr dist_nonneg hc2r
    _ ≤ Real.sinh r * dist σ.direction τ.direction :=
      mul_le_mul_of_nonneg_left hangle (Real.sinh_nonneg_iff.mpr hr.le)
    _ ≤ (r * Real.sinh 1) * dist σ.direction τ.direction :=
      mul_le_mul_of_nonneg_right hsinh dist_nonneg
    _ = Real.sinh 1 * r * dist σ.direction τ.direction := by ring

end DifferentialGeometry.Geometry.Comparison.Toponogov
