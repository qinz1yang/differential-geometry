import DifferentialGeometry.Geometry.Metric.Approximation.ConeRadialExtension
import DifferentialGeometry.Geometry.Comparison.EqualLegAngleDefect
import DifferentialGeometry.Geometry.Comparison.TriangleExcessAngle
import DifferentialGeometry.Geometry.Comparison.AngleShortening
import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening
import DifferentialGeometry.Geometry.Comparison.EqualRadiusStrainerMargin
import DifferentialGeometry.Topology.MetricSpace.EqualRadiusEndpoints

/-!
# Annular strainers at an exact prescribed scale (LC65, metric kernel)

Blueprint `master207A.tex`, LC65 (`lem:collapse-annular-exact-strainer`, lines 23765–23840).
A pointed Kleiner–Lott `δ`-map from `(X, p)` to a cone carrying `RadialConeData`, on a geodesic
space whose four-point comparison at curvature `-(1/60)²` holds on the ball `B(p, 21)`, gives at
every point `q` of the CLOSED shell `1/10 ≤ d(p, q) ≤ 10` and for every factor `λ ≥ Λσ` a
one-strainer of quality `σ` at the EXACT scale `L = σ⁻¹` of the rescaled distance `λ d`, with
comparison curvature `-σ`. Its inward anchor lies on the chosen minimizing segment from `q` to
`p`; its outward anchor lies on a minimizing segment from `q` to the point `z` built from LC25.

The proof follows the blueprint: LC25 supplies the outward point, the equal-leg defect
(`pi_sub_lt_comparisonAngle_equal`) bounds the angle of `(q; p, z)` at curvature `-(1/60)²`,
the AC64 shortening monotonicity (`comparisonAngleNegCurvature_le_of_shortening_left/right`)
keeps it under shortening to length `L / λ`, and the chord at that length forces the angle at
curvature `-σ` in the rescaled distance. The constants differ from the blueprint's explicit
sufficient values only in the choice of the auxiliary angle `θ`: here `θ` is chosen so that
`4 cosh(2√σ L)(1 - cos(θ/2)) < 1 - cos σ`, which replaces the blueprint's `arsinh` side `c_σ`
by the general excess bound `one_add_cos_comparisonAngle_le_excess`.

The Riemannian statement (curvature of `λ² g₀` on the normalized `L`-ball, and the comparison
ball from sectional curvature) is the binding in `Geometry/Collapse/AnnularExactStrainer.lean`.
-/

set_option autoImplicit false

open Set Metric Real
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

/-- A comparison angle above `π - θ` at any nonpositive model curvature forces the Euclidean
chord of an equal-leg triangle above `2 s cos(θ/2)`. -/
theorem two_mul_cos_half_lt_of_pi_sub_lt_comparisonAngleNegCurvature
    {κ s c θ : ℝ} (hκ : 0 ≤ κ) (hs : 0 < s) (hc : 0 ≤ c) (hcs : c ≤ 2 * s)
    (hθ : 0 ≤ θ) (hθpi : θ ≤ π)
    (h : π - θ < comparisonAngleNegCurvature κ s s c) :
    2 * s * cos (θ / 2) < c := by
  have h1 := comparisonAngleNegCurvature_le_comparisonAngle hκ hs hs
    (by simpa only [sub_self, abs_zero] using hc) (by linarith)
  rw [comparisonAngle_eq_two_arcsin_of_equal_legs hs hc hcs] at h1
  have h2 : (π - θ) / 2 < arcsin (c / (2 * s)) := by linarith
  have hmem : c / (2 * s) ∈ Icc (-1 : ℝ) 1 :=
    ⟨by have : 0 ≤ c / (2 * s) := by positivity
        linarith, (div_le_one₀ (by positivity)).mpr hcs⟩
  have h3 := (lt_arcsin_iff_sin_lt ⟨by linarith [pi_pos], by linarith⟩ hmem).mp h2
  rw [show (π - θ) / 2 = π / 2 - θ / 2 by ring, sin_pi_div_two_sub] at h3
  have h4 := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * s)).mp h3
  linarith

/-- The general excess bound gives a lower bound `π - τ` for a comparison angle at curvature
`-κ²` whenever the excess budget is below `1 - cos τ`. -/
theorem pi_sub_lt_comparisonAngleNegCurvature_of_excess
    {κ a b c τ : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) (hlo : |a - b| ≤ c)
    (hhi : c ≤ a + b) (hτ : 0 ≤ τ)
    (hbudget : cosh (κ * (a + b)) * (a + b - c) * (a + b) / (a * b) < 1 - cos τ) :
    π - τ < comparisonAngleNegCurvature (κ ^ 2) a b c := by
  have hbound := one_add_cos_comparisonAngle_le_excess hκ ha hb hlo hhi
  by_contra h
  have hh := cos_le_cos_of_nonneg_of_le_pi
    (comparisonAngleNegCurvature_mem_Icc (κ ^ 2) a b c).1
    (show π - τ ≤ π by linarith) (le_of_not_gt h)
  rw [cos_pi_sub] at hh
  linarith

/-- The auxiliary angle of LC65: for `0 < σ < 1` there is `0 < θ ≤ 1` with
`4 cosh(√σ (σ⁻¹ + σ⁻¹)) (1 - cos(θ/2)) < 1 - cos σ`. -/
theorem exists_annular_strainer_angle {σ : ℝ} (hσ : 0 < σ) (hσone : σ < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      4 * cosh (sqrt σ * (σ⁻¹ + σ⁻¹)) * (1 - cos (θ / 2)) < 1 - cos σ := by
  have hpos : 0 < 1 - cos σ := by
    have h := cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [two_le_pi]) hσ
    rw [cos_zero] at h
    linarith
  have hcont : Continuous fun θ : ℝ =>
      4 * cosh (sqrt σ * (σ⁻¹ + σ⁻¹)) * (1 - cos (θ / 2)) := by fun_prop
  have hev : ∀ᶠ θ in nhds (0 : ℝ),
      4 * cosh (sqrt σ * (σ⁻¹ + σ⁻¹)) * (1 - cos (θ / 2)) < 1 - cos σ := by
    apply hcont.continuousAt.eventually_lt continuousAt_const
    simpa using hpos
  obtain ⟨θ, hθ, hθ'⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (Ioc_mem_nhdsGT one_pos)).exists
  exact ⟨θ, hθ'.1, hθ'.2, hθ⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v

/-- **LC65 (metric kernel).** For every `0 < σ < 1` there are an auxiliary angle `θ` and
constants `δσ, Λσ > 0`, uniform in the space, the cone, the map and the points, such that the
following holds. Let `X` be a geodesic metric space, `φ` a pointed Kleiner–Lott `δ`-map from
`(X, p)` to a cone with `RadialConeData`, `δ < δσ`, and suppose four-point comparison at
curvature `-(1/60)²` on `B(p, 21)`. For every `q` in the closed shell `1/10 ≤ d(p,q) ≤ 10` and
every `λ ≥ Λσ` there are a point `z` with `d(q,z) = d(p,q)` and `2 d(p,q) - d(p,z) < 15 δ`
(from LC25), whose angle at `q` exceeds `π - θ` at curvature `-(1/60)²`, and anchors `a` on a
minimizing segment from `q` to `p` and `b` on one from `q` to `z`, both at exact distance
`σ⁻¹ / λ` from `q`, whose comparison angle at `q` for the distance `λ d` and curvature `-σ`
exceeds `π - σ`. -/
theorem exists_annular_exact_scale_strainer {σ : ℝ} (hσ : 0 < σ) (hσone : σ < 1) :
    ∃ θ δσ Λσ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 < δσ ∧ 0 < Λσ ∧
      ∀ (X : Type u) (C : Type v) [MetricSpace X] [MetricSpace C],
      (∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
        Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (f s) (f t) = dist x y * dist s t) →
      ∀ (p : X) (o : C), RadialConeData o → ∀ {δ : ℝ}, KleinerLottApprox p o δ →
      δ < δσ → fourPointComparison ((1 / 60) ^ 2) (ball p 21) →
      ∀ q : X, 1 / 10 ≤ dist p q → dist p q ≤ 10 → ∀ lam : ℝ, Λσ ≤ lam →
      ∃ a b z : X,
        dist q z = dist p q ∧ 2 * dist p q - dist p z < 15 * δ ∧
        π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) (dist q p) (dist q z) (dist p z) ∧
        dist q a = σ⁻¹ / lam ∧ dist q b = σ⁻¹ / lam ∧
        dist q a + dist a p = dist q p ∧ dist q b + dist b z = dist q z ∧
        π - σ < comparisonAngleNegCurvature σ (lam * dist q a) (lam * dist q b)
          (lam * dist a b) := by
  obtain ⟨θ, hθ, hθone, hθbudget⟩ := exists_annular_strainer_angle hσ hσone
  have hcosθ : 0 < 1 - cos θ := by
    have h := cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [two_le_pi]) hθ
    rw [cos_zero] at h
    linarith
  set L : ℝ := σ⁻¹ with hL
  have hLpos : 0 < L := inv_pos.mpr hσ
  refine ⟨θ, min (1 / 100) ((1 - cos θ) / 600), 20 * L, hθ, hθone,
    lt_min (by norm_num) (by positivity), by positivity, ?_⟩
  intro X C _ _ hsegments p o H δ φ hδ hcomp q hq1 hq2 lam hlam
  have hseg' : ∀ x y : X, ∃ c : Icc (0 : ℝ) 1 → X,
      c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (c s) (c t) = dist x y * dist s t := by
    intro x y
    obtain ⟨f, _, h0, h1, hd⟩ := hsegments x y
    exact ⟨f, h0, h1, hd⟩
  have hδpos := φ.error_pos
  have hδ1 : δ < 1 / 100 := hδ.trans_le (min_le_left _ _)
  have hδ2 : δ < (1 - cos θ) / 600 := hδ.trans_le (min_le_right _ _)
  set D : ℝ := dist p q with hD
  have hDpos : 0 < D := by linarith
  -- LC25: the outward point at twice the radius.
  obtain ⟨q', hpq', hlow, hhigh⟩ := φ.exists_outward_point_on_annulus H hsegments
    (a := 1 / 10) (b := 10) (by norm_num) (by norm_num) (by linarith) (by linarith) ⟨hq1, hq2⟩
  -- The point `z` at distance `D` from `q` on a segment towards `q'`.
  obtain ⟨z, -, hqz, -, hzq', -, -, -⟩ :=
    exists_equal_radius_endpoints_with_excess_le hseg' q q' q' dist_nonneg hlow hlow
  have hpz_low : 2 * D - 15 * δ < dist p z := by
    have h := dist_triangle p z q'
    linarith
  have hpz_up : dist p z ≤ 2 * D := by
    have h := dist_triangle p q z
    linarith
  have hpz_nonneg : 0 ≤ dist p z := dist_nonneg
  have hqp : dist q p = D := dist_comm q p
  -- The angle at `q` of `(q; p, z)` at curvature `-(1/60)²`.
  have hangle0 : π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) D D (dist p z) := by
    apply pi_sub_lt_comparisonAngle_equal (by norm_num) hDpos hpz_nonneg hpz_up
      (by nlinarith) hθ.le
    rw [div_lt_iff₀ hDpos]
    have : 4 * (2 * D - dist p z) < 60 * δ := by linarith
    nlinarith
  -- Shortening to the exact length `s = L / λ`.
  set s : ℝ := L / lam with hs
  have hlampos : 0 < lam := lt_of_lt_of_le (by positivity) hlam
  have hspos : 0 < s := div_pos hLpos hlampos
  have hs20 : s ≤ 1 / 20 := by
    rw [hs, div_le_iff₀ hlampos]
    linarith
  have hsD : s ≤ D := by linarith
  obtain ⟨a, b, hqa, hqb, hap, hbz, -, -⟩ :=
    exists_equal_radius_endpoints_with_excess_le hseg' q p z hspos.le
      (by rw [hqp]; exact hsD) (by rw [hqz]; exact hsD)
  have hmem (x : X) (hx : dist x p < 21) : x ∈ ball p 21 := hx
  have hpB : p ∈ ball p 21 := mem_ball_self (by norm_num)
  have hqB : q ∈ ball p 21 := hmem q (by rw [hqp]; linarith)
  have hzB : z ∈ ball p 21 := hmem z (by rw [dist_comm]; linarith)
  have haB : a ∈ ball p 21 := hmem a (by rw [hap, hqp]; linarith)
  have hbB : b ∈ ball p 21 := hmem b (by
    have h := dist_triangle b q p
    rw [dist_comm b q, hqb, hqp] at h
    linarith)
  have hzq : z ≠ q := by
    intro h
    rw [h, dist_self] at hqz
    linarith
  have haq : a ≠ q := by
    intro h
    rw [h, dist_self] at hqa
    linarith
  have hκ : (0 : ℝ) ≤ (1 / 60) ^ 2 := by positivity
  have hsh1 := comparisonAngleNegCurvature_le_of_shortening_left hκ hcomp hqB haB hpB hzB
    (by rw [hqa]; exact hspos) hzq (by rw [hqa, hap]; ring)
  have hsh2 := comparisonAngleNegCurvature_le_of_shortening_right hκ hcomp hqB hbB hzB haB
    (by rw [hqb]; exact hspos) haq (by rw [hqb, hbz]; ring)
  have hangle_s : π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) s s (dist a b) := by
    have h0 : π - θ < comparisonAngleNegCurvature ((1 / 60) ^ 2) (dist q p) (dist q z)
        (dist p z) := by rw [hqp, hqz]; exact hangle0
    have h := (h0.trans_le hsh1).trans_le hsh2
    rwa [hqa, hqb] at h
  have hab_up : dist a b ≤ 2 * s := by
    have h := dist_triangle a q b
    rw [dist_comm a q, hqa, hqb] at h
    linarith
  have hchord := two_mul_cos_half_lt_of_pi_sub_lt_comparisonAngleNegCurvature hκ hspos
    dist_nonneg hab_up hθ.le (by linarith [two_le_pi]) hangle_s
  -- The comparison angle in the rescaled distance at curvature `-σ`.
  have hlams : lam * s = L := by
    rw [hs]
    field_simp
  have hc_up : lam * dist a b ≤ L + L := by nlinarith
  have hc_low : 2 * L * cos (θ / 2) < lam * dist a b := by nlinarith
  have hfinal : π - σ < comparisonAngleNegCurvature (sqrt σ ^ 2) L L (lam * dist a b) := by
    apply pi_sub_lt_comparisonAngleNegCurvature_of_excess (sqrt_nonneg σ) hLpos hLpos
      (by rw [sub_self, abs_zero]; positivity) hc_up hσ.le
    have hK : 0 < cosh (sqrt σ * (L + L)) := cosh_pos _
    rw [div_lt_iff₀ (by positivity)]
    have hexcess : L + L - lam * dist a b < 2 * L * (1 - cos (θ / 2)) := by linarith
    have h1 : cosh (sqrt σ * (L + L)) * (L + L - lam * dist a b) * (L + L) <
        cosh (sqrt σ * (L + L)) * (2 * L * (1 - cos (θ / 2))) * (L + L) := by
      apply mul_lt_mul_of_pos_right _ (by positivity)
      exact mul_lt_mul_of_pos_left hexcess hK
    have h2 : cosh (sqrt σ * (L + L)) * (2 * L * (1 - cos (θ / 2))) * (L + L) =
        (4 * cosh (sqrt σ * (σ⁻¹ + σ⁻¹)) * (1 - cos (θ / 2))) * (L * L) := by
      rw [hL]
      ring
    have h3 : (4 * cosh (sqrt σ * (σ⁻¹ + σ⁻¹)) * (1 - cos (θ / 2))) * (L * L) <
        (1 - cos σ) * (L * L) := mul_lt_mul_of_pos_right hθbudget (by positivity)
    linarith
  rw [sq_sqrt hσ.le] at hfinal
  refine ⟨a, b, z, hqz, by linarith, by rw [hqp, hqz]; exact hangle0, hqa, hqb, by rw [hqa, hap]; ring,
    by rw [hqb, hbz]; ring, ?_⟩
  rw [hqa, hqb, hlams]
  exact hfinal

end GC.MetricGeometry
