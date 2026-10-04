import DifferentialGeometry.Geometry.Metric.Approximation.RayConeAtInfinity
import DifferentialGeometry.Topology.MetricSpace.GeodesicMidpoint
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# The cone at infinity is geodesic, nonnegatively curved, and of no larger dimension

Tier T4 of the Tits-cone producer of chapter 13 (design
`docs/geometrization/chapter13/design-tits-cone-20261004.md` §3 "Tier 2", §4 table; required by the
external review `build-logs/inbox/review-tits-cone.md` §9). It completes the LC21 package
(`docs/geometrization/blueprint/master207A.tex:20789`) with the additional properties LFR59 lists
(A:29862–29885): the ray cone `RayCone hcomp q` of tier T3 is

* nonnegatively curved in the four-point sense (`fourPointComparison_rayCone`), from the general
  kernel `fourPointComparison_zero_of_tendsto_mul_dist`: four-point comparison `0` passes to a metric
  space whose distances are limits of scaled distances of `Y` (the comparison angle is scale
  invariant and continuous where its first two sides are positive; the pattern of
  `fourPointComparison.closure_zero`);
* geodesic (`rayCone_segments`), from approximate midpoints (`RayCone.exists_approx_midpoint`: the
  metric midpoint of two far points of `Y`, moved onto a ray by tier T2's density `exists_ray_near`,
  or replaced by the apex when it stays near `q`), properness (`properSpace_rayCone`) and the existing
  `Metric.exists_metric_segment_of_approximate_midpoints`;
* of Hausdorff dimension at most that of `Y` (`dimH_univ_rayCone_le`): the radial projection
  `rayConeProj hcomp 1` maps the ray union ONTO the cone (`rayConeProj_one_surjective`) and is
  `1`-Lipschitz (T1's chord monotonicity), so Mathlib's `LipschitzWith.dimH_range_le` applies to
  the whole cone, with no density or closure step.

`exists_cone_at_infinity_package_of_fourPointComparison_zero` is the full LC21 package: the
conclusion of (F) together with `CompleteSpace C`, segments in `C`, `fourPointComparison 0` on `C`
and `dimH C ≤ dimH Y`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped NNReal Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u

/-! ## Four-point comparison passes to limits of scaled distances -/

/-- If every distance of `C` is the limit of the scaled distances `lam i * d(P i z, P i w)` of
lifts in a space `X` with nonnegative four-point comparison, then `C` has nonnegative four-point
comparison. -/
theorem fourPointComparison_zero_of_tendsto_mul_dist {ι Z X C : Type*} [MetricSpace X]
    [MetricSpace C] {l : Filter ι} [l.NeBot] (hX : fourPointComparison 0 (univ : Set X))
    {π : Z → C} (hπ : Function.Surjective π) (P : ι → Z → X) {lam : ι → ℝ}
    (hlam : ∀ i, 0 < lam i)
    (hlim : ∀ z w, Tendsto (fun i => lam i * dist (P i z) (P i w)) l (𝓝 (dist (π z) (π w)))) :
    fourPointComparison 0 (univ : Set C) := by
  intro x _ a _ b _ c _ hax hbx hcx
  obtain ⟨zx, rfl⟩ := hπ x
  obtain ⟨za, rfl⟩ := hπ a
  obtain ⟨zb, rfl⟩ := hπ b
  obtain ⟨zc, rfl⟩ := hπ c
  have hxa := dist_pos.mpr hax.symm
  have hxb := dist_pos.mpr hbx.symm
  have hxc := dist_pos.mpr hcx.symm
  have hev : ∀ᶠ i in l,
      comparisonAngle (lam i * dist (P i zx) (P i za)) (lam i * dist (P i zx) (P i zb))
          (lam i * dist (P i za) (P i zb)) +
        comparisonAngle (lam i * dist (P i zx) (P i zb)) (lam i * dist (P i zx) (P i zc))
          (lam i * dist (P i zb) (P i zc)) +
        comparisonAngle (lam i * dist (P i zx) (P i zc)) (lam i * dist (P i zx) (P i za))
          (lam i * dist (P i zc) (P i za)) ≤ 2 * Real.pi := by
    filter_upwards [(hlim zx za).eventually (Ioi_mem_nhds hxa),
      (hlim zx zb).eventually (Ioi_mem_nhds hxb),
      (hlim zx zc).eventually (Ioi_mem_nhds hxc)] with i h1 h2 h3
    have hne (w : Z) (hw : 0 < lam i * dist (P i zx) (P i w)) : P i w ≠ P i zx := by
      intro h
      rw [h, dist_self, mul_zero] at hw
      exact lt_irrefl 0 hw
    have h := hX (P i zx) (mem_univ _) (P i za) (mem_univ _) (P i zb) (mem_univ _) (P i zc)
      (mem_univ _) (hne za h1) (hne zb h2) (hne zc h3)
    simp only [comparisonAngleNegCurvature_zero] at h
    rw [comparisonAngle_scale _ _ _ (hlam i), comparisonAngle_scale _ _ _ (hlam i),
      comparisonAngle_scale _ _ _ (hlam i)]
    exact h
  have hang (v w : Z) (hv : 0 < dist (π zx) (π v)) (hw : 0 < dist (π zx) (π w)) :
      Tendsto (fun i => comparisonAngle (lam i * dist (P i zx) (P i v))
          (lam i * dist (P i zx) (P i w)) (lam i * dist (P i v) (P i w))) l
        (𝓝 (comparisonAngle (dist (π zx) (π v)) (dist (π zx) (π w)) (dist (π v) (π w)))) := by
    have h := tendsto_comparisonAngleNegCurvature_zero (κ := fun _ => (0 : ℝ)) tendsto_const_nhds
      (hlim zx v) (hlim zx w) (hlim v w) (Eventually.of_forall fun _ => le_refl 0) hv hw
    simpa only [comparisonAngleNegCurvature_zero] using h
  have hsum := ((hang za zb hxa hxb).add (hang zb zc hxb hxc)).add (hang zc za hxc hxa)
  simp only [comparisonAngleNegCurvature_zero]
  exact le_of_tendsto hsum hev

variable {Y : Type u} [mY : MetricSpace Y]

/-- (b) The ray cone has nonnegative four-point comparison: its distances are the limits of the
distances of `(n + 1)⁻¹ Y` (T1's I3). -/
theorem fourPointComparison_rayCone (hcomp : fourPointComparison 0 (univ : Set Y)) (q : Y) :
    fourPointComparison 0 (univ : Set (RayCone hcomp q)) :=
  fourPointComparison_zero_of_tendsto_mul_dist (l := atTop) hcomp (RayCone.surjective_mk hcomp q)
    (fun (n : ℕ) (z : RayConeCarrier q) => z.ray (z.radius * ((n : ℝ≥0) + 1)))
    (lam := fun n : ℕ => ((n : ℝ) + 1)⁻¹) (fun n => by positivity)
    (fun z w => (tendsto_rayConeApprox_dist hcomp q z w).congr fun n => by
      rw [rayConeApprox_dist, div_eq_inv_mul])

/-! ## Hausdorff dimension -/

/-- The radial projection at scale `1` maps the ray union ONTO the cone. -/
theorem rayConeProj_one_surjective (hcomp : fourPointComparison 0 (univ : Set Y)) (q : Y) :
    Function.Surjective (rayConeProj hcomp 1 (q := q)) := by
  intro z
  obtain ⟨⟨σ, hσ, b⟩, rfl⟩ := RayCone.surjective_mk hcomp q z
  exact ⟨⟨σ b, mem_rayUnion hσ b⟩, by rw [rayConeProj_mk_of_ray, one_mul]⟩

/-- The radial projection at scale `c` is `c`-Lipschitz. -/
theorem lipschitzWith_rayConeProj (hcomp : fourPointComparison 0 (univ : Set Y)) (q : Y)
    (c : ℝ≥0) : LipschitzWith c (rayConeProj hcomp c (q := q)) :=
  LipschitzWith.of_dist_le_mul fun x y => dist_rayConeProj_le hcomp c x y

/-- (c) The cone has Hausdorff dimension at most that of the ray union. -/
theorem dimH_univ_rayCone_le_rayUnion (hcomp : fourPointComparison 0 (univ : Set Y)) (q : Y) :
    dimH (univ : Set (RayCone hcomp q)) ≤ dimH (rayUnion q) := by
  rw [← (rayConeProj_one_surjective hcomp q).range_eq]
  calc dimH (range (rayConeProj hcomp 1 (q := q))) ≤ dimH (univ : Set (rayUnion q)) :=
        (lipschitzWith_rayConeProj hcomp q 1).dimH_range_le
    _ = dimH (rayUnion q) := by
        rw [← isometry_subtype_coe.dimH_image, image_univ, Subtype.range_coe]

/-- (c) The cone has Hausdorff dimension at most that of `Y`. -/
theorem dimH_univ_rayCone_le (hcomp : fourPointComparison 0 (univ : Set Y)) (q : Y) :
    dimH (univ : Set (RayCone hcomp q)) ≤ dimH (univ : Set Y) :=
  (dimH_univ_rayCone_le_rayUnion hcomp q).trans (dimH_mono (subset_univ _))

/-! ## Geodesicity -/

/-- (a) Approximate midpoints in the ray cone: the metric midpoint of `γ(a t)` and `σ(b t)` in `Y`
for a large `t`, moved onto a nearby ray (T2's I5) at the same radius, or replaced by the apex if it
stays near `q`. -/
theorem RayCone.exists_approx_midpoint (hcomp : fourPointComparison 0 (univ : Set Y))
    [ProperSpace Y]
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (q : Y) (x y : RayCone hcomp q) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : RayCone hcomp q, dist x z ≤ dist x y / 2 + ε ∧ dist y z ≤ dist x y / 2 + ε := by
  obtain ⟨⟨γ, hγ, a⟩, rfl⟩ := RayCone.surjective_mk hcomp q x
  obtain ⟨⟨σ, hσ, b⟩, rfl⟩ := RayCone.surjective_mk hcomp q y
  set D : ℝ := dist (RayCone.mk hcomp ⟨γ, hγ, a⟩) (RayCone.mk hcomp ⟨σ, hσ, b⟩) with hD
  have hD0 : 0 ≤ D := dist_nonneg
  have ha0 : (0 : ℝ) ≤ a := a.2
  have hb0 : (0 : ℝ) ≤ b := b.2
  set K : ℝ := a + b + D + ε with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  set η : ℝ := ε / (2 * K) with hη
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηK : η * K = ε / 2 := by rw [hη]; field_simp
  obtain ⟨r₀, hr₀⟩ := exists_ray_near hcomp hsegments q hηpos
  set r : ℝ := max r₀ 0 with hr
  have hr0 : 0 ≤ r := le_max_right _ _
  have hr₀r : r₀ ≤ r := le_max_left _ _
  have hlim : Tendsto (fun t : ℝ≥0 => dist (γ (a * t)) (σ (b * t)) / (t : ℝ)) atTop (𝓝 D) :=
    tendsto_dist_mul_div_of_ray hcomp hγ hσ a b
  obtain ⟨t, hLt, htr, htpos⟩ : ∃ t : ℝ≥0, dist (γ (a * t)) (σ (b * t)) / (t : ℝ) < D + ε ∧
      (⟨2 * r / ε, div_nonneg (mul_nonneg zero_le_two hr0) hε.le⟩ : ℝ≥0) ≤ t ∧ 0 < t :=
    ((hlim.eventually (gt_mem_nhds (by linarith : D < D + ε))).and
      ((eventually_ge_atTop _).and (eventually_gt_atTop 0))).exists
  have htR : (0 : ℝ) < t := htpos
  have hL : dist (γ (a * t)) (σ (b * t)) < D * t + ε * t := by
    rw [div_lt_iff₀ htR] at hLt
    linarith
  have htr' : 2 * r ≤ ε * t := by
    have h : 2 * r / ε ≤ t := htr
    rw [div_le_iff₀ hε] at h
    linarith
  obtain ⟨f, -, hf0, hf1, hfd⟩ := hsegments (γ (a * t)) (σ (b * t))
  set L : ℝ := dist (γ (a * t)) (σ (b * t)) with hLdef
  set m : Y := f ⟨1 / 2, by norm_num⟩ with hm
  have hum : dist (γ (a * t)) m = L / 2 := by
    have h := hfd ⟨0, by norm_num⟩ ⟨1 / 2, by norm_num⟩
    rw [hf0, Subtype.dist_eq, Real.dist_eq] at h
    rw [h]
    norm_num
    ring
  have hmv : dist m (σ (b * t)) = L / 2 := by
    have h := hfd ⟨1 / 2, by norm_num⟩ ⟨1, by norm_num⟩
    rw [hf1, Subtype.dist_eq, Real.dist_eq] at h
    rw [h]
    norm_num
    ring
  have hqu : dist q (γ (a * t)) = a * t := by rw [dist_of_ray hγ, NNReal.coe_mul]
  have hqv : dist q (σ (b * t)) = b * t := by rw [dist_of_ray hσ, NNReal.coe_mul]
  set s : ℝ := dist q m with hs
  have hsu : s ≤ a * t + L / 2 := by
    have h := dist_triangle q (γ (a * t)) m
    linarith
  have hsv : s ≤ b * t + L / 2 := by
    have h := dist_triangle q (σ (b * t)) m
    rw [dist_comm (σ (b * t)) m] at h
    linarith
  have hus : a * t ≤ s + L / 2 := by
    have h := dist_triangle q m (γ (a * t))
    rw [dist_comm m (γ (a * t))] at h
    linarith
  have hvs : b * t ≤ s + L / 2 := by
    have h := dist_triangle q m (σ (b * t))
    linarith
  have hat0 : 0 ≤ (a : ℝ) * t := mul_nonneg ha0 htR.le
  have hbt0 : 0 ≤ (b : ℝ) * t := mul_nonneg hb0 htR.le
  have hDt0 : 0 ≤ D * t := mul_nonneg hD0 htR.le
  have hεt0 : 0 ≤ ε * t := mul_nonneg hε.le htR.le
  have htK : t * K = a * t + b * t + D * t + ε * t := by rw [hK]; ring
  have hηtK : η * (t * K) = ε / 2 * t := by rw [← hηK]; ring
  by_cases hfar : r₀ ≤ s
  · obtain ⟨τ, hτ, hclose⟩ := hr₀ m hfar
    set s' : ℝ≥0 := ⟨s, dist_nonneg⟩ with hs'
    have hsK : s ≤ t * K := by linarith
    have hηs : η * s ≤ η * (t * K) := mul_le_mul_of_nonneg_left hsK hηpos.le
    have h3 : dist m (τ s') ≤ η * s := hclose
    refine ⟨RayCone.mk hcomp ⟨τ, hτ, t⁻¹ * s'⟩, ?_, ?_⟩
    · have hca : t⁻¹ * (a * t) = a := by
        rw [mul_comm a t, ← mul_assoc, inv_mul_cancel₀ htpos.ne', one_mul]
      have h := rayConeDist_mk_mul_le hcomp hγ hτ t⁻¹ (a * t) s'
      rw [hca] at h
      change rayConeDist q _ _ ≤ D / 2 + ε
      calc _ ≤ ((t⁻¹ : ℝ≥0) : ℝ) * dist (γ (a * t)) (τ s') := h
        _ ≤ (t : ℝ)⁻¹ * ((D / 2 + ε) * t) := by
          rw [NNReal.coe_inv]
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr htR.le)
          have h2 := dist_triangle (γ (a * t)) m (τ s')
          linarith
        _ = D / 2 + ε := by field_simp
    · have hcb : t⁻¹ * (b * t) = b := by
        rw [mul_comm b t, ← mul_assoc, inv_mul_cancel₀ htpos.ne', one_mul]
      have h := rayConeDist_mk_mul_le hcomp hσ hτ t⁻¹ (b * t) s'
      rw [hcb] at h
      change rayConeDist q _ _ ≤ D / 2 + ε
      calc _ ≤ ((t⁻¹ : ℝ≥0) : ℝ) * dist (σ (b * t)) (τ s') := h
        _ ≤ (t : ℝ)⁻¹ * ((D / 2 + ε) * t) := by
          rw [NNReal.coe_inv]
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr htR.le)
          have h2 := dist_triangle (σ (b * t)) m (τ s')
          rw [dist_comm (σ (b * t)) m] at h2
          linarith
        _ = D / 2 + ε := by field_simp
  · push Not at hfar
    refine ⟨RayCone.mk hcomp ⟨γ, hγ, 0⟩, ?_, ?_⟩
    · change rayConeDist q _ _ ≤ D / 2 + ε
      rw [rayConeDist_zero_right q _ _ rfl]
      have h : (a : ℝ) * t < (D / 2 + ε) * t := by linarith
      exact (lt_of_mul_lt_mul_right h htR.le).le
    · change rayConeDist q _ _ ≤ D / 2 + ε
      rw [rayConeDist_zero_right q _ _ rfl]
      have h : (b : ℝ) * t < (D / 2 + ε) * t := by linarith
      exact (lt_of_mul_lt_mul_right h htR.le).le

/-- (a) The ray cone is geodesic: constant-speed segments between any two points, in the form
(F) takes as its segment hypothesis. -/
theorem rayCone_segments (hcomp : fourPointComparison 0 (univ : Set Y)) [ProperSpace Y]
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (q : Y) :
    ∀ a b : RayCone hcomp q, ∃ f : Icc (0 : ℝ) 1 → RayCone hcomp q, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  have := properSpace_rayCone hcomp q
  exact Metric.exists_metric_segment_of_approximate_midpoints
    fun x y ε hε => RayCone.exists_approx_midpoint hcomp hsegments q x y hε

/-! ## The full LC21 package -/

/-- The LC21 cone-at-infinity package with the properties LFR59 lists: a proper space `Y` with
segments and nonnegative four-point comparison has a cone at infinity `(C, o)`, fixed before `ε`,
with AC82 radial data, proper and complete, geodesic, with nonnegative four-point comparison and
`dimH C ≤ dimH Y`, and Kleiner–Lott `ε`-maps from every blow-down `(R⁻¹ Y, q)`, `R ≥ R₀(ε)`.
Bounded `Y` has the one-point cone; otherwise `C` is the ray cone (the cone of (F)). -/
theorem exists_cone_at_infinity_package_of_fourPointComparison_zero
    {Y : Type u} [mY : MetricSpace Y] [ProperSpace Y]
    (hcomp : fourPointComparison 0 (univ : Set Y))
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (q : Y) :
    ∃ (C : Type u) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
      ProperSpace C ∧ CompleteSpace C ∧
      (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
        f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
      fourPointComparison 0 (univ : Set C) ∧ dimH (univ : Set C) ≤ dimH (univ : Set Y) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox Y C (mY.rescale R⁻¹ (inv_pos.mpr hR)) mC q o ε) := by
  by_cases hb : Bornology.IsBounded (univ : Set Y)
  · refine ⟨PUnit, inferInstance, PUnit.unit, ⟨RadialConeData.punit⟩, inferInstance,
      inferInstance, fun a b => ⟨fun _ => a, continuous_const, rfl, Subsingleton.elim _ _,
        fun s t => by rw [Subsingleton.elim a b, dist_self, zero_mul]⟩,
      fun x _ a _ _ _ _ _ hax _ _ => (hax (Subsingleton.elim a x)).elim, ?_,
      fun ε hε hε1 => exists_kleinerLottApprox_rescale_point_of_isBounded q hb hε hε1⟩
    rw [dimH_subsingleton subsingleton_univ]
    exact zero_le
  · obtain ⟨r₀, hr₀⟩ := exists_ray_near hcomp hsegments q (η := 1) one_pos
    obtain ⟨x, hx⟩ : ∃ x : Y, r₀ ≤ dist q x := by
      by_contra h
      push Not at h
      exact hb ((isBounded_closedBall (x := q) (r := r₀)).subset fun x _ => by
        rw [mem_closedBall, dist_comm]
        exact (h x).le)
    obtain ⟨γ₀, hγ₀, -⟩ := hr₀ x hx
    have := properSpace_rayCone hcomp q
    exact ⟨RayCone hcomp q, inferInstance, rayConeApex hcomp hγ₀, ⟨rayConeRadialData hcomp hγ₀⟩,
      inferInstance, inferInstance, rayCone_segments hcomp hsegments q,
      fourPointComparison_rayCone hcomp q, dimH_univ_rayCone_le hcomp q,
      fun ε hε hε1 => exists_kleinerLottApprox_rayCone hcomp hsegments hγ₀ hε hε1⟩

end GC.MetricGeometry
