import DifferentialGeometry.Geometry.Metric.RayCone
import DifferentialGeometry.Geometry.Metric.Approximation.CompactParameterMaps
import DifferentialGeometry.Geometry.Metric.Approximation.ConeAtInfinity

/-!
# The cone at infinity of a space with nonnegative four-point comparison

Tier T3 ("RayCone") of the Tits-cone producer of chapter 13, part (ii): the Kleiner–Lott maps to
the ray cone at every large scale and the frozen producer statement (F) of the design
`docs/geometrization/chapter13/design-tits-cone-20261004.md` (§1.1, §2 "KL maps"), the metric form
of the blueprint's LFR58 (`docs/geometrization/blueprint/master207A.tex:29719–29926`) and the
producer of the LC21 cone-at-infinity package that LC24 consumes (A:20776–20951).

* `exists_kleinerLottApprox_rayCone`: for a proper space `Y` with segments and
  `fourPointComparison 0 univ`, and every ray `γ₀` from `q`, the ray cone `(RayCone hcomp q, apex)`
  receives, for every `0 < δ < 1`, an actual pointed Kleiner–Lott `δ`-map from `(R⁻¹ Y, q)` for
  EVERY real `R ≥ R₀(δ)`. It is the existing `exists_kleinerLott_approx_of_compact_parameters`
  applied to the compact parameters `Z_R = rayUnion q ∩ B̄(q, R/δ)` with the radial projection
  `rayConeProj hcomp R⁻¹`; the distortion comes from tier T2's error budget
  `exists_uniform_dist_le_of_ray` and the coverage from T2's density of rays `exists_ray_near`.
* `exists_cone_at_infinity_of_fourPointComparison_zero` (F): one cone `(C, o)`, fixed before `ε`,
  with AC82 radial data, proper, and Kleiner–Lott `ε`-maps `(R⁻¹ Y, q) → (C, o)` for all large
  real `R`. Bounded `Y` has the one-point cone (`exists_kleinerLottApprox_rescale_point_of_isBounded`);
  otherwise a ray exists (T2's density at any far point) and `C` is the ray cone.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped NNReal Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u

variable {Y : Type u} [mY : MetricSpace Y]

/-- LFR58 (metric): Kleiner–Lott maps from every large blow-down to the ray cone. -/
theorem exists_kleinerLottApprox_rayCone (hcomp : fourPointComparison 0 (univ : Set Y))
    [ProperSpace Y]
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    {q : Y} {γ₀ : ℝ≥0 → Y} (hγ₀ : Isometry γ₀ ∧ γ₀ 0 = q) {δ : ℝ} (hδ : 0 < δ)
    (hδone : δ < 1) :
    ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox Y (RayCone hcomp q) (mY.rescale R⁻¹ (inv_pos.mpr hR)) _ q
        (rayConeApex hcomp hγ₀) δ) := by
  obtain ⟨R₁, -, hR₁⟩ := exists_uniform_dist_le_of_ray hcomp q (ω := δ / 4) (by positivity) δ⁻¹
  obtain ⟨r₀, hr₀⟩ := exists_ray_near hcomp hsegments q (η := δ ^ 2 / 8) (by positivity)
  set r : ℝ := max r₀ 0 with hr
  have hr0 : 0 ≤ r := le_max_right _ _
  refine ⟨max R₁ (8 * r / δ), fun R hR hR₀ => ?_⟩
  have hR₁R : R₁ ≤ R := (le_max_left _ _).trans hR₀
  have hrR : r / R ≤ δ / 8 := by
    have h := (le_max_right _ _).trans hR₀
    rw [div_le_iff₀ hδ] at h
    rw [div_le_iff₀ hR]
    linarith
  set c : ℝ≥0 := ⟨R⁻¹, (inv_pos.mpr hR).le⟩ with hc
  have hcR : (c : ℝ) = R⁻¹ := rfl
  set K : Set Y := rayUnion q ∩ closedBall q (R / δ) with hK
  have hKc : IsCompact K := (isCompact_closedBall q (R / δ)).inter_left (isClosed_rayUnion q)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hRδ : R / δ = δ⁻¹ * R := by rw [div_eq_inv_mul]
  have hqK : q ∈ K := by
    refine ⟨?_, mem_closedBall_self (by positivity)⟩
    have h := mem_rayUnion hγ₀ 0
    rwa [hγ₀.2] at h
  let Φ : K → RayCone hcomp q := fun z => rayConeProj hcomp c ⟨z.1, z.2.1⟩
  let z₀ : K := ⟨q, hqK⟩
  have hdistΦ (z : K) : dist (Φ z) (rayConeApex hcomp hγ₀) = R⁻¹ * dist q (z : Y) :=
    dist_rayConeProj_mk_zero hcomp c ⟨z.1, z.2.1⟩ hγ₀
  have hΦz₀ : Φ z₀ = rayConeApex hcomp hγ₀ := by
    apply dist_eq_zero.mp
    rw [hdistΦ z₀]
    change R⁻¹ * dist q q = 0
    rw [dist_self, mul_zero]
  have hball (z : K) : dist q (z : Y) ≤ δ⁻¹ * R := by
    have h := z.2.2
    rw [mem_closedBall, dist_comm] at h
    rwa [← hRδ]
  set β : ℝ := δ / 8 + r / R with hβ
  obtain ⟨f, -⟩ := @exists_kleinerLott_approx_of_compact_parameters Y (RayCone hcomp q) K
    (mY.rescale R⁻¹ (inv_pos.mpr hR)) _ _ _ Subtype.val Φ continuous_subtype_val z₀ δ β (δ / 4)
    hδ hδone (by rw [hβ]; linarith)
    (fun z => by
      change R⁻¹ * dist (z : Y) q = dist (Φ z) (Φ z₀)
      rw [hΦz₀, hdistΦ, dist_comm])
    (fun z => by
      rw [mem_closedBall, hΦz₀, hdistΦ]
      calc R⁻¹ * dist q (z : Y) ≤ R⁻¹ * (δ⁻¹ * R) :=
            mul_le_mul_of_nonneg_left (hball z) (inv_nonneg.mpr hR.le)
        _ = δ⁻¹ := by field_simp)
    (fun y hy => by
      obtain ⟨⟨σ, hσ, b⟩, rfl⟩ := RayCone.surjective_mk hcomp q y
      rw [mem_closedBall, hΦz₀, dist_comm, rayConeApex, RayCone.dist_mk,
        rayConeDist_zero_left q _ _ rfl] at hy
      let s : ℝ≥0 := b * ⟨R, hR.le⟩
      have hs : (s : ℝ) = b * R := rfl
      have hsK : σ s ∈ K := by
        refine ⟨mem_rayUnion hσ s, ?_⟩
        rw [mem_closedBall, dist_comm, dist_of_ray hσ, hs, hRδ]
        exact mul_le_mul_of_nonneg_right hy hR.le
      refine ⟨⟨σ s, hsK⟩, ?_⟩
      change rayConeProj hcomp c ⟨σ s, mem_rayUnion hσ s⟩ = _
      have hcs : c * s = b := NNReal.eq (by rw [NNReal.coe_mul, hcR, hs]; field_simp)
      rw [rayConeProj_mk_of_ray, hcs])
    (fun z w => by
      change dist (Φ z) (Φ w) ≤ R⁻¹ * dist (z : Y) (w : Y)
      exact dist_rayConeProj_le hcomp c ⟨z.1, z.2.1⟩ ⟨w.1, w.2.1⟩)
    (fun z w => by
      change R⁻¹ * dist (z : Y) (w : Y) - dist (Φ z) (Φ w) ≤ δ / 4
      have h := hR₁ R hR₁R (rayThrough (⟨z.1, z.2.1⟩ : rayUnion q))
        (rayThrough (⟨w.1, w.2.1⟩ : rayUnion q)) (rayThrough_isRay _) (rayThrough_isRay _)
        ⟨dist q (z : Y), dist_nonneg⟩ ⟨dist q (w : Y), dist_nonneg⟩ (hball z) (hball w)
      rw [rayThrough_apply, rayThrough_apply] at h
      have hΦ := dist_rayConeProj_eq hcomp c ⟨z.1, z.2.1⟩ ⟨w.1, w.2.1⟩
      change dist (Φ z) (Φ w) = R⁻¹ * _ at hΦ
      rw [hΦ]
      have hmul := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hR.le)
      have hRR : R⁻¹ * (δ / 4 * R) = δ / 4 := by field_simp
      change R⁻¹ * dist (z : Y) (w : Y) ≤ R⁻¹ * (Real.sqrt ((dist q (z : Y) - dist q (w : Y)) ^ 2 +
        dist q (z : Y) * dist q (w : Y) * rayChordLimit (rayThrough (⟨z.1, z.2.1⟩ : rayUnion q))
          (rayThrough (⟨w.1, w.2.1⟩ : rayUnion q)) ^ 2) + δ / 4 * R) at hmul
      rw [mul_add, hRR] at hmul
      linarith)
    (fun x hx => by
      change R⁻¹ * dist x q ≤ δ⁻¹ at hx
      have hxq : dist q x ≤ R / δ := by
        rw [hRδ, dist_comm]
        rw [inv_mul_le_iff₀ hR] at hx
        linarith
      by_cases hfar : r ≤ dist q x
      · obtain ⟨γ, hγ, hclose⟩ := hr₀ x ((le_max_left _ _).trans hfar)
        have hyK : γ ⟨dist q x, dist_nonneg⟩ ∈ K := by
          refine ⟨mem_rayUnion hγ _, ?_⟩
          have hγx := dist_of_ray hγ (⟨dist q x, dist_nonneg⟩ : ℝ≥0)
          rw [mem_closedBall, dist_comm, hγx]
          exact hxq
        refine (@infDist_le_dist_of_mem Y (mY.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace
          (range (Subtype.val : K → Y)) x _ ⟨⟨_, hyK⟩, rfl⟩).trans ?_
        change R⁻¹ * dist x (γ ⟨dist q x, dist_nonneg⟩) ≤ β
        calc R⁻¹ * dist x (γ ⟨dist q x, dist_nonneg⟩) ≤ R⁻¹ * (δ ^ 2 / 8 * (R / δ)) := by
              apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR.le)
              exact hclose.trans (mul_le_mul_of_nonneg_left hxq (by positivity))
          _ = δ / 8 := by field_simp
          _ ≤ β := by rw [hβ]; linarith [div_nonneg hr0 hR.le]
      · refine (@infDist_le_dist_of_mem Y (mY.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace
          (range (Subtype.val : K → Y)) x _ ⟨z₀, rfl⟩).trans ?_
        change R⁻¹ * dist x q ≤ β
        rw [dist_comm, ← div_eq_inv_mul]
        have h1 : dist q x / R ≤ r / R :=
          div_le_div_of_nonneg_right (not_le.mp hfar).le hR.le
        rw [hβ]
        linarith)
  rw [hΦz₀] at f
  exact ⟨f⟩

/-- (F), the LC21 producer: a proper space with segments and nonnegative four-point comparison has
a proper AC82 cone at infinity, fixed before `ε`, with Kleiner–Lott `ε`-maps from every blow-down
`(R⁻¹ Y, q)`, `R ≥ R₀(ε)`. -/
theorem exists_cone_at_infinity_of_fourPointComparison_zero
    {Y : Type u} [mY : MetricSpace Y] [ProperSpace Y]
    (hcomp : fourPointComparison 0 (univ : Set Y))
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (q : Y) :
    ∃ (C : Type u) (mC : MetricSpace C) (o : C), Nonempty (@RadialConeData C mC o) ∧
      @ProperSpace C mC.toPseudoMetricSpace ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox Y C (mY.rescale R⁻¹ (inv_pos.mpr hR)) mC q o ε) := by
  by_cases hb : Bornology.IsBounded (univ : Set Y)
  · exact ⟨PUnit, inferInstance, PUnit.unit, ⟨RadialConeData.punit⟩, inferInstance,
      fun ε hε hε1 => exists_kleinerLottApprox_rescale_point_of_isBounded q hb hε hε1⟩
  · obtain ⟨r₀, hr₀⟩ := exists_ray_near hcomp hsegments q (η := 1) one_pos
    obtain ⟨x, hx⟩ : ∃ x : Y, r₀ ≤ dist q x := by
      by_contra h
      push Not at h
      exact hb ((isBounded_closedBall (x := q) (r := r₀)).subset fun x _ => by
        rw [mem_closedBall, dist_comm]
        exact (h x).le)
    obtain ⟨γ₀, hγ₀, -⟩ := hr₀ x hx
    exact ⟨RayCone hcomp q, inferInstance, rayConeApex hcomp hγ₀, ⟨rayConeRadialData hcomp hγ₀⟩,
      properSpace_rayCone hcomp q,
      fun ε hε hε1 => exists_kleinerLottApprox_rayCone hcomp hsegments hγ₀ hε hε1⟩

end GC.MetricGeometry
