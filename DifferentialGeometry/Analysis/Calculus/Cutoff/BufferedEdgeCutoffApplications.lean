import DifferentialGeometry.Analysis.Calculus.Cutoff.BufferedEdgeCutoff
import DifferentialGeometry.Analysis.Calculus.Cutoff.UniformAxisCutoffApplications

/-!
# Consumers of CFS23

* `smoothTransition_cfs23_profile`: Mathlib's `Real.smoothTransition` is an admissible CFS23
  profile (the four CFS22 profile conditions and monotonicity).
* `cfs23_row_scalar`: the scalar edge block of the blueprint (`x' : H →L ℝ`, `x'(F p) = ρ t z₀`,
  `t ≥ 0` on `D = ⋃ U_i`), from `cfs23_row`.
* `cfs23_relative_support`: the review's wording of the support clause (closure taken inside
  `O = {x_ρ > 0}`), together with the value form `ψ_e(f p) = 0` off the joint outer region.
* `cfs23_endpoint_derivative`: `f(p) ∈ O` and `‖Dψ_e(f p)‖ ≤ C₀/ρ(p)`.
* An `example` with the blueprint's verbatim profile `h` (smooth, zero outside `(1/5, 9)`,
  equal to `1 − χ_{8,9}` on `[3/10, ∞)`); those two extra properties of `h` are not needed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff BigOperators

namespace GC.MetricGeometry

/-- `Real.smoothTransition` is an admissible CFS23 profile. -/
theorem smoothTransition_cfs23_profile :
    ContDiff ℝ ∞ Real.smoothTransition ∧ (∀ t ≤ 0, Real.smoothTransition t = 0) ∧
      (∀ t, 1 ≤ t → Real.smoothTransition t = 1) ∧
      (∀ t, Real.smoothTransition t ∈ Icc (0 : ℝ) 1) ∧ Monotone Real.smoothTransition :=
  ⟨smoothTransition_cfs_profile.1, smoothTransition_cfs_profile.2.1,
    smoothTransition_cfs_profile.2.2.1, smoothTransition_cfs_profile.2.2.2,
    Real.smoothTransition.monotone⟩

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {I : Type*} [Fintype I] {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]

/-- CFS23 with the blueprint's scalar edge block: `x'(F p) = ρ t z₀`, `t ≥ 0` on `D`. -/
theorem cfs23_row_scalar {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (hχmono : Monotone χ)
    {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ) (u : ∀ i, H →L[ℝ] E i)
    (v : I → H →L[ℝ] ℝ) (xρ x1 x2 : H →L[ℝ] ℝ) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hxρ : ‖xρ‖ ≤ 1) (hx1 : ‖x1‖ ≤ 1) (hx2 : ‖x2‖ ≤ 1) {X : Type*} {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (R : I → ℝ) (hR : ∀ i, 0 < R i) (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (U : I → Set X)
    (η : ∀ i, X → E i) (ζ : I → X → ℝ) (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1) (F f : X → H)
    (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * Δ)
    (hpert : ∀ p, ‖f p - F p‖ ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32)
    (t : X → ℝ) (ht0 : ∀ p, (∃ i, p ∈ U i) → 0 ≤ t p) (h : ℝ → ℝ)
    (hhI : ∀ s, h s ∈ Icc (0 : ℝ) 1) (hhg : ∀ s, 3 / 10 ≤ s → h s = 1 - cfsRamp χ 8 9 s)
    (hxρF : ∀ p, xρ (F p) = ρ p)
    (hedgeblock : ∀ p, (∃ i, p ∈ U i) →
      x1 (F p) = ρ p * t p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)) ∧
      x2 (F p) = ρ p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)))
    (hedge : ∀ i p, p ∈ U i → ‖η i p‖ < 8 * Δ → ζ i p = 1 - cfsRamp χ 8 9 (t p / Δ)) :
    ContDiffOn ℝ ∞ (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) {z | 0 < xρ z} ∧
      (∀ z, cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ i, p ∈ U i ∧ ‖η i p‖ < 6 * Δ ∧ t p < 6 * Δ) →
        cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 (f p) = 1) ∧
      (∀ p, f p ∈ tsupport (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) →
        ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * Δ ∧ t p < 7 * Δ) ∧
      (∀ p, ∀ s ∈ Icc (0 : ℝ) 1, 0 < xρ ((1 - s) • F p + s • f p) ∧
        ‖fderiv ℝ (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) ((1 - s) • F p + s • f p)‖ ≤
          10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p) := by
  refine cfs23_row R u v xρ x1 x2 hχ hχ0 hχ1 hχI hχmono hP1 hP N hu hv hxρ hx1 hx2 hΔ hR ρ hρ U
    η ζ hζI F f hζU hblock hcount hcomp hpert hZM t h hhI hhg hxρF ?_ hedge
  intro p hD
  refine ⟨?_, (hedgeblock p hD).2⟩
  rw [(hedgeblock p hD).1, Real.norm_eq_abs]
  obtain ⟨h1a, -⟩ := hhI (t p / Δ)
  obtain ⟨h2a, -⟩ := cfsRamp_mem_Icc hχI (1 / 2) 1 (∑ j, ζ j p)
  exact abs_of_nonneg (mul_nonneg (mul_nonneg (hρ p).le (ht0 p hD)) (mul_nonneg h1a h2a))

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']

/-- The support clause in the review's wording (closure inside `O = {x_ρ > 0}`), and its value
form: `ψ_e(f p) = 0` off the joint outer region. -/
theorem cfs23_relative_support {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (hχmono : Monotone χ)
    {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ) (u : ∀ i, H →L[ℝ] E i)
    (v : I → H →L[ℝ] ℝ) (xρ : H →L[ℝ] ℝ) (x1 : H →L[ℝ] E') (x2 : H →L[ℝ] ℝ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) (hxρ : ‖xρ‖ ≤ 1) (hx1 : ‖x1‖ ≤ 1)
    (hx2 : ‖x2‖ ≤ 1) {X : Type*} {Δ : ℝ} (hΔ : 1 ≤ Δ) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (U : I → Set X) (η : ∀ i, X → E i) (ζ : I → X → ℝ)
    (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1) (F f : X → H) (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * Δ)
    (hpert : ∀ p, ‖f p - F p‖ ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32)
    (t : X → ℝ) (h : ℝ → ℝ) (hhg : ∀ s, 3 / 10 ≤ s → h s = 1 - cfsRamp χ 8 9 s)
    (hxρF : ∀ p, xρ (F p) = ρ p)
    (hedgeblock : ∀ p, (∃ i, p ∈ U i) →
      ‖x1 (F p)‖ = ρ p * t p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)) ∧
      x2 (F p) = ρ p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)))
    (hedge : ∀ i p, p ∈ U i → ‖η i p‖ < 8 * Δ → ζ i p = 1 - cfsRamp χ 8 9 (t p / Δ)) (p : X) :
    (f p ∈ closure (Function.support (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) ∩
        {z | 0 < xρ z}) → ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * Δ ∧ t p < 7 * Δ) ∧
      ((¬∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * Δ ∧ t p < 7 * Δ) →
        cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 (f p) = 0) := by
  have hloc := cfs23_support R u v xρ x1 x2 hχ hχ0 hχ1 hχI hχmono hP1 hP N hu hv hxρ hx1 hx2
    hΔ hR ρ hρ U η ζ hζI F f hζU hblock hcount hcomp hpert hZM t h hhg hxρF hedgeblock hedge p
  refine ⟨fun hcl => ?_, fun hnot => (hloc hnot).self_of_nhds⟩
  by_contra hnot
  have hns : f p ∉ tsupport (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) :=
    notMem_tsupport_iff_eventuallyEq.mpr (hloc hnot)
  exact hns (closure_mono inter_subset_left hcl)

/-- The endpoint `f(p)` lies in `O` and `‖Dψ_e(f p)‖ ≤ 10⁴ (N+1)² P⁴ / ρ(p)`. -/
theorem cfs23_endpoint_derivative {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ t ≤ 0, χ t = 0) (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1)
    {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ) (u : ∀ i, H →L[ℝ] E i)
    (v : I → H →L[ℝ] ℝ) (xρ : H →L[ℝ] ℝ) (x1 : H →L[ℝ] E') (x2 : H →L[ℝ] ℝ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) (hxρ : ‖xρ‖ ≤ 1) (hx1 : ‖x1‖ ≤ 1)
    (hx2 : ‖x2‖ ≤ 1) {X : Type*} {Δ : ℝ} (hΔ : 1 ≤ Δ) (R : I → ℝ) (hR : ∀ i, 0 < R i)
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (ζ : I → X → ℝ) (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1)
    (F f : X → H) (hvblock : ∀ i p, v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hscale : ∀ i p, 0 < ζ i p → ρ p ≤ 5 / 4 * R i)
    (hpert : ∀ p, ‖f p - F p‖ ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32) (hxρF : ∀ p, xρ (F p) = ρ p)
    (hx2F : ∀ i p, 0 < ζ i p → |x2 (F p)| ≤ ρ p) (p : X) :
    0 < xρ (f p) ∧ ‖fderiv ℝ (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) (f p)‖ ≤
      10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p := by
  have h := cfs23_segment R u v xρ x1 x2 hχ hχ0 hχ1 hχI hP1 hP N hu hv hxρ hx1 hx2 hΔ hR ρ hρ ζ
    hζI F f hvblock hcount hscale hpert hZM hxρF hx2F p (s := 1) ⟨zero_le_one, le_rfl⟩
  simpa using h

/-- The verbatim blueprint profile `h` (smooth, zero outside `(1/5, 9)`, `= 1 − χ_{8,9}` on
`[3/10, ∞)`) with the scalar edge block: `cfs23_row_scalar` applies (smoothness of `h` and its
vanishing outside `(1/5, 9)` are not needed for it); those two properties give the smooth edge
profile `s ↦ h(s/Δ)` and the zero-output branch `x''(F p) = 0` for `t ≥ 9Δ` on `D`. -/
example {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (hχmono : Monotone χ)
    {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ) (u : ∀ i, H →L[ℝ] E i)
    (v : I → H →L[ℝ] ℝ) (xρ x1 x2 : H →L[ℝ] ℝ) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hxρ : ‖xρ‖ ≤ 1) (hx1 : ‖x1‖ ≤ 1) (hx2 : ‖x2‖ ≤ 1) {X : Type*} {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (R : I → ℝ) (hR : ∀ i, 0 < R i) (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (U : I → Set X)
    (η : ∀ i, X → E i) (ζ : I → X → ℝ) (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1) (F f : X → H)
    (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * Δ)
    (hpert : ∀ p, ‖f p - F p‖ ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32)
    (t : X → ℝ) (ht0 : ∀ p, (∃ i, p ∈ U i) → 0 ≤ t p) (h : ℝ → ℝ) (hhsmooth : ContDiff ℝ ∞ h)
    (hhI : ∀ s, h s ∈ Icc (0 : ℝ) 1) (hhzero : ∀ s, s ∉ Ioo (1 / 5 : ℝ) 9 → h s = 0)
    (hhg : ∀ s, 3 / 10 ≤ s → h s = 1 - cfsRamp χ 8 9 s) (hxρF : ∀ p, xρ (F p) = ρ p)
    (hedgeblock : ∀ p, (∃ i, p ∈ U i) →
      x1 (F p) = ρ p * t p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)) ∧
      x2 (F p) = ρ p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)))
    (hedge : ∀ i p, p ∈ U i → ‖η i p‖ < 8 * Δ → ζ i p = 1 - cfsRamp χ 8 9 (t p / Δ)) :
    (ContDiffOn ℝ ∞ (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) {z | 0 < xρ z} ∧
      (∀ z, cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ i, p ∈ U i ∧ ‖η i p‖ < 6 * Δ ∧ t p < 6 * Δ) →
        cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 (f p) = 1) ∧
      (∀ p, f p ∈ tsupport (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) →
        ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * Δ ∧ t p < 7 * Δ) ∧
      (∀ p, ∀ s ∈ Icc (0 : ℝ) 1, 0 < xρ ((1 - s) • F p + s • f p) ∧
        ‖fderiv ℝ (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) ((1 - s) • F p + s • f p)‖ ≤
          10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p)) ∧
      ContDiff ℝ ∞ (fun s => h (s / Δ)) ∧
      (∀ p, (∃ i, p ∈ U i) → 9 * Δ ≤ t p → x2 (F p) = 0) := by
  refine ⟨cfs23_row_scalar hχ hχ0 hχ1 hχI hχmono hP1 hP N u v xρ x1 x2 hu hv hxρ hx1 hx2 hΔ R hR
    ρ hρ U η ζ hζI F f hζU hblock hcount hcomp hpert hZM t ht0 h hhI hhg hxρF hedgeblock hedge,
    hhsmooth.comp (contDiff_id.div_const Δ), fun p hD ht9 => ?_⟩
  have hΔ0 : 0 < Δ := by linarith
  have h9 : 9 ≤ t p / Δ := by
    rw [le_div_iff₀ hΔ0]
    linarith
  rw [(hedgeblock p hD).2, hhzero _ (fun hmem => (not_le.mpr hmem.2) h9), zero_mul, mul_zero]

end GC.MetricGeometry
