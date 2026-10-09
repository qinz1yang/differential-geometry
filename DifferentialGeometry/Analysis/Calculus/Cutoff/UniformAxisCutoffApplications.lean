import DifferentialGeometry.Analysis.Calculus.Cutoff.UniformAxisCutoff
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Consumers of CFS22

* `smoothTransition_cfs_profile`: Mathlib's `Real.smoothTransition` satisfies the four profile
  hypotheses of `cfs22_row` (smooth, `0` on `(−∞, 0]`, `1` on `[1, ∞)`, values in `[0, 1]`).
* `cfs22_cutoff_eq_zero_off_seven`: under the hypotheses of `cfs22_row`, the cutoff vanishes at
  `f(p)` whenever no `|η_i(p)| < 7ℓ` on `U_i` (closed-support localization, value form).
* `cfs22_endpoint_derivative`: the derivative bound at the perturbed point `f(p)` itself.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff BigOperators

namespace GC.MetricGeometry

/-- `Real.smoothTransition` is an admissible CFS22 profile. -/
theorem smoothTransition_cfs_profile :
    ContDiff ℝ ∞ Real.smoothTransition ∧ (∀ t ≤ 0, Real.smoothTransition t = 0) ∧
      (∀ t, 1 ≤ t → Real.smoothTransition t = 1) ∧
      ∀ t, Real.smoothTransition t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.contDiff, fun _ ht => Real.smoothTransition.zero_of_nonpos ht,
    fun _ ht => Real.smoothTransition.one_of_one_le ht,
    fun t => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩⟩

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {I : Type*} [Fintype I] {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]

/-- Value form of the closed-support localization. -/
theorem cfs22_cutoff_eq_zero_off_seven {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ t ≤ 0, χ t = 0) (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1)
    {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ)
    (u : ∀ i, H →L[ℝ] E i) (v : I → H →L[ℝ] ℝ) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    {X : Type*} {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (R : I → ℝ) (hR : ∀ i, 0 < R i) (ρ : X → ℝ)
    (hρ : ∀ p, 0 < ρ p) (U : I → Set X) (η : ∀ i, X → E i) (ζ : I → X → ℝ)
    (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1) (F f : X → H)
    (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * ℓ)
    (hplateau : ∀ i p, p ∈ U i → ‖η i p‖ < 6 * ℓ → ζ i p = 1)
    (hpert : ∀ p, ‖f p - F p‖ ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32) (p : X)
    (hp : ∀ i, p ∈ U i → 7 * ℓ ≤ ‖η i p‖) :
    cfsUniformAxisCutoff χ ℓ R u v (f p) = 0 := by
  have h := (cfs22_row hχ hχ0 hχ1 hχI hP1 hP N u v hu hv hℓ R hR ρ hρ U η ζ hζI F f hζU hblock
    hcount hcomp hplateau hpert hZM).2.2.2.1 p
  by_contra hne
  obtain ⟨i, hiU, hη⟩ := h (subset_tsupport _ hne)
  exact absurd (hp i hiU) (not_le.mpr hη)

/-- The derivative bound at the perturbed point `f(p)` (segment parameter `t = 1`). -/
theorem cfs22_endpoint_derivative {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ t ≤ 0, χ t = 0) (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1)
    {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ)
    (u : ∀ i, H →L[ℝ] E i) (v : I → H →L[ℝ] ℝ) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    {X : Type*} {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (R : I → ℝ) (hR : ∀ i, 0 < R i) (ρ : X → ℝ)
    (hρ : ∀ p, 0 < ρ p) (U : I → Set X) (η : ∀ i, X → E i) (ζ : I → X → ℝ)
    (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1) (F f : X → H)
    (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * ℓ)
    (hplateau : ∀ i p, p ∈ U i → ‖η i p‖ < 6 * ℓ → ζ i p = 1)
    (hpert : ∀ p, ‖f p - F p‖ ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32) (p : X) :
    ‖fderiv ℝ (cfsUniformAxisCutoff χ ℓ R u v) (f p)‖ ≤
      10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p := by
  have h := (cfs22_row hχ hχ0 hχ1 hχI hP1 hP N u v hu hv hℓ R hR ρ hρ U η ζ hζI F f hζU hblock
    hcount hcomp hplateau hpert hZM).2.2.2.2 p 1 ⟨zero_le_one, le_rfl⟩
  simpa using h

end GC.MetricGeometry
