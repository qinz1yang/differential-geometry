import DifferentialGeometry.Topology.Manifold.RatioCompatibleDefiner
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# `v ≠ R` normalisation regression for the ratio-compatible global definer (D78-5, D74-7)

Lane S-FIX-REG (suffix `_FXR`), G2. Review 78 D78-5 asks for a regression that the positive-factor
correction of `exists_ratioCompatible_global_definer_ZSP35` is actually used when `v ≠ R`.

The linearized global function `H_lin` of ZSP02 satisfies on the buffer
`H_lin − 2/5 = (v/R)(u/v − 2/5)`, NOT `u/v − 2/5` itself. In the one-dimensional model `M = ℝ`
with `R = 1`, `v = 2R = 2` and `u = x`:

* `ratio r x = u/v − 2/5 = x/2 − 2/5` (the prescribed local ratio),
* `G x = H_lin − 2/5 = x − 4/5` (the available global function), `G = a · r` with `a ≡ v/R = 2`.

Results:

* `hlin_normalisation_v_two_R_FXR`: the identity `H_lin − 2/5 = (v/R)(u/v − 2/5)` at `v = 2R`, and
  `normalisation_ne_v_two_R_FXR`: it is NOT `u/v − 2/5` unless `u = 4R/5` (so `ratio_buffer := rfl`
  is false when `v ≠ R`).
* `ratio_definer_v_two_R_FXR`: the kernel applied to `G = x − 4/5`, `a = 2`, `r = x/2 − 2/5`
  produces a smooth `F` equal to `r` near the zero level, with the same sublevel `Iic (4/5)` and
  level `{4/5}`, nonzero differential at the zero, and `F` is NOT `G` at some point of the buffer.
* `ratio_definer_variable_factor_FXR`: the same with a non-constant factor `a = 1 + x²`
  (`v/R = 1 + x²`, `v ≠ R` away from `0`), `G = (1 + x²)(x − 4/5)`.
* `global_function_not_ratio_FXR`: the global function `G` itself is never equal to the ratio `r` on
  a neighbourhood of its zero (no `ratio_buffer := rfl`), so the factor division is necessary.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

/-- **D74-7 normalisation at `v = 2R`**: `H_lin − 2/5 = (v/R)(u/v − 2/5)` with `v = 2R`, written as
`u/R − 4/5` (`H_lin = u/R − 2/5`). -/
theorem hlin_normalisation_v_two_R_FXR {u R : ℝ} (hR : R ≠ 0) :
    (u / R - 2 / 5) - 2 / 5 = (2 * R / R) * (u / (2 * R) - 2 / 5) := by
  field_simp
  ring

/-- At `v = 2R` the normalised function is NOT the buffer ratio `u/v − 2/5` unless
`u = 4R/5`: `ratio_buffer := rfl` is false for `v ≠ R`. -/
theorem normalisation_ne_v_two_R_FXR {u R : ℝ} (hR : R ≠ 0) (hu : u ≠ 4 / 5 * R) :
    (2 * R / R) * (u / (2 * R) - 2 / 5) ≠ u / (2 * R) - 2 / 5 := by
  intro h
  apply hu
  field_simp at h
  linarith

/-- The model function `G x = x − 4/5` is smooth. -/
theorem contMDiff_sub_FXR : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : ℝ => x - 4 / 5) :=
  contMDiff_id.sub contMDiff_const

/-- The differential of `x ↦ x − 4/5` never vanishes. -/
theorem mfderiv_sub_ne_zero_FXR (x : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun x : ℝ => x - 4 / 5) x ≠ 0 := by
  have h := ((hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) (M := ℝ) x).sub
    (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (M := ℝ) (M' := ℝ) (4 / 5 : ℝ) x)).mfderiv
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (id - fun _ : ℝ => (4 / 5 : ℝ)) x ≠ 0
  rw [h]
  intro h0
  have h1 := congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) x =>
    L (1 : ℝ)) h0
  have h2 : (1 : ℝ) - 0 = 0 := h1
  simp at h2

/-- **The `v = 2R` numeric consumer**: on `M = ℝ` with `G x = x − 4/5 = a · r`, `a ≡ 2 = v/R`,
`r x = x/2 − 2/5 = u/v − 2/5`, the kernel's `F = G/â` equals `r` near the zero level
`{4/5}` (not `G`), has the same sublevel and level, nonzero differential at the zero, and is
different from `G` at a point of the buffer `N` (the factor `2` is really divided out). -/
theorem ratio_definer_v_two_R_FXR :
    ∃ (F : ℝ → ℝ) (N : Set ℝ), IsOpen N ∧ {x : ℝ | x - 4 / 5 = 0} ⊆ N ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ F ∧ (∀ x ∈ N, F x = x / 2 - 2 / 5) ∧
      {x | F x ≤ 0} = Iic (4 / 5) ∧ {x | F x = 0} = {4 / 5} ∧
      (∀ x, F x = 0 → mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) F x ≠ 0) ∧ ∃ x ∈ N, F x ≠ x - 4 / 5 := by
  obtain ⟨F, N, hNo, hZN, -, hF, hFN, hle, hlv, hreg⟩ :=
    exists_ratioCompatible_global_definer_ZSP35 (I := 𝓘(ℝ, ℝ)) (M := ℝ)
      (G := fun x : ℝ => x - 4 / 5) contMDiff_sub_FXR
      (fun x _ => mfderiv_sub_ne_zero_FXR x) (O := univ) isOpen_univ (subset_univ _)
      (r := fun x : ℝ => x / 2 - 2 / 5) (a := fun _ : ℝ => (2 : ℝ))
      contMDiff_const.contMDiffOn (fun _ _ => two_pos) (fun x _ => by ring)
  have h45 : (4 / 5 : ℝ) ∈ N := hZN (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hNo _ h45
  have hx : 4 / 5 + ε / 2 ∈ N := hball (by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_pos (by linarith)]
    linarith)
  refine ⟨F, N, hNo, hZN, hF, hFN, ?_, ?_, fun x hx0 => ?_, 4 / 5 + ε / 2, hx, ?_⟩
  · rw [hle]
    ext x
    simp only [mem_ofPred_eq, mem_Iic]
    constructor <;> intro h <;> linarith
  · rw [hlv]
    ext x
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  · exact hreg x hx0
  · rw [hFN _ hx]
    intro h
    linarith

/-- The factor `b x = 1 + x²` is smooth. -/
theorem contMDiff_one_add_sq_FXR : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : ℝ => 1 + x ^ 2) :=
  contMDiff_const.add (contMDiff_id.pow 2)

/-- **A non-constant positive factor** `a = 1 + x²` (`v/R = 1 + x²`, `v ≠ R` away from `0`):
`G x = (x − 4/5)(1 + x²)`, `r x = x − 4/5`; the produced `F` equals `r` on the buffer and differs
from `G` at a buffer point. -/
theorem ratio_definer_variable_factor_FXR :
    ∃ (F : ℝ → ℝ) (N : Set ℝ), IsOpen N ∧ (4 / 5 : ℝ) ∈ N ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ F ∧ (∀ x ∈ N, F x = x - 4 / 5) ∧
      {x | F x ≤ 0} = Iic (4 / 5) ∧ ∃ x ∈ N, F x ≠ (x - 4 / 5) * (1 + x ^ 2) := by
  have hG : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : ℝ => (x - 4 / 5) * (1 + x ^ 2)) :=
    contMDiff_sub_FXR.mul contMDiff_one_add_sq_FXR
  have hreg : ∀ x : ℝ, (x - 4 / 5) * (1 + x ^ 2) = 0 →
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun x : ℝ => (x - 4 / 5) * (1 + x ^ 2)) x ≠ 0 := by
    intro x hx
    have hx45 : x - 4 / 5 = 0 := by
      rcases mul_eq_zero.mp hx with h | h
      · exact h
      · nlinarith [sq_nonneg x]
    rw [mfderiv_mul_of_eq_zero_ZSP35 (I := 𝓘(ℝ, ℝ)) (M := ℝ)
      (contMDiff_sub_FXR.mdifferentiableAt (by simp))
      (contMDiff_one_add_sq_FXR.mdifferentiableAt (by simp)) hx45]
    exact smul_ne_zero (by positivity) (mfderiv_sub_ne_zero_FXR x)
  obtain ⟨F, N, hNo, hZN, -, hF, hFN, hle, -, -⟩ :=
    exists_ratioCompatible_global_definer_ZSP35 (I := 𝓘(ℝ, ℝ)) (M := ℝ)
      (G := fun x : ℝ => (x - 4 / 5) * (1 + x ^ 2)) hG hreg (O := univ) isOpen_univ
      (subset_univ _) (r := fun x : ℝ => x - 4 / 5) (a := fun x : ℝ => 1 + x ^ 2)
      contMDiff_one_add_sq_FXR.contMDiffOn (fun x _ => by positivity) (fun x _ => by ring)
  have h45 : (4 / 5 : ℝ) ∈ N := hZN (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hNo _ h45
  have hx : 4 / 5 + ε / 2 ∈ N := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
    linarith)
  refine ⟨F, N, hNo, h45, hF, hFN, ?_, 4 / 5 + ε / 2, hx, ?_⟩
  · rw [hle]
    ext x
    simp only [mem_ofPred_eq, mem_Iic]
    constructor
    · intro h
      by_contra hlt
      have : 0 < (x - 4 / 5) * (1 + x ^ 2) := mul_pos (by linarith [not_le.mp hlt]) (by positivity)
      linarith
    · intro h
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  · rw [hFN _ hx]
    intro h
    have ht : 0 < 4 / 5 + ε / 2 := by linarith
    have h1 : (4 / 5 + ε / 2 - 4 / 5) * (4 / 5 + ε / 2) ^ 2 = 0 := by linarith
    have h2 : 0 < (4 / 5 + ε / 2 - 4 / 5) * (4 / 5 + ε / 2) ^ 2 :=
      mul_pos (by linarith) (pow_pos ht 2)
    linarith

/-- **The global function is not the ratio**: `G x = x − 4/5` equals `r x = x/2 − 2/5` on no
neighbourhood of the zero level (`v ≠ R`: `ratio_buffer := rfl` is false), so the correction
`F = G/â` of the kernel is needed. -/
theorem global_function_not_ratio_FXR {N : Set ℝ} (hN : IsOpen N) (h45 : (4 / 5 : ℝ) ∈ N) :
    ∃ x ∈ N, x - 4 / 5 ≠ x / 2 - 2 / 5 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hN _ h45
  refine ⟨4 / 5 + ε / 2, hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
    linarith), fun h => ?_⟩
  linarith

end DifferentialGeometry.Topology.Manifold
