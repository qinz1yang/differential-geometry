import DifferentialGeometry.Geometry.Curvature.ConformalIndexFormGE

/-!
# `index_form_nonneg_GE` 的非空性检验（S-W-GEO G2）

平坦情形 `ρ ≡ 1`、`c(s) = s`（`ℂ` 里的线段，`‖c′‖ = 1`）：`C¹` 曲线类里固定端点的长度极小性是
`‖η(L) − η(0)‖ ≤ ∫‖η′‖`（标准），所以 `index_form_nonneg_GE` 的全部假设可同时满足；
结论 `0 ≤ ∫ φ′²`（`K̂ = 0`）。
-/

set_option autoImplicit false
noncomputable section

open Set intervalIntegral
open scoped ContDiff

namespace DifferentialGeometry.Geometry

/-- 线段 `c(s) = s` 在 `ρ ≡ 1` 下是 `C¹` 曲线类里的固定端点极小元。 -/
theorem flat_hmin_GE {L : ℝ} (hL : 0 ≤ L) :
    ∀ η : ℝ → ℂ, ContDiff ℝ 1 η → η 0 = (fun s : ℝ => (s : ℂ)) 0 →
      η L = (fun s : ℝ => (s : ℂ)) L →
      ∫ s in (0 : ℝ)..L, (fun _ : ℂ => (1 : ℝ)) ((fun s : ℝ => (s : ℂ)) s) *
          ‖deriv (fun s : ℝ => (s : ℂ)) s‖ ≤
        ∫ s in (0 : ℝ)..L, (fun _ : ℂ => (1 : ℝ)) (η s) * ‖deriv η s‖ := by
  intro η hη h0 hL'
  have hder : ∀ s : ℝ, deriv (fun s : ℝ => (s : ℂ)) s = 1 := fun s =>
    (Complex.ofRealCLM.hasDerivAt (x := s)).deriv
  have hcont : Continuous (deriv η) := hη.continuous_deriv le_rfl
  have hftc : ∫ s in (0 : ℝ)..L, deriv η s = η L - η 0 :=
    intervalIntegral.integral_deriv_eq_sub (fun s _ => (hη.differentiable (by norm_num)) s)
      (hcont.intervalIntegrable 0 L)
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume)
    (f := deriv η) hL
  rw [hftc, hL', h0] at hnorm
  simpa [hder, abs_of_nonneg hL] using hnorm

/-- 平坦情形的 `index_form_nonneg_GE`：`ρ ≡ 1`，`c(s) = s`。 -/
theorem flat_index_form_GE {L : ℝ} (hL : 0 ≤ L) :
    ∀ φ φ' : ℝ → ℝ, (∀ s, HasDerivAt φ (φ' s) s) → Continuous φ' → φ 0 = 0 → φ L = 0 →
      0 ≤ ∫ s in (0 : ℝ)..L, (φ' s ^ 2 / ((fun _ : ℂ => (1 : ℝ)) ((fun s : ℝ => (s : ℂ)) s) *
          ‖deriv (fun s : ℝ => (s : ℂ)) s‖) -
        (-((fun _ : ℂ => (1 : ℝ)) ((fun s : ℝ => (s : ℂ)) s))⁻¹ ^ 2 *
          Laplacian.laplacian (fun p => Real.log ((fun _ : ℂ => (1 : ℝ)) p))
            ((fun s : ℝ => (s : ℂ)) s)) *
        ((fun _ : ℂ => (1 : ℝ)) ((fun s : ℝ => (s : ℂ)) s) *
          ‖deriv (fun s : ℝ => (s : ℂ)) s‖) * φ s ^ 2) := by
  intro φ φ' h1 h2 h3 h4
  have hder : ∀ s : ℝ, deriv (fun s : ℝ => (s : ℂ)) s = 1 := fun s =>
    (Complex.ofRealCLM.hasDerivAt (x := s)).deriv
  exact index_form_nonneg_GE (ρ := fun _ => (1 : ℝ)) (c := fun s : ℝ => (s : ℂ))
    contDiff_const (fun _ => one_pos) Complex.ofRealCLM.contDiff (fun s => by simp [hder]) hL
    (flat_hmin_GE hL) h1 h2 h3 h4

end DifferentialGeometry.Geometry
