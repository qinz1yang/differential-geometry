import DifferentialGeometry.Geometry.Metric.RetainedMarkerBindings
import DifferentialGeometry.Analysis.Calculus.CutoffAdjustment
import DifferentialGeometry.Analysis.ParameterSelection.AdjustmentBudget
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
noncomputable section
open Set Metric
namespace GC.MetricGeometry

theorem nearest_displacement_at_perturbed_input
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : H → H) (A : H →L[ℝ] H) (o y : H)
    {r ρ σ ε E : ℝ} (hε : 0 ≤ ε)
    (hradius : r ≤ (5 / 3 : ℝ) * σ * ρ)
    (ho : o ∈ ball o r) (hy : y ∈ ball o r)
    (hP : ∀ z ∈ ball o r, DifferentiableAt ℝ P z)
    (hA : ‖A - ContinuousLinearMap.id ℝ H‖ ≤ 1)
    (hderiv : ∀ z ∈ ball o r, ‖fderiv ℝ P z - A‖ ≤ ε)
    (hcenter : ‖P o - o‖ ≤ ε * r)
    (hprior : ‖y - o‖ ≤ E * ρ) :
    ‖P y - y‖ ≤ ((5 / 3 : ℝ) * ε * σ + (1 + ε) * E) * ρ := by
  have hd (z : H) (hz : z ∈ ball o r) :
      ‖fderiv ℝ (fun q => P q - q) z‖ ≤ 1 + ε := by
    change ‖fderiv ℝ (fun q => P q - id q) z‖ ≤ 1 + ε
    rw [fderiv_fun_sub (hP z hz) (differentiableAt_id), fderiv_id]
    have heq : fderiv ℝ P z - ContinuousLinearMap.id ℝ H =
      (fderiv ℝ P z - A) + (A - ContinuousLinearMap.id ℝ H) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith [hderiv z hz])
  have hint := (convex_ball o r).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hP z hz).sub differentiableAt_id) hd ho hy
  change ‖(P y - y) - (P o - o)‖ ≤ (1 + ε) * ‖y - o‖ at hint
  have ht := norm_sub_le ((P y - y) - (P o - o)) (-(P o - o))
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at ht
  have he := mul_le_mul_of_nonneg_left hprior (by linarith : 0 ≤ 1 + ε)
  have hr := mul_le_mul_of_nonneg_left hradius hε
  nlinarith

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem projected_cumulative_adjustment_of_original_ball {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f₀ : E → H} {ψ : H → ℝ} {P : F → F} {x : E}
    (Q : H →L[ℝ] F) (J : F →L[ℝ] H) (A : F →L[ℝ] F)
    (hQ : ‖Q‖ ≤ 1) (hJ : ‖J‖ ≤ 1) (hA : ‖ContinuousLinearMap.id ℝ F - A‖ ≤ 1)
    (hf : DifferentiableAt ℝ f x) (hψ : DifferentiableAt ℝ ψ (f x))
    {b L d ν ρ E₀ H₀ r σ : ℝ}
    (ho : Q (f₀ x) ∈ ball (Q (f₀ x)) r)
    (hy : Q (f x) ∈ ball (Q (f₀ x)) r)
    (hPball : ∀ z ∈ ball (Q (f₀ x)) r, DifferentiableAt ℝ P z)
    (hradius : r ≤ (5 / 3 : ℝ) * σ * ρ)
    (hcenter : ‖P (Q (f₀ x)) - Q (f₀ x)‖ ≤ d * r)
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hd : 0 ≤ d) (hH : 0 ≤ H₀) (hρ : 0 < ρ)
    (hcutoff : 0 ≤ ψ (f x) ∧ ψ (f x) ≤ 1)
    (hcutoffDeriv : ‖fderiv ℝ ψ (f x)‖ ≤ b / ρ)
    (hfirst : ‖fderiv ℝ f₀ x‖ ≤ L)
    (hcomparison : ∀ z ∈ ball (Q (f₀ x)) r, ‖fderiv ℝ P z - A‖ ≤ d)
    (hnormal : ‖(ContinuousLinearMap.id ℝ F - A).comp (Q.comp (fderiv ℝ f₀ x))‖ ≤ ν)
    (hpriorValue : ‖f x - f₀ x‖ ≤ E₀ * ρ)
    (hpriorDeriv : ‖fderiv ℝ f x - fderiv ℝ f₀ x‖ ≤ H₀) :
    let a := (5 / 3 : ℝ) * d * σ + (1 + d) * E₀
    let g : E → H := fun y => f y + ψ (f y) • J (P (Q (f y)) - Q (f y))
    ‖g x - f₀ x‖ ≤ (E₀ + a) * ρ ∧
      ‖fderiv ℝ g x - fderiv ℝ f₀ x‖ ≤
        a * b * (L + H₀) + d * (L + H₀) + ν + 2 * H₀ := by
  have hpriorQ : ‖Q (f x) - Q (f₀ x)‖ ≤ E₀ * ρ := by
    rw [← map_sub]
    exact ((Q.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right hQ (norm_nonneg _)).trans_eq (one_mul _))).trans hpriorValue
  have hvalue := nearest_displacement_at_perturbed_input P A (Q (f₀ x)) (Q (f x))
    hd hradius ho hy hPball (by simpa only [norm_sub_rev] using hA)
    hcomparison hcenter hpriorQ
  exact DifferentialGeometry.Analysis.projected_cutoff_adjustment_cumulative_le
    Q J A hQ hJ hA hf hψ (hPball _ hy) hb hL hd hH hρ hcutoff hvalue
    hcutoffDeriv hfirst (hcomparison _ hy) hnormal hpriorValue hpriorDeriv

theorem projected_original_ball_adjustment_lt_of_threshold {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f₀ : E → H} {ψ : H → ℝ} {P : F → F} {x : E}
    (Q : H →L[ℝ] F) (J : F →L[ℝ] H) (A : F →L[ℝ] F)
    (hQ : ‖Q‖ ≤ 1) (hJ : ‖J‖ ≤ 1) (hA : ‖ContinuousLinearMap.id ℝ F - A‖ ≤ 1)
    (hf : DifferentiableAt ℝ f x) (hψ : DifferentiableAt ℝ ψ (f x))
    {b L d ν ρ E₀ H₀ r σ c μ : ℝ}
    (ho : Q (f₀ x) ∈ ball (Q (f₀ x)) r)
    (hy : Q (f x) ∈ ball (Q (f₀ x)) r)
    (hPball : ∀ z ∈ ball (Q (f₀ x)) r, DifferentiableAt ℝ P z)
    (hradius : r ≤ (5 / 3 : ℝ) * σ * ρ)
    (hcenter : ‖P (Q (f₀ x)) - Q (f₀ x)‖ ≤ d * r)
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hd : 0 ≤ d) (hH : 0 ≤ H₀) (hρ : 0 < ρ)
    (hcutoff : 0 ≤ ψ (f x) ∧ ψ (f x) ≤ 1)
    (hcutoffDeriv : ‖fderiv ℝ ψ (f x)‖ ≤ b / ρ)
    (hfirst : ‖fderiv ℝ f₀ x‖ ≤ L)
    (hcomparison : ∀ z ∈ ball (Q (f₀ x)) r, ‖fderiv ℝ P z - A‖ ≤ d)
    (hnormal : ‖(ContinuousLinearMap.id ℝ F - A).comp (Q.comp (fderiv ℝ f₀ x))‖ ≤ ν)
    (hpriorValue : ‖f x - f₀ x‖ ≤ E₀ * ρ)
    (hpriorDeriv : ‖fderiv ℝ f x - fderiv ℝ f₀ x‖ ≤ H₀)
    (hc : 0 < c) (hc1 : c ≤ 1) (hμ : 0 < μ) (hE : 0 ≤ E₀)
    (hdsmall : d ≤ 1 / 10) (hσsmall : σ ≤ 1 / 2) (hνsmall : ν ≤ c / 16)
    (hdα : d ≤ min (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L))))
    (hEα : E₀ ≤ min (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L))))
    (hHα : H₀ ≤ min (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L)))) :
    let g : E → H := fun y => f y + ψ (f y) • J (P (Q (f y)) - Q (f y))
    ‖g x - f₀ x‖ < c * ρ ∧ ‖fderiv ℝ g x - fderiv ℝ f₀ x‖ < c := by
  have hactual := projected_cumulative_adjustment_of_original_ball Q J A hQ hJ hA hf hψ
    ho hy hPball hradius hcenter hb hL hd hH hρ hcutoff hcutoffDeriv hfirst hcomparison
    hnormal hpriorValue hpriorDeriv
  obtain ⟨hv, hder, _⟩ := DifferentialGeometry.Analysis.adjustment_errors_lt_of_threshold
    hc hc1 hμ hb hL hd hE hH hdsmall hσsmall hνsmall hdα hEα hHα
  exact ⟨hactual.1.trans_lt (mul_lt_mul_of_pos_right hv hρ), hactual.2.trans_lt hder⟩

end GC.MetricGeometry
