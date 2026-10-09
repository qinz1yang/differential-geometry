import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

private theorem projection_error_components
    (A : H →L[𝕜] H) (P : Submodule 𝕜 H) [P.HasOrthogonalProjection]
    {μ : 𝕜} {v : H} (heigen : A v = μ • v) :
    P.starProjection ((A - P.starProjection) v) = (μ - 1) • P.starProjection v ∧
      Pᗮ.starProjection ((A - P.starProjection) v) = μ • Pᗮ.starProjection v := by
  have hp : P.starProjection ((A - P.starProjection) v) = (μ - 1) • P.starProjection v := by
    simp only [sub_apply, heigen, map_sub, map_smul, sub_smul, one_smul]
    rw [Submodule.starProjection_eq_self_iff.mpr (P.starProjection_apply_mem v)]
  have hn : Pᗮ.starProjection ((A - P.starProjection) v) = μ • Pᗮ.starProjection v := by
    simp only [sub_apply, heigen, map_sub, map_smul]
    rw [Submodule.starProjection_orthogonal_apply_eq_zero (P.starProjection_apply_mem v), sub_zero]
  exact ⟨hp, hn⟩

theorem eigenvector_projection_error_bounds
    (A : H →L[𝕜] H) (P : Submodule 𝕜 H) [P.HasOrthogonalProjection]
    {ε : ℝ} {μ : 𝕜} (hclose : ‖A - P.starProjection‖ ≤ ε)
    {v : H} (heigen : A v = μ • v) :
    ‖μ - 1‖ * ‖P.starProjection v‖ ≤ ε * ‖v‖ ∧
      ‖μ‖ * ‖Pᗮ.starProjection v‖ ≤ ε * ‖v‖ := by
  have herr : ‖(A - P.starProjection) v‖ ≤ ε * ‖v‖ :=
    ((A - P.starProjection).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hclose (norm_nonneg v))
  obtain ⟨hp, hn⟩ := projection_error_components A P heigen
  constructor
  · have h := (P.norm_starProjection_apply_le ((A - P.starProjection) v)).trans herr
    rwa [hp, norm_smul] at h
  · have h := (Pᗮ.norm_starProjection_apply_le ((A - P.starProjection) v)).trans herr
    rwa [hn, norm_smul] at h

theorem min_norm_mul_norm_le_norm_smul_sub_starProjection
    (P : Submodule 𝕜 H) [P.HasOrthogonalProjection] (μ : 𝕜) (v : H) :
    min ‖μ‖ ‖μ - 1‖ * ‖v‖ ≤ ‖μ • v - P.starProjection v‖ := by
  have hc : 0 ≤ min ‖μ‖ ‖μ - 1‖ := le_min (norm_nonneg _) (norm_nonneg _)
  obtain ⟨hp, hn⟩ := projection_error_components (μ • ContinuousLinearMap.id 𝕜 H) P
    (v := v) (μ := μ) rfl
  have hdecomp := P.norm_sq_eq_add_norm_sq_starProjection (μ • v - P.starProjection v)
  change P.starProjection (μ • v - P.starProjection v) = _ at hp
  change Pᗮ.starProjection (μ • v - P.starProjection v) = _ at hn
  rw [hp, hn, norm_smul, norm_smul, mul_pow, mul_pow] at hdecomp
  have hvdecomp := P.norm_sq_eq_add_norm_sq_starProjection v
  have hc1 := sq_le_sq₀ hc (norm_nonneg μ) |>.mpr (min_le_left ‖μ‖ ‖μ - 1‖)
  have hc2 := sq_le_sq₀ hc (norm_nonneg (μ - 1)) |>.mpr (min_le_right ‖μ‖ ‖μ - 1‖)
  have h1 := mul_le_mul_of_nonneg_right hc1 (sq_nonneg ‖Pᗮ.starProjection v‖)
  have h2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg ‖P.starProjection v‖)
  apply (sq_le_sq₀ (mul_nonneg hc (norm_nonneg v)) (norm_nonneg _)).mp
  nlinarith

theorem norm_smul_sub_apply_ge_of_norm_sub_starProjection_le
    (A : H →L[𝕜] H) (P : Submodule 𝕜 H) [P.HasOrthogonalProjection]
    {ε : ℝ} (hclose : ‖A - P.starProjection‖ ≤ ε) (μ : 𝕜) (v : H) :
    (min ‖μ‖ ‖μ - 1‖ - ε) * ‖v‖ ≤ ‖μ • v - A v‖ := by
  have hl := min_norm_mul_norm_le_norm_smul_sub_starProjection P μ v
  have herr : ‖A v - P.starProjection v‖ ≤ ε * ‖v‖ :=
    ((A - P.starProjection).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hclose (norm_nonneg v))
  have ht := norm_sub_le_norm_sub_add_norm_sub (μ • v) (A v) (P.starProjection v)
  linarith

theorem norm_eigenvalue_or_sub_one_le_of_norm_sub_starProjection_le
    (A : H →L[𝕜] H) (P : Submodule 𝕜 H) [P.HasOrthogonalProjection]
    {ε : ℝ} {μ : 𝕜} (hclose : ‖A - P.starProjection‖ ≤ ε)
    (hμ : Module.End.HasEigenvalue A.toLinearMap μ) :
    ‖μ‖ ≤ ε ∨ ‖μ - 1‖ ≤ ε := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have heigen : A v = μ • v := hv.apply_eq_smul
  have hl := norm_smul_sub_apply_ge_of_norm_sub_starProjection_le A P hclose μ v
  rw [heigen, sub_self, norm_zero] at hl
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv.2
  have hmin : min ‖μ‖ ‖μ - 1‖ ≤ ε := by nlinarith
  exact min_le_iff.mp hmin

theorem spectrum_subset_closedBall_union_of_norm_sub_starProjection_le
    [FiniteDimensional 𝕜 H] (A : H →L[𝕜] H) (P : Submodule 𝕜 H)
    {ε : ℝ} (hclose : ‖A - P.starProjection‖ ≤ ε) :
    spectrum 𝕜 A ⊆ Metric.closedBall 0 ε ∪ Metric.closedBall 1 ε := by
  let : CompleteSpace H := FiniteDimensional.complete 𝕜 H
  intro μ hμ
  rw [ContinuousLinearMap.spectrum_eq] at hμ
  have h := norm_eigenvalue_or_sub_one_le_of_norm_sub_starProjection_le A P hclose
    (Module.End.HasEigenvalue.of_mem_spectrum hμ)
  simpa only [Set.mem_union, Metric.mem_closedBall, dist_eq_norm, sub_zero] using h

theorem norm_sub_spectrum_ge_of_norm_sub_starProjection_le
    [FiniteDimensional 𝕜 H] (A : H →L[𝕜] H) (P : Submodule 𝕜 H)
    {ε r : ℝ} (hclose : ‖A - P.starProjection‖ ≤ ε)
    {ζ μ : 𝕜} (hζ : ‖ζ - 1‖ = r) (hμ : μ ∈ spectrum 𝕜 A) :
    min r (1 - r) - ε ≤ ‖ζ - μ‖ := by
  have h := spectrum_subset_closedBall_union_of_norm_sub_starProjection_le A P hclose hμ
  simp only [Set.mem_union, Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  rcases h with h | h
  · have hζnorm := norm_sub_norm_le (1 : 𝕜) ζ
    rw [norm_one, norm_sub_rev, hζ] at hζnorm
    have hm := norm_sub_norm_le ζ μ
    linarith [min_le_right r (1 - r)]
  · have hm := norm_sub_norm_le (ζ - 1) (μ - 1)
    rw [hζ, sub_sub_sub_cancel_right] at hm
    linarith [min_le_left r (1 - r)]

end ContinuousLinearMap
