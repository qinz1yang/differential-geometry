import DifferentialGeometry.Analysis.Spectral.FiniteDimensional.SmoothEigenpair
import DifferentialGeometry.Analysis.Spectral.FiniteDimensional.EigenvectorAxisEstimate
import DifferentialGeometry.Analysis.Spectral.FiniteDimensional.LeastEigenvalueGap

noncomputable section
open Set
open scoped ContDiff InnerProductSpace

namespace DifferentialGeometry.Analysis

theorem exists_smooth_least_eigenpair_of_axis_error
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : P → E →L[ℝ] E) {U : Set P} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    (hself : ∀ p ∈ U, IsSelfAdjoint (A p)) (v : P → E)
    (hv : ContinuousOn v U) (hunit : ∀ p ∈ U, ‖v p‖ = 1)
    {κ ε : ℝ} (hκ : 0 < κ) (hε : ε < κ / 2)
    (herror : ∀ p ∈ U, ∀ x : E,
      ‖A p x - κ • (x - ⟪v p, x⟫_ℝ • v p)‖ ≤ ε * ‖x‖)
    {p₀ : P} (hp₀ : p₀ ∈ U) :
    ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ V ⊆ U ∧
      ∃ (μ : P → ℝ) (w : P → E), ContDiffOn ℝ ∞ μ V ∧ ContDiffOn ℝ ∞ w V ∧
        ∀ p ∈ V, ‖w p‖ = 1 ∧ A p (w p) = μ p • w p ∧
          (∀ x : E, ‖x‖ = 1 → μ p ≤ ⟪A p x, x⟫_ℝ) ∧ |μ p| ≤ ε ∧
          0 < ⟪v p, w p⟫_ℝ ∧
          Module.End.eigenspace (A p).toLinearMap (μ p) = Submodule.span ℝ {w p} := by
  obtain ⟨μ₀, w₀, hw₀, heigen₀, _, hμ₀, hpos₀, _, hsimple₀⟩ :=
    exists_least_eigenvector_close_to_axis (A p₀) (hself p₀ hp₀) (v p₀)
      (hunit p₀ hp₀) hκ hε (herror p₀ hp₀)
  obtain ⟨V, hV, hpV, hVU, μ, w, hμ, hw, heqμ, heqw, heigen⟩ :=
    exists_smooth_eigenpair_near_simple A hU hA hp₀ (hself p₀ hp₀)
      μ₀ w₀ hw₀ heigen₀ hsimple₀
  let W := (V ∩ μ ⁻¹' Iio (κ - ε)) ∩
    (V ∩ (fun p ↦ ⟪v p, w p⟫_ℝ) ⁻¹' Ioi 0)
  have hW : IsOpen W :=
    (hμ.continuousOn.isOpen_inter_preimage hV isOpen_Iio).inter
      (((hv.mono hVU).inner hw.continuousOn).isOpen_inter_preimage hV isOpen_Ioi)
  have hpW : p₀ ∈ W := by
    refine ⟨⟨hpV, ?_⟩, hpV, ?_⟩
    · change μ p₀ < κ - ε
      rw [heqμ]
      have hh := le_abs_self μ₀
      linarith
    · change 0 < ⟪v p₀, w p₀⟫_ℝ
      rwa [heqw]
  have hWV : W ⊆ V := fun _ hp ↦ hp.1.1
  refine ⟨W, hW, hpW, hWV.trans hVU, μ, w, hμ.mono hWV, hw.mono hWV, ?_⟩
  intro p hp
  have hpU := hVU (hWV hp)
  obtain ⟨hnorm, hroot⟩ := heigen p (hWV hp)
  have hmin := is_least_eigenvalue_of_axis_error (A p) (hself p hpU) (v p)
    (herror p hpU) (w p) hnorm hroot hp.1.2
  have habs := abs_least_eigenvalue_le_axis_error (A p) (v p) (hunit p hpU)
    hκ.le (herror p hpU) (w p) hnorm hroot hmin
  refine ⟨hnorm, hroot, hmin, habs, hp.2.2, ?_⟩
  apply eigenspace_eq_span_of_axis_error (A p) (v p) hκ (herror p hpU)
    (by linarith) (w p) _ hroot
  intro hz
  simp [hz] at hnorm

end DifferentialGeometry.Analysis
