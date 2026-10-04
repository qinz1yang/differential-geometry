import DifferentialGeometry.Topology.Manifold.SmoothApproximation.SourceChartConvergence

/-!
# Consumer of the source-chart reading of the approximations (LFR48 T2b)

`exists_pointed_smooth_seq_symm_comp_tendsto_id_near_Icc`: for a `C²` diffeomorphism `f` of the
NONCOMPACT line there are maps `fs n`, smooth near `[0, 1]` and fixing the value at `0`, with
`f⁻¹ ∘ fs n → id` in `C²` on `[0, 1]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

/-- Smooth pointed approximations of a `C²` diffeomorphism of `ℝ` near `[0, 1]`, read through
`f⁻¹`. -/
theorem exists_pointed_smooth_seq_symm_comp_tendsto_id_near_Icc
    (f : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ((2 : ℕ) : ℕ∞ω)) :
    ∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ∃ fs : ℕ → ℝ → ℝ,
      (∀ n, ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fs n) O) ∧ (∀ n, fs n 0 = f 0) ∧
      MapCPConvergenceOn (Icc 0 1) 2 (fun n y => f.symm (fs n y)) id := by
  obtain ⟨O, hO, hCO, -, hOj, fs, hsm, hpt, -, hconv, -⟩ :=
    exists_smooth_partialDiffeomorph_seq_near_isCompact (by norm_num) f.toPartialDiffeomorph
      isCompact_Icc (fun x _ => mem_univ x) (left_mem_Icc.mpr zero_le_one)
  have h := (eventually_mapsTo_and_mapCPConvergenceOn_chart_symm_comp le_rfl
    f.toPartialDiffeomorph hO (subset_closure.trans hOj)
    (fun n => (hsm n).of_le (WithTop.coe_le_coe.mpr le_top))
    (fun p q K hK hKO hKm => hconv p q K hK
      (fun y hy => ⟨(hKO hy).1, subset_closure (hKO hy).2⟩) hKm)
    (0 : ℝ) isCompact_Icc (fun y hy => ⟨by simp, by simpa using hCO hy⟩)).2
  refine ⟨O, hO, hCO, fs, hsm, hpt, ?_⟩
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, PartialEquiv.refl_symm,
    id_eq] at h
  exact h

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
