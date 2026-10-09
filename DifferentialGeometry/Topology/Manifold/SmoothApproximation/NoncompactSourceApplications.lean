import DifferentialGeometry.Topology.Manifold.SmoothApproximation.NoncompactSource

/-!
# Consumer of the noncompact-source approximation (LFR48 T1)

`exists_pointed_smooth_approx_near_Icc`: a `C²` function on the NONCOMPACT line is approximated near
`[0, 1]` by functions smooth on a fixed open neighbourhood, all taking the value `f 0` at `0`, uniformly
on that neighbourhood and in `C²` on every compact subset of it (identity charts).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

/-- Pointed smooth approximation of a `C²` function on `ℝ` near `[0, 1]`. -/
theorem exists_pointed_smooth_approx_near_Icc {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((2 : ℕ) : ℕ∞) f) :
    ∃ W : Set ℝ, IsOpen W ∧ Icc (0 : ℝ) 1 ⊆ W ∧ ∃ fs : ℕ → ℝ → ℝ,
      (∀ j, ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fs j) W) ∧ (∀ j, fs j 0 = f 0) ∧
      TendstoUniformlyOn fs f atTop W ∧
      ∀ K : Set ℝ, IsCompact K → K ⊆ W → MapCPConvergenceOn K 2 fs f := by
  obtain ⟨W, hW, hCW, -, fs, hsm, hpt, hun, hchart⟩ :=
    exists_smooth_seq_chart_tendsto_near_isCompact (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)) 2
      isOpen_univ hf.contMDiff.contMDiffOn isCompact_Icc (subset_univ _)
      (left_mem_Icc.mpr zero_le_one)
  refine ⟨W, hW, hCW, fs, hsm, hpt, hun, fun K hK hKW => ?_⟩
  have h := (hchart 0 0 K hK (fun y hy => ⟨by simp, by simpa using hKW hy⟩)
    (fun y _ => by simp)).2
  simpa using h

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
