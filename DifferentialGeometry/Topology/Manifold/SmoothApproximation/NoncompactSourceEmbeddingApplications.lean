import DifferentialGeometry.Topology.Manifold.SmoothApproximation.NoncompactSourceEmbedding

/-!
# Consumer of the smooth partial-diffeomorphism upgrade (LFR48 T2)

`exists_pointed_smooth_partialDiffeomorph_near_Icc`: a `C²` diffeomorphism of the NONCOMPACT line
is approximated near `[0, 1]` by maps fixing the value at `0`, converging uniformly near `[0, 1]`,
which are eventually SMOOTH partial diffeomorphisms on one fixed open neighbourhood of `[0, 1]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

/-- Pointed smooth partial diffeomorphisms near `[0, 1]` approximating a `C²` diffeomorphism of
`ℝ`. -/
theorem exists_pointed_smooth_partialDiffeomorph_near_Icc
    (f : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ((2 : ℕ) : ℕ∞ω)) :
    ∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ∃ fs : ℕ → ℝ → ℝ,
      (∀ n, fs n 0 = f 0) ∧ TendstoUniformlyOn fs f atTop O ∧
      ∀ᶠ n in atTop, ∃ d : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
        d.source = O ∧ (d : ℝ → ℝ) = fs n := by
  obtain ⟨O, hO, hCO, -, -, fs, -, hpt, hun, -, hev⟩ :=
    exists_smooth_partialDiffeomorph_seq_near_isCompact (by norm_num) f.toPartialDiffeomorph
      isCompact_Icc (fun x _ => mem_univ x) (left_mem_Icc.mpr zero_le_one)
  refine ⟨O, hO, hCO, fs, hpt, hun.mono subset_closure, ?_⟩
  filter_upwards [hev] with n hn
  obtain ⟨d, hd, -, hdf⟩ := hn
  exact ⟨d, hd, hdf⟩

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
