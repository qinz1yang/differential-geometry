import DifferentialGeometry.Geometry.Comparison.Variation.Coordinates.FixedChartIdentities
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open Set Filter Function
open scoped Topology Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem exists_smooth_variation_fixed_initial_germ
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f)
    {c b : ℝ} (hcb : c < b) :
    ∃ F : ℝ → ℝ → M,
      IsSmoothVariation (I := I) F ∧
      F 0 = f 0 ∧
      (∀ u, F u =ᶠ[𝓝 c] f 0) ∧
      (∀ u, F u b = f u b) := by
  obtain ⟨chi, hchi, _hcpt, hone, hsupp, _hrange⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact
      (K := ({b} : Set ℝ)) isCompact_singleton (U := Ioi ((c + b) / 2))
      isOpen_Ioi (by intro t ht; rw [mem_singleton_iff] at ht; subst t; change (c + b) / 2 < b; linarith)
  have hchib : chi b = 1 := by
    have hb : chi =ᶠ[𝓝 b] 1 := by simpa only [nhdsSet_singleton] using hone
    exact hb.self_of_nhds
  have hzero : chi =ᶠ[𝓝 c] 0 := by
    filter_upwards [Iio_mem_nhds (by linarith : c < (c + b) / 2)] with s hs
    apply notMem_support.mp
    intro hmem
    have hx := hsupp (subset_closure hmem)
    exact (not_lt_of_ge hs.le) (show (c + b) / 2 < s from hx)
  let F : ℝ → ℝ → M := fun u s ↦ f (chi s * u) s
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · have hchiM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (8 : ℕ) chi :=
      hchi.contMDiff.of_le (by
        change ((8 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
    exact hf.comp (((hchiM.comp contMDiff_snd).mul contMDiff_fst).prodMk contMDiff_snd)
  · funext s
    simp only [F, mul_zero]
  · intro u
    filter_upwards [hzero] with s hs
    simp only [F, hs, Pi.zero_apply, zero_mul]
  · intro u
    simp only [F, hchib, one_mul]

end DifferentialGeometry.Geometry.Riemannian.Variation
