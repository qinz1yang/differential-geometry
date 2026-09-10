import DifferentialGeometry.Topology.Manifold.Interval.CompressionInverse

open Set Function Manifold
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.Interval

theorem exists_smooth_compression {ε r : ℝ} [Fact ((0 : ℝ) < ε)]
    (hr : 0 < r) (hrε : 2 * r ≤ ε) :
    ∃ a : ℝ, 0 < a ∧ a < r ∧
      ∃ σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε),
        ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ σ ∧ StrictMono σ ∧
        range σ = {t : Icc (0 : ℝ) ε | a ≤ t.val} ∧
        (∀ t : Icc (0 : ℝ) ε, t.val ≤ r → (σ t).val = t.val + a) ∧
        ∀ t : Icc (0 : ℝ) ε, 2 * r ≤ t.val → σ t = t := by
  obtain ⟨a, ha, har, σ, _, _, hs, hm, hrange, hnear, hfix⟩ :=
    exists_smooth_compression_with_diffeomorph hr hrε
  exact ⟨a, ha, har, σ, hs, hm, hrange, hnear, hfix⟩

end Poincare.Manifold.Interval
