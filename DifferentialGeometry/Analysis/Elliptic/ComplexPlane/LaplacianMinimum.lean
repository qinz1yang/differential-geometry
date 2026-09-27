import DifferentialGeometry.Analysis.Elliptic.Euclidean.MaximumPrinciple
import Mathlib.Analysis.Complex.Basic



open Filter
open scoped Topology

namespace DifferentialGeometry.Analysis



theorem differential_laplacian_at_nonnegative_zero {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hn : ∀ᶠ q in 𝓝 z, 0 ≤ f q) (hz : f z = 0) :
    fderiv ℝ f z = 0 ∧ 0 ≤ Laplacian.laplacian f z := by
  have hm : IsLocalMin f z := by
    change ∀ᶠ q in 𝓝 z, f z ≤ f q
    simpa only [hz] using hn
  exact ⟨hm.fderiv_eq_zero, laplacian_nonneg_of_localMin hf hm⟩

end DifferentialGeometry.Analysis
