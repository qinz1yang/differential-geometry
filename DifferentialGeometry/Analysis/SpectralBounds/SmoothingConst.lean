import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SmoothingHs

/-!
# Scalar smoothing constant for spectral analytic-semigroup bounds

This file is a thin namespace alias forwarding to the smoothing constant
and its scalar bound currently defined in the tensor heat-equation file
`DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SmoothingHs`.
The alias provides the canonical scalar-facing name for downstream
spectral consumers, decoupling them from the tensor namespace. Future
cleanup may move the original definitions here and have the tensor side
import from this file.

## Contents

* `spectralSmoothingConst μ` — the explicit smoothing constant
  `max 1 ((μ/2)^μ · exp(-μ) · exp 2)`.
* `one_le_spectralSmoothingConst`, `spectralSmoothingConst_pos`,
  `spectralSmoothingConst_nonneg` — positivity / lower-bound facts.
* `spectralSmoothingScalarBound` — the scalar smoothing inequality
  `(1 + λ)^μ · exp(-2λt) ≤ spectralSmoothingConst μ · t^{-μ}` for
  `μ ≥ 0`, `0 < t ≤ 1`, `λ ≥ 0`.
-/

noncomputable section

namespace DifferentialGeometry
namespace Analysis
namespace SpectralBounds

/-- The explicit scalar smoothing constant
`C(μ) = max 1 ((μ/2)^μ · e^{-μ} · e²)`. Alias of the tensor-side
constant. -/
noncomputable def spectralSmoothingConst (μ : ℝ) : ℝ :=
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSmoothingConst μ

/-- The smoothing constant is at least `1`. -/
lemma one_le_spectralSmoothingConst (μ : ℝ) : 1 ≤ spectralSmoothingConst μ :=
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.one_le_tensorSmoothingConst μ

/-- The smoothing constant is positive. -/
lemma spectralSmoothingConst_pos (μ : ℝ) : 0 < spectralSmoothingConst μ :=
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSmoothingConst_pos μ

/-- The smoothing constant is non-negative. -/
lemma spectralSmoothingConst_nonneg (μ : ℝ) : 0 ≤ spectralSmoothingConst μ :=
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSmoothingConst_nonneg μ

/-- **Scalar smoothing bound.** For `μ ≥ 0`, `0 < t ≤ 1`, and `λ ≥ 0`,

  `(1 + λ)^μ · exp(-2λt) ≤ spectralSmoothingConst μ · t^{-μ}`.

This is the one-variable estimate underlying the analytic-semigroup
smoothing of the heat semigroup on the spectral Sobolev scale. -/
theorem spectralSmoothingScalarBound {μ : ℝ} (hμ : 0 ≤ μ) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) {lam : ℝ} (hlam : 0 ≤ lam) :
    (1 + lam) ^ μ * Real.exp (-(2 * lam * t)) ≤
      spectralSmoothingConst μ * t ^ (-μ) :=
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSmoothingScalarBound
    hμ ht ht1 hlam

end SpectralBounds
end Analysis
end DifferentialGeometry

end

