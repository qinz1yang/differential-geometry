import DifferentialGeometry.Interface.Sobolev
import DifferentialGeometry.Analysis.HeatEquation.Semigroup

/-!
# Public heat semigroup adapters

This file is a consumption-facing facade exposing the heat semigroup
`e^{t Δ_g}` on a closed Riemannian manifold under a single namespace,
together with friendly one-line adapters that accept a smooth scalar
function directly (instead of an `L²` element) and hide the L² lifting.

For scalars on a closed Riemannian manifold `(M, g)`:
- `heatFlow g t f hf` evolves the smooth scalar `f` for time `t ≥ 0`,
  returning the `Lp ℝ 2 μ_g` representative `e^{t Δ_g} (smoothScalarToLp g f hf)`.
- `heatFlow_zero` identifies the time-zero output with `smoothScalarToLp g f hf`.
- `heatFlow_norm_le` gives the L²-contraction bound for `t ≥ 0`.

The underlying primitives `heatSemigroup`, `heatSemigroup_zero`,
`heatSemigroup_add`, `heatSemigroup_opNorm_le_one`,
`heatSemigroup_isSelfAdjoint`, `heatSemigroup_continuous_at_zero` are
re-exported into the `DifferentialGeometry.Interface` namespace.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Interface

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.HeatEquation

/-- One-line adapter: apply the heat semigroup `e^{t Δ_g}` to a smooth real
scalar `f : M → ℝ`, returning the `Lp ℝ 2 μ_g` representative of the
evolved function. -/
noncomputable def heatFlow (g : SmoothRiemannianMetric I M) (t : ℝ)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  heatSemigroup (I := I) (M := M) g t
    (smoothScalarToLp (I := I) (M := M) g f hf)

set_option linter.unusedSectionVars false in
/-- At time `t = 0`, the smooth-scalar heat flow is the L² representative of
the input. -/
theorem heatFlow_zero (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    heatFlow (I := I) (M := M) g 0 f hf =
      smoothScalarToLp (I := I) (M := M) g f hf := by
  unfold heatFlow
  rw [heatSemigroup_zero (I := I) (M := M) g]
  rfl

set_option linter.unusedSectionVars false in
/-- L² contraction bound for the smooth-scalar heat flow at `t ≥ 0`:
`‖heatFlow g t f hf‖ ≤ ‖smoothScalarToLp g f hf‖`. -/
theorem heatFlow_norm_le {t : ℝ} (ht : 0 ≤ t) (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ‖heatFlow (I := I) (M := M) g t f hf‖ ≤
      ‖smoothScalarToLp (I := I) (M := M) g f hf‖ := by
  unfold heatFlow
  have h_op : ‖heatSemigroup (I := I) (M := M) g t‖ ≤ 1 :=
    heatSemigroup_opNorm_le_one (I := I) (M := M) g ht
  have h_apply :
      ‖heatSemigroup (I := I) (M := M) g t
          (smoothScalarToLp (I := I) (M := M) g f hf)‖ ≤
        ‖heatSemigroup (I := I) (M := M) g t‖ *
          ‖smoothScalarToLp (I := I) (M := M) g f hf‖ :=
    ContinuousLinearMap.le_opNorm _ _
  refine h_apply.trans ?_
  have h_norm_nn : 0 ≤ ‖smoothScalarToLp (I := I) (M := M) g f hf‖ := norm_nonneg _
  have h_mul := mul_le_mul_of_nonneg_right h_op h_norm_nn
  rw [one_mul] at h_mul
  exact h_mul

end Interface
end DifferentialGeometry

namespace DifferentialGeometry.Interface

export DifferentialGeometry.Analysis.HeatEquation
  (heatSemigroup heatSemigroup_zero heatSemigroup_add
   heatSemigroup_opNorm_le_one heatSemigroup_isSelfAdjoint
   heatSemigroup_continuous_at_zero)

end DifferentialGeometry.Interface

end
