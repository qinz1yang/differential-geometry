import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Scalar
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.EnergyEstimates.MildSolutionBound

/-!
# Short-time existence with a-priori `Hˢ`-norm bound

This file packages the short-time existence theorem for the quasi-linear
scalar heat equation together with the a-priori `Hˢ`-norm bound for the
continuous mild solution produced by the existence theorem. Given a
closed Riemannian manifold `(M, g)`, a Sobolev exponent `σ`, an initial
datum `u₀`, and a globally Lipschitz lower-order nonlinearity `N`, the
combined statement asserts the existence of a positive existence time
`T`, a continuous path `u : [0, T] → Hˢ` solving the Duhamel mild-form
equation, and the pointwise norm estimate
`‖u t‖ ≤ (‖u₀‖ + ‖N 0‖ · t) · exp(L · t)` on `[0, T]`.

The proof is a direct refinement: invoke
`scalar_quasilinear_local_existence` to obtain a mild solution, then
apply `mild_solution_norm_le` to that solution to extract the norm
bound. The integer-Sobolev version is a one-line `:=` specialisation
at `σ = (k : ℝ)`.

## Main results

* `scalar_quasilinear_local_existence_with_norm_bound` — short-time
  existence of a continuous mild solution to the quasi-linear scalar
  heat equation on the spectral `Hˢ`-scale, packaged with the a-priori
  `Hˢ`-norm bound.
* `scalar_quasilinear_local_existence_with_Hk_bound` — integer-exponent
  specialisation on `HkScalar g k = scalarHs g (k : ℝ)`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff BigOperators NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear
namespace EnergyEstimates

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Hk
open DifferentialGeometry.Analysis.Laplacian.Spectral
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Short-time existence of a mild solution of the quasi-linear scalar
heat equation on the spectral `Hˢ`-scale, with a-priori `Hˢ`-norm bound.**

For a closed Riemannian manifold `(M, g)`, a Sobolev exponent `σ`, an
initial datum `u₀ : scalarHs g σ`, and a globally Lipschitz nonlinearity
`N : scalarHs g σ → scalarHs g σ`, there is a positive existence time
`T` and a continuous path `u : [0, T] → scalarHs g σ` solving the
Duhamel mild-form equation `u(t) = e^{t Δ_g} u₀ + ∫₀ᵗ e^{(t-τ) Δ_g}(N(u τ)) dτ`
with `u(0) = u₀`, satisfying the pointwise norm bound
`‖u t‖ ≤ (‖u₀‖ + ‖N 0‖ · t) · exp(L · t)` on `[0, T]`. -/
theorem scalar_quasilinear_local_existence_with_norm_bound
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (u₀ : scalarHs (I := I) (M := M) g σ)
    {N : scalarHs (I := I) (M := M) g σ → scalarHs (I := I) (M := M) g σ}
    {L : ℝ≥0} (hN : LipschitzWith L N) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → scalarHs (I := I) (M := M) g σ,
      ContinuousOn u (Set.Icc 0 T) ∧
      u 0 = u₀ ∧
      (∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatSemigroupHkExt (I := I) (M := M) g σ t u₀ +
          ∫ τ in (0:ℝ)..t,
            heatSemigroupHkExt (I := I) (M := M) g σ (t - τ) (N (u τ))) ∧
      (∀ t ∈ Set.Icc (0:ℝ) T,
        ‖u t‖ ≤ (‖u₀‖ + ‖N 0‖ * t) * Real.exp ((L : ℝ) * t)) := by
  obtain ⟨T, hT_pos, u, hu_cont, hu_zero, hu_eq⟩ :=
    scalar_quasilinear_local_existence (I := I) (M := M) g σ u₀ hN
  refine ⟨T, hT_pos, u, hu_cont, hu_zero, hu_eq, ?_⟩
  exact mild_solution_norm_le (I := I) (M := M) (g := g) (σ := σ) u₀ hN
    hT_pos.le hu_cont hu_eq

/-- **Short-time existence of a mild solution of the quasi-linear scalar
heat equation on the integer Sobolev scale `Hᵏ`, with a-priori
`Hᵏ`-norm bound.**

The integer-exponent specialisation of
`scalar_quasilinear_local_existence_with_norm_bound`. -/
theorem scalar_quasilinear_local_existence_with_Hk_bound
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    (u₀ : HkScalar (I := I) (M := M) g k)
    {N : HkScalar (I := I) (M := M) g k → HkScalar (I := I) (M := M) g k}
    {L : ℝ≥0} (hN : LipschitzWith L N) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → HkScalar (I := I) (M := M) g k,
      ContinuousOn u (Set.Icc 0 T) ∧
      u 0 = u₀ ∧
      (∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatSemigroupHkExt (I := I) (M := M) g (k : ℝ) t u₀ +
          ∫ τ in (0:ℝ)..t,
            heatSemigroupHkExt (I := I) (M := M) g (k : ℝ) (t - τ) (N (u τ))) ∧
      (∀ t ∈ Set.Icc (0:ℝ) T,
        ‖u t‖ ≤ (‖u₀‖ + ‖N 0‖ * t) * Real.exp ((L : ℝ) * t)) :=
  scalar_quasilinear_local_existence_with_norm_bound (I := I) (M := M) g
    (k : ℝ) u₀ hN

end EnergyEstimates
end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
