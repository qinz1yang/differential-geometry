import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Existence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.ScalarInstance

/-!
# Quasi-linear scalar heat equation on the spectral Sobolev scale

For a closed Riemannian manifold `(M, g)` and a spectral Sobolev exponent
`σ`, the extended scalar heat semigroup `e^{t Δ_g}` on `scalarHs g σ` is
a bounded strongly continuous one-parameter contraction semigroup
(packaged as `scalarHsBoundedC0Semigroup g σ`). Feeding this into the
abstract semilinear existence/uniqueness machinery yields a short-time
mild solution of the **quasi-linear** scalar heat equation

  `∂_t u = Δ_g u + N(u)`,  `u(0) = u_0`,

for a globally Lipschitz lower-order nonlinearity
`N : scalarHs g σ → scalarHs g σ`.

## Main results

* `scalar_quasilinear_local_existence` — short-time existence of a
  continuous mild solution of the quasi-linear scalar heat equation on
  the spectral `Hˢ`-scale.
* `scalar_quasilinear_local_unique` — uniqueness of the mild solution
  on a short time interval.
* `scalar_quasilinear_local_existence_Hk` — integer-exponent
  specialisation on `HkScalar g k = scalarHs g (k : ℝ)`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Hs
open DifferentialGeometry.Analysis.Laplacian.Spectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Short-time existence of a mild solution of the quasi-linear scalar
heat equation on the spectral `Hˢ`-scale.**

For a closed Riemannian manifold `(M, g)`, a spectral Sobolev exponent
`σ`, an initial datum `u₀ : scalarHs g σ`, and a globally Lipschitz
lower-order nonlinearity `N`, there is a positive existence time `T`
and a continuous path `u : [0, T] → scalarHs g σ` solving the Duhamel
integral equation

  `u(t) = e^{t Δ_g} u₀ + ∫₀ᵗ e^{(t-τ) Δ_g} (N (u τ)) dτ`

with `u(0) = u₀`. -/
theorem scalar_quasilinear_local_existence
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (u₀ : scalarHs (I := I) (M := M) g σ)
    {N : scalarHs (I := I) (M := M) g σ → scalarHs (I := I) (M := M) g σ}
    {L : ℝ≥0} (hN : LipschitzWith L N) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → scalarHs (I := I) (M := M) g σ,
      ContinuousOn u (Set.Icc 0 T) ∧
      u 0 = u₀ ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatSemigroupHsExt (I := I) (M := M) g σ t u₀ +
          ∫ τ in (0:ℝ)..t,
            heatSemigroupHsExt (I := I) (M := M) g σ (t - τ) (N (u τ)) := by
  obtain ⟨T, hT_pos, u, hu_cont, hu_zero, hu_eq⟩ :=
    semilinear_mild_solution_existence
      (scalarHsBoundedC0Semigroup (I := I) (M := M) g σ) u₀ hN
  refine ⟨T, hT_pos, u, hu_cont, hu_zero, ?_⟩
  intro t ht
  have h := hu_eq t ht
  simpa only [scalarHsBoundedC0Semigroup_apply] using h

/-- **Uniqueness of the mild solution of the quasi-linear scalar heat
equation on the spectral `Hˢ`-scale.**

Any two continuous paths `u, v : [0, T] → scalarHs g σ` solving the
quasi-linear scalar heat Duhamel integral equation with the same
initial datum `u₀` coincide on `[0, T]`, provided `(L : ℝ) * T < 1`. -/
theorem scalar_quasilinear_local_unique
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (u₀ : scalarHs (I := I) (M := M) g σ)
    {N : scalarHs (I := I) (M := M) g σ → scalarHs (I := I) (M := M) g σ}
    {L : ℝ≥0} (hN : LipschitzWith L N)
    {T : ℝ} (hT : 0 < T) (hTL : (L : ℝ) * T < 1)
    {u v : ℝ → scalarHs (I := I) (M := M) g σ}
    (hu : ContinuousOn u (Set.Icc 0 T)) (hv : ContinuousOn v (Set.Icc 0 T))
    (hu_eq : ∀ t ∈ Set.Icc (0:ℝ) T,
      u t = heatSemigroupHsExt (I := I) (M := M) g σ t u₀ +
        ∫ τ in (0:ℝ)..t,
          heatSemigroupHsExt (I := I) (M := M) g σ (t - τ) (N (u τ)))
    (hv_eq : ∀ t ∈ Set.Icc (0:ℝ) T,
      v t = heatSemigroupHsExt (I := I) (M := M) g σ t u₀ +
        ∫ τ in (0:ℝ)..t,
          heatSemigroupHsExt (I := I) (M := M) g σ (t - τ) (N (v τ))) :
    Set.EqOn u v (Set.Icc 0 T) := by
  refine semilinear_mild_solution_unique
    (scalarHsBoundedC0Semigroup (I := I) (M := M) g σ) u₀ hN
    hT hTL hu hv ?_ ?_
  · intro t ht
    simpa only [scalarHsBoundedC0Semigroup_apply] using hu_eq t ht
  · intro t ht
    simpa only [scalarHsBoundedC0Semigroup_apply] using hv_eq t ht

/-- **Short-time existence of a mild solution of the quasi-linear scalar
heat equation on the integer Sobolev scale `Hᵏ`.**

The integer-exponent specialisation of `scalar_quasilinear_local_existence`. -/
theorem scalar_quasilinear_local_existence_Hk
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    (u₀ : HkScalar (I := I) (M := M) g k)
    {N : HkScalar (I := I) (M := M) g k → HkScalar (I := I) (M := M) g k}
    {L : ℝ≥0} (hN : LipschitzWith L N) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → HkScalar (I := I) (M := M) g k,
      ContinuousOn u (Set.Icc 0 T) ∧
      u 0 = u₀ ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatSemigroupHsExt (I := I) (M := M) g (k : ℝ) t u₀ +
          ∫ τ in (0:ℝ)..t,
            heatSemigroupHsExt (I := I) (M := M) g (k : ℝ) (t - τ) (N (u τ)) :=
  scalar_quasilinear_local_existence (I := I) (M := M) g (k : ℝ) u₀ hN

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
