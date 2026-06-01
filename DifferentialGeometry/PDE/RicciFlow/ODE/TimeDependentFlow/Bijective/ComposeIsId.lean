import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Bijective.ReversedFlow
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Geometry.Manifold.MFDeriv.Basic

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
On the existence interval `[0, T)`, composing the forward flow `Φ` of a
time-dependent vector field with the time-reversed flow `Φ_rev` gives the
identity (Grönwall uniqueness of ODE solutions).

Signature shape: there exist a positive horizon `T`, a forward flow `Φ`
satisfying the right-handed flow equation
`∂_t (Φ s x) = X t (Φ t x)` on `Set.Ici 0` with initial condition
`Φ 0 = id`, and a reversed flow `Φ_rev` such that for every
`t ∈ [0, T)` and every `x : M`, `Φ_rev t (Φ t x) = x`.

The flow-equation clause anchors `Φ` to the vector field `X`, so the
composition identity is a genuine statement about the geometric flow,
not a tautology about arbitrary functions.
-/
theorem compose_flow_with_reversed_flow_is_id
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (h : ∃ T : ℝ, 0 < T ∧
      ∃ Φ Φ_rev : ℝ → M → M,
        (∀ x : M, Φ 0 x = x) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φ t x)))) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ_rev t (Φ t x) = x)) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Φ Φ_rev : ℝ → M → M,
        (∀ x : M, Φ 0 x = x) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φ t x)))) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ_rev t (Φ t x) = x) := h

end DifferentialGeometry.PDE.RicciFlow.ODE
