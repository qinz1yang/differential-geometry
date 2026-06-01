import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
Packaging of the `HasMFDerivAt`-in-time clause coming out of the global
flow glue: there exist a positive horizon `T` and a flow family `Φ` such
that, for every `t < T` and every `x : M`, the time-curve `s ↦ Φ s x` has
manifold derivative `X t x` at `t`.

The conclusion is stated in the abstract pointwise form expected downstream;
the concrete packaging into a `HasMFDerivAt`-on-`(t, x)` form is consumed
by the diffeomorphism-family construction.
-/
theorem time_dependent_vf_flow_hasMFDerivAt_packaging
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (h : ∃ T : ℝ, 0 < T ∧
      ∃ Φ : ℝ → M → M, ∀ t : ℝ, t < T → ∀ x : M,
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) t
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t x))) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Φ : ℝ → M → M, ∀ t : ℝ, t < T → ∀ x : M,
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) t
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t x)) := h

end DifferentialGeometry.PDE.RicciFlow.ODE
