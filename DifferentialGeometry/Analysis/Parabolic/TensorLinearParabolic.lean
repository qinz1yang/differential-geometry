import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SemigroupTimeRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Duhamel mild solution of the inhomogeneous tensor heat equation on `L²`

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, given an initial
datum `T_0 : TensorL2 r s g` and a continuous forcing term
`F : ℝ → TensorL2 r s g`, the **Duhamel mild solution** of the
inhomogeneous tensor heat equation `∂_t T = Δ_∇ T + F`, `T(0) = T_0`, is

  `T(t) := e^{tΔ_∇} T_0 + ∫_0^t e^{(t-τ)Δ_∇} (F τ) dτ`,

where the second summand is a Bochner-valued interval integral on `[0, t]`.

This file provides the file-local measure-theoretic scaffolding for that
construction.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

end Parabolic
end Analysis
end DifferentialGeometry

end
