import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.CompactInclusionIntrinsic
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Rellich.Tensor
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Resolvent

/-!
# Compactness and self-adjointness of the L²-side tensor resolvent (chart-locality-free)

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, this file
establishes — without any auxiliary chart-selection hypothesis — that the
L²-side variational tensor resolvent

  `tensorResolventL2 g r s : TensorL2 r s g →L[ℝ] TensorL2 r s g`

is simultaneously a compact operator and self-adjoint.

The L²-side resolvent factors as
`tensorResolventL2 g r s = TensorH1ComplToTensorL2 g r s ∘ tensorResolvent g r s`,
where `tensorResolvent` is the bounded resolvent `TensorL2 → TensorH1Compl`
and `TensorH1ComplToTensorL2` is the bounded H¹ → L² inclusion. The two
analytic ingredients are:

* **Compactness of the H¹ → L² inclusion (chart-locality-free)** —
  `tensorH1ComplToTensorL2_isCompactOperator_intrinsic`, whose uniform
  component-wise chart-Sobolev bound is supplied unconditionally by the
  intrinsic Hebey block (no `HasLocallyConstantChartAt` hypothesis).

* **The compositional reduction** —
  `tensorResolventL2_isCompactOperator_of_isCompactOperator`: postcomposing
  the bounded `tensorResolvent` with the compact inclusion yields the compact
  L²-side resolvent.

Self-adjointness is already unconditional
(`tensorResolventL2_isSelfAdjoint`, from the symmetry of the H¹ inner
product). The headline `tensorResolventL2_isCompactOperator`
produces exactly the `IsCompactOperator (tensorResolventL2 g r s)` predicate
consumed by the resolvent eigenbasis construction
(`tensorResolventHilbertEigenbasisSigma`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Compactness of the L²-side tensor resolvent (chart-locality-free).**
For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, the L²-side
variational tensor resolvent
`tensorResolventL2 g r s : TensorL2 r s g →L[ℝ] TensorL2 r s g`
is a compact operator. No chart-selection hypothesis is required.

The proof combines:
* `tensorH1ComplToTensorL2_isCompactOperator_intrinsic`: the unconditional
  compactness of the H¹ → L² tensor inclusion;
* `tensorResolventL2_isCompactOperator_of_isCompactOperator`: the
  compositional reduction deriving L²-side compactness from H¹ → L²
  compactness via the factorisation
  `tensorResolventL2 = TensorH1ComplToTensorL2 ∘L tensorResolvent`. -/
theorem tensorResolventL2_isCompactOperator
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) :=
  tensorResolventL2_isCompactOperator_of_isCompactOperator
    (I := I) (M := M) g r s
    (tensorH1ComplToTensorL2_isCompactOperator_intrinsic
      (I := I) (M := M) g r s)

/-- The L²-side tensor resolvent `tensorResolventL2 g r s` on a closed
Riemannian manifold is both a compact operator and self-adjoint, with no
chart-selection hypothesis. Compactness is `tensorResolventL2_isCompactOperator`
and self-adjointness is `tensorResolventL2_isSelfAdjoint`. -/
theorem tensorResolventL2_isCompactOperator_isSelfAdjoint_intrinsic
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) ∧
      IsSelfAdjoint (tensorResolventL2 (I := I) (M := M) g r s) :=
  ⟨tensorResolventL2_isCompactOperator (I := I) (M := M) g r s,
   tensorResolventL2_isSelfAdjoint (I := I) (M := M) g r s⟩

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) :=
  tensorResolventL2_isCompactOperator (I := I) (M := M) g r s

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
