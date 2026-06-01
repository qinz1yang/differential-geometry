import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Resolvent
import Mathlib.Analysis.Normed.Operator.Compact

/-!
# Tensor Rellich-Kondrachov compactness: chart-frame component reduction

For a closed Riemannian manifold `(M, g)`, the natural inclusion
`TensorH1ComplToTensorL2 g r s : TensorH1Compl g r s →L[ℝ] TensorL2 r s g`
is a compact operator. Composing on the right with the bounded resolvent
`tensorResolvent g r s` yields a compact operator
`tensorResolventL2 g r s : TensorL2 r s g →L[ℝ] TensorL2 r s g`.

This file installs the *compositional reduction* of the L²-side compactness
from the H¹→L² compactness, which is the trivial half of the argument:
postcomposing a continuous linear map with a compact operator yields a
compact operator. Combined with the H¹→L² compactness, this yields the
L²-side compactness as a direct corollary.

The H¹→L² compactness itself is proved by chart-frame component reduction:
a tensor section is decomposed in each chart's frame into finitely many
scalar component functions, each of which lies in a chart-Sobolev space.
The scalar Rellich-Kondrachov subsequence-extraction theorem
(`Analysis/Sobolev/Manifold/RellichOnM.lean::rellich_kondrachov_chart_seq`)
extracts an L² convergent subsequence for each (chart, multi-index) pair.
A finite diagonal extraction over the finite atlas × finite multi-index
set yields a single subsequence, and a partition-of-unity reassembly
yields a tensor L²-convergent subsequence.

The chart-frame component infrastructure used in the reduction is built
in subsequent files. The present file isolates the
trivial compositional reduction step so that downstream consumers
(eigenbasis construction, discrete spectrum) can be wired to the L²-side
resolvent as soon as the H¹→L² compactness is in place.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The L²-side tensor resolvent factors as the composition of the
bounded tensor resolvent into `TensorH1Compl` followed by the
H¹ → L² inclusion. -/
lemma tensorResolventL2_eq_comp (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    tensorResolventL2 (I := I) (M := M) g r s =
      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s).comp
        (tensorResolvent (I := I) (M := M) g r s) := rfl

/-- The L²-side tensor resolvent as a function is the composition of the
underlying functions of the H¹ → L² inclusion and the bounded resolvent. -/
lemma tensorResolventL2_apply_eq_comp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (f : TensorL2 r s g) :
    (tensorResolventL2 (I := I) (M := M) g r s) f =
      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)
        ((tensorResolvent (I := I) (M := M) g r s) f) := rfl

/-- **Compositional compactness**: if the H¹ → L² inclusion is a compact
operator, then the L²-side tensor resolvent is a compact operator.

The L²-side resolvent factors as `TensorH1ComplToTensorL2 ∘ tensorResolvent`,
and postcomposing a continuous linear map with a compact operator yields a
compact operator. -/
theorem tensorResolventL2_isCompactOperator_of_isCompactOperator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_H1L2 :
      IsCompactOperator
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) := by
  have h_comp : IsCompactOperator
      ((fun v : TensorH1Compl g r s =>
          TensorH1ComplToTensorL2 (I := I) (M := M) g r s v) ∘
        (fun f : TensorL2 r s g =>
          tensorResolvent (I := I) (M := M) g r s f)) :=
    h_H1L2.comp_clm (tensorResolvent (I := I) (M := M) g r s)
  exact h_comp

/-- Companion phrasing: the *self-adjoint* compact L²-side resolvent
predicate. The self-adjointness is already established in
`Resolvent.lean::tensorResolventL2_isSelfAdjoint`; combining with the
compactness predicate gives the precise hypothesis needed for the
compact self-adjoint spectral theorem on the L² Hilbert space. -/
theorem tensorResolventL2_isCompactOperator_and_isSelfAdjoint
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_H1L2 :
      IsCompactOperator
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) ∧
      IsSelfAdjoint (tensorResolventL2 (I := I) (M := M) g r s) :=
  ⟨tensorResolventL2_isCompactOperator_of_isCompactOperator
    (I := I) (M := M) g r s h_H1L2,
   tensorResolventL2_isSelfAdjoint (I := I) (M := M) g r s⟩

example (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h : IsCompactOperator (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) :=
  tensorResolventL2_isCompactOperator_of_isCompactOperator
    (I := I) (M := M) g r s h

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
