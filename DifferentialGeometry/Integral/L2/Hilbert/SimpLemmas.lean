import DifferentialGeometry.Integral.L2.Hilbert.Defs
import DifferentialGeometry.Integral.L2.Hilbert.Inherited
import DifferentialGeometry.Integral.L2.Hilbert.DenseSubset
import DifferentialGeometry.Integral.L2.SmoothSections.Defs
import DifferentialGeometry.Integral.L2.SmoothSections.PreHilbert
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion

/-!
# `simp` lemmas bridging `toL2` with the algebraic structure

The canonical embedding
`SmoothCcTensor.toL2 : SmoothCcTensor g r s →L[ℝ] TensorL2 r s g` is a
continuous linear map and therefore commutes with the standard
algebraic operations on both sides: zero, addition, negation,
subtraction, and real scalar multiplication.

This file collects these basic compatibilities as `@[simp]` lemmas,
allowing downstream `simp`-based proofs to rewrite expressions
involving `toL2` directly into the corresponding algebraic
combinations on the `L²` side, without going through the generic
`ContinuousLinearMap.map_*` API.

Each lemma is a one-liner deduced from the fact that `toL2` is a
continuous linear map.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace SmoothCcTensor

section SimpLemmas

variable [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

set_option linter.unusedSectionVars false in
/-- The embedding `toL2` sends the zero section to the zero element of
`TensorL2 r s g`. -/
@[simp] theorem toL2_zero :
    (toL2 (g := g) (r := r) (s := s)) 0 = 0 :=
  ContinuousLinearMap.map_zero _

set_option linter.unusedSectionVars false in
/-- The embedding `toL2` is additive: it sends the sum of two
compactly-supported smooth sections to the sum of their images in the
`L²` Hilbert space. -/
@[simp] theorem toL2_add (S T : SmoothCcTensor g r s) :
    (toL2 (g := g) (r := r) (s := s)) (S + T) =
      (toL2 (g := g) (r := r) (s := s)) S +
        (toL2 (g := g) (r := r) (s := s)) T :=
  ContinuousLinearMap.map_add _ _ _

set_option linter.unusedSectionVars false in
/-- The embedding `toL2` commutes with negation. -/
@[simp] theorem toL2_neg (S : SmoothCcTensor g r s) :
    (toL2 (g := g) (r := r) (s := s)) (-S) =
      -((toL2 (g := g) (r := r) (s := s)) S) :=
  ContinuousLinearMap.map_neg _ _

set_option linter.unusedSectionVars false in
/-- The embedding `toL2` commutes with subtraction. -/
@[simp] theorem toL2_sub (S T : SmoothCcTensor g r s) :
    (toL2 (g := g) (r := r) (s := s)) (S - T) =
      (toL2 (g := g) (r := r) (s := s)) S -
        (toL2 (g := g) (r := r) (s := s)) T :=
  ContinuousLinearMap.map_sub _ _ _

set_option linter.unusedSectionVars false in
/-- The embedding `toL2` commutes with real scalar multiplication. -/
@[simp] theorem toL2_smul (c : ℝ) (S : SmoothCcTensor g r s) :
    (toL2 (g := g) (r := r) (s := s)) (c • S) =
      c • ((toL2 (g := g) (r := r) (s := s)) S) :=
  ContinuousLinearMap.map_smul _ _ _

end SimpLemmas

end SmoothCcTensor

end L2
end Integral
end DifferentialGeometry

end
