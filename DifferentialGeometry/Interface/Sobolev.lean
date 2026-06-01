import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.L2Inclusion
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.H1Compl

/-!
# Public Sobolev / H¹ adapters

This file is a consumption-facing facade gathering the project's smooth ↔
H¹ Hilbert ↔ L² infrastructure under a single namespace. A downstream user
who only needs to push a smooth scalar function into the H¹ Hilbert
completion or into its L² representative can import this single file and
work with one-line adapters.

For scalars on a closed Riemannian manifold `(M, g)`:
- `smoothScalarToH1` takes `(f : M → ℝ)` and `(hf : ContMDiff … ∞ f)` and
  produces an element of the H¹ Hilbert completion `H1Compl g`.
- `smoothScalarToLp` further composes with the H¹ → L² extension, returning
  the `Lp ℝ 2 μ_g` representative.

The corresponding tensor-section primitives `TensorH1Compl`,
`smoothToTensorH1Compl`, `TensorH1ComplToTensorL2`, and the scalar
primitives `H1Compl`, `smoothToH1Compl`, `H1ComplToLp` are re-exported
under the `DifferentialGeometry.Interface` namespace so that consumers
can `open DifferentialGeometry.Interface` and refer to all of them
without qualification.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Interface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

/-- One-line adapter from a smooth real-valued function `f : M → ℝ` (with
smoothness witness `hf`) to its image in the H¹ Hilbert completion
`H1Compl g`. -/
noncomputable def smoothScalarToH1 (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    H1Compl g :=
  smoothToH1Compl (I := I) (M := M) g ⟨f, hf⟩

/-- One-line adapter from a smooth real-valued function `f : M → ℝ` (with
smoothness witness `hf`) to its `Lp ℝ 2 μ_g` representative, obtained by
composing the inclusion into the H¹ completion with the continuous linear
H¹ → L² extension. -/
noncomputable def smoothScalarToLp (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  H1ComplToLp (I := I) (M := M) g
    (smoothToH1Compl (I := I) (M := M) g ⟨f, hf⟩)

set_option linter.unusedSectionVars false in
/-- The smooth-to-Lp adapter factors through the smooth-to-H¹ adapter. -/
@[simp] lemma smoothScalarToLp_eq (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    smoothScalarToLp (I := I) (M := M) g f hf =
      H1ComplToLp (I := I) (M := M) g
        (smoothScalarToH1 (I := I) (M := M) g f hf) := rfl

end Interface
end DifferentialGeometry

namespace DifferentialGeometry.Interface

export DifferentialGeometry.Analysis.Laplacian
  (H1Compl smoothToH1Compl H1ComplToLp)

export DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (TensorH1Compl smoothToTensorH1Compl TensorH1ComplToTensorL2)

end DifferentialGeometry.Interface

end
