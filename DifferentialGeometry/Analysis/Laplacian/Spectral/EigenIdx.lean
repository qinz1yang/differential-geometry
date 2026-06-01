import DifferentialGeometry.Analysis.Laplacian.Spectral.EigenBasis

/-!
# Scalar Laplacian spectral sigma index

For a closed Riemannian manifold `(M, g)`, this file packages the scalar
spectral basis index as a single sigma-type alongside the Laplacian
eigenvalue accessor.

The eigenbasis of the scalar L² resolvent
`R := resolventL2 g : Lp ℝ 2 μ_g →L[ℝ] Lp ℝ 2 μ_g` is naturally indexed by
pairs of a nonzero resolvent eigenvalue and a finite-dimensional eigenspace
index. The abbreviation `EigenIdx g` collects this index, and
`EigenIdx.lambda i` returns the corresponding Laplacian eigenvalue
`(1 - μ) / μ`, which is non-negative.

## Main definitions

* `EigenIdx g` — the sigma-indexed basis-index type for the scalar L²
  eigenbasis.
* `EigenIdx.lambda` — the Laplacian eigenvalue attached to a sigma index.

## Main results

* `EigenIdx.lambda_nonneg` — `0 ≤ EigenIdx.lambda i`.

## Sign convention

We follow the geometer convention `Δ_g = div_g ∘ grad_g`, so the Laplacian
is non-positive on a closed manifold. The resolvent is `(1 - Δ_g)⁻¹` with
spectrum in `(0, 1]`, and the translated Laplacian eigenvalue
`λ = (1 - μ) / μ` is non-negative for `μ ∈ (0, 1]`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace Spectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Sigma-index for the scalar L² eigenbasis of the Laplacian resolvent:
pairs a nonzero eigenvalue `μ` of `R := resolventL2 g` with an index into the
standard orthonormal basis of the eigenspace at `μ`. -/
abbrev EigenIdx (g : SmoothRiemannianMetric I M) : Type _ :=
  Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
    Fin (Module.finrank ℝ (resolventEigenspace (I := I) (M := M) g μ.val))

/-- The Laplacian eigenvalue `(1 - μ) / μ` attached to a sigma-index `i`. -/
noncomputable abbrev EigenIdx.lambda
    {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) : ℝ :=
  laplacianEigenvalueOf i.fst.val

/-- The Laplacian eigenvalue attached to a sigma-index is non-negative. -/
theorem EigenIdx.lambda_nonneg
    {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) :
    0 ≤ EigenIdx.lambda (I := I) (M := M) i :=
  laplacianEigenvalueOf_nonneg (I := I) (M := M) i.fst

end Spectral
end Laplacian
end Analysis
end DifferentialGeometry

end
