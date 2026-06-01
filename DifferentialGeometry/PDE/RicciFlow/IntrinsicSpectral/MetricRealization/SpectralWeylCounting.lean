import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.EigenvalueTailSummableUncond

/-!
# The Weyl-counting reduction of the spectral smooth-representative gate

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled
on a finite-dimensional real inner-product space `E` and ranks `(r, s)`, this file
isolates a single clean classical input — a **polynomial bound on the
eigenvalue-counting function** of the connection (rough) Laplacian on
`(r, s)`-tensor fields — and proves that it closes the entire spectral
smooth-representative gate.

## The counting predicate

`EigenvalueCountingBound g r s` asks that *some* polynomial degree `q` and constant
`A ≥ 0` bound the counting function: for every threshold `Λ : ℝ`, the sub-level set
`{i : 1 + λᵢ < Λ}` is contained in a finite family `count Λ` whose cardinality is
at most `A · Λ^q`. This is exactly the classical Weyl counting statement
`N(Λ) = #{i : 1 + λᵢ < Λ} ≲ Λ^q` (with multiplicity), phrased so it is directly
consumable by the dyadic counting → summability converter.

The geometric *content* (the local reproducing-kernel diagonal estimate
`∑_{1+λᵢ ≤ Λ} ‖bᵢ(x)‖² ≲ Λ^q`, integrated over `M` against the orthonormality
`‖bᵢ‖_{L²} = 1`) is the standard route to this bound; it is **not** assumed here.
This file performs only the purely analytic / spectral reduction:
```
  EigenvalueCountingBound
    ⟹ EigenvalueTailSummable                    (the dyadic Weyl ⟹ Schatten step)
    ⟹ SpectralChartRegularity                   (the general-element ℓ¹ control)
    ⟹ SpectralSmoothRealizesAsSmooth            (the chart → C^∞ reconstruction).
```
The first arrow specialises the abstract converter `eigenvalueTailSummable_of_polynomial_counting_bound`
at the dyadic thresholds `Λ = 2^{n+1}`; the second and third are the proven
reduction theorems of the gate.

## Sign convention

Geometer convention `Δ_∇ = -∇*∇`, spectrum `⊆ (-∞, 0]`; resolvent `(1 - Δ_∇)⁻¹`,
eigenvalues `λᵢ ≥ 0`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Polynomial eigenvalue-counting bound (predicate).**

`EigenvalueCountingBound g r s` holds when the connection-Laplacian
eigenvalue-counting function of `(r, s)`-tensor fields admits a polynomial
bound: there exist a degree `q : ℕ`, a constant `A ≥ 0`, and, for every real
threshold `Λ`, a finite family `count Λ : Finset (TensorEigenIdx g r s)`
containing every index `i` with `1 + λᵢ < Λ`, whose cardinality is at most
`A · Λ^q`.

This is the classical Weyl counting statement
`N(Λ) = #{i : 1 + λᵢ < Λ} ≲ Λ^q` (eigenvalues counted with multiplicity, which is
automatic here because `TensorEigenIdx` already pairs each eigenvalue with a basis
index of its finite-dimensional eigenspace). It is the single geometric input that
closes the spectral smooth-representative gate; everything downstream of it is the
purely analytic dyadic-decomposition and general-element reduction proved below. -/
def EigenvalueCountingBound (g : SmoothRiemannianMetric I M) (r s : ℕ) : Prop :=
  ∃ (q : ℕ) (A : ℝ), 0 ≤ A ∧
    ∃ count : ℝ → Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
      (∀ (Λ : ℝ) (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
        1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ → i ∈ count Λ) ∧
      (∀ Λ : ℝ, ((count Λ).card : ℝ) ≤ A * Λ ^ q)

/-- **The Weyl counting bound forces eigenvalue-tail summability.**

Specialising the polynomial counting bound at the dyadic thresholds `Λ = 2^{n+1}`
yields exactly the dyadic `count`/`hcount_card` data consumed by the abstract
converter `eigenvalueTailSummable_of_polynomial_counting_bound`, with the explicit summability
exponent `p = q + 2 > 0`.

Concretely, for the dyadic shell at level `n` we take `countDyadic n := count (2^{n+1})`;
the membership hypothesis is the threshold-membership of the predicate at `Λ = 2^{n+1}`,
and the cardinality bound is `#(count (2^{n+1})) ≤ A · (2^{n+1})^q = A · 2^{(n+1)·q}`,
which is the converter's polynomial-in-`2^n` counting bound of degree `q`. -/
theorem eigenvalueTailSummable_of_countingBound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h : EigenvalueCountingBound (I := I) (M := M) g r s) :
    EigenvalueTailSummable (I := I) (M := M) g r s := by
  obtain ⟨q, A, hA, count, hcount_mem, hcount_card⟩ := h
  refine eigenvalueTailSummable_of_polynomial_counting_bound (I := I) (M := M) g r s q A hA
    (fun n => count ((2 : ℝ) ^ (n + 1))) ?_ ?_
  · intro n i hi
    exact hcount_mem ((2 : ℝ) ^ (n + 1)) i hi
  · intro n
    refine (hcount_card ((2 : ℝ) ^ (n + 1))).trans (le_of_eq ?_)
    congr 1
    rw [← pow_mul]

/-- **The all-orders spectral→chart Sobolev regularity from the Weyl counting
bound.** Granting the polynomial eigenvalue-counting bound, every gate element
(an `L²` tensor lying in every `Hˢ`) has all of its canonical chart components in
`W^{2k,2}` on every chart target, for every order `k`. This is
`spectralChartRegularity_of_eigenvalueTailSummable` precomposed with the
counting ⟹ tail-summability reduction. -/
theorem spectralChartRegularity_of_countingBound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h : EigenvalueCountingBound (I := I) (M := M) g r s) :
    SpectralChartRegularity (I := I) (M := M) g r s :=
  spectralChartRegularity_of_eigenvalueTailSummable (I := I) (M := M) g r s
    (eigenvalueTailSummable_of_countingBound (I := I) (M := M) g r s h)

/-- **The full spectral smooth-representative gate from the Weyl counting bound.**

Granting the polynomial eigenvalue-counting bound, every `L²` tensor lying in every
`Hˢ` admits a genuine `C^∞` (`SmoothCcTensor`) representative. This is the complete
chain
```
  EigenvalueCountingBound
    ⟹ EigenvalueTailSummable
    ⟹ SpectralChartRegularity
    ⟹ SpectralSmoothRealizesAsSmooth.
```
It is the clean public statement that the spectral gate reduces to the single
classical Weyl counting input. -/
theorem spectralSmoothRealizesAsSmooth_of_countingBound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h : EigenvalueCountingBound (I := I) (M := M) g r s) :
    SpectralSmoothRealizesAsSmooth (I := I) (M := M) g r s :=
  spectralSmoothRealizesAsSmooth_of_eigenvalueTailSummable (I := I) (M := M) g r s
    (eigenvalueTailSummable_of_countingBound (I := I) (M := M) g r s h)

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
