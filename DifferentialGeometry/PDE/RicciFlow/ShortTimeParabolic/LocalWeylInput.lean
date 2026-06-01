/-
The single isolated open analytic input of the Ricci-flow short-time-existence
development: the classical local Weyl law for the intrinsic tensor Laplacian on a
closed manifold, in its pointwise on-diagonal reproducing-kernel form.

Every other lemma in the short-time-existence proof is proven outright; this file
holds the one deferred classical theorem
`weyl_pointwise_diagonalKernel_bound_of_closed`. It is the *pointwise* (per-point)
form of the local Weyl law — the supercritical on-diagonal reproducing-kernel
estimate — which is strictly stronger than the integrated eigenvalue-counting
bound `EigenvalueCountingBound`. From this single node we re-derive:

* `weyl_eigenvalue_counting_bound_of_closed` — the integrated polynomial counting
  bound, by integrating the pointwise kernel estimate over the closed manifold
  (`eigenvalueCountingBound_of_pointwiseDiagonalKernelBound`); this in turn drives
  the proven clean chain `EigenvalueCountingBound ⟹ EigenvalueTailSummable ⟹
  SpectralChartRegularity ⟹ SpectralSmoothRealizesAsSmooth` of
  `SpectralWeylCounting.lean`, the spectral smooth-representative gate; and

* the two pointwise realize-transport inputs in `RealizeTransport.lean` (the
  supercritical weighted summability of the per-eigenmode realize values and the
  absolutely-convergent realize eigen-expansion), which are exactly the realize
  read-off of the same on-diagonal kernel content.

Consolidating to this one node is the project's deliberate isolation of the single
open classical analytic gap.
-/
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.SpectralWeylCounting
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.SpectralDiagonalCounting
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.EigenCombination
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.TensorHsRealize

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The pointwise local Weyl law for the intrinsic tensor connection-Laplacian on
a closed manifold, in its supercritical on-diagonal reproducing-kernel form: for a
smooth Riemannian metric `g` and bidegree `(r, s)`, the conjunction of a polynomial
diagonal-kernel bound and (at supercritical Sobolev order) two realize read-offs of
the same on-diagonal kernel content. This is the project's single deferred classical
analytic input (kept as the only `sorry` on the short-time-existence dependency
graph); the three conjuncts package the heat-kernel-parametrix / Karamata-Tauberian
content of the on-diagonal heat trace, none of which is available in Mathlib:

1. **Polynomial diagonal-kernel bound.** There are a degree `q`, a constant
   `B ≥ 0` and a threshold-capturing finite family `count Λ` (containing every
   index with `1 + λᵢ < Λ`) such that the on-diagonal reproducing kernel
   `diagonalKernel g r s (count Λ) x = ∑_{i ∈ count Λ} ‖bᵢ(x)‖²_g` is bounded by
   `B · Λ^q` pointwise on `M`. Integrating against the unit-energy identity gives
   the integrated counting bound `EigenvalueCountingBound` (the sibling
   `weyl_eigenvalue_counting_bound_of_closed`).

2. **Supercritical weighted summability of the realize values.** At a
   supercritical Sobolev order `2a > finrank ℝ E + 4`, the per-eigenmode realize
   values `eᵢ(x,v,w) = ccTensorBilinSymm g (eigenvectorSmooth g 0 2 i) x v w`
   for the bidegree `(0, 2)` spectrum decay so that the `Hᵃ`-Riesz weight
   `tensorSobolevWeight i a · (eᵢ(x,v,w) · (tensorSobolevWeight i a)⁻¹)²` is
   summable over `i`. (Via the fibre Cauchy–Schwarz `eᵢ(x,v,w)² ≲ ‖bᵢ(x)‖²_g` this
   is dominated by the on-diagonal kernel tail `∑ᵢ ‖bᵢ(x)‖²_g · (1+λᵢ)^{-a} < ∞`.)

3. **The realize eigen-expansion.** At the same supercritical order, the
   realize-evaluation `ccTensorBilinSymm g T x v w` of a smooth compactly-supported
   `(0, 2)`-tensor `T` is the `HasSum` of the eigen-series of its `L²`-coordinates
   `tensorL2Coeff (SmoothCcTensor.toL2 T) i` weighted by the per-eigenmode
   realize values.

Every other consumer (the integrated counting bound, the realize transport
functional in `RealizeTransport.lean`) is re-derived from this node. -/
theorem weyl_pointwise_diagonalKernel_bound_of_closed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    (∃ (q : ℕ) (B : ℝ), 0 ≤ B ∧
      ∃ count : ℝ → Finset
          (Analysis.Parabolic.TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
        (∀ (Λ : ℝ)
            (i : Analysis.Parabolic.TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
          1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) i < Λ → i ∈ count Λ) ∧
        (∀ (Λ : ℝ) (x : M),
          diagonalKernel (I := I) (M := M) g r s (count Λ) x ≤ B * Λ ^ q)) ∧
    (∀ (a : ℕ), 2 * a > Module.finrank ℝ E + 4 →
      (∀ (x : M) (v w : TangentSpace I x),
        Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g 0 2 =>
          tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
            (ccTensorBilinSymm (I := I) g
                (eigenvectorSmooth (I := I) (M := M) g 0 2 i) x v w *
              (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹) ^ 2)) ∧
      (∀ (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x),
        HasSum
          (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g 0 2 =>
            tensorL2Coeff (I := I) (M := M)
                (hCompact (I := I) (M := M) g) (SmoothCcTensor.toL2 T) i *
              ccTensorBilinSymm (I := I) g
                (eigenvectorSmooth (I := I) (M := M) g 0 2 i) x v w)
          (ccTensorBilinSymm (I := I) g T x v w))) := sorry

/-- The integrated polynomial eigenvalue-counting bound `EigenvalueCountingBound g r s`
for the tensor connection-Laplacian spectrum on a closed manifold. Re-derived from the
pointwise on-diagonal kernel estimate `weyl_pointwise_diagonalKernel_bound_of_closed` by
integrating it against the closed-manifold Riemannian volume (the unit-energy
`∫_M ‖bᵢ‖²_g = 1` reproducing-kernel identity), via
`eigenvalueCountingBound_of_pointwiseDiagonalKernelBound`. Every spectral consumer
(smooth-representative gate, eigenvalue-tail summability) reduces to this one
statement through the proven chain in `SpectralWeylCounting.lean`. -/
theorem weyl_eigenvalue_counting_bound_of_closed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    EigenvalueCountingBound (I := I) (M := M) g r s := by
  obtain ⟨⟨q, B, hB, count, hmem, hkernel⟩, _⟩ :=
    weyl_pointwise_diagonalKernel_bound_of_closed (I := I) (M := M) g r s
  exact eigenvalueCountingBound_of_pointwiseDiagonalKernelBound
    (I := I) (M := M) g r s q B hB count hmem hkernel

end DifferentialGeometry.PDE.RicciFlow
