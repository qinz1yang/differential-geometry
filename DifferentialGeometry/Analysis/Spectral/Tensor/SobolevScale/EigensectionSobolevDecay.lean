import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace

/-!
# Uniform-in-index spectral Sobolev decay of the smooth eigensections

For a closed Riemannian manifold `(M, g)`, the smooth representatives
`eigenvectorSmooth g 0 2 i` of the orthonormal `L²` eigenbasis of the connection
Laplacian's resolvent have order-`σ` spectral Sobolev norm given *exactly* by the
eigenvalue power: in the canonical spectral embedding `ccSpectralEmbed`,

`‖ccSpectralEmbed g σ (eigenvectorSmooth g 0 2 i)‖² = (1 + λᵢ)^σ = tensorSobolevWeight i σ`,

because the eigenvectors are `L²`-orthonormal (`tensorL2Coeff_ofCompact_eigenSmooth`,
the Kronecker delta) and the squared spectral norm is the eigenvalue-weighted sum of
squared coordinates (`ccSpectralEmbed_norm_sq_eq_tsum`).

Routed through the partition-of-unity Sobolev norm equivalence
(`tensorPouSobolevHilbert_norm_eq`, `tensorPouSobolevHsNorm_le_ccSpectralEmbed`), this
yields the *uniform-in-`i`* decay of the order-`2k` partition-of-unity Sobolev norm of the
smooth eigensection as a fixed power of its eigenvalue:

`∃ C ≥ 0, ∀ i, ‖(eigenvectorSmooth g 0 2 i).toHs (2k)‖ ≤ C · (1 + λᵢ)^(2k)`.

This is the reusable spectral input behind the eigen-series `M`-test majorant for the
joint chart-Gram smoothness of a realized time-smooth spectral family: it lets a single
eigenvalue-power factor stand in for every eigensection's chart-jet norm, so the Weyl
summability `tensorEigen_summable_negpow` controls the across-modes sum. -/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth) in
/-- **The squared spectral norm of a smooth eigensection is its eigenvalue weight.**
Since the eigenvectors are `L²`-orthonormal (`tensorL2Coeff_ofCompact_eigenSmooth` gives the
Kronecker delta for their coordinates), the eigenvalue-weighted sum of squared coordinates
collapses to the single weight at index `i`:
`‖ccSpectralEmbed g σ (eᵢ)‖² = ∑ⱼ (1+λⱼ)^σ δᵢⱼ² = (1+λᵢ)^σ = tensorSobolevWeight i σ`. -/
theorem ccSpectralEmbed_eigenvectorSmooth_norm_sq
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ‖ccSpectralEmbed (I := I) (M := M) g σ
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i)‖ ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i σ := by
  classical
  rw [ccSpectralEmbed_norm_sq_eq_tsum]
  have hcoeff : ∀ j : TensorEigenIdx (I := I) (M := M) g 0 2,
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (SmoothCcTensor.toL2 (eigenvectorSmooth (I := I) (M := M) g 0 2 i)) j =
      (if j = i then (1 : ℝ) else 0) := by
    intro j
    have hk := tensorL2Coeff_ofCompact_eigenSmooth (I := I) (M := M) g j i
    rw [← hk]
    congr 1
  simp_rw [hcoeff]
  rw [tsum_congr (fun j => by
    rw [show (if j = i then (1 : ℝ) else 0) ^ 2 = (if j = i then (1 : ℝ) else 0) by
      split <;> simp, mul_ite, mul_one, mul_zero])]
  rw [tsum_ite_eq i]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth) in
/-- **Uniform-in-index spectral Sobolev decay of the smooth eigensections.**
For each natural order `k` there is a single constant `C` such that every smooth eigensection
`eigenvectorSmooth g 0 2 i` has order-`2k` partition-of-unity Sobolev norm bounded by
`C · (1 + λᵢ)^(2k)`.

The bridge `tensorPouSobolevHilbert_norm_eq` reads the `.toHs (2k)` norm as the partition-of-unity
Sobolev norm, `tensorPouSobolevHsNorm_le_ccSpectralEmbed` bounds it by the spectral norm at order
`2·(2k) = 4k`, and `ccSpectralEmbed_eigenvectorSmooth_norm_sq` evaluates that spectral norm exactly
as `(1 + λᵢ)^(4k)`, whose square root is `(1 + λᵢ)^(2k)`.  The achievable exponent is `2k` (forced
by the order-doubling bridge), not `k`. -/
theorem eigenvectorSmooth_toHs_norm_le_lambda_pow
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
        ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k)
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i)‖ ≤
          C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) := by
  classical
  obtain ⟨C, hC_nn, hbridge⟩ :=
    tensorPouSobolevHsNorm_le_ccSpectralEmbed (I := I) (M := M) g (2 * k)
  refine ⟨C, hC_nn, fun i => ?_⟩
  set ei := eigenvectorSmooth (I := I) (M := M) g 0 2 i with hei_def
  rw [tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g (2 * k) ei]
  refine le_trans (hbridge ei) ?_
  have hspec : ‖ccSpectralEmbed (I := I) (M := M) g ((2 * (2 * k) : ℕ) : ℝ) ei‖ =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) := by
    have hsq := ccSpectralEmbed_eigenvectorSmooth_norm_sq (I := I) (M := M) g
      ((2 * (2 * k) : ℕ) : ℝ) i
    have hbase_nn : (0 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
      have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
    have hw : tensorSobolevWeight (I := I) (M := M) i ((2 * (2 * k) : ℕ) : ℝ) =
        ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k)) ^ 2 := by
      unfold tensorSobolevWeight
      rw [show ((2 * (2 * k) : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) * 2 by push_cast; ring,
        Real.rpow_mul hbase_nn, Real.rpow_natCast, Real.rpow_two]
    rw [hw] at hsq
    have hnn_pow : (0 : ℝ) ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) :=
      pow_nonneg hbase_nn _
    nlinarith [norm_nonneg (ccSpectralEmbed (I := I) (M := M) g ((2 * (2 * k) : ℕ) : ℝ) ei),
      hsq, hnn_pow]
  rw [hspec]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
