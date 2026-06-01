import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenBasis
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Tensor heat semigroup: eigen-index and per-eigenvalue heat coefficient

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, this file
introduces the sigma-typed basis-index `TensorEigenIdx g r s` for the
L²-side tensor eigenbasis of the resolvent

  `R := tensorResolventL2 g r s : TensorL2 r s g →L[ℝ] TensorL2 r s g`,

and proves the basic non-negativity / unit-interval bound of the per-
eigenvalue heat coefficient `exp(-λ_i · t)` for `t ≥ 0`, where `λ_i` is
the connection-Laplacian eigenvalue translated from the corresponding
nonzero resolvent eigenvalue via `λ = (1 - μ)/μ`.

This is the tensor analogue of the scalar `EigenIdx` / `lambda` /
`heat_coeff_mem_unit_interval` triple, and serves as the indexing layer
for the eventual tensor heat semigroup
`∑' i, exp(-λ_i · t) • ⟪b i, T⟫ • b i`.

## Main definitions

* `TensorEigenIdx g r s` — the sigma-indexed basis-index type for the
  L² eigenbasis: pairs of a nonzero resolvent eigenvalue and a finite
  index into its eigenspace orthonormal basis.
* `TensorEigenIdx.lambda` — the connection-Laplacian eigenvalue
  attached to a sigma-index, defined as
  `tensorLaplacianEigenvalueOf μ.val = (1 - μ.val) / μ.val`.

## Main results

* `tensor_lambda_nonneg` — `0 ≤ TensorEigenIdx.lambda i`.
* `tensor_heat_coeff_mem_unit_interval` — for `t ≥ 0`,
  `exp(-λ_i · t) ∈ (0, 1]`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum
`⊆ (-∞, 0]`. The resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`), so
the translated Laplacian eigenvalue `λ = (1 - μ)/μ` is non-negative for
`μ ∈ (0, 1]`. The per-eigenvalue heat coefficient is then
`exp(-λ · t)`, contractive for `t ≥ 0`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Sigma-index for the tensor eigenbasis: pairs an eigenvalue `μ`
(nonzero, nontrivial eigenspace) with a finite-dimensional eigenspace
index. -/
abbrev TensorEigenIdx (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ :=
  Σ μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s,
    Fin (Module.finrank ℝ
      (tensorResolventEigenspace (I := I) (M := M) g r s μ.val))

/-- The connection-Laplacian eigenvalue associated with the resolvent
eigenvalue at sigma index `i`, defined as `(1 - μ)/μ`. -/
noncomputable abbrev TensorEigenIdx.lambda
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) : ℝ :=
  tensorLaplacianEigenvalueOf i.fst.val

/-- The per-eigenvalue Laplacian eigenvalue is non-negative. -/
theorem tensor_lambda_nonneg
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i := by
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  have h_mem_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 :=
    tensorResolvent_eigenvalue_mem_unit_interval
      (I := I) (M := M) g r s hu_in hu_ne
  exact tensorLaplacianEigenvalueOf_nonneg_of_resolventEigenvalue h_mem_unit

/-- The per-eigenvalue heat coefficient `exp(-λ_i · t)` is in `(0, 1]`
for non-negative time. -/
theorem tensor_heat_coeff_mem_unit_interval
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : 0 ≤ t) :
    0 < Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) ∧
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) ≤ 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  rw [Real.exp_le_one_iff]
  have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
    tensor_lambda_nonneg (I := I) (M := M) i
  nlinarith

/-- The squared heat coefficient is bounded by `1` for `t ≥ 0`. -/
lemma tensor_heat_coeff_sq_le_one
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : 0 ≤ t) :
    (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 ≤ 1 := by
  obtain ⟨h_pos, h_le⟩ :=
    tensor_heat_coeff_mem_unit_interval (I := I) (M := M) i ht
  have h_nn : 0 ≤ Real.exp
      (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) := h_pos.le
  nlinarith [sq_nonneg
    (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1)]

/-- Parseval-type square-summability of the tensor basis coefficients for
the chart-locality-free eigenbasis. -/
lemma tensorSummable_basis_coeff_sq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (T : TensorL2 r s g) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      ‖⟪tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_compact i, T⟫_ℝ‖ ^ 2) := by
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_compact
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_orthFam :
      OrthogonalFamily ℝ
        (fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ)
        (fun i => LinearIsometry.toSpanSingleton ℝ
          (TensorL2 r s g) (h_orthonormal.1 i)) :=
    h_orthonormal.orthogonalFamily
  have h_summable_smul : Summable
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ⟪b i, T⟫_ℝ • b i) := by
    have h_hsum : HasSum (fun i => b.repr T i • b i) T := b.hasSum_repr T
    have h_eq : (fun i => b.repr T i • b i) =
        (fun i => ⟪b i, T⟫_ℝ • b i) := by
      funext i
      rw [b.repr_apply_apply]
    rw [h_eq] at h_hsum
    exact h_hsum.summable
  have h_iff := h_orthFam.summable_iff_norm_sq_summable
    (fun i : TensorEigenIdx (I := I) (M := M) g r s => ⟪b i, T⟫_ℝ)
  have h_map_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        LinearIsometry.toSpanSingleton ℝ
          (TensorL2 r s g) (h_orthonormal.1 i) (⟪b i, T⟫_ℝ)) =
      (fun i => ⟪b i, T⟫_ℝ • b i) := by
    funext i
    rw [LinearIsometry.toSpanSingleton_apply]
  rw [h_map_eq] at h_iff
  exact h_iff.mp h_summable_smul

/-- Parseval identity for the chart-locality-free tensor eigenbasis: the
squared L²-norm of `T` equals the sum of the squared basis coefficients. -/
lemma tensorParseval_norm_sq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (T : TensorL2 r s g) :
    ‖T‖ ^ 2 =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        ‖⟪tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_compact i, T⟫_ℝ‖ ^ 2 := by
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_compact
  have h_par := b.tsum_inner_mul_inner T T
  have h_sq : ⟪T, T⟫_ℝ = ‖T‖ ^ 2 := real_inner_self_eq_norm_sq T
  have h_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ⟪T, b i⟫_ℝ * ⟪b i, T⟫_ℝ) =
      (fun i => ‖⟪b i, T⟫_ℝ‖ ^ 2) := by
    funext i
    rw [show ⟪T, b i⟫_ℝ = ⟪b i, T⟫_ℝ from real_inner_comm _ _,
        Real.norm_eq_abs, sq_abs, sq]
  rw [h_eq] at h_par
  linarith [h_par, h_sq]

example (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ :=
  TensorEigenIdx (I := I) (M := M) g r s

example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) : ℝ :=
  TensorEigenIdx.lambda (I := I) (M := M) i

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
