import DifferentialGeometry.Analysis.Parabolic.AbstractSpectralSemigroupContinuity
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.Semigroup
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.CompactSAResolventIntrinsic

/-!
# Intrinsic tensor heat semigroup of the connection Laplacian

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, this file
constructs the heat semigroup `e^{t Δ_∇}` on the tensor `L²` Hilbert
space `TensorL2 r s g` **without any chart-selection hypothesis**.

The construction instantiates the generic spectral heat semigroup
`abstractSpectralSemigroup` (built from a Hilbert basis of eigenvectors
and a non-negative eigenvalue family) with:

* the intrinsic resolvent eigenbasis
  `tensorResolventHilbertEigenbasisSigma`, fed the
  unconditional compactness witness
  `tensorResolventL2_isCompactOperator`;
* the connection-Laplacian eigenvalue family `TensorEigenIdx.lambda`,
  whose non-negativity is `tensor_lambda_nonneg`.

## Main definition

* `tensorHeatSemigroup g r s` — the one-parameter family
  `ℝ → (TensorL2 r s g →L[ℝ] TensorL2 r s g)`.

## Main results

* `tensorHeatSemigroup_intrinsic_apply_zero` — `S(0) = id`.
* `tensorHeatSemigroup_intrinsic_apply_add` — `S(t + s) = S(t) ∘ S(s)`
  for `t, s ≥ 0`.
* `tensorHeatSemigroup_intrinsic_opNorm_le_one` — `‖S(t)‖ ≤ 1` for `t ≥ 0`.
* `tensorHeatSemigroup_intrinsic_continuousOn` — strong continuity
  `ContinuousOn (fun t => S(t) v) (Ici 0)`.

These four are exactly the data of a `BoundedC0Semigroup`.

## Sign convention

Geometer convention `Δ_∇ = -∇*∇`, spectrum `⊆ (-∞, 0]`; the resolvent is
`(1 - Δ_∇)⁻¹` with eigenvalues `μ ∈ (0, 1]`, and the translated
Laplacian eigenvalues `λ = (1 - μ)/μ ≥ 0` make `e^{tΔ_∇}` a contraction
for `t ≥ 0`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The intrinsic resolvent eigenbasis of `TensorL2 r s g`, obtained from
the unconditional compactness witness `tensorResolventL2_isCompactOperator`.
No chart-selection hypothesis is required. -/
private noncomputable def intrinsicEigenbasis
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    HilbertBasis (TensorEigenIdx (I := I) (M := M) g r s) ℝ (TensorL2 r s g) :=
  tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)

/-- Non-negativity of the connection-Laplacian eigenvalue family on the
intrinsic eigen-index. -/
private lemma intrinsic_lambda_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
  fun i => tensor_lambda_nonneg (I := I) (M := M) i

/-- The intrinsic tensor heat semigroup `e^{t Δ_∇}` on `TensorL2 r s g`,
constructed **without any chart-selection hypothesis**.

For `t ≥ 0` it is the spectral series
`T ↦ ∑' i, exp(-(λ_i) t) • ⟪b i, T⟫ • b i`, a contraction (operator norm
`≤ 1`); for `t < 0` it is the zero operator. Here `b` is the intrinsic
resolvent eigenbasis and `λ_i = (1 - μ_i)/μ_i ≥ 0` the translated
connection-Laplacian eigenvalues. -/
noncomputable def tensorHeatSemigroup
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (t : ℝ) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g :=
  abstractSpectralSemigroup (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s) t

/-- At `t = 0`, the intrinsic tensor heat semigroup is the identity. -/
theorem tensorHeatSemigroup_intrinsic_apply_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    tensorHeatSemigroup (I := I) (M := M) g r s 0 =
      ContinuousLinearMap.id ℝ (TensorL2 r s g) :=
  abstractSpectralSemigroup_apply_zero (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s)

/-- The semigroup law `S(t + s) = S(t) ∘ S(s)` for `t, s ≥ 0`. -/
theorem tensorHeatSemigroup_intrinsic_apply_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t s' : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s') :
    tensorHeatSemigroup (I := I) (M := M) g r s (t + s') =
      (tensorHeatSemigroup (I := I) (M := M) g r s t).comp
        (tensorHeatSemigroup (I := I) (M := M) g r s s') :=
  abstractSpectralSemigroup_apply_add (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s) ht hs

/-- The operator norm of `S(t)` is `≤ 1` for every `t : ℝ` (in particular
for `t ≥ 0`, where it is the spectral-series contraction). -/
theorem tensorHeatSemigroup_intrinsic_opNorm_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (t : ℝ) :
    ‖tensorHeatSemigroup (I := I) (M := M) g r s t‖ ≤ 1 :=
  abstractSpectralSemigroup_opNorm_le_one (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s) t

/-- Strong continuity of the intrinsic tensor heat semigroup on `[0, ∞)`:
`t ↦ S(t) T` is continuous on `Ici 0` for every `T`. -/
theorem tensorHeatSemigroup_intrinsic_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : TensorL2 r s g) :
    ContinuousOn (fun t : ℝ =>
        tensorHeatSemigroup (I := I) (M := M) g r s t T)
      (Set.Ici (0 : ℝ)) :=
  abstractSpectralSemigroup_continuousOn (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s) T

/-- **Diagonal eigenbasis action of the intrinsic heat semigroup.**

For `t ≥ 0`, the inner product of the intrinsic eigenbasis vector `bᵢ`
against `S(t) u₀` equals `exp(-λᵢ t)` times the inner product of `bᵢ`
against `u₀`, where `b` is the intrinsic resolvent eigenbasis. No
chart-selection hypothesis is required. -/
theorem tensorHeatSemigroup_intrinsic_inner_eigenbasis
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (u₀ : TensorL2 r s g)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ⟪tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i,
      tensorHeatSemigroup (I := I) (M := M) g r s t u₀⟫_ℝ =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        ⟪tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i,
          u₀⟫_ℝ := by
  classical
  set b := intrinsicEigenbasis (I := I) (M := M) g r s with hb_def
  change ⟪b i, tensorHeatSemigroup (I := I) (M := M) g r s t u₀⟫_ℝ =
    Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * ⟪b i, u₀⟫_ℝ
  have h_apply :
      tensorHeatSemigroup (I := I) (M := M) g r s t u₀ =
        ∑' j, heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
          ⟪b j, u₀⟫_ℝ • b j := by
    unfold tensorHeatSemigroup
    rw [abstractSpectralSemigroup_apply_of_nonneg b
      (intrinsic_lambda_nonneg (I := I) (M := M) g r s) ht u₀]
  rw [h_apply]
  have h_summable :=
    summable_heatTerm b (intrinsic_lambda_nonneg (I := I) (M := M) g r s) ht u₀
  have h_hsum := h_summable.hasSum
  have h_inner_hsum := h_hsum.mapL (innerSL ℝ (b i))
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_inner_eq : ∀ j : TensorEigenIdx (I := I) (M := M) g r s,
      ⟪b i, b j⟫_ℝ = if j = i then (1 : ℝ) else 0 := by
    intro j
    rw [show ⟪b i, b j⟫_ℝ = ⟪b j, b i⟫_ℝ from real_inner_comm _ _]
    exact (orthonormal_iff_ite (𝕜 := ℝ) (v := b)).mp h_orthonormal j i
  have h_summand_eq : ∀ j : TensorEigenIdx (I := I) (M := M) g r s,
      (innerSL ℝ (b i))
          (heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
            ⟪b j, u₀⟫_ℝ • b j) =
        if j = i then
          heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j *
            ⟪b j, u₀⟫_ℝ
        else 0 := by
    intro j
    change ⟪b i,
        heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
          ⟪b j, u₀⟫_ℝ • b j⟫_ℝ = _
    rw [real_inner_smul_right, real_inner_smul_right, h_inner_eq]
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  have h_inner_hsum' : HasSum (fun j =>
      if j = i then
        heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j *
          ⟪b j, u₀⟫_ℝ
      else 0)
      ((innerSL ℝ (b i))
        (∑' j, heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
          ⟪b j, u₀⟫_ℝ • b j)) := by
    convert h_inner_hsum using 1
    funext j
    exact (h_summand_eq j).symm
  have h_tsum_ite :
      ∑' j : TensorEigenIdx (I := I) (M := M) g r s,
        (if j = i then
          heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j *
            ⟪b j, u₀⟫_ℝ
        else 0) =
      heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t i *
        ⟪b i, u₀⟫_ℝ := by
    rw [tsum_ite_eq i]
  have h_eq := h_inner_hsum'.tsum_eq
  rw [h_tsum_ite] at h_eq
  have h_inner_val :
      ⟪b i, ∑' j, heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
            ⟪b j, u₀⟫_ℝ • b j⟫_ℝ =
        heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t i *
          ⟪b i, u₀⟫_ℝ := h_eq.symm
  rw [h_inner_val, heatCoeff_def]

example (g : SmoothRiemannianMetric I M) (r s : ℕ) (t : ℝ) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g :=
  tensorHeatSemigroup (I := I) (M := M) g r s t

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
