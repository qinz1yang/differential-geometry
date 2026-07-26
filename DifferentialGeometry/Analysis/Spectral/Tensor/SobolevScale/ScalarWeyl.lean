import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralDiagonalCounting
import DifferentialGeometry.Analysis.Spectral.Intrinsic.TensorHsInterpolationLimit
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2Pointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothCcDense

/-!
# Scalar spectral tail summability

This file proves the polynomial counting estimate needed for the rank-zero
tensor connection-Laplacian.  The proof uses the scalar point-evaluation
Sobolev bound on a finite reproducing-kernel combination, rather than the
strong local Weyl-law input used for arbitrary tensor valence.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private noncomputable def scalarCombo
    (g : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 0))
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ) :
    SmoothCcTensor g 0 0 :=
  ∑ i ∈ F, c i • eigenvectorSmooth (I := I) (M := M) g 0 0 i

private lemma combo_hs
    (g : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 0))
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ)
    (σ : ℝ) (hσ : 0 ≤ σ) :
    ccTensorToHs (I := I) (M := M) g 0 σ
        (scalarCombo (I := I) (M := M) g F c) =
      ∑ i ∈ F, c i •
        tensorHsBasisVec (I := I) (M := M)
          (g := g) (r := 0) (s := 0) σ i := by
  rw [← ccToHsLin_apply]
  simp only [scalarCombo, map_sum, map_smul, ccToHsLin_apply,
    ccToHs_eigen (I := I) (M := M) g 0 hσ]

omit [BoundarylessManifold I M] in
private lemma combo_val
    (g : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 0))
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ)
    (x : M) :
    TensorRSField.scalar0
        (scalarCombo (I := I) (M := M) g F c).toSection x =
      ∑ i ∈ F, c i * TensorRSField.scalar0
        (eigenvectorSmooth (I := I) (M := M) g 0 0 i).toSection x := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      simp [scalarCombo]
  | @insert i F hi ih =>
      unfold scalarCombo at ih ⊢
      simp [hi, ih, smul_eq_mul]

omit [BoundarylessManifold I M] in
open scoped Classical in
private lemma basis_sum_coeff
    (g : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 0))
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ)
    (σ : ℝ) (i : TensorEigenIdx (I := I) (M := M) g 0 0) :
    (∑ j ∈ F, c j •
      tensorHsBasisVec (I := I) (M := M)
        (g := g) (r := 0) (s := 0) σ j).coeff i =
      if i ∈ F then c i else 0 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      simp
  | @insert j F hj ih =>
      rw [Finset.sum_insert hj]
      simp only [tensorHs.add_coeff, tensorHs.smul_coeff,
        tensorHsBasisVec_coeff]
      by_cases hij : i = j
      · subst i
        rw [ih, if_neg hj]
        simp [hj]
      · simp [hij, ih]

private lemma combo_norm_sq
    (g : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 0))
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ)
    (σ : ℝ) (hσ : 0 ≤ σ) :
    ‖ccTensorToHs (I := I) (M := M) g 0 σ
        (scalarCombo (I := I) (M := M) g F c)‖ ^ 2 =
      ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2 := by
  rw [combo_hs (I := I) (M := M) g F c σ hσ,
    tensorHs.norm_sq_eq_tsum]
  rw [tsum_eq_sum (s := F) (f := fun i =>
    tensorSobolevWeight (I := I) (M := M) i σ *
      ((∑ j ∈ F, c j •
        tensorHsBasisVec (I := I) (M := M)
          (g := g) (r := 0) (s := 0) σ j).coeff i) ^ 2) ?_]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [basis_sum_coeff (I := I) (M := M), if_pos hi]
  · intro i hi
    change tensorSobolevWeight (I := I) (M := M) i σ *
      ((∑ j ∈ F, c j •
        tensorHsBasisVec (I := I) (M := M)
          (g := g) (r := 0) (s := 0) σ j).coeff i) ^ 2 = 0
    rw [basis_sum_coeff (I := I) (M := M), if_neg hi]
    ring

/-- The rank-zero connection-Laplacian has a polynomial pointwise diagonal
kernel bound.  Unlike the arbitrary-valence local Weyl statement, this follows
from the already proved scalar Sobolev point-evaluation estimate. -/
theorem scalar_diag_le
    (g : SmoothRiemannianMetric I M) :
    ∃ (q : ℕ) (B : ℝ), 0 ≤ B ∧
      ∃ count : ℝ → Finset (TensorEigenIdx (I := I) (M := M) g 0 0),
        (∀ (Λ : ℝ) (i : TensorEigenIdx (I := I) (M := M) g 0 0),
          1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ →
            i ∈ count Λ) ∧
        (∀ (Λ : ℝ) (x : M),
          diagonalKernel (I := I) (M := M) g 0 0 (count Λ) x ≤
            B * Λ ^ q) := by
  classical
  let k : ℕ := Module.finrank ℝ E / 2 + 1
  let count : ℝ → Finset (TensorEigenIdx (I := I) (M := M) g 0 0) :=
    fun Λ =>
      (tensorEigenIdx_one_add_lambda_lt_finite
        (I := I) (M := M) g 0 0 Λ).toFinset
  obtain ⟨C, hC, hpoint⟩ := scalar0_abs_le_hs (I := I) (M := M) g
  refine ⟨2 * k, C ^ 2, sq_nonneg C, count, ?_, ?_⟩
  · intro Λ i hi
    simpa only [count, Set.Finite.mem_toFinset] using hi
  · intro Λ x
    by_cases hΛ : 1 < Λ
    · let F := count Λ
      let c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ :=
        fun i => TensorRSField.scalar0
          (eigenvectorSmooth (I := I) (M := M) g 0 0 i).toSection x
      let S : ℝ := ∑ i ∈ F, (c i) ^ 2
      have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (c i))
      have hkernel :
          diagonalKernel (I := I) (M := M) g 0 0 F x = S := by
        unfold diagonalKernel S
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← scalar0_fiber_sq (I := I) (M := M) g
          (eigenvectorSmooth (I := I) (M := M) g 0 0 i) x]
        symm
        rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
        rfl
      have hvalue :
          TensorRSField.scalar0
              (scalarCombo (I := I) (M := M) g F c).toSection x = S := by
        rw [combo_val (I := I) (M := M) g F c x]
        unfold S
        refine Finset.sum_congr rfl (fun i _ => ?_)
        change c i * c i = c i ^ 2
        ring
      have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hpoint' :
          S ≤ C * ‖ccTensorToHs (I := I) (M := M) g 0 (k : ℝ)
            (scalarCombo (I := I) (M := M) g F c)‖ := by
        have h := hpoint (scalarCombo (I := I) (M := M) g F c) x
        rw [hvalue, abs_of_nonneg hS] at h
        exact h
      have hpoint_sq :
          S ^ 2 ≤ C ^ 2 *
            ‖ccTensorToHs (I := I) (M := M) g 0 (k : ℝ)
              (scalarCombo (I := I) (M := M) g F c)‖ ^ 2 := by
        have hright : 0 ≤ C *
            ‖ccTensorToHs (I := I) (M := M) g 0 (k : ℝ)
              (scalarCombo (I := I) (M := M) g F c)‖ :=
          mul_nonneg hC (norm_nonneg _)
        have hsquare := pow_le_pow_left₀ hS hpoint' 2
        nlinarith
      have hnorm :
          ‖ccTensorToHs (I := I) (M := M) g 0 (k : ℝ)
              (scalarCombo (I := I) (M := M) g F c)‖ ^ 2 ≤
            Λ ^ k * S := by
        rw [combo_norm_sq (I := I) (M := M) g F c (k : ℝ) hk_nonneg]
        unfold S
        calc
          ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (k : ℝ) *
                (c i) ^ 2 ≤
              ∑ i ∈ F, Λ ^ k * (c i) ^ 2 := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            have hi_lt :
                1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ := by
              simpa only [F, count, Set.Finite.mem_toFinset] using hi
            have hbase :
                0 ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
              linarith [tensor_lambda_nonneg (I := I) (M := M) i]
            calc
              tensorSobolevWeight (I := I) (M := M) i (k : ℝ) * (c i) ^ 2 =
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ k *
                    (c i) ^ 2 := by
                      unfold tensorSobolevWeight
                      rw [Real.rpow_natCast]
              _ ≤ Λ ^ k * (c i) ^ 2 :=
                mul_le_mul_of_nonneg_right
                  (pow_le_pow_left₀ hbase hi_lt.le k) (sq_nonneg _)
          _ = Λ ^ k * ∑ i ∈ F, (c i) ^ 2 := by
            rw [Finset.mul_sum]
      have hmain : S ^ 2 ≤ C ^ 2 * (Λ ^ k * S) :=
        hpoint_sq.trans
          (mul_le_mul_of_nonneg_left hnorm (sq_nonneg C))
      have hsmall : S ≤ C ^ 2 * Λ ^ k := by
        by_cases hS0 : S = 0
        · rw [hS0]
          exact mul_nonneg (sq_nonneg C)
            (pow_nonneg (le_trans zero_le_one hΛ.le) k)
        · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
          nlinarith
      have hpow : Λ ^ k ≤ Λ ^ (2 * k) :=
        pow_le_pow_right₀ hΛ.le (by omega)
      rw [hkernel]
      exact hsmall.trans
        (mul_le_mul_of_nonneg_left hpow (sq_nonneg C))
    · have hcount : count Λ = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hi_lt :
            1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ := by
          simpa only [count, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hi
        exact (not_lt_of_ge
          (by linarith [tensor_lambda_nonneg (I := I) (M := M) i])) hi_lt
      have hpow : 0 ≤ Λ ^ (2 * k) := by
        rw [mul_comm 2 k, pow_mul]
        positivity
      rw [hcount]
      simpa only [diagonalKernel, Finset.sum_empty] using
        (mul_nonneg (sq_nonneg C) hpow)

/-- A negative power of the rank-zero tensor eigenvalues is summable.  This is
the scalar spectral input used by the conjugate-heat Galerkin construction. -/
theorem scalar_eigen_tail
    (g : SmoothRiemannianMetric I M) :
    EigenvalueTailSummable (I := I) (M := M) g 0 0 := by
  obtain ⟨q, B, hB, count, hmem, hkernel⟩ :=
    scalar_diag_le (I := I) (M := M) g
  exact eigenvalueTailSummable_of_countingBound (I := I) (M := M) g 0 0
    (eigenvalueCountingBound_of_pointwiseDiagonalKernelBound
      (I := I) (M := M) g 0 0 q B hB count hmem hkernel)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
