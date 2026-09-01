import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.ApplicationJetWindow
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2PointwiseUnif
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralNormLIterateLadder


noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem operator_field_application_second_covariant_derivative_pairing_h2_bound
    (g : SmoothRiemannianMetric I M) {K B : ℝ}
    (hact : IsCurvAction0 (I := I) (M := M) g 2 K)
    (hB : 0 ≤ B) (Φ : SmoothCcTensor g 4 2)
    (hΦ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        (Φ.toSection x) ≤ B ^ 2)
    (W : SmoothCcTensor g 0 2) :
    |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2 W).toFun
        (operatorFieldApply (I := I) (M := M) g 4 2 Φ
          (iteratedCovGrad (I := I) g 0 2 2 W)).toFun| ≤
      B * h2CovsumC K *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ ^ 2 := by
  classical
  let L : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 W
  let A : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 Φ
      (iteratedCovGrad (I := I) g 0 2 2 W)
  let H2 : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖
  have hH2 : 0 ≤ H2 := norm_nonneg _
  have hK : 0 ≤ h2CovsumC K := h2CovsumC_nonneg K
  have hW2sum :
      ‖iteratedCovGrad (I := I) g 0 2 2 W‖ ≤
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j W‖ := by
    exact Finset.single_le_sum
      (fun j _ => norm_nonneg (iteratedCovGrad (I := I) g 0 2 j W))
      (by decide)
  have hW2 :
      ‖iteratedCovGrad (I := I) g 0 2 2 W‖ ≤ h2CovsumC K * H2 :=
    hW2sum.trans (by
      simpa only [H2] using
        covsum_hs_two (I := I) (M := M) g 2 hact W)
  have hA : ‖A‖ ≤ B * (h2CovsumC K * H2) := by
    have happ := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g 4 2 Φ
      (iteratedCovGrad (I := I) g 0 2 2 W) B hB hΦ
    exact happ.trans (mul_le_mul_of_nonneg_left hW2 hB)
  have hL : ‖L‖ = H2 := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 1 W
    rw [show (1 : ℕ) = 0 + 1 from rfl,
      oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_zero,
      SmoothCcTensor.norm_toL2] at heven
    rw [show (((2 * (0 + 1) : ℕ) : ℝ)) = 2 by norm_num] at heven
    simpa only [L, H2, Nat.zero_add, Nat.reduceMul, Nat.cast_ofNat,
      norm_ccHs_eq_smoothHs] using heven.symm
  have hpair :
      |tensorL2Inner (I := I) (M := M) g 0 2 L.toFun A.toFun| ≤
        ‖L‖ * ‖A‖ := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) L A]
    exact abs_real_inner_le_norm L A
  change |tensorL2Inner (I := I) (M := M) g 0 2 L.toFun A.toFun| ≤ _
  calc
    |tensorL2Inner (I := I) (M := M) g 0 2 L.toFun A.toFun|
        ≤ ‖L‖ * ‖A‖ := hpair
    _ ≤ H2 * (B * (h2CovsumC K * H2)) := by
      rw [hL]
      exact mul_le_mul_of_nonneg_left hA hH2
    _ = B * h2CovsumC K * H2 ^ 2 := by ring

theorem operator_field_application_second_covariant_derivative_pairing_h4_bound
    (g : SmoothRiemannianMetric I M) {K B : ℝ}
    (hact : IsCurvAction0 (I := I) (M := M) g 2 K)
    (hB : 0 ≤ B) (Φ : SmoothCcTensor g 4 2)
    (hΦ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        (Φ.toSection x) ≤ B ^ 2)
    (U : SmoothCcTensor g 0 2) :
    |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 U)).toFun
        (operatorFieldApply (I := I) (M := M) g 4 2 Φ
          (iteratedCovGrad (I := I) g 0 2 2
            (oneMinusConnLapSmooth (I := I) g 0 2 U))).toFun| ≤
      B * h2CovsumC K *
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ ^ 2 := by
  have hpair := operator_field_application_second_covariant_derivative_pairing_h2_bound (I := I) (M := M) g hact hB Φ hΦ
    (oneMinusConnLapSmooth (I := I) g 0 2 U)
  have hshift :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (oneMinusConnLapSmooth (I := I) g 0 2 U)‖ =
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ := by
    rw [norm_ccHs_eq_smoothHs, norm_ccHs_eq_smoothHs]
    exact (smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
      (I := I) (M := M) g 2 U).symm
  rwa [hshift] at hpair

end DifferentialGeometry.Analysis.Spectral

end
