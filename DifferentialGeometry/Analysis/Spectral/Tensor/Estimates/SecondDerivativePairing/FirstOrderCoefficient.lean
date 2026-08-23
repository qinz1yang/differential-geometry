import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.SecondDerivativePairing.ZeroOrderCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.H1Jet
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.UnifBochnerGap

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem one_minus_connection_laplacian_squared_pairing_h3_h1_bound
    (g : SmoothRiemannianMetric I M) (W A : SmoothCcTensor g 0 2) :
    |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 W)).toFun A.toFun| ≤
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ *
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) A‖ := by
  let L : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 W
  let V : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 L
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) A‖
  let a : ℝ := ‖L‖
  let b : ℝ := ‖covGrad (I := I) (M := M) g 0 2 L‖
  let c : ℝ := ‖A‖
  let d : ℝ := ‖covGrad (I := I) (M := M) g 0 2 A‖
  have hy : 0 ≤ y := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hW : y ^ 2 = a ^ 2 + b ^ 2 := by
    have hodd := smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad
      (I := I) (M := M) g 1 W
    simpa only [y, a, b, L, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat,
      norm_ccHs_eq_smoothHs, oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_zero, SmoothCcTensor.norm_toL2] using hodd
  have hA : z ^ 2 = c ^ 2 + d ^ 2 := by
    simpa only [z, c, d] using cc_h1_jet_sq (I := I) (M := M) g A
  have hcs : a * c + b * d ≤ y * z := by
    apply (sq_le_sq₀ (add_nonneg (mul_nonneg ha hc) (mul_nonneg hb hd))
      (mul_nonneg hy hz)).mp
    rw [mul_pow, hW, hA]
    calc
      (a * c + b * d) ^ 2 ≤
          (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      _ = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by ring
  have hsplit := oneMinusConnLapSmooth_l2Inner_eq_add_covGrad
    (I := I) (M := M) g 0 2 L A
  change tensorL2Inner (I := I) (M := M) g 0 2 V.toFun A.toFun = _ at hsplit
  have hp₀ :
      |tensorL2Inner (I := I) (M := M) g 0 2 L.toFun A.toFun| ≤ a * c := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) L A]
    exact abs_real_inner_le_norm L A
  have hp₁ :
      |tensorL2Inner (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 L).toFun
          (covGrad (I := I) (M := M) g 0 2 A).toFun| ≤ b * d := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M)
      (covGrad (I := I) (M := M) g 0 2 L)
      (covGrad (I := I) (M := M) g 0 2 A)]
    exact abs_real_inner_le_norm _ _
  change |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun A.toFun| ≤ y * z
  calc
    _ = |tensorL2Inner (I := I) (M := M) g 0 2 L.toFun A.toFun +
        tensorL2Inner (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 L).toFun
          (covGrad (I := I) (M := M) g 0 2 A).toFun| := congrArg abs hsplit
    _ ≤ |tensorL2Inner (I := I) (M := M) g 0 2 L.toFun A.toFun| +
        |tensorL2Inner (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 L).toFun
          (covGrad (I := I) (M := M) g 0 2 A).toFun| := abs_add_le _ _
    _ ≤ a * c + b * d := add_le_add hp₀ hp₁
    _ ≤ y * z := hcs

theorem operator_field_application_second_covariant_derivative_pairing_h3_bound
    (g : SmoothRiemannianMetric I M) {K₀ K₁ B₀ B₁ : ℝ}
    (hact₀ : IsCurvAction0 (I := I) (M := M) g 2 K₀)
    (hact₁ : IsCurvAction0 (I := I) (M := M) g 3 K₁)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (Φ : SmoothCcTensor g 4 2)
    (hΦ₀ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        (Φ.toSection x) ≤ B₀ ^ 2)
    (hΦ₁ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 3 x
        ((covGrad (I := I) (M := M) g 4 2 Φ).toSection x) ≤ B₁ ^ 2)
    (W : SmoothCcTensor g 0 2) :
    |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 W)).toFun
        (operatorFieldApply (I := I) (M := M) g 4 2 Φ
          (iteratedCovGrad (I := I) g 0 2 2 W)).toFun| ≤
      B₀ * h2CovsumC K₀ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ ^ 2 +
        B₁ * h2CovsumC K₀ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ +
        Real.sqrt (Module.finrank ℝ E) * B₀ * h3CovsumC K₀ K₁ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖ ^ 2 := by
  classical
  let L : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 W
  let V : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 L
  let D₂ : SmoothCcTensor g 0 4 :=
    iteratedCovGrad (I := I) g 0 2 2 W
  let A : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 Φ D₂
  let Y₁ : SmoothCcTensor g 0 3 :=
    operatorFieldApply (I := I) (M := M) g 4 3
      (covGrad (I := I) (M := M) g 4 2 Φ) D₂
  let Y₀ : SmoothCcTensor g 0 3 :=
    operatorFieldApply (I := I) (M := M) g 5 3
      (slotExtend (I := I) (M := M) g 4 2 Φ)
      (covGrad (I := I) (M := M) g 0 4 D₂)
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W‖
  let C₂ : ℝ := h2CovsumC K₀
  let C₃ : ℝ := h3CovsumC K₀ K₁
  let d : ℝ := Module.finrank ℝ E
  let sd : ℝ := Real.sqrt d
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hsd : 0 ≤ sd := Real.sqrt_nonneg _
  have hL : ‖L‖ = x := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 1 W
    rw [show (1 : ℕ) = 0 + 1 from rfl,
      oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_zero,
      SmoothCcTensor.norm_toL2] at heven
    simpa only [L, x, Nat.reduceMul, Nat.cast_ofNat,
      norm_ccHs_eq_smoothHs] using heven.symm
  have hgradL :
      ‖covGrad (I := I) (M := M) g 0 2 L‖ ≤ y := by
    have hodd := smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad
      (I := I) (M := M) g 1 W
    have hodd' : y ^ 2 = ‖L‖ ^ 2 +
        ‖covGrad (I := I) (M := M) g 0 2 L‖ ^ 2 := by
      simpa only [y, L, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat,
        norm_ccHs_eq_smoothHs, oneMinusConnLapSmoothIter_succ,
        oneMinusConnLapSmoothIter_zero, SmoothCcTensor.norm_toL2] using hodd
    apply (sq_le_sq₀ (norm_nonneg _) hy).mp
    rw [hodd']
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hD₂ : ‖D₂‖ ≤ C₂ * x := by
    have hpick : ‖D₂‖ ≤
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j W‖ := by
      exact Finset.single_le_sum
        (fun j _ => norm_nonneg (iteratedCovGrad (I := I) g 0 2 j W))
        (by decide)
    exact hpick.trans (by
      simpa only [C₂, x] using
        covsum_hs_two (I := I) (M := M) g 2 hact₀ W)
  have hD₃ :
      ‖covGrad (I := I) (M := M) g 0 4 D₂‖ ≤ C₃ * y := by
    have hcomp :
        ‖covGrad (I := I) (M := M) g 0 4 D₂‖ =
          ‖iteratedCovGrad (I := I) g 0 2 3 W‖ := by
      dsimp only [D₂]
      exact iteratedCovGrad_comp_norm (I := I) (M := M) g 2 2 1 W
    rw [hcomp]
    exact (Finset.single_le_sum (s := Finset.range 4)
      (f := fun j => ‖iteratedCovGrad (I := I) g 0 2 j W‖)
      (fun j _ => norm_nonneg _) (show 3 ∈ Finset.range 4 by decide)).trans (by
        simpa only [C₃, y] using
          covsum_hs_three (I := I) (M := M) g 2 hact₀ hact₁ W)
  have hA : ‖A‖ ≤ B₀ * (C₂ * x) := by
    have h := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g 4 2 Φ D₂ B₀ hB₀ hΦ₀
    exact h.trans (mul_le_mul_of_nonneg_left hD₂ hB₀)
  have hY₁ : ‖Y₁‖ ≤ B₁ * (C₂ * x) := by
    have h := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g 4 3
      (covGrad (I := I) (M := M) g 4 2 Φ) D₂ B₁ hB₁ hΦ₁
    exact h.trans (mul_le_mul_of_nonneg_left hD₂ hB₁)
  have hslot : ∀ p : M,
      riemannianFiberNormSq (I := I) (M := M) g 5 3 p
          ((slotExtend (I := I) (M := M) g 4 2 Φ).toSection p) ≤
        (sd * B₀) ^ 2 := by
    intro p
    rw [riemannianFiberNormSq_slotExtend_eq (I := I) (M := M) g 4 2 Φ p]
    calc
      (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g 4 2 p
            (Φ.toSection p) ≤ d * B₀ ^ 2 :=
        mul_le_mul_of_nonneg_left (hΦ₀ p) (Nat.cast_nonneg _)
      _ = (sd * B₀) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by dsimp only [d]; positivity)]
  have hY₀ : ‖Y₀‖ ≤ (sd * B₀) * (C₃ * y) := by
    have h := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g 5 3
      (slotExtend (I := I) (M := M) g 4 2 Φ)
      (covGrad (I := I) (M := M) g 0 4 D₂)
      (sd * B₀) (mul_nonneg hsd hB₀) hslot
    exact h.trans (mul_le_mul_of_nonneg_left hD₃
      (mul_nonneg hsd hB₀))
  have hgradA :
      covGrad (I := I) (M := M) g 0 2 A = Y₁ + Y₀ := by
    dsimp only [A, Y₁, Y₀]
    exact covGrad_operatorFieldApply_eq (I := I) (M := M) g 4 2 Φ D₂
  have hsplit := oneMinusConnLapSmooth_l2Inner_eq_add_covGrad
    (I := I) (M := M) g 0 2 L A
  change tensorL2Inner (I := I) (M := M) g 0 2 V.toFun A.toFun = _ at hsplit
  have hadd := tensorL2Inner_add_right (I := I) (M := M) g 0 3
    (covGrad (I := I) (M := M) g 0 2 L).toFun Y₁.toFun Y₀.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (covGrad (I := I) (M := M) g 0 2 L) Y₁)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (covGrad (I := I) (M := M) g 0 2 L) Y₀)
  rw [hgradA, SmoothCcTensor.toFun_add, hadd] at hsplit
  have hp₀ :
      |tensorL2Inner (I := I) (M := M) g 0 2 L.toFun A.toFun| ≤
        x * (B₀ * (C₂ * x)) := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) L A]
    exact (abs_real_inner_le_norm L A).trans (by
      rw [hL]
      exact mul_le_mul_of_nonneg_left hA hx)
  have hp₁ :
      |tensorL2Inner (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 L).toFun Y₁.toFun| ≤
        y * (B₁ * (C₂ * x)) := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M)
      (covGrad (I := I) (M := M) g 0 2 L) Y₁]
    exact (abs_real_inner_le_norm
      (covGrad (I := I) (M := M) g 0 2 L) Y₁).trans
        (mul_le_mul hgradL hY₁ (norm_nonneg _) hy)
  have hp₂ :
      |tensorL2Inner (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 L).toFun Y₀.toFun| ≤
        y * ((sd * B₀) * (C₃ * y)) := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M)
      (covGrad (I := I) (M := M) g 0 2 L) Y₀]
    exact (abs_real_inner_le_norm
      (covGrad (I := I) (M := M) g 0 2 L) Y₀).trans
        (mul_le_mul hgradL hY₀ (norm_nonneg _) hy)
  change |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun A.toFun| ≤ _
  calc
    _ = |tensorL2Inner (I := I) (M := M) g 0 2 L.toFun A.toFun +
        (tensorL2Inner (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 L).toFun Y₁.toFun +
          tensorL2Inner (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 L).toFun Y₀.toFun)| :=
      congrArg abs hsplit
    _ ≤
      |tensorL2Inner (I := I) (M := M) g 0 2 L.toFun A.toFun| +
        |tensorL2Inner (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 L).toFun Y₁.toFun| +
        |tensorL2Inner (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 L).toFun Y₀.toFun| := by
        calc
          _ ≤ |tensorL2Inner (I := I) (M := M) g 0 2 L.toFun A.toFun| +
              |tensorL2Inner (I := I) (M := M) g 0 3
                  (covGrad (I := I) (M := M) g 0 2 L).toFun Y₁.toFun +
                tensorL2Inner (I := I) (M := M) g 0 3
                  (covGrad (I := I) (M := M) g 0 2 L).toFun Y₀.toFun| :=
            abs_add_le _ _
          _ ≤ |tensorL2Inner (I := I) (M := M) g 0 2 L.toFun A.toFun| +
                (|tensorL2Inner (I := I) (M := M) g 0 3
                    (covGrad (I := I) (M := M) g 0 2 L).toFun Y₁.toFun| +
                  |tensorL2Inner (I := I) (M := M) g 0 3
                    (covGrad (I := I) (M := M) g 0 2 L).toFun Y₀.toFun|) :=
            add_le_add le_rfl (abs_add_le _ _)
          _ = _ := by ring
    _ ≤ x * (B₀ * (C₂ * x)) + y * (B₁ * (C₂ * x)) +
        y * ((sd * B₀) * (C₃ * y)) := by
      gcongr
    _ = B₀ * h2CovsumC K₀ * x ^ 2 +
        B₁ * h2CovsumC K₀ * y * x +
        Real.sqrt (Module.finrank ℝ E) * B₀ * h3CovsumC K₀ K₁ * y ^ 2 := by
      dsimp only [C₂, C₃, sd, d]
      ring

end DifferentialGeometry.Analysis.Spectral

end
