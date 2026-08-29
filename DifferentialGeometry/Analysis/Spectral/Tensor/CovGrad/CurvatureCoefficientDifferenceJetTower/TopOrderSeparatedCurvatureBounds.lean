import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.TopOrderSeparatedTransport
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.PairTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.TraceGrid

open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Geometry.Operator

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel
    ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

namespace CurvatureCoefficientDifferenceJetTower
end CurvatureCoefficientDifferenceJetTower

open CurvatureCoefficientDifferenceJetTower

section TopOrderSeparatedRungSlotInsert



namespace CurvatureCoefficientDifferenceJetTower

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
lemma cometricRaiseSlot0Field_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W W' : SmoothCcTensor g₀ 0 (s + 2)) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ s (W - W') =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ s W -
        cometricRaiseSlot0Field (I := I) (M := M) g₀ s W' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((cometricRaiseSlot0Field (I := I) (M := M) g₀ s W -
        cometricRaiseSlot0Field (I := I) (M := M) g₀ s W').toSection x) =
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W).toSection x -
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W').toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [cometricRaiseSlot0Field_toSection, cometricRaiseSlot0Field_toSection,
    cometricRaiseSlot0Field_toSection]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (W - W').toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [show ((W - W').toSection x) = W.toSection x - W'.toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rfl]
  apply ContinuousLinearMap.ext
  intro om
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (show TensorRSSpace 1 (s + 1) I x from
          cometricRaiseSlot0Fib g₀ s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
              (unitTensor (I := I) (M := M) x))) -
        (show TensorRSSpace 1 (s + 1) I x from
          cometricRaiseSlot0Fib g₀ s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W'.toSection x)
              (unitTensor (I := I) (M := M) x)))) om) =
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        cometricRaiseSlot0Fib g₀ s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
            (unitTensor (I := I) (M := M) x))) om -
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        cometricRaiseSlot0Fib g₀ s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W'.toSection x)
            (unitTensor (I := I) (M := M) x))) om from rfl]
  rw [cometricRaiseSlot0Fib_clm_apply, cometricRaiseSlot0Fib_clm_apply,
    cometricRaiseSlot0Fib_clm_apply]
  set DW : Tensor0SSpace (s + 2) I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hDW_def
  set DW' : Tensor0SSpace (s + 2) I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W'.toSection x)
      (unitTensor (I := I) (M := M) x) with hDW'_def
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  calc Tensor0SSpace.toModel
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (s + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) (DW - DW')) w
      = Tensor0SSpace.toModel (DW - DW')
          (Fin.cons
            (tangentSpaceModelContinuousLinearEquiv (I := I) x
              (inverseMetricSharpFib (I := I) g₀ x om)) w) :=
        interiorProduct_toModel_apply (I := I) (M := M) (s + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) (DW - DW') w
    _ = Tensor0SSpace.toModel DW
          (Fin.cons
            (tangentSpaceModelContinuousLinearEquiv (I := I) x
              (inverseMetricSharpFib (I := I) g₀ x om)) w) -
        Tensor0SSpace.toModel DW'
          (Fin.cons
            (tangentSpaceModelContinuousLinearEquiv (I := I) x
              (inverseMetricSharpFib (I := I) g₀ x om)) w) := by
        rw [Tensor0SSpace.toModel_sub]
        simp only [sub_apply]
    _ = Tensor0SSpace.toModel
          (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (s + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) DW) w -
        Tensor0SSpace.toModel
          (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (s + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) DW') w := by
        rw [interiorProduct_toModel_apply (I := I) (M := M) (s + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) DW w]
        rw [interiorProduct_toModel_apply (I := I) (M := M) (s + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) DW' w]
    _ = Tensor0SSpace.toModel
          (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (s + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) DW -
          Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (s + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) DW') w := by
        rw [Tensor0SSpace.toModel_sub]
        simp only [sub_apply]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_cometricRaiseSlot0Field_eq (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g₀ 0 (s + 2)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (s + 1) x
        ((cometricRaiseSlot0Field (I := I) (M := M) g₀ s W).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 2) x (W.toSection x) := by
  have h := riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ s W 0 x
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma iteratedCovGrad_operatorFieldComposition_eq_coefficient_head_add_tail (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) (W : SmoothCcTensor g₀ a b) (j : ℕ) :
    iteratedCovGrad (I := I) g₀ a c j (ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W) =
      ccOperatorFieldComp (I := I) (M := M) g₀ a b (c + j)
          (iteratedCovGrad (I := I) g₀ b c j Φ) W +
        ∑ k ∈ Finset.range j,
          ccOperatorFieldComp (I := I) (M := M) g₀ a (b + (k + 1)) (c + j)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ b c Φ j (k + 1))
            (iteratedCovGrad (I := I) g₀ a b (k + 1) W) := by
  rw [iteratedCovGrad_operatorFieldComposition_eq (I := I) (M := M) g₀ a b c Φ W j]
  rw [Finset.sum_range_succ' (fun k =>
    ccOperatorFieldComp (I := I) (M := M) g₀ a (b + k) (c + j)
      (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ b c Φ j k)
      (iteratedCovGrad (I := I) g₀ a b k W)) j]
  have hf0 : ccOperatorFieldComp (I := I) (M := M) g₀ a (b + 0) (c + j)
      (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ b c Φ j 0)
      (iteratedCovGrad (I := I) g₀ a b 0 W) =
      ccOperatorFieldComp (I := I) (M := M) g₀ a b (c + j)
        (iteratedCovGrad (I := I) g₀ b c j Φ) W :=
    congrArg (fun Z : SmoothCcTensor g₀ b (c + j) =>
      ccOperatorFieldComp (I := I) (M := M) g₀ a b (c + j) Z W)
      (operatorFieldApplicationLeibnizPsi_zero_right_eq (I := I) (M := M) g₀ b c Φ j)
  rw [hf0]
  exact add_comm _ _

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_operatorFieldComposition_parallel_argument_head_le (g₀ : SmoothRiemannianMetric I M) (p a b : ℕ)
    (Φ : SmoothCcTensor g₀ a b) (i : ℕ) (HX : SmoothCcTensor g₀ p (a + i)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ p (b + i) x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ p (a + i) (b + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ a b Φ i i) HX).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ a b x (Φ.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ p (a + i) x (HX.toSection x) :=
  riemannianFiberNormSq_operatorFieldComposition_operatorFieldApplicationLeibnizPsi_diag_le (I := I) (M := M) g₀ p a b Φ i HX x

omit [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_operatorFieldComposition_parallel_argument_residual_le (g₀ : SmoothRiemannianMetric I M) (p a b : ℕ)
    (Φ : SmoothCcTensor g₀ a b)
    (hΦ : covGrad (I := I) (M := M) g₀ a b Φ = 0)
    (X : SmoothCcTensor g₀ p a) (i : ℕ) (HX : SmoothCcTensor g₀ p (a + i)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ p (b + i) x
        ((iteratedCovGrad (I := I) g₀ p b i (ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ X) -
          ccOperatorFieldComp (I := I) (M := M) g₀ p (a + i) (b + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ a b Φ i i) HX).toSection x) ≤
      2 * (riemannianFiberNormSq (I := I) (M := M) g₀ a b x (Φ.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ p (a + i) x
          ((iteratedCovGrad (I := I) g₀ p a i X - HX).toSection x)) := by
  have hsplit : iteratedCovGrad (I := I) g₀ p b i
        (ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ X) -
        ccOperatorFieldComp (I := I) (M := M) g₀ p (a + i) (b + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ a b Φ i i) HX =
      ccOperatorFieldComp (I := I) (M := M) g₀ p (a + i) (b + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ a b Φ i i)
          (iteratedCovGrad (I := I) g₀ p a i X - HX) +
        ∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ p (a + k) (b + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ a b Φ i k)
            (iteratedCovGrad (I := I) g₀ p a k X) := by
    rw [iteratedCovGrad_operatorFieldComposition_eq_argCorner_add_lower (I := I) (M := M) g₀ p a b Φ X i]
    rw [operatorFieldComposition_sub_right_cc (I := I) (M := M) g₀ p (a + i) (b + i)
      (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ a b Φ i i)
      (iteratedCovGrad (I := I) g₀ p a i X) HX]
    exact add_sub_right_comm _ _ _
  rw [hsplit]
  rw [show (((ccOperatorFieldComp (I := I) (M := M) g₀ p (a + i) (b + i)
        (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ a b Φ i i)
        (iteratedCovGrad (I := I) g₀ p a i X - HX) +
      ∑ k ∈ Finset.range i,
        ccOperatorFieldComp (I := I) (M := M) g₀ p (a + k) (b + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ a b Φ i k)
          (iteratedCovGrad (I := I) g₀ p a k X)).toSection x)) =
      (ccOperatorFieldComp (I := I) (M := M) g₀ p (a + i) (b + i)
        (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ a b Φ i i)
        (iteratedCovGrad (I := I) g₀ p a i X - HX)).toSection x +
      (∑ k ∈ Finset.range i,
        ccOperatorFieldComp (I := I) (M := M) g₀ p (a + k) (b + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ a b Φ i k)
          (iteratedCovGrad (I := I) g₀ p a k X)).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ p (b + i) x _ _) ?_
  have hcorr : riemannianFiberNormSq (I := I) (M := M) g₀ p (b + i) x
      ((∑ k ∈ Finset.range i,
        ccOperatorFieldComp (I := I) (M := M) g₀ p (a + k) (b + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ a b Φ i k)
          (iteratedCovGrad (I := I) g₀ p a k X)).toSection x) ≤ 0 := by
    refine le_trans (riemannianFiberNormSq_operatorFieldComposition_argLower_le (I := I) (M := M) g₀ p a b Φ X i x) ?_
    have hzero : ∀ k ∈ Finset.range i,
        riemannianFiberNormSq (I := I) (M := M) g₀ a (b + (i - k)) x
            ((iteratedCovGrad (I := I) g₀ a b (i - k) Φ).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ p (a + k) x
            ((iteratedCovGrad (I := I) g₀ p a k X).toSection x) = 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show i - k = (i - k - 1) + 1 from by omega]
      rw [iteratedCovGrad_zero_of_covGrad_zero (I := I) (M := M) g₀ a b Φ hΦ (i - k - 1)]
      rw [SmoothCcTensor.toSection_zero]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
      rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ a (b + ((i - k - 1) + 1)) x]
      ring
    rw [Finset.sum_congr rfl hzero, Finset.sum_const, smul_zero, mul_zero]
  have hhead := le_trans
    (riemannianFiberNormSq_operatorFieldComposition_operatorFieldApplicationLeibnizPsi_diag_le (I := I) (M := M) g₀ p a b Φ i
      (iteratedCovGrad (I := I) g₀ p a i X - HX) x) (le_refl _)
  linarith [hhead, hcorr]

end CurvatureCoefficientDifferenceJetTower

theorem riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_topOrderSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 1 (1 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 1 i
                    (slotInsertEndoCc (I := I) (M := M) g₀ 0
                      (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨KtA, hKtA_nn, KcA, hKcA_nn, hA⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_topOrderSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨S, hS_nn, hS⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_sharpFlatEndoCc_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨CDel, hCDel_nn, hCDel⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciMixedSharpBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cPhi, hcPhi_nn, hcPhi⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
  obtain ⟨cB, hcB_nn, hcB⟩ := exists_backgroundJet_riemannianFiberNormSq_bound (I := I) (M := M) g₀ 1 1
    (slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricEndoRaisedField (I := I) (M := M) g₀))
  obtain ⟨cId, hcId_nn, hcId⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 1 1
    (slotInsertEndoCc (I := I) (M := M) g₀ 0 (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀))
  refine ⟨cPhi * KtA * S 0,
    mul_nonneg (mul_nonneg hcPhi_nn hKtA_nn) (hS_nn 0), ?_⟩
  refine ⟨fun i => 4 * (cPhi * (KcA i) * S 0) +
      4 * ((i : ℝ) * ∑ k ∈ Finset.range i,
        operatorFieldApplicationGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
          Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) +
      4 * (operatorFieldApplicationGdiag (E := E) i * ∑ a' ∈ Finset.range (i + 1),
        cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))),
    fun i => by
      have h1 : (0 : ℝ) ≤ cPhi * (KcA i) * S 0 :=
        mul_nonneg (mul_nonneg hcPhi_nn (hKcA_nn i)) (hS_nn 0)
      have h2 : (0 : ℝ) ≤ (i : ℝ) * ∑ k ∈ Finset.range i,
          operatorFieldApplicationGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
            Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2) :=
        mul_nonneg (Nat.cast_nonneg i) (Finset.sum_nonneg fun k _ =>
          mul_nonneg (mul_nonneg (mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
            (hCDel_nn _)) (hS_nn _)) (Combinatorics.windowPairCellCount_nonneg _ _))
      have h3 : (0 : ℝ) ≤ operatorFieldApplicationGdiag (E := E) i * ∑ a' ∈ Finset.range (i + 1),
          cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l)) :=
        mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i) (Finset.sum_nonneg fun a' _ =>
          mul_nonneg (hcB_nn a') (Finset.sum_nonneg fun l _ => by
            have := hS_nn 0; have := hS_nn l; linarith))
      linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  obtain ⟨HdA, hHdA_head, hHdA_res⟩ := hA g₁ T htie hδ_le hδ0 hbound i
  set dTr : SmoothCcTensor g₀ 4 2 := cometricDoubleTraceField (I := I) g₀ 2 with hdTr_def
  set RLD : SmoothCcTensor g₀ 0 4 :=
    riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ with hRLD_def
  set Z : SmoothCcTensor g₀ 0 2 := ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 2 dTr RLD with hZ_def
  set ZS : SmoothCcTensor g₀ 0 2 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) Z with hZS_def
  set sF : SmoothCcTensor g₀ 1 1 := sharpFlatEndoCc (I := I) g₀ g₁ with hsF_def
  set B0f : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricEndoRaisedField (I := I) (M := M) g₀)
    with hB0f_def
  set Dg : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)
    with hDg_def
  set InsId : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀)
    with hInsId_def
  set Delta : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
      slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricEndoRaisedField (I := I) (M := M) g₀)
    with hDelta_def
  have hdTr_par : covGrad (I := I) (M := M) g₀ 4 2 dTr = 0 :=
    cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2
  have hsF_split : sF = Dg + InsId := by
    rw [hsF_def, hDg_def, hInsId_def,
      sharpFlatEndoCc_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁,
      metricComparisonEndomorphismField_diff_split (I := I) (M := M) g₀ g₁,
      slotInsertEndoCc_add_endo (I := I) (M := M) g₀ 0]
  have hDg_eq : Dg = sF - InsId := eq_sub_of_add_eq hsF_split.symm
  have hBmix : slotInsertEndoCc (I := I) (M := M) g₀ 0
      (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) = Delta + B0f := by
    rw [hDelta_def, hB0f_def]; abel
  have hDeltaDg : ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta Dg =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta sF -
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta InsId := by
    rw [hDg_eq]
    exact operatorFieldComposition_sub_right_cc (I := I) (M := M) g₀ 1 1 1 Delta sF InsId
  have hInsRet : ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta InsId = Delta := by
    rw [hInsId_def]
    exact operatorFieldComposition_slotInsert_id_eq (I := I) (M := M) g₀ 0 1 Delta
  have hXsplit : slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta sF +
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 B0f Dg := by
    calc slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)
        = (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀)) +
          ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) :=
          slotInsertEndoCc_zero_ricEndoBackgroundDifference_telescope (I := I) (M := M) g₀ g₁
      _ = Delta + ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 (Delta + B0f) Dg := by
          rw [← hDelta_def, ← hDg_def, hBmix]
      _ = Delta + (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta Dg +
            ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 B0f Dg) := by
          rw [operatorFieldComposition_add_left_cc (I := I) (M := M) g₀ 1 1 1 Delta B0f Dg]
      _ = Delta + ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta sF - Delta) +
            ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 B0f Dg) := by
          rw [hDeltaDg, hInsRet]
      _ = ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta sF +
            ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 B0f Dg := by abel
  have hΔrepr := slotInsert_ricMixedSharp_sub_ricEndoRaised_eq_raise_doubleTrace
    (I := I) (M := M) g₀ g₁
  obtain ⟨σs, hσs⟩ := exists_iteratedCovGrad_domDomCongrSection_eq (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) Z i
  obtain ⟨σr, hσr⟩ := exists_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M)
    g₀ 0 ZS i
  set HdZ : SmoothCcTensor g₀ 0 (2 + i) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + i) (2 + i)
      (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 4 2 dTr i i) HdA with hHdZ_def
  set HdD : SmoothCcTensor g₀ 1 (1 + i) :=
    castCcTensorRank g₀ 1 (by omega : (0 + i) + 1 = (0 + 1) + i)
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ (0 + i)
        (domDomCongrSection (I := I) g₀ σr
          (castCcTensorRank g₀ 0 (by omega : (0 + 2) + i = (0 + i) + 2)
            (domDomCongrSection (I := I) g₀ σs HdZ)))) with hHdD_def
  refine ⟨ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (1 + i) HdD sF, ?_, ?_⟩
  · intro x
    have hHdD_riemannianFiberNormSq : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (HdD.toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x (HdZ.toSection x) := by
      rw [hHdD_def]
      rw [riemannianFiberNormSq_castCcTensorRank_eq (I := I) (M := M) g₀ 1
        (by omega : (0 + i) + 1 = (0 + 1) + i) _ x]
      rw [riemannianFiberNormSq_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ (0 + i) _ x]
      rw [riemannianFiberNormSq_domDomCongrSection_eq (I := I) (M := M) g₀ σr _ x]
      rw [riemannianFiberNormSq_castCcTensorRank_eq (I := I) (M := M) g₀ 0
        (by omega : (0 + 2) + i = (0 + i) + 2) _ x]
      rw [riemannianFiberNormSq_domDomCongrSection_eq (I := I) (M := M) g₀ σs _ x]
    rw [operatorFieldComposition_toSection (I := I) (M := M) g₀ 1 1 (1 + i) HdD sF x]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 (1 + i) x
      _ _) ?_
    have hHdZ_le : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        (HdZ.toSection x) ≤
        cPhi * (KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
      rw [hHdZ_def]
      refine le_trans (riemannianFiberNormSq_operatorFieldComposition_parallel_argument_head_le (I := I) (M := M) g₀ 0 4 2 dTr i HdA x) ?_
      exact mul_le_mul (hcPhi x) (hHdA_head x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x _) hcPhi_nn
    have hsF0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (sF.toSection x) ≤ S 0 := by
      have h := hS g₁ T htie hδ_le hδ0 hbound 0 x
      rw [iteratedCovGrad_zero] at h
      rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
      exact h
    have hb_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)
    have hHdD_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + i) x
      (HdD.toSection x)
    have hsF_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x (sF.toSection x)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (HdD.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (sF.toSection x)
        ≤ (cPhi * (KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) * S 0 := by
          refine mul_le_mul ?_ hsF0 hsF_nn ?_
          · rw [hHdD_riemannianFiberNormSq]; exact hHdZ_le
          · exact mul_nonneg hcPhi_nn (mul_nonneg hKtA_nn hb_nn)
      _ = cPhi * KtA * S 0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
    have hb : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hWfin_def
    have hWfin_nn : 0 ≤ Wfin :=
      Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
    have hWfin_one : 1 ≤ Wfin :=
      Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
    have hNdDiff : iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD =
        castCcTensorRank g₀ 1 (by omega : (0 + i) + 1 = (0 + 1) + i)
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ (0 + i)
            (domDomCongrSection (I := I) g₀ σr
              (castCcTensorRank g₀ 0 (by omega : (0 + 2) + i = (0 + i) + 2)
                (domDomCongrSection (I := I) g₀ σs
                  (iteratedCovGrad (I := I) g₀ 0 2 i Z - HdZ))))) := by
      have hNdDelta : iteratedCovGrad (I := I) g₀ 1 1 i Delta =
          castCcTensorRank g₀ 1 (by omega : (0 + i) + 1 = (0 + 1) + i)
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ (0 + i)
              (domDomCongrSection (I := I) g₀ σr
                (castCcTensorRank g₀ 0 (by omega : (0 + 2) + i = (0 + i) + 2)
                  (domDomCongrSection (I := I) g₀ σs
                    (iteratedCovGrad (I := I) g₀ 0 2 i Z))))) := by
        calc iteratedCovGrad (I := I) g₀ 1 1 i Delta
            = iteratedCovGrad (I := I) g₀ 1 (0 + 1) i
                (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 ZS) := by
              rw [hDelta_def, hΔrepr, hZS_def, hZ_def, hdTr_def, hRLD_def]
          _ = castCcTensorRank g₀ 1 (by omega : (0 + i) + 1 = (0 + 1) + i)
                (cometricRaiseSlot0Field (I := I) (M := M) g₀ (0 + i)
                  (domDomCongrSection (I := I) g₀ σr
                    (castCcTensorRank g₀ 0 (by omega : (0 + 2) + i = (0 + i) + 2)
                      (iteratedCovGrad (I := I) g₀ 0 (0 + 2) i ZS)))) := hσr
          _ = _ := by
              rw [show (iteratedCovGrad (I := I) g₀ 0 (0 + 2) i ZS) =
                  domDomCongrSection (I := I) g₀ σs
                    (iteratedCovGrad (I := I) g₀ 0 2 i Z) from by
                rw [← hσs, hZS_def]]
      rw [hNdDelta, hHdD_def]
      rw [← castCcTensorRank_sub (I := I) (M := M) g₀ 1
        (by omega : (0 + i) + 1 = (0 + 1) + i)]
      rw [← cometricRaiseSlot0Field_sub (I := I) (M := M) g₀ (0 + i)]
      rw [← domDomCongrSection_sub (I := I) (M := M) g₀ σr]
      rw [← castCcTensorRank_sub (I := I) (M := M) g₀ 0
        (by omega : (0 + 2) + i = (0 + i) + 2)]
      rw [← domDomCongrSection_sub (I := I) (M := M) g₀ σs]
    have hΔres : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD).toSection x) ≤
        2 * (cPhi * (KcA i * Wfin)) := by
      rw [hNdDiff]
      rw [riemannianFiberNormSq_castCcTensorRank_eq (I := I) (M := M) g₀ 1
        (by omega : (0 + i) + 1 = (0 + 1) + i) _ x]
      rw [riemannianFiberNormSq_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ (0 + i) _ x]
      rw [riemannianFiberNormSq_domDomCongrSection_eq (I := I) (M := M) g₀ σr _ x]
      rw [riemannianFiberNormSq_castCcTensorRank_eq (I := I) (M := M) g₀ 0
        (by omega : (0 + 2) + i = (0 + i) + 2) _ x]
      rw [riemannianFiberNormSq_domDomCongrSection_eq (I := I) (M := M) g₀ σs _ x]
      rw [hHdZ_def, hZ_def]
      refine le_trans (riemannianFiberNormSq_operatorFieldComposition_parallel_argument_residual_le (I := I) (M := M) g₀ 0 4 2 dTr
        hdTr_par RLD i HdA x) ?_
      have hres := hHdA_res x
      have hd_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA).toSection x)
      have hKcW_nn : 0 ≤ KcA i * Wfin := mul_nonneg (hKcA_nn i) hWfin_nn
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine mul_le_mul (hcPhi x) ?_ hd_nn hcPhi_nn
      exact hres
    set P1t := ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (1 + i)
        (iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD) sF with hP1t_def
    set P2t := ∑ k ∈ Finset.range i,
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (1 + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1))
          (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF) with hP2t_def
    set P3t := iteratedCovGrad (I := I) g₀ 1 1 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 B0f Dg) with hP3t_def
    have hsplit : iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)) -
          ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (1 + i) HdD sF =
        P1t + (P2t + P3t) := by
      rw [hP1t_def, hP2t_def, hP3t_def, hXsplit]
      rw [iteratedCovGrad_add (I := I) g₀ 1 1 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 Delta sF)
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1 B0f Dg)]
      rw [iteratedCovGrad_operatorFieldComposition_eq_coefficient_head_add_tail (I := I) (M := M) g₀ 1 1 1 Delta sF i]
      rw [operatorFieldComposition_sub_left_cc (I := I) (M := M) g₀ 1 1 (1 + i)
        (iteratedCovGrad (I := I) g₀ 1 1 i Delta) HdD sF]
      abel
    rw [hsplit]
    rw [show ((P1t + (P2t + P3t)).toSection x) =
        P1t.toSection x + (P2t + P3t).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + i) x _ _) ?_
    rw [show ((P2t + P3t).toSection x) = P2t.toSection x + P3t.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    have hP1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (P1t.toSection x) ≤ 2 * (cPhi * (KcA i)) * S 0 * Wfin := by
      rw [hP1t_def]
      rw [operatorFieldComposition_toSection (I := I) (M := M) g₀ 1 1 (1 + i)
        (iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD) sF x]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1
        (1 + i) x _ _) ?_
      have hsF0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (sF.toSection x) ≤
          S 0 := by
        have h := hS g₁ T htie hδ_le hδ0 hbound 0 x
        rw [iteratedCovGrad_zero] at h
        rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
        exact h
      have hsF_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x
        (sF.toSection x)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (sF.toSection x)
          ≤ (2 * (cPhi * (KcA i * Wfin))) * S 0 := by
            refine mul_le_mul hΔres hsF0 hsF_nn ?_
            exact mul_nonneg (by norm_num)
              (mul_nonneg hcPhi_nn (mul_nonneg (hKcA_nn i) hWfin_nn))
        _ = 2 * (cPhi * (KcA i)) * S 0 * Wfin := by ring
    have hP2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (P2t.toSection x) ≤
        ((i : ℝ) * ∑ k ∈ Finset.range i,
          operatorFieldApplicationGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
            Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin := by
      rw [hP2t_def]
      rw [SmoothCcTensor.toSection_sum_apply]
      refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g₀ 1
        (1 + i) x (Finset.range i) _) ?_
      rw [Finset.card_range]
      have hterm : ∀ k ∈ Finset.range i,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (1 + i)
              (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1))
              (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF)).toSection x) ≤
          (operatorFieldApplicationGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
            Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [operatorFieldComposition_toSection (I := I) (M := M) g₀ 1 (1 + (k + 1)) (1 + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1))
          (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF) x]
        refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1
          (1 + (k + 1)) (1 + i) x _ _) ?_
        have hPsi : riemannianFiberNormSq (I := I) (M := M) g₀ (1 + (k + 1)) (1 + i) x
            ((operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1)).toSection x) ≤
            operatorFieldApplicationGdiag (E := E) i *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (i - (k + 1))) x
                ((iteratedCovGrad (I := I) g₀ 1 1 (i - (k + 1)) Delta).toSection x) := by
          have hw := riemannianFiberNormSq_iteratedCovGrad_operatorFieldApplicationLeibnizPsi_window_le (I := I) (M := M) g₀ 1 1
            Delta i (k + 1) 0 (by omega) x
          rw [iteratedCovGrad_zero] at hw
          rw [riemannianFiberNormSq_iteratedCovGrad_order_congr (I := I) (M := M) g₀ 1 1
            (show (i - (k + 1)) + 0 = i - (k + 1) from by omega) Delta x] at hw
          exact hw
        have hDeltaJets : riemannianFiberNormSq (I := I) (M := M) g₀ 1
            (1 + (i - (k + 1))) x
            ((iteratedCovGrad (I := I) g₀ 1 1 (i - (k + 1)) Delta).toSection x) ≤
            CDel (i - (k + 1)) *
              Combinatorics.boundedFactorGridWindow b (i + 1) ((i - (k + 1)) + 3) := by
          refine le_trans (hCDel g₁ T htie hδ_le hδ0 hbound (i - (k + 1)) x) ?_
          refine mul_le_mul_of_nonneg_left ?_ (hCDel_nn (i - (k + 1)))
          exact sum_antidiagonalTupleGrid_le_boundedFactorGridWindow b hb (by omega) (by omega)
        have hsFjet : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (k + 1)) x
            ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF).toSection x) ≤
            S (k + 1) * Combinatorics.boundedFactorGridWindow b (i + 1) (k + 2) := by
          refine le_trans (hS g₁ T htie hδ_le hδ0 hbound (k + 1) x) ?_
          refine mul_le_mul_of_nonneg_left ?_ (hS_nn (k + 1))
          rw [Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
            (show k + 1 ≤ i + 1 from by omega)]
          exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
        have hpair : Combinatorics.boundedFactorGridWindow b (i + 1) ((i - (k + 1)) + 3) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (k + 2) ≤
            Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2) * Wfin := by
          refine le_trans (Combinatorics.boundedFactorGridWindow_mul_le b hb (i + 1)
            ((i - (k + 1)) + 3) (k + 2) (by omega) (by omega)) ?_
          refine mul_le_mul_of_nonneg_left ?_
            (Combinatorics.windowPairCellCount_nonneg _ _)
          rw [hWfin_def]
          refine Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) ?_
          omega
        calc riemannianFiberNormSq (I := I) (M := M) g₀ (1 + (k + 1)) (1 + i) x
              ((operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF).toSection x)
            ≤ (operatorFieldApplicationGdiag (E := E) i *
                (CDel (i - (k + 1)) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) ((i - (k + 1)) + 3))) *
              (S (k + 1) * Combinatorics.boundedFactorGridWindow b (i + 1) (k + 2)) := by
              refine mul_le_mul ?_ hsFjet
                (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + (k + 1)) x _) ?_
              · refine le_trans hPsi ?_
                exact mul_le_mul_of_nonneg_left hDeltaJets (operatorFieldApplicationGdiag_nonneg (E := E) i)
              · exact mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
                  (mul_nonneg (hCDel_nn _)
                    (Combinatorics.boundedFactorGridWindow_nonneg b hb _ _))
          _ = (operatorFieldApplicationGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1)) *
              (Combinatorics.boundedFactorGridWindow b (i + 1) ((i - (k + 1)) + 3) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (k + 2)) := by ring
          _ ≤ (operatorFieldApplicationGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1)) *
              (Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2) * Wfin) := by
              refine mul_le_mul_of_nonneg_left hpair ?_
              exact mul_nonneg (mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
                (hCDel_nn _)) (hS_nn _)
          _ = (operatorFieldApplicationGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
              Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin := by
              ring
      calc ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
              ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (1 + i)
                (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1))
                (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF)).toSection x)
          ≤ ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
              (operatorFieldApplicationGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
                Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg i)
        _ = ((i : ℝ) * ∑ k ∈ Finset.range i,
              operatorFieldApplicationGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
                Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin := by
            rw [← Finset.sum_mul]
            ring
    have hP3 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (P3t.toSection x) ≤
        (operatorFieldApplicationGdiag (E := E) i * ∑ a' ∈ Finset.range (i + 1),
          cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))) * Wfin := by
      rw [hP3t_def]
      refine le_trans (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ i 1 1 1 B0f Dg x) ?_
      have hDjet : ∀ l : ℕ, l ≤ i →
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x) ≤
          (2 * S 0 + 2 * cId + S l) * Wfin := by
        intro l hl
        match l with
        | 0 =>
          rw [iteratedCovGrad_zero]
          have hDx : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (Dg.toSection x) ≤
              2 * S 0 + 2 * cId := by
            rw [hDg_eq]
            rw [show ((sF - InsId).toSection x) = sF.toSection x - InsId.toSection x from by
              rw [SmoothCcTensor.toSection_sub]; rfl]
            refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 1 1 x _ _) ?_
            have hsF0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
                (sF.toSection x) ≤ S 0 := by
              have h := hS g₁ T htie hδ_le hδ0 hbound 0 x
              rw [iteratedCovGrad_zero] at h
              rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
              exact h
            have hIdx := hcId x
            rw [hInsId_def] at *
            linarith
          calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (Dg.toSection x)
              ≤ 2 * S 0 + 2 * cId := hDx
            _ = (2 * S 0 + 2 * cId) * 1 := by ring
            _ ≤ (2 * S 0 + 2 * cId + S 0) * Wfin := by
                refine mul_le_mul ?_ hWfin_one (by norm_num) ?_
                · have := hS_nn 0; linarith
                · have := hS_nn 0; have := hcId_nn; linarith
        | (l' + 1) =>
          have hNdD : iteratedCovGrad (I := I) g₀ 1 1 (l' + 1) Dg =
              iteratedCovGrad (I := I) g₀ 1 1 (l' + 1) sF := by
            rw [hDg_eq, iteratedCovGrad_sub (I := I) g₀ 1 1 (l' + 1) sF InsId]
            rw [hInsId_def,
              iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero (I := I) (M := M) g₀ l']
            rw [sub_zero]
          rw [hNdD]
          refine le_trans (hS g₁ T htie hδ_le hδ0 hbound (l' + 1) x) ?_
          have hgrid : Combinatorics.antidiagonalTupleGrid b (l' + 1) ≤ Wfin := by
            rw [Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
              (show l' + 1 ≤ i + 1 from by omega)]
            rw [hWfin_def]
            exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
          calc S (l' + 1) * Combinatorics.antidiagonalTupleGrid b (l' + 1)
              ≤ S (l' + 1) * Wfin := mul_le_mul_of_nonneg_left hgrid (hS_nn (l' + 1))
            _ ≤ (2 * S 0 + 2 * cId + S (l' + 1)) * Wfin := by
                refine mul_le_mul_of_nonneg_right ?_ hWfin_nn
                have := hS_nn 0
                linarith [hcId_nn]
      have hterm : ∀ a' ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + a') x
              ((iteratedCovGrad (I := I) g₀ 1 1 a' B0f).toSection x) *
            (∑ l ∈ Finset.range (i + 1 - a'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x)) ≤
          (cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))) * Wfin := by
        intro a' ha'
        rw [Finset.mem_range] at ha'
        have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + a') x
            ((iteratedCovGrad (I := I) g₀ 1 1 a' B0f).toSection x) ≤ cB a' := by
          have h := hcB a' x
          rw [hB0f_def]
          exact h
        have hDsum : (∑ l ∈ Finset.range (i + 1 - a'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x)) ≤
            (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l)) * Wfin := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum (fun l hl => ?_)
          rw [Finset.mem_range] at hl
          exact hDjet l (by omega)
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + a') x
              ((iteratedCovGrad (I := I) g₀ 1 1 a' B0f).toSection x) *
            (∑ l ∈ Finset.range (i + 1 - a'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x))
            ≤ cB a' * ((∑ l ∈ Finset.range (i + 1 - a'),
                (2 * S 0 + 2 * cId + S l)) * Wfin) := by
              refine mul_le_mul hB hDsum ?_ (hcB_nn a')
              exact Finset.sum_nonneg (fun l _ =>
                riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x _)
          _ = (cB a' * (∑ l ∈ Finset.range (i + 1 - a'),
                (2 * S 0 + 2 * cId + S l))) * Wfin := by ring
      calc operatorFieldApplicationGdiag (E := E) i *
            ∑ a' ∈ Finset.range (i + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + a') x
                  ((iteratedCovGrad (I := I) g₀ 1 1 a' B0f).toSection x) *
                ∑ l ∈ Finset.range (i + 1 - a'),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                    ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x)
          ≤ operatorFieldApplicationGdiag (E := E) i *
            ∑ a' ∈ Finset.range (i + 1),
              (cB a' * (∑ l ∈ Finset.range (i + 1 - a'),
                (2 * S 0 + 2 * cId + S l))) * Wfin :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
              (operatorFieldApplicationGdiag_nonneg (E := E) i)
        _ = (operatorFieldApplicationGdiag (E := E) i * ∑ a' ∈ Finset.range (i + 1),
              cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))) *
            Wfin := by
            rw [← Finset.sum_mul]
            ring
    have hP23 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (P2t.toSection x + P3t.toSection x) ≤
        2 * (((i : ℝ) * ∑ k ∈ Finset.range i,
            operatorFieldApplicationGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
              Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin) +
        2 * ((operatorFieldApplicationGdiag (E := E) i * ∑ a' ∈ Finset.range (i + 1),
            cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))) * Wfin) := by
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + i) x _ _) ?_
      exact add_le_add (mul_le_mul_of_nonneg_left hP2 (by norm_num))
        (mul_le_mul_of_nonneg_left hP3 (by norm_num))
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (P1t.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          (P2t.toSection x + P3t.toSection x)
        ≤ 2 * (2 * (cPhi * (KcA i)) * S 0 * Wfin) +
          2 * (2 * (((i : ℝ) * ∑ k ∈ Finset.range i,
              operatorFieldApplicationGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
                Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin) +
            2 * ((operatorFieldApplicationGdiag (E := E) i * ∑ a' ∈ Finset.range (i + 1),
              cB a' * (∑ l ∈ Finset.range (i + 1 - a'),
                (2 * S 0 + 2 * cId + S l))) * Wfin)) :=
          add_le_add (mul_le_mul_of_nonneg_left hP1 (by norm_num))
            (mul_le_mul_of_nonneg_left hP23 (by norm_num))
      _ = (4 * (cPhi * (KcA i) * S 0) +
          4 * ((i : ℝ) * ∑ k ∈ Finset.range i,
            operatorFieldApplicationGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
              Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) +
          4 * (operatorFieldApplicationGdiag (E := E) i * ∑ a' ∈ Finset.range (i + 1),
            cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l)))) *
          Wfin := by ring

end TopOrderSeparatedRungSlotInsert

section TopOrderSeparatedRungLoweringSplit



theorem riemannianFiberNormSq_iteratedCovGrad_riemannG1LoweringDifference_topOrderSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 0 (4 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                ((iteratedCovGrad (I := I) g₀ 0 4 i
                    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                      riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨KtA, hKtA_nn, KcA, hKcA_nn, hA⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_topOrderSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cfix, hcfix_nn, hcfix⟩ := exists_backgroundJet_riemannianFiberNormSq_bound (I := I) (M := M) g₀ 0 4
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨n ^ 5 * KtA, mul_nonneg (pow_nonneg hn_nn 5) hKtA_nn, ?_⟩
  refine ⟨fun i => 2 * (n ^ 5 * (2 * KcA i + 2 * cfix i)) +
      2 * ((i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
        ∑ k ∈ Finset.range i, 2 * n ^ 3 * (CA k + cfix k)),
    fun i => by
      have h1 : (0 : ℝ) ≤ n ^ 5 * (2 * KcA i + 2 * cfix i) :=
        mul_nonneg (pow_nonneg hn_nn 5) (by have := hKcA_nn i; have := hcfix_nn i; linarith)
      have h2 : (0 : ℝ) ≤ (i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
          ∑ k ∈ Finset.range i, 2 * n ^ 3 * (CA k + cfix k) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg i) (operatorFieldApplicationGdiag_nonneg (E := E) i))
          (Finset.sum_nonneg fun k _ => mul_nonneg
            (mul_nonneg (by norm_num) (pow_nonneg hn_nn 3))
            (by have := hCA_nn k; have := hcfix_nn k; linarith))
      linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  obtain ⟨HdA, hHdA_head, hHdA_res⟩ := hA g₁ T htie hδ_le hδ0 hbound i
  set Dress : SmoothCcTensor g₀ 4 4 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 3
      (perturbationSharpEndoField (I := I) (M := M) g₀ T) with hDress_def
  set RLCmix : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁
    with hRLCmix_def
  set RLCfix : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀
    with hRLCfix_def
  set RLD : SmoothCcTensor g₀ 0 4 :=
    riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ with hRLD_def
  have hmix_split : RLCmix = RLD + RLCfix := by
    rw [hRLD_def, riemannLoweredBackgroundDifference, ← hRLCmix_def, ← hRLCfix_def]
    abel
  set WS : SmoothCcTensor g₀ 0 4 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1) RLCmix with hWS_def
  set Ybig : SmoothCcTensor g₀ 0 4 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4 Dress WS with hYbig_def
  have hrepr : riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
      riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1) Ybig := by
    rw [hYbig_def, hWS_def, hRLCmix_def, hDress_def]
    exact riemannG1LoweringDifference_slotInsert_repr (I := I) (M := M) g₀ g₁ T htie
  obtain ⟨σo, hσo⟩ := exists_iteratedCovGrad_domDomCongrSection_eq (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 4) 1) Ybig i
  obtain ⟨σw, hσw⟩ := exists_iteratedCovGrad_domDomCongrSection_eq (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 4) 1) RLCmix i
  set Hd0 : SmoothCcTensor g₀ 0 (4 + i) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
      (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
      (domDomCongrSection (I := I) g₀ σw HdA) with hHd0_def
  have hDress0 : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 4 y (Dress.toSection y) ≤ n ^ 5 := by
    intro y
    have h1 := riemannianFiberNormSq_iteratedCovGrad_slotInsert3_perturbationSharp_le (I := I) (M := M)
      g₀ T 0 y
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h1
    have h2 := riemannianFiberNormSq_symmS_zero_le_of_ball (I := I) (M := M) g₀ T hδ0 hbound y
    have hδ1 : δ ^ 2 ≤ 1 := by
      have hδle1 : δ ≤ 1 := le_of_lt (lt_of_le_of_lt hδ_le hδ₀)
      exact pow_le_one₀ hδ0 hδle1
    have h3 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
        ((symmS (I := I) (M := M) g₀ T).toSection y) ≤ n ^ 2 := by
      refine le_trans h2 ?_
      calc n ^ 2 * δ ^ 2 ≤ n ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hδ1 (pow_nonneg hn_nn 2)
        _ = n ^ 2 := by ring
    rw [hDress_def]
    refine le_trans h1 ?_
    calc n ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
          ((symmS (I := I) (M := M) g₀ T).toSection y)
        ≤ n ^ 3 * n ^ 2 := mul_le_mul_of_nonneg_left h3 (pow_nonneg hn_nn 3)
      _ = n ^ 5 := by ring
  refine ⟨domDomCongrSection (I := I) g₀ σo Hd0, ?_, ?_⟩
  · intro x
    rw [riemannianFiberNormSq_domDomCongrSection_eq (I := I) (M := M) g₀ σo Hd0 x]
    rw [hHd0_def]
    refine le_trans (riemannianFiberNormSq_operatorFieldComposition_operatorFieldApplicationLeibnizPsi_diag_le (I := I) (M := M) g₀ 0 4 4
      Dress i (domDomCongrSection (I := I) g₀ σw HdA) x) ?_
    rw [riemannianFiberNormSq_domDomCongrSection_eq (I := I) (M := M) g₀ σw HdA x]
    have hb_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 4 x (Dress.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (HdA.toSection x)
        ≤ n ^ 5 * (KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
          refine mul_le_mul (hDress0 x) (hHdA_head x) ?_ (pow_nonneg hn_nn 5)
          exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x _
      _ = n ^ 5 * KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
    have hb : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hWfin_def
    have hWfin_nn : 0 ≤ Wfin :=
      Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
    have hWfin_one : 1 ≤ Wfin :=
      Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
    have hdiff : iteratedCovGrad (I := I) g₀ 0 4 i
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
            riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) -
          domDomCongrSection (I := I) g₀ σo Hd0 =
        domDomCongrSection (I := I) g₀ σo
          (iteratedCovGrad (I := I) g₀ 0 4 i Ybig - Hd0) := by
      rw [hrepr, hσo]
      rw [domDomCongrSection_sub (I := I) (M := M) g₀ σo]
    rw [hdiff]
    rw [riemannianFiberNormSq_domDomCongrSection_eq (I := I) (M := M) g₀ σo _ x]
    have hWSsplit : iteratedCovGrad (I := I) g₀ 0 4 i WS -
        domDomCongrSection (I := I) g₀ σw HdA =
        domDomCongrSection (I := I) g₀ σw
          ((iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA) +
            iteratedCovGrad (I := I) g₀ 0 4 i RLCfix) := by
      rw [hWS_def, hσw]
      rw [← domDomCongrSection_sub (I := I) (M := M) g₀ σw]
      rw [show iteratedCovGrad (I := I) g₀ 0 4 i RLCmix =
          iteratedCovGrad (I := I) g₀ 0 4 i RLD +
            iteratedCovGrad (I := I) g₀ 0 4 i RLCfix from by
        rw [← iteratedCovGrad_add (I := I) g₀ 0 4 i RLD RLCfix, ← hmix_split]]
      rw [add_sub_right_comm]
    have hfirst : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
          (iteratedCovGrad (I := I) g₀ 0 4 i WS -
            domDomCongrSection (I := I) g₀ σw HdA)).toSection x) ≤
        n ^ 5 * ((2 * KcA i + 2 * cfix i) * Wfin) := by
      refine le_trans (riemannianFiberNormSq_operatorFieldComposition_operatorFieldApplicationLeibnizPsi_diag_le (I := I) (M := M) g₀ 0 4 4
        Dress i _ x) ?_
      have hinner : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i WS -
            domDomCongrSection (I := I) g₀ σw HdA).toSection x) ≤
          (2 * KcA i + 2 * cfix i) * Wfin := by
        rw [hWSsplit]
        rw [riemannianFiberNormSq_domDomCongrSection_eq (I := I) (M := M) g₀ σw _ x]
        rw [show (((iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA) +
              iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) =
            (iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA).toSection x +
              (iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x from by
          rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i)
          x _ _) ?_
        have h1 := hHdA_res x
        have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) ≤
            cfix i * Wfin := by
          have h2a : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) ≤ cfix i := by
            rw [hRLCfix_def]
            exact hcfix i x
          calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x)
              ≤ cfix i := h2a
            _ = cfix i * 1 := by ring
            _ ≤ cfix i * Wfin := mul_le_mul_of_nonneg_left hWfin_one (hcfix_nn i)
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x)
            ≤ 2 * (KcA i * Wfin) + 2 * (cfix i * Wfin) := by
              refine add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
                (mul_le_mul_of_nonneg_left h2 (by norm_num))
          _ = (2 * KcA i + 2 * cfix i) * Wfin := by ring
      refine mul_le_mul (hDress0 x) hinner
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x _)
        (pow_nonneg hn_nn 5)
    have hcorr : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
            (iteratedCovGrad (I := I) g₀ 0 4 k WS)).toSection x) ≤
        (i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
          ∑ k ∈ Finset.range i, (2 * n ^ 3 * (CA k + cfix k)) * Wfin := by
      refine le_trans (riemannianFiberNormSq_operatorFieldComposition_argLower_le (I := I) (M := M) g₀ 0 4 4 Dress WS i x) ?_
      rw [mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg i)
      refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) i)
      refine Finset.sum_le_sum (fun k hk => ?_)
      rw [Finset.mem_range] at hk
      have hDjet : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + (i - k)) x
          ((iteratedCovGrad (I := I) g₀ 4 4 (i - k) Dress).toSection x) ≤
          n ^ 3 * b (i - k) := by
        rw [hDress_def]
        refine le_trans (riemannianFiberNormSq_iteratedCovGrad_slotInsert3_perturbationSharp_le
          (I := I) (M := M) g₀ T (i - k) x) ?_
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hn_nn 3)
        exact riemannianFiberNormSq_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ T (i - k) x
      have hWjet : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 4 k WS).toSection x) ≤
          2 * (CA k * (∑ k' ∈ Finset.range (k + 3),
            Combinatorics.antidiagonalTupleGrid b k')) + 2 * cfix k := by
        rw [hWS_def]
        rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M)
          g₀ (Equiv.swap (0 : Fin 4) 1) RLCmix k x]
        rw [show iteratedCovGrad (I := I) g₀ 0 4 k RLCmix =
            iteratedCovGrad (I := I) g₀ 0 4 k RLD +
              iteratedCovGrad (I := I) g₀ 0 4 k RLCfix from by
          rw [← iteratedCovGrad_add (I := I) g₀ 0 4 k RLD RLCfix, ← hmix_split]]
        rw [show ((iteratedCovGrad (I := I) g₀ 0 4 k RLD +
              iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) =
            (iteratedCovGrad (I := I) g₀ 0 4 k RLD).toSection x +
              (iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x from by
          rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + k)
          x _ _) ?_
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
            ((iteratedCovGrad (I := I) g₀ 0 4 k RLD).toSection x) ≤
            CA k * (∑ k' ∈ Finset.range (k + 3),
              Combinatorics.antidiagonalTupleGrid b k') := by
          have h := hCA g₁ T htie hδ_le hδ0 hbound k x
          rw [hRLD_def]
          exact h
        have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
            ((iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) ≤ cfix k := by
          rw [hRLCfix_def]; exact hcfix k x
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
          (mul_le_mul_of_nonneg_left h2 (by norm_num))
      have hbW : b (i - k) * (∑ k' ∈ Finset.range (k + 3),
          Combinatorics.antidiagonalTupleGrid b k') ≤ Wfin := by
        refine le_trans (mul_le_mul_of_nonneg_left
          (sum_antidiagonalTupleGrid_le_boundedFactorGridWindow b hb (show k + 3 ≤ (i + 1) + 1 from by omega)
            (le_refl (k + 3))) (hb (i - k))) ?_
        refine le_trans (Combinatorics.single_factor_mul_boundedFactorGridWindow_le b hb
          (show 1 ≤ i - k from by omega) (show i - k ≤ i + 1 from by omega)) ?_
        rw [hWfin_def]
        refine Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) ?_
        omega
      have hbAlone : b (i - k) ≤ Wfin := by
        have h1 := Combinatorics.single_factor_mul_boundedFactorGrid_le b hb 0 (i - k)
          (show 1 ≤ i - k from by omega) (show i - k ≤ i + 1 from by omega)
        rw [Combinatorics.boundedFactorGrid_zero, mul_one] at h1
        refine le_trans h1 ?_
        rw [show 0 + (i - k) = i - k from by omega, hWfin_def]
        exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + (i - k)) x
            ((iteratedCovGrad (I := I) g₀ 4 4 (i - k) Dress).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
            ((iteratedCovGrad (I := I) g₀ 0 4 k WS).toSection x)
          ≤ (n ^ 3 * b (i - k)) *
            (2 * (CA k * (∑ k' ∈ Finset.range (k + 3),
              Combinatorics.antidiagonalTupleGrid b k')) + 2 * cfix k) := by
            refine mul_le_mul hDjet hWjet ?_ ?_
            · exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + k) x _
            · exact mul_nonneg (pow_nonneg hn_nn 3) (hb (i - k))
        _ = 2 * n ^ 3 * CA k *
              (b (i - k) * (∑ k' ∈ Finset.range (k + 3),
                Combinatorics.antidiagonalTupleGrid b k')) +
            2 * n ^ 3 * cfix k * b (i - k) := by ring
        _ ≤ 2 * n ^ 3 * CA k * Wfin + 2 * n ^ 3 * cfix k * Wfin := by
            refine add_le_add ?_ ?_
            · refine mul_le_mul_of_nonneg_left hbW ?_
              exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hn_nn 3)) (hCA_nn k)
            · refine mul_le_mul_of_nonneg_left hbAlone ?_
              exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hn_nn 3))
                (hcfix_nn k)
        _ = (2 * n ^ 3 * (CA k + cfix k)) * Wfin := by ring
    have hsplitY : iteratedCovGrad (I := I) g₀ 0 4 i Ybig - Hd0 =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
            (iteratedCovGrad (I := I) g₀ 0 4 i WS -
              domDomCongrSection (I := I) g₀ σw HdA) +
          ∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
              (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
              (iteratedCovGrad (I := I) g₀ 0 4 k WS) := by
      rw [hYbig_def]
      rw [iteratedCovGrad_operatorFieldComposition_eq_argCorner_add_lower (I := I) (M := M) g₀ 0 4 4
        Dress WS i]
      rw [hHd0_def]
      rw [operatorFieldComposition_sub_right_cc (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
        (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
        (iteratedCovGrad (I := I) g₀ 0 4 i WS)
        (domDomCongrSection (I := I) g₀ σw HdA)]
      exact add_sub_right_comm _ _ _
    rw [hsplitY]
    rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
          (iteratedCovGrad (I := I) g₀ 0 4 i WS -
            domDomCongrSection (I := I) g₀ σw HdA) +
        ∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
            (iteratedCovGrad (I := I) g₀ 0 4 k WS)).toSection x) =
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
          (iteratedCovGrad (I := I) g₀ 0 4 i WS -
            domDomCongrSection (I := I) g₀ σw HdA)).toSection x +
        (∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
            (iteratedCovGrad (I := I) g₀ 0 4 k WS)).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i) x _ _) ?_
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
            (iteratedCovGrad (I := I) g₀ 0 4 i WS -
              domDomCongrSection (I := I) g₀ σw HdA)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
              (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
              (iteratedCovGrad (I := I) g₀ 0 4 k WS)).toSection x)
        ≤ 2 * (n ^ 5 * ((2 * KcA i + 2 * cfix i) * Wfin)) +
          2 * ((i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
            ∑ k ∈ Finset.range i, (2 * n ^ 3 * (CA k + cfix k)) * Wfin) :=
        add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num))
          (mul_le_mul_of_nonneg_left hcorr (by norm_num))
      _ = (2 * (n ^ 5 * (2 * KcA i + 2 * cfix i)) +
          2 * ((i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
            ∑ k ∈ Finset.range i, 2 * n ^ 3 * (CA k + cfix k))) * Wfin := by
          rw [← Finset.sum_mul]
          ring

end TopOrderSeparatedRungLoweringSplit

section TopOrderSeparatedRungCurvCoeff



namespace CurvatureCoefficientDifferenceJetTower

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma slotInsertEndoCc_succ_eq_reindex_slotExtend
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ (s + 1) Λ =
      reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
        (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
          (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ s Λ)))
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1) Λ).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ s Λ)))
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)).toSection x) D) m
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply, rsDomDomCongrSection_toSection,
    toModel_rsDomDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply, slotExtend_toSection]
  rw [show (fun k : Fin (s + 1 + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) =
      Fin.cons (m 1) (fun j : Fin (s + 1) =>
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ j))) from by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.cons_zero, Equiv.swap_apply_left]
    · simp only [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval]
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval,
    TensorMultilinear.tensor0S_curry_toModel_apply,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  have hswap_succ0 : (Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (0 : Fin (s + 1))) = 0 := by
    rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
  rw [hswap_succ0]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k₁ => ?_) k
  · rw [Equiv.swap_apply_left,
      show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl, Fin.cons_succ,
      Function.update_self, Function.update_self]
  · refine Fin.cases ?_ (fun k₂ => ?_) k₁
    · have h10 : (1 : Fin (s + 1 + 1)) ≠ 0 := by
        rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact Fin.succ_ne_zero _
      rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl,
        Function.update_of_ne h10, Equiv.swap_apply_right, Fin.cons_zero]
    · have hne0 : (Fin.succ (Fin.succ k₂) : Fin (s + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
      have hne1 : (Fin.succ (Fin.succ k₂) : Fin (s + 1 + 1)) ≠ 1 := by
        rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
      rw [Function.update_of_ne hne0, Equiv.swap_apply_of_ne_of_ne hne0 hne1, Fin.cons_succ,
        Function.update_of_ne (Fin.succ_ne_zero k₂)]
      change m (Fin.succ (Fin.succ k₂)) =
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k₂)))
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_reindexCoeffGen_eq (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x
        ((reindexCoeffGen (I := I) (M := M) g₀ r s R σ').toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r s x (R.toSection x) := by
  have h := riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ r s R σ' 0 x
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
  exact h

omit [SigmaCompactSpace M] in
lemma exists_slotExtend_head_transport (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (V : SmoothCcTensor g₀ r s) (i : ℕ) (HV : SmoothCcTensor g₀ r (s + i)) :
    ∃ HW : SmoothCcTensor g₀ (r + 1) ((s + 1) + i),
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) x
            (HW.toSection x) ≤
          (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x (HV.toSection x)) ∧
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
                (slotExtend (I := I) (M := M) g₀ r s V) - HW).toSection x) ≤
          (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
              ((iteratedCovGrad (I := I) g₀ r s i V - HV).toSection x)) := by
  obtain ⟨σa, hσa⟩ := exists_iteratedCovGrad_slotExtend_rsDomDomCongr (I := I) (M := M)
    g₀ r s V i
  refine ⟨rsDomDomCongrSection (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa
    (castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
      (slotExtend (I := I) (M := M) g₀ r (s + i) HV)), ?_, ?_⟩
  · intro x
    rw [riemannianFiberNormSq_rsDomDomCongrSection_eq (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa _ x]
    rw [riemannianFiberNormSq_castCcTensorRank_eq (I := I) (M := M) g₀ (r + 1)
      (by omega : (s + i) + 1 = (s + 1) + i) _ x]
    rw [riemannianFiberNormSq_slotExtend_eq (I := I) (M := M) g₀ r (s + i) HV x]
  · intro x
    have hpt : ((iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
          (slotExtend (I := I) (M := M) g₀ r s V) -
        rsDomDomCongrSection (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa
          (castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i) HV))).toSection x) =
        rsDomDomCongr (I := I) (M := M) σa
          ((castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i)
              (iteratedCovGrad (I := I) g₀ r s i V - HV))).toSection x) := by
      rw [show ((iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
            (slotExtend (I := I) (M := M) g₀ r s V) -
          rsDomDomCongrSection (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa
            (castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
              (slotExtend (I := I) (M := M) g₀ r (s + i) HV))).toSection x) =
          (iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
            (slotExtend (I := I) (M := M) g₀ r s V)).toSection x -
          (rsDomDomCongrSection (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa
            (castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
              (slotExtend (I := I) (M := M) g₀ r (s + i) HV))).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [hσa x, rsDomDomCongrSection_toSection]
      rw [← tensorRS_domDomCongr_sub (I := I) (M := M) σa]
      rw [show ((castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i)
              (iteratedCovGrad (I := I) g₀ r s i V))).toSection x -
          (castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i) HV)).toSection x) =
          ((castCcTensorRank g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i)
                (iteratedCovGrad (I := I) g₀ r s i V) -
              slotExtend (I := I) (M := M) g₀ r (s + i) HV)).toSection x) from by
        rw [castCcTensorRank_sub, SmoothCcTensor.toSection_sub]; rfl]
      rw [← slotExtend_sub (I := I) (M := M) g₀ r (s + i)]
    rw [hpt]
    rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ (r + 1)
      ((s + 1) + i) x σa _]
    rw [riemannianFiberNormSq_castCcTensorRank_eq (I := I) (M := M) g₀ (r + 1)
      (by omega : (s + i) + 1 = (s + 1) + i) _ x]
    rw [riemannianFiberNormSq_slotExtend_eq (I := I) (M := M) g₀ r (s + i) _ x]

omit [SigmaCompactSpace M] in
lemma exists_rsDomDomCongrSection_head_transport (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (V : SmoothCcTensor g₀ r s) (i : ℕ)
    (HV : SmoothCcTensor g₀ r (s + i)) :
    ∃ HW : SmoothCcTensor g₀ r (s + i),
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x (HW.toSection x) ≤
          riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x (HV.toSection x)) ∧
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
            ((iteratedCovGrad (I := I) g₀ r s i
                (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ V) - HW).toSection x) ≤
          riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
            ((iteratedCovGrad (I := I) g₀ r s i V - HV).toSection x)) := by
  obtain ⟨σ', hσ'⟩ := exists_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M)
    g₀ r s σ V i
  refine ⟨rsDomDomCongrSection (I := I) (M := M) g₀ r (s + i) σ' HV, ?_, ?_⟩
  · intro x
    rw [riemannianFiberNormSq_rsDomDomCongrSection_eq (I := I) (M := M) g₀ r (s + i) σ' HV x]
  · intro x
    have hpt : ((iteratedCovGrad (I := I) g₀ r s i
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ V) -
        rsDomDomCongrSection (I := I) (M := M) g₀ r (s + i) σ' HV).toSection x) =
        rsDomDomCongr (I := I) (M := M) σ'
          ((iteratedCovGrad (I := I) g₀ r s i V - HV).toSection x) := by
      rw [show ((iteratedCovGrad (I := I) g₀ r s i
            (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ V) -
          rsDomDomCongrSection (I := I) (M := M) g₀ r (s + i) σ' HV).toSection x) =
          (iteratedCovGrad (I := I) g₀ r s i
            (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ V)).toSection x -
          (rsDomDomCongrSection (I := I) (M := M) g₀ r (s + i) σ' HV).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [hσ' x, rsDomDomCongrSection_toSection]
      rw [← tensorRS_domDomCongr_sub (I := I) (M := M) σ']
      rw [show ((iteratedCovGrad (I := I) g₀ r s i V).toSection x - HV.toSection x) =
          ((iteratedCovGrad (I := I) g₀ r s i V - HV).toSection x) from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [hpt]
    rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ r (s + i) x σ' _]

end CurvatureCoefficientDifferenceJetTower

theorem riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0CurvCoeff_backgroundDifference_topOrderSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
                ((iteratedCovGrad (I := I) g₀ 2 2 i
                    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨KtB, hKtB_nn, KcB, hKcB_nn, hB⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_topOrderSeparated_le
      (I := I) (M := M) g₀ hδ₀
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨4 * (n * KtB), by positivity, ?_⟩
  refine ⟨fun i => 4 * (n * KcB i),
    fun i => by have := hKcB_nn i; positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  obtain ⟨HdB, hB_head, hB_res⟩ := hB g₁ T htie hδ_le hδ0 hbound i
  set Lam := ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ with hLam_def
  set X : SmoothCcTensor g₀ 1 1 := slotInsertEndoCc (I := I) (M := M) g₀ 0 Lam with hX_def
  set V : SmoothCcTensor g₀ 2 2 := slotInsertEndoCc (I := I) (M := M) g₀ 1 Lam with hV_def
  have hVrepr : V =
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotExtend (I := I) (M := M) g₀ 1 1 X))
        (Equiv.swap (0 : Fin 2) 1) := by
    rw [hV_def, hX_def]
    exact slotInsertEndoCc_succ_eq_reindex_slotExtend (I := I) (M := M) g₀ 0 Lam
  obtain ⟨HdX1, hX1_head, hX1_res⟩ := exists_slotExtend_head_transport (I := I) (M := M)
    g₀ 1 1 X i HdB
  obtain ⟨HdX2, hX2_head, hX2_res⟩ := exists_rsDomDomCongrSection_head_transport (I := I) (M := M)
    g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) (slotExtend (I := I) (M := M) g₀ 1 1 X) i HdX1
  set HdV : SmoothCcTensor g₀ 2 (2 + i) :=
    reindexCoeffGen (I := I) (M := M) g₀ 2 (2 + i) HdX2 (Equiv.swap (0 : Fin 2) 1)
    with hHdV_def
  have hHdV_head : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdV.toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (HdB.toSection x) := by
    intro x
    rw [hHdV_def, riemannianFiberNormSq_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 (2 + i) HdX2 _ x]
    exact le_trans (hX2_head x) (hX1_head x)
  have hHdV_res : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V - HdV).toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i X - HdB).toSection x) := by
    intro x
    have hVd : iteratedCovGrad (I := I) g₀ 2 2 i V - HdV =
        reindexCoeffGen (I := I) (M := M) g₀ 2 (2 + i)
          (iteratedCovGrad (I := I) g₀ 2 2 i
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotExtend (I := I) (M := M) g₀ 1 1 X)) - HdX2)
          (Equiv.swap (0 : Fin 2) 1) := by
      rw [hVrepr, hHdV_def]
      rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M) g₀ 2 2 _ _ i]
      rw [reindexCoeffGen_sub (I := I) (M := M) (r := 2) (s := 2 + i) g₀]
    rw [hVd]
    rw [riemannianFiberNormSq_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 (2 + i) _ _ x]
    exact le_trans (hX2_res x) (hX1_res x)
  obtain ⟨HdV2i, h2i_head, h2i_res⟩ := exists_rsDomDomCongrSection_head_transport (I := I) (M := M)
    g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) V i HdV
  set HdV2 : SmoothCcTensor g₀ 2 (2 + i) :=
    reindexCoeffGen (I := I) (M := M) g₀ 2 (2 + i) HdV2i (Equiv.swap (0 : Fin 2) 1)
    with hHdV2_def
  set V2 : SmoothCcTensor g₀ 2 2 :=
    reindexCoeffGen (I := I) (M := M) g₀ 2 2
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) V)
      (Equiv.swap (0 : Fin 2) 1) with hV2_def
  have hHdV2_head : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdV2.toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (HdB.toSection x) := by
    intro x
    rw [hHdV2_def, riemannianFiberNormSq_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 (2 + i) HdV2i _ x]
    exact le_trans (h2i_head x) (hHdV_head x)
  have hHdV2_res : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2).toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i X - HdB).toSection x) := by
    intro x
    have hV2d : iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2 =
        reindexCoeffGen (I := I) (M := M) g₀ 2 (2 + i)
          (iteratedCovGrad (I := I) g₀ 2 2 i
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) V) -
            HdV2i)
          (Equiv.swap (0 : Fin 2) 1) := by
      rw [hV2_def, hHdV2_def]
      rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M) g₀ 2 2 _ _ i]
      rw [reindexCoeffGen_sub (I := I) (M := M) (r := 2) (s := 2 + i) g₀]
    rw [hV2d]
    rw [riemannianFiberNormSq_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 (2 + i) _ _ x]
    exact le_trans (h2i_res x) (hHdV_res x)
  refine ⟨HdV + HdV2, ?_, ?_⟩
  · intro x
    rw [show ((HdV + HdV2).toSection x) = HdV.toSection x + HdV2.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have h1 := le_trans (hHdV_head x) (mul_le_mul_of_nonneg_left (hB_head x) hn_nn)
    have h2 := le_trans (hHdV2_head x) (mul_le_mul_of_nonneg_left (hB_head x) hn_nn)
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdV.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdV2.toSection x)
        ≤ 2 * (n * (KtB * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) +
          2 * (n * (KtB * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
            (mul_le_mul_of_nonneg_left h2 (by norm_num))
      _ = 4 * (n * KtB) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    have hdecomp := ricciArmOrder0CurvCoeff_backgroundDifference_decomp (I := I) (M := M)
      g₀ g₁
    have hsplit : iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) -
          (HdV + HdV2) =
        (iteratedCovGrad (I := I) g₀ 2 2 i V - HdV) +
          (iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2) := by
      rw [show (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) = V + V2 from by
        rw [hV_def, hV2_def, hLam_def]
        exact hdecomp]
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i V V2]
      abel
    rw [hsplit]
    rw [show (((iteratedCovGrad (I := I) g₀ 2 2 i V - HdV) +
          (iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2)).toSection x) =
        (iteratedCovGrad (I := I) g₀ 2 2 i V - HdV).toSection x +
          (iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have h1 := le_trans (hHdV_res x) (mul_le_mul_of_nonneg_left (hB_res x) hn_nn)
    have h2 := le_trans (hHdV2_res x) (mul_le_mul_of_nonneg_left (hB_res x) hn_nn)
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V - HdV).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2).toSection x)
        ≤ 2 * (n * (KcB i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3))) +
          2 * (n * (KcB i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3))) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
            (mul_le_mul_of_nonneg_left h2 (by norm_num))
      _ = 4 * (n * KcB i) * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3) := by
          ring

end TopOrderSeparatedRungCurvCoeff

section TopOrderSeparatedRungRiemannCoeff



private lemma ts_two_mul_add_mul_factor (a b x : ℝ) :
    2 * (a * x) + 2 * (b * x) = (2 * a + 2 * b) * x := by
  ring

private lemma ts_head_bound_factor (d p n k x : ℝ) :
    (2 : ℝ) ^ 2 * (2 * (d * ((n * n) * (k * x))) + 2 * (p * ((n * n) * (k * x)))) =
      8 * (n * n) * (d + p) * k * x := by
  ring

private lemma ts_twice_pair_plus_factor (a b c x : ℝ) :
    2 * ((2 * a + 2 * b) * x) + 2 * (c * x) = (4 * a + 4 * b + 2 * c) * x := by
  ring

private lemma ts_grid_sum_factor (a b c x : ℝ) :
    2 * (a * x) + 2 * (2 * (b * x) + 2 * c) = (2 * a + 4 * b) * x + 4 * c := by
  ring

private lemma ts_product_sum_expand (a n b c x y : ℝ) :
    (a * x) * (n * (b * y + c)) = a * n * b * (x * y) + a * n * c * x := by
  ring

private lemma ts_product_sum_factor (a n b c p x : ℝ) :
    a * n * b * (p * x) + a * n * c * x = (a * n * (b * p + c)) * x := by
  ring

private lemma ts_residual_bound_factor (a b c d x : ℝ) :
    (2 : ℝ) ^ 2 * (2 * (2 * (a * x) + 2 * (b * x)) + 2 * (2 * (c * (d * x)))) =
      (4 * (2 * (2 * a + 2 * b) + 2 * (2 * c * d))) * x := by
  ring

private lemma ts_residual_sum_factor {α : Type*} (s : Finset α) (f : α → ℝ)
    (a b x : ℝ) :
    2 * (a * x) + 2 * (b * (∑ k ∈ s, f k * x)) =
      2 * (a * x) + 2 * ((b * (∑ k ∈ s, f k)) * x) := by
  rw [← Finset.sum_mul]
  ring

private lemma ts_nested_mul_assoc (c n d w : ℝ) :
    2 * (c * (n * (d * w))) = 2 * ((c * n) * (d * w)) := by
  ring

omit [SigmaCompactSpace M] in
private lemma ts_riemann_coeff_sub_head_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ)
    (Dpt phiDt : SmoothCcTensor g₀ 6 2) (WBig WVd : SmoothCcTensor g₀ 2 6)
    (HdT1 HdT2 : SmoothCcTensor g₀ 2 (2 + i))
    (hRiemD : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig +
        (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd) :
    iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
        (2 : ℝ) • (HdT1 + HdT2) =
      (2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1) +
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2)) := by
  rw [hRiemD]
  rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _]
  rw [iteratedCovGrad_smul_pt (I := I) (M := M) g₀ 2 2 i 2 _]
  rw [iteratedCovGrad_smul_pt (I := I) (M := M) g₀ 2 2 i 2 _]
  simp only [smul_add, smul_sub]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma ts_combine_riemannianFiberNormSq_residual
    (g₀ : SmoothRiemannianMetric I M) (i : ℕ) (x : M)
    (R Z₁ Z₂ H₁ H₂ : SmoothCcTensor g₀ 2 (2 + i)) (a b c d w : ℝ)
    (hR : R - (2 : ℝ) • (H₁ + H₂) = (2 : ℝ) • ((Z₁ - H₁) + (Z₂ - H₂)))
    (h₁ : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((Z₁ - H₁).toSection x) ≤ 2 * (a * w) + 2 * (b * w))
    (h₂ : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((Z₂ - H₂).toSection x) ≤ 2 * (c * (d * w))) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((R - (2 : ℝ) • (H₁ + H₂)).toSection x) ≤
      (4 * (2 * (2 * a + 2 * b) + 2 * (2 * c * d))) * w := by
  rw [hR]
  rw [show (((2 : ℝ) • ((Z₁ - H₁) + (Z₂ - H₂))).toSection x) =
      (2 : ℝ) • (((Z₁ - H₁) + (Z₂ - H₂)).toSection x) from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [riemannianFiberNormSq_smul_pt (I := I) (M := M) g₀ 2 (2 + i) x 2 _]
  rw [show (((Z₁ - H₁) + (Z₂ - H₂)).toSection x) =
      (Z₁ - H₁).toSection x + (Z₂ - H₂).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  calc (2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((Z₁ - H₁).toSection x + (Z₂ - H₂).toSection x)
      ≤ (2 : ℝ) ^ 2 *
          (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((Z₁ - H₁).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((Z₂ - H₂).toSection x)) :=
        mul_le_mul_of_nonneg_left
          (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
          (by norm_num)
    _ ≤ (2 : ℝ) ^ 2 *
          (2 * (2 * (a * w) + 2 * (b * w)) + 2 * (2 * (c * (d * w)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact add_le_add (mul_le_mul_of_nonneg_left h₁ (by norm_num))
          (mul_le_mul_of_nonneg_left h₂ (by norm_num))
    _ = (4 * (2 * (2 * a + 2 * b) + 2 * (2 * c * d))) * w :=
      ts_residual_bound_factor a b c d w

theorem riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_topOrderSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
                ((iteratedCovGrad (I := I) g₀ 2 2 i
                    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨KtA, hKtA_nn, KcA, hKcA_nn, hA⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_topOrderSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtA', hKtA'_nn, KcA', hKcA'_nn, hA'⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannG1LoweringDifference_topOrderSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨C1, hC1_nn, hC1⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannG1LoweringDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CD, hCD_nn, hCD⟩ := exists_riemannianFiberNormSq_iteratedCovGrad_pairTraceOp_diff_grid
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨cfix, hcfix_nn, hcfix⟩ := exists_backgroundJet_riemannianFiberNormSq_bound (I := I) (M := M) g₀ 0 4
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)
  obtain ⟨cP, hcP_nn, hcP⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 6 2 (CurvatureCoefficientDifferenceJetTower.pairTraceOp (I := I) (M := M) g₀ g₀)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨8 * (n * n) * (CD 0 + cP) * (2 * KtA' + 2 * KtA),
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hn_nn hn_nn))
      (add_nonneg (hCD_nn 0) hcP_nn))
        (add_nonneg (mul_nonneg (by norm_num) hKtA'_nn)
          (mul_nonneg (by norm_num) hKtA_nn)), ?_⟩
  refine ⟨fun i => 4 * (2 * (2 * (CD 0 * (n * n) *
        (4 * KcA' i + 4 * KcA i + 2 * cfix i)) +
      2 * ((i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
        ∑ k ∈ Finset.range i, CD (i - k) * (n * n) *
          ((2 * C1 k + 4 * CA k) *
              Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k))) +
      2 * (2 * (cP * (n * n)) * (2 * KcA' i + 2 * KcA i))),
    fun i => by
      have hp1 : (0 : ℝ) ≤ CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i) :=
        mul_nonneg (mul_nonneg (hCD_nn 0) (mul_nonneg hn_nn hn_nn))
          (add_nonneg
            (add_nonneg (mul_nonneg (by norm_num) (hKcA'_nn i))
              (mul_nonneg (by norm_num) (hKcA_nn i)))
            (mul_nonneg (by norm_num) (hcfix_nn i)))
      have hp2 : (0 : ℝ) ≤ (i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
          ∑ k ∈ Finset.range i, CD (i - k) * (n * n) *
            ((2 * C1 k + 4 * CA k) *
                Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg i) (operatorFieldApplicationGdiag_nonneg (E := E) i))
          (Finset.sum_nonneg fun k _ => mul_nonneg
            (mul_nonneg (hCD_nn _) (mul_nonneg hn_nn hn_nn))
            (add_nonneg
              (mul_nonneg
                (add_nonneg (mul_nonneg (by norm_num) (hC1_nn k))
                  (mul_nonneg (by norm_num) (hCA_nn k)))
                (Combinatorics.windowPairCellCount_nonneg _ _))
              (mul_nonneg (by norm_num) (hcfix_nn k))))
      have hp3 : (0 : ℝ) ≤ 2 * (cP * (n * n)) * (2 * KcA' i + 2 * KcA i) :=
        mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hcP_nn (mul_nonneg hn_nn hn_nn)))
          (add_nonneg (mul_nonneg (by norm_num) (hKcA'_nn i))
            (mul_nonneg (by norm_num) (hKcA_nn i)))
      exact mul_nonneg (by norm_num)
        (add_nonneg
          (mul_nonneg (by norm_num)
            (add_nonneg (mul_nonneg (by norm_num) hp1) (mul_nonneg (by norm_num) hp2)))
          (mul_nonneg (by norm_num) hp3)), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  obtain ⟨HdA, hHdA_head, hHdA_res⟩ := hA g₁ T htie hδ_le hδ0 hbound i
  obtain ⟨HdA', hHdA'_head, hHdA'_res⟩ := hA' g₁ T htie hδ_le hδ0 hbound i
  set RLC11 : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁
    with hRLC11_def
  set RLC01 : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁
    with hRLC01_def
  set RLCfix : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀
    with hRLCfix_def
  set Vd : SmoothCcTensor g₀ 0 4 := RLC11 - RLCfix with hVd_def
  set phiDt : SmoothCcTensor g₀ 6 2 := CurvatureCoefficientDifferenceJetTower.pairTraceOp (I := I) (M := M) g₀ g₀ with hphiDt_def
  set Dpt : SmoothCcTensor g₀ 6 2 :=
    CurvatureCoefficientDifferenceJetTower.pairTraceOp (I := I) (M := M) g₀ g₁ - CurvatureCoefficientDifferenceJetTower.pairTraceOp (I := I) (M := M) g₀ g₀ with hDpt_def
  have hphiDt_par : covGrad (I := I) (M := M) g₀ 6 2 phiDt = 0 := by
    rw [hphiDt_def, pairTraceOp_self_eq (I := I) (M := M) g₀]
    exact phiDtPair_covGrad_zero (I := I) (M := M) g₀
  have hIter2 : ∀ Z : SmoothCcTensor g₀ 0 4,
      slotExtendIter (I := I) (M := M) g₀ 0 4 2 Z =
        slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 Z) :=
    fun Z => rfl
  set WBig : SmoothCcTensor g₀ 2 6 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
      (slotExtend (I := I) (M := M) g₀ 1 5
        (slotExtend (I := I) (M := M) g₀ 0 4 RLC11)) with hWBig_def
  set WVd : SmoothCcTensor g₀ 2 6 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
      (slotExtend (I := I) (M := M) g₀ 1 5
        (slotExtend (I := I) (M := M) g₀ 0 4 Vd)) with hWVd_def
  have hWfix_sub : rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
        (slotExtend (I := I) (M := M) g₀ 1 5
          (slotExtend (I := I) (M := M) g₀ 0 4 RLCfix)) =
      WBig - WVd := by
    rw [hWBig_def, hWVd_def, hVd_def]
    rw [slotExtend_sub (I := I) (M := M) g₀ 0 4 RLC11 RLCfix]
    rw [slotExtend_sub (I := I) (M := M) g₀ 1 5]
    rw [rsDomDomCongrSection_sub_cc (I := I) (M := M) g₀ 2 6 sigmaE0]
    abel
  have hRiemD : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig +
        (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd := by
    have hL1 := riemannCoeff_eq_pairTrace_L11 (I := I) (M := M) g₀ g₁
    have hL0 := riemannCoeff_eq_pairTrace_L11 (I := I) (M := M) g₀ g₀
    rw [hIter2 (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)] at hL1
    rw [hIter2 (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)] at hL0
    rw [hL1, hL0]
    rw [show (CurvatureCoefficientDifferenceJetTower.pairTraceOp (I := I) (M := M) g₀ g₁) = Dpt + phiDt from by
      rw [hDpt_def, hphiDt_def]; abel]
    rw [operatorFieldComposition_add_left_cc (I := I) (M := M) g₀ 2 6 2 Dpt phiDt]
    rw [← hWBig_def, ← hRLCfix_def, hWfix_sub]
    rw [← hphiDt_def]
    rw [operatorFieldComposition_sub_right (I := I) (M := M) g₀ 2 6 2 phiDt WBig WVd]
    rw [smul_add, smul_sub]
    abel
  obtain ⟨HW1c, h1c_head, h1c_res⟩ := exists_slotExtend_head_transport (I := I) (M := M)
    g₀ 0 4 RLC11 i (HdA' + HdA)
  obtain ⟨HW2c, h2c_head, h2c_res⟩ := exists_slotExtend_head_transport (I := I) (M := M)
    g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 RLC11) i HW1c
  obtain ⟨HW11, h11_head, h11_res⟩ := exists_rsDomDomCongrSection_head_transport (I := I) (M := M)
    g₀ 2 6 sigmaE0
    (slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 RLC11))
    i HW2c
  obtain ⟨HW1d, h1d_head, h1d_res⟩ := exists_slotExtend_head_transport (I := I) (M := M)
    g₀ 0 4 Vd i (HdA' + HdA)
  obtain ⟨HW2d, h2d_head, h2d_res⟩ := exists_slotExtend_head_transport (I := I) (M := M)
    g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 Vd) i HW1d
  obtain ⟨HWd, hWd_head, hWd_res⟩ := exists_rsDomDomCongrSection_head_transport (I := I) (M := M)
    g₀ 2 6 sigmaE0
    (slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 Vd))
    i HW2d
  set HdT1 : SmoothCcTensor g₀ 2 (2 + i) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
      (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i) HW11 with hHdT1_def
  set HdT2 : SmoothCcTensor g₀ 2 (2 + i) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
      (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 6 2 phiDt i i) HWd with hHdT2_def
  have hHVc_head : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x ((HdA' + HdA).toSection x) ≤
        (2 * KtA' + 2 * KtA) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by
    intro x
    rw [show ((HdA' + HdA).toSection x) = HdA'.toSection x + HdA.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i) x _ _) ?_
    have h1 := hHdA'_head x
    have h2 := hHdA_head x
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (HdA'.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (HdA.toSection x)
        ≤ 2 * (KtA' * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) +
          2 * (KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
            (mul_le_mul_of_nonneg_left h2 (by norm_num))
      _ = (2 * KtA' + 2 * KtA) * riemannianFiberNormSq (I := I) (M := M) g₀ 0
            (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) :=
          ts_two_mul_add_mul_factor KtA' KtA _
  refine ⟨(2 : ℝ) • (HdT1 + HdT2), ?_, ?_⟩
  · intro x
    rw [show (((2 : ℝ) • (HdT1 + HdT2)).toSection x) =
        (2 : ℝ) • ((HdT1 + HdT2).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [riemannianFiberNormSq_smul_pt (I := I) (M := M) g₀ 2 (2 + i) x 2 _]
    rw [show ((HdT1 + HdT2).toSection x) = HdT1.toSection x + HdT2.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    have hb_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)
    have hHVchain : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
        (HW11.toSection x) ≤
        (n * n) * ((2 * KtA' + 2 * KtA) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
      refine le_trans (h11_head x) ?_
      refine le_trans (h2c_head x) ?_
      calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x (HW1c.toSection x)
          ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((HdA' + HdA).toSection x)) :=
            mul_le_mul_of_nonneg_left (h1c_head x) hn_nn
        _ ≤ n * (n * ((2 * KtA' + 2 * KtA) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
            refine mul_le_mul_of_nonneg_left ?_ hn_nn
            exact mul_le_mul_of_nonneg_left (hHVc_head x) hn_nn
        _ = (n * n) * ((2 * KtA' + 2 * KtA) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) :=
            (mul_assoc n n _).symm
    have hHWdchain : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
        (HWd.toSection x) ≤
        (n * n) * ((2 * KtA' + 2 * KtA) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
      refine le_trans (hWd_head x) ?_
      refine le_trans (h2d_head x) ?_
      calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x (HW1d.toSection x)
          ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((HdA' + HdA).toSection x)) :=
            mul_le_mul_of_nonneg_left (h1d_head x) hn_nn
        _ ≤ n * (n * ((2 * KtA' + 2 * KtA) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
            refine mul_le_mul_of_nonneg_left ?_ hn_nn
            exact mul_le_mul_of_nonneg_left (hHVc_head x) hn_nn
        _ = (n * n) * ((2 * KtA' + 2 * KtA) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) :=
            (mul_assoc n n _).symm
    have hDpt0 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x (Dpt.toSection x) ≤
        CD 0 := by
      have h := hCD g₁ T htie hδ_le hδ0 hbound 0 x
      rw [iteratedCovGrad_zero] at h
      rw [Finset.sum_range_one, Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
      rw [hDpt_def]
      exact h
    have hT1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        (HdT1.toSection x) ≤
        CD 0 * ((n * n) * ((2 * KtA' + 2 * KtA) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
      rw [hHdT1_def]
      refine le_trans (riemannianFiberNormSq_operatorFieldComposition_operatorFieldApplicationLeibnizPsi_diag_le (I := I) (M := M) g₀ 2 6 2
        Dpt i HW11 x) ?_
      refine mul_le_mul hDpt0 hHVchain
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x _) (hCD_nn 0)
    have hT2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        (HdT2.toSection x) ≤
        cP * ((n * n) * ((2 * KtA' + 2 * KtA) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
      rw [hHdT2_def]
      refine le_trans (riemannianFiberNormSq_operatorFieldComposition_operatorFieldApplicationLeibnizPsi_diag_le (I := I) (M := M) g₀ 2 6 2
        phiDt i HWd x) ?_
      refine mul_le_mul ?_ hHWdchain
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x _) hcP_nn
      rw [hphiDt_def]
      exact hcP x
    calc (2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          (HdT1.toSection x + HdT2.toSection x)
        ≤ (2 : ℝ) ^ 2 * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            (HdT1.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdT2.toSection x)) :=
          mul_le_mul_of_nonneg_left
            (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
            (by norm_num)
      _ ≤ (2 : ℝ) ^ 2 * (2 * (CD 0 * ((n * n) * ((2 * KtA' + 2 * KtA) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)))) +
          2 * (cP * ((n * n) * ((2 * KtA' + 2 * KtA) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact add_le_add (mul_le_mul_of_nonneg_left hT1 (by norm_num))
            (mul_le_mul_of_nonneg_left hT2 (by norm_num))
      _ = 8 * (n * n) * (CD 0 + cP) * (2 * KtA' + 2 * KtA) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) :=
          ts_head_bound_factor (CD 0) cP n (2 * KtA' + 2 * KtA) _
  · intro x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
    have hb : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hWfin_def
    have hWfin_nn : 0 ≤ Wfin :=
      Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
    have hWfin_one : 1 ≤ Wfin :=
      Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
    have hVd_res : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)).toSection x) ≤
        (2 * KcA' i + 2 * KcA i) * Wfin := by
      have hVd_split : iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA) =
          (iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA') +
            (iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) - HdA) := by
        rw [show (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) =
            RLC01 - RLCfix from by
          rw [riemannLoweredBackgroundDifference, hRLC01_def, hRLCfix_def]]
        rw [show Vd = (RLC11 - RLC01) + (RLC01 - RLCfix) from by rw [hVd_def]; abel]
        rw [iteratedCovGrad_add (I := I) g₀ 0 4 i (RLC11 - RLC01) (RLC01 - RLCfix)]
        abel
      rw [hVd_split]
      rw [show (((iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA') +
            (iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) -
              HdA)).toSection x) =
          (iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA').toSection x +
            (iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) -
              HdA).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i) x _ _) ?_
      have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA').toSection x) ≤
          KcA' i * Wfin := by
        have h := hHdA'_res x
        rw [hRLC11_def, hRLC01_def]
        exact h
      have h2 := hHdA_res x
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA').toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) -
              HdA).toSection x)
          ≤ 2 * (KcA' i * Wfin) + 2 * (KcA i * Wfin) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
              (mul_le_mul_of_nonneg_left h2 (by norm_num))
        _ = (2 * KcA' i + 2 * KcA i) * Wfin :=
          ts_two_mul_add_mul_factor (KcA' i) (KcA i) Wfin
    have hRLC11_res : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i RLC11 - (HdA' + HdA)).toSection x) ≤
        (4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin := by
      have hsplit : iteratedCovGrad (I := I) g₀ 0 4 i RLC11 - (HdA' + HdA) =
          (iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)) +
            iteratedCovGrad (I := I) g₀ 0 4 i RLCfix := by
        rw [show RLC11 = Vd + RLCfix from by rw [hVd_def]; abel]
        rw [iteratedCovGrad_add (I := I) g₀ 0 4 i Vd RLCfix]
        abel
      rw [hsplit]
      rw [show (((iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)) +
            iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) =
          (iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)).toSection x +
            (iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i) x _ _) ?_
      have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) ≤ cfix i * Wfin := by
        have h2a : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) ≤ cfix i := by
          rw [hRLCfix_def]
          exact hcfix i x
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x)
            ≤ cfix i := h2a
          _ = cfix i * 1 := (mul_one (cfix i)).symm
          _ ≤ cfix i * Wfin := mul_le_mul_of_nonneg_left hWfin_one (hcfix_nn i)
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x)
          ≤ 2 * ((2 * KcA' i + 2 * KcA i) * Wfin) + 2 * (cfix i * Wfin) :=
            add_le_add (mul_le_mul_of_nonneg_left hVd_res (by norm_num))
              (mul_le_mul_of_nonneg_left h2 (by norm_num))
        _ = (4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin :=
          ts_twice_pair_plus_factor (KcA' i) (KcA i) (cfix i) Wfin
    have hT2res : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2).toSection x) ≤
        2 * (cP * ((n * n) * ((2 * KcA' i + 2 * KcA i) * Wfin))) := by
      rw [hHdT2_def]
      refine le_trans (riemannianFiberNormSq_operatorFieldComposition_parallel_argument_residual_le (I := I) (M := M) g₀ 2 6 2
        phiDt hphiDt_par WVd i HWd x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have hchain : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i WVd - HWd).toSection x) ≤
          (n * n) * ((2 * KcA' i + 2 * KcA i) * Wfin) := by
        have hs1 := hWd_res x
        rw [← hWVd_def] at hs1
        refine le_trans hs1 ?_
        refine le_trans (h2d_res x) ?_
        calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 5 i
                (slotExtend (I := I) (M := M) g₀ 0 4 Vd) - HW1d).toSection x)
            ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                ((iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)).toSection x)) :=
              mul_le_mul_of_nonneg_left (h1d_res x) hn_nn
          _ ≤ n * (n * ((2 * KcA' i + 2 * KcA i) * Wfin)) := by
              refine mul_le_mul_of_nonneg_left ?_ hn_nn
              exact mul_le_mul_of_nonneg_left hVd_res hn_nn
          _ = (n * n) * ((2 * KcA' i + 2 * KcA i) * Wfin) :=
            (mul_assoc n n _).symm
      have hp0 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x (phiDt.toSection x) ≤
          cP := by
        rw [hphiDt_def]; exact hcP x
      refine mul_le_mul hp0 hchain
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x _) hcP_nn
    have hT1res : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1).toSection x) ≤
        2 * ((CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i)) * Wfin) +
        2 * ((i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
          ∑ k ∈ Finset.range i, (CD (i - k) * (n * n) *
            ((2 * C1 k + 4 * CA k) *
                Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k)) *
            Wfin) := by
      have hsplitT1 : iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1 =
          ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11) +
            ∑ k ∈ Finset.range i,
              ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
                (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i k)
                (iteratedCovGrad (I := I) g₀ 2 6 k WBig) := by
        rw [iteratedCovGrad_operatorFieldComposition_eq_argCorner_add_lower (I := I) (M := M) g₀ 2 6 2
          Dpt WBig i]
        rw [hHdT1_def]
        rw [operatorFieldComposition_sub_right_cc (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
          (iteratedCovGrad (I := I) g₀ 2 6 i WBig) HW11]
        exact add_sub_right_comm _ _ _
      rw [hsplitT1]
      rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
            (iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11) +
          ∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
              (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i k)
              (iteratedCovGrad (I := I) g₀ 2 6 k WBig)).toSection x) =
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
            (iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11)).toSection x +
          (∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
              (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i k)
              (iteratedCovGrad (I := I) g₀ 2 6 k WBig)).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
      have hDpt0 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x (Dpt.toSection x) ≤
          CD 0 := by
        have h := hCD g₁ T htie hδ_le hδ0 hbound 0 x
        rw [iteratedCovGrad_zero] at h
        rw [Finset.sum_range_one, Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
        rw [hDpt_def]
        exact h
      have hpiece1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
            (iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11)).toSection x) ≤
          CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin := by
        refine le_trans (riemannianFiberNormSq_operatorFieldComposition_operatorFieldApplicationLeibnizPsi_diag_le (I := I) (M := M) g₀ 2 6 2
          Dpt i _ x) ?_
        have hchain : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11).toSection x) ≤
            (n * n) * ((4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin) := by
          have hs1 := h11_res x
          rw [← hWBig_def] at hs1
          refine le_trans hs1 ?_
          refine le_trans (h2c_res x) ?_
          calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 5 i
                  (slotExtend (I := I) (M := M) g₀ 0 4 RLC11) - HW1c).toSection x)
              ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 i RLC11 -
                    (HdA' + HdA)).toSection x)) :=
                mul_le_mul_of_nonneg_left (h1c_res x) hn_nn
            _ ≤ n * (n * ((4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin)) := by
                refine mul_le_mul_of_nonneg_left ?_ hn_nn
                exact mul_le_mul_of_nonneg_left hRLC11_res hn_nn
            _ = (n * n) * ((4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin) :=
              (mul_assoc n n _).symm
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x (Dpt.toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
                ((iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11).toSection x)
            ≤ CD 0 * ((n * n) * ((4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin)) := by
              refine mul_le_mul hDpt0 hchain
                (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x _)
                (hCD_nn 0)
          _ = CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin := by
            simp only [mul_assoc]
      have hpiece2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
              (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i k)
              (iteratedCovGrad (I := I) g₀ 2 6 k WBig)).toSection x) ≤
          (i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
            ∑ k ∈ Finset.range i, (CD (i - k) * (n * n) *
              ((2 * C1 k + 4 * CA k) *
                  Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k)) *
              Wfin := by
        refine le_trans (riemannianFiberNormSq_operatorFieldComposition_argLower_le (I := I) (M := M) g₀ 2 6 2 Dpt WBig i x) ?_
        rw [mul_assoc, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg i)
        refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) i)
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        have hDptjet : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + (i - k)) x
            ((iteratedCovGrad (I := I) g₀ 6 2 (i - k) Dpt).toSection x) ≤
            CD (i - k) * (∑ l ∈ Finset.range ((i - k) + 1),
              Combinatorics.antidiagonalTupleGrid b l) := by
          have h := hCD g₁ T htie hδ_le hδ0 hbound (i - k) x
          rw [hDpt_def]
          exact h
        have hWjet : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + k) x
            ((iteratedCovGrad (I := I) g₀ 2 6 k WBig).toSection x) ≤
            (n * n) * ((2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
              Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k) := by
          rw [hWBig_def]
          rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6
            sigmaE0 _ k x]
          refine le_trans (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
            (slotExtend (I := I) (M := M) g₀ 0 4 RLC11) k x) ?_
          have hinner : riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((4 + 1) + k) x
              ((iteratedCovGrad (I := I) g₀ 1 (4 + 1) k
                (slotExtend (I := I) (M := M) g₀ 0 4 RLC11)).toSection x) ≤
              n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                ((iteratedCovGrad (I := I) g₀ 0 4 k RLC11).toSection x) :=
            riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4 RLC11 k x
          have hRLC11jet : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
              ((iteratedCovGrad (I := I) g₀ 0 4 k RLC11).toSection x) ≤
              (2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k := by
            have hsplit11 : iteratedCovGrad (I := I) g₀ 0 4 k RLC11 =
                iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01) +
                  (iteratedCovGrad (I := I) g₀ 0 4 k
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) +
                    iteratedCovGrad (I := I) g₀ 0 4 k RLCfix) := by
              rw [← iteratedCovGrad_add (I := I) g₀ 0 4 k
                (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) RLCfix]
              rw [← iteratedCovGrad_add (I := I) g₀ 0 4 k (RLC11 - RLC01) _]
              refine congrArg (fun Z => iteratedCovGrad (I := I) g₀ 0 4 k Z) ?_
              rw [show (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) =
                  RLC01 - RLCfix from by
                rw [riemannLoweredBackgroundDifference, hRLC01_def, hRLCfix_def]]
              abel
            rw [hsplit11]
            rw [show ((iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01) +
                  (iteratedCovGrad (I := I) g₀ 0 4 k
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) +
                    iteratedCovGrad (I := I) g₀ 0 4 k RLCfix)).toSection x) =
                (iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01)).toSection x +
                  ((iteratedCovGrad (I := I) g₀ 0 4 k
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x +
                    (iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) from by
              rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_add]; rfl]
            refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + k)
              x _ _) ?_
            have hd1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                ((iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01)).toSection x) ≤
                C1 k * (∑ k' ∈ Finset.range (k + 3),
                  Combinatorics.antidiagonalTupleGrid b k') := by
              have h := hC1 g₁ T htie hδ_le hδ0 hbound k x
              rw [hRLC11_def, hRLC01_def]
              exact h
            have hd23 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                ((iteratedCovGrad (I := I) g₀ 0 4 k
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x +
                  (iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) ≤
                2 * (CA k * (∑ k' ∈ Finset.range (k + 3),
                  Combinatorics.antidiagonalTupleGrid b k')) + 2 * cfix k := by
              refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0
                (4 + k) x _ _) ?_
              have hd2 := hCA g₁ T htie hδ_le hδ0 hbound k x
              have hd3 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) ≤ cfix k := by
                rw [hRLCfix_def]; exact hcfix k x
              exact add_le_add (mul_le_mul_of_nonneg_left hd2 (by norm_num))
                (mul_le_mul_of_nonneg_left hd3 (by norm_num))
            calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01)).toSection x) +
                2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 k
                      (riemannLoweredBackgroundDifference (I := I) (M := M)
                        g₀ g₁)).toSection x +
                    (iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x)
                ≤ 2 * (C1 k * (∑ k' ∈ Finset.range (k + 3),
                    Combinatorics.antidiagonalTupleGrid b k')) +
                  2 * (2 * (CA k * (∑ k' ∈ Finset.range (k + 3),
                    Combinatorics.antidiagonalTupleGrid b k')) + 2 * cfix k) :=
                  add_le_add (mul_le_mul_of_nonneg_left hd1 (by norm_num))
                    (mul_le_mul_of_nonneg_left hd23 (by norm_num))
              _ = (2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                    Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k :=
                ts_grid_sum_factor (C1 k) (CA k) (cfix k) _
          calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((4 + 1) + k) x
                ((iteratedCovGrad (I := I) g₀ 1 (4 + 1) k
                  (slotExtend (I := I) (M := M) g₀ 0 4 RLC11)).toSection x)
              ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 k RLC11).toSection x)) :=
                mul_le_mul_of_nonneg_left hinner hn_nn
            _ ≤ n * (n * ((2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                  Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k)) := by
                refine mul_le_mul_of_nonneg_left ?_ hn_nn
                exact mul_le_mul_of_nonneg_left hRLC11jet hn_nn
            _ = (n * n) * ((2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                  Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k) :=
              (mul_assoc n n _).symm
        have hDptW : (∑ l ∈ Finset.range ((i - k) + 1),
            Combinatorics.antidiagonalTupleGrid b l) ≤
            Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) :=
          sum_antidiagonalTupleGrid_le_boundedFactorGridWindow b hb (by omega) (le_refl _)
        have htgW : (∑ k' ∈ Finset.range (k + 3),
            Combinatorics.antidiagonalTupleGrid b k') ≤
            Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3) :=
          sum_antidiagonalTupleGrid_le_boundedFactorGridWindow b hb (by omega) (le_refl _)
        have hWpair : Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3) ≤
            Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) * Wfin := by
          refine le_trans (Combinatorics.boundedFactorGridWindow_mul_le b hb (i + 1)
            ((i - k) + 1) (k + 3) (by omega) (by omega)) ?_
          refine mul_le_mul_of_nonneg_left ?_
            (Combinatorics.windowPairCellCount_nonneg _ _)
          rw [hWfin_def]
          refine Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) ?_
          omega
        have hDptWfin : Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) ≤
            Wfin := by
          rw [hWfin_def]
          exact Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) (by omega)
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + (i - k)) x
              ((iteratedCovGrad (I := I) g₀ 6 2 (i - k) Dpt).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + k) x
              ((iteratedCovGrad (I := I) g₀ 2 6 k WBig).toSection x)
            ≤ (CD (i - k) * (∑ l ∈ Finset.range ((i - k) + 1),
                Combinatorics.antidiagonalTupleGrid b l)) *
              ((n * n) * ((2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k)) := by
              refine mul_le_mul hDptjet hWjet
                (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + k) x _) ?_
              exact mul_nonneg (hCD_nn _) (Finset.sum_nonneg fun l _ =>
                Combinatorics.antidiagonalTupleGrid_nonneg b hb l)
          _ ≤ (CD (i - k) * Combinatorics.boundedFactorGridWindow b (i + 1)
                ((i - k) + 1)) *
              ((n * n) * ((2 * C1 k + 4 * CA k) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3) + 4 * cfix k)) := by
              refine mul_le_mul ?_ ?_ ?_ ?_
              · exact mul_le_mul_of_nonneg_left hDptW (hCD_nn _)
              · refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hn_nn hn_nn)
                refine add_le_add ?_ (le_refl _)
                refine mul_le_mul_of_nonneg_left htgW ?_
                exact add_nonneg (mul_nonneg (by norm_num) (hC1_nn k))
                  (mul_nonneg (by norm_num) (hCA_nn k))
              · refine mul_nonneg (mul_nonneg hn_nn hn_nn) ?_
                refine add_nonneg ?_ ?_
                · refine mul_nonneg ?_ (Finset.sum_nonneg fun k' _ =>
                    Combinatorics.antidiagonalTupleGrid_nonneg b hb k')
                  exact add_nonneg (mul_nonneg (by norm_num) (hC1_nn k))
                    (mul_nonneg (by norm_num) (hCA_nn k))
                · exact mul_nonneg (by norm_num) (hcfix_nn k)
              · exact mul_nonneg (hCD_nn _)
                  (Combinatorics.boundedFactorGridWindow_nonneg b hb _ _)
          _ = CD (i - k) * (n * n) * (2 * C1 k + 4 * CA k) *
                (Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3)) +
              CD (i - k) * (n * n) * (4 * cfix k) *
                Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) :=
              ts_product_sum_expand (CD (i - k)) (n * n) (2 * C1 k + 4 * CA k)
                (4 * cfix k)
                (Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1))
                (Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3))
          _ ≤ CD (i - k) * (n * n) * (2 * C1 k + 4 * CA k) *
                (Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) * Wfin) +
              CD (i - k) * (n * n) * (4 * cfix k) * Wfin := by
              refine add_le_add ?_ ?_
              · refine mul_le_mul_of_nonneg_left hWpair ?_
                refine mul_nonneg (mul_nonneg (hCD_nn _) (mul_nonneg hn_nn hn_nn)) ?_
                exact add_nonneg (mul_nonneg (by norm_num) (hC1_nn k))
                  (mul_nonneg (by norm_num) (hCA_nn k))
              · refine mul_le_mul_of_nonneg_left hDptWfin ?_
                refine mul_nonneg (mul_nonneg (hCD_nn _) (mul_nonneg hn_nn hn_nn)) ?_
                exact mul_nonneg (by norm_num) (hcfix_nn k)
          _ = (CD (i - k) * (n * n) *
              ((2 * C1 k + 4 * CA k) *
                  Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k)) *
              Wfin :=
            ts_product_sum_factor (CD (i - k)) (n * n) (2 * C1 k + 4 * CA k)
              (4 * cfix k) (Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3)) Wfin
      have htwo : (0 : ℝ) ≤ 2 := by norm_num
      exact add_le_add (mul_le_mul_of_nonneg_left hpiece1 htwo)
        (mul_le_mul_of_nonneg_left hpiece2 htwo)
    have hsmul_diff : iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
          (2 : ℝ) • (HdT1 + HdT2) =
        (2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1) +
          (iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2)) :=
      ts_riemann_coeff_sub_head_eq g₀ g₁ i Dpt phiDt WBig WVd HdT1 HdT2 hRiemD
    have hT1res' := hT1res.trans_eq
      (ts_residual_sum_factor (Finset.range i)
        (fun k => CD (i - k) * (n * n) *
          ((2 * C1 k + 4 * CA k) *
              Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k))
        (CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i))
        ((i : ℝ) * operatorFieldApplicationGdiag (E := E) i) Wfin)
    have hT2res' := hT2res.trans_eq
      (ts_nested_mul_assoc cP (n * n) (2 * KcA' i + 2 * KcA i) Wfin)
    exact ts_combine_riemannianFiberNormSq_residual g₀ i x
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀))
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 Dpt WBig))
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 phiDt WVd))
      HdT1 HdT2
      (CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i))
      ((i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
        ∑ k ∈ Finset.range i, CD (i - k) * (n * n) *
          ((2 * C1 k + 4 * CA k) *
              Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k))
      (cP * (n * n)) (2 * KcA' i + 2 * KcA i) Wfin hsmul_diff hT1res' hT2res'

end TopOrderSeparatedRungRiemannCoeff

end Spectral
end Analysis
end DifferentialGeometry

end
