import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantDerivativePointwiseBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroCoefficientDifferenceRadiusFree

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_lieCorrectionZeroVectorBundle_antidiagonalTupleGridWindow_bound (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ Kvb : ℕ → ℝ, (∀ i, 0 ≤ Kvb i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (_hP1 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 1 ≤ Λ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁)).toSection x) ≤
          Kvb i * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀
              (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (i + 1) := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨Kmcd, hKmcd_nn, hmcd⟩ :=
    metricConnectionDifferenceLoweredCoefficient_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ g₀ hδ₀
  obtain ⟨KΩ, hKΩ_nn, hΩ⟩ := deTurckVectorFieldCovector_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ g₀ hδ₀
  obtain ⟨cip, hcip_nn, hip⟩ := riemannianFiberNormSq_iteratedCovGrad_ipLow_le (I := I) (M := M) g₀
  obtain ⟨Kcg, hKcg_nn, hcg⟩ := riemannianFiberNormSq_iteratedCovGrad_cometricCastG0_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KA : ℕ → ℝ := fun i => fr * Kmcd i with hKA_def
  have hKA_nn : ∀ i, 0 ≤ KA i := fun i => mul_nonneg hfr_nn (hKmcd_nn i)
  set KB : ℕ → ℝ := fun q => cip q * ∑ m ∈ Finset.range (q + 1), KΩ m with hKB_def
  have hKB_nn : ∀ q, 0 ≤ KB q :=
    fun q => mul_nonneg (hcip_nn q) (Finset.sum_nonneg (fun m _ => hKΩ_nn m))
  set KC : ℕ → ℝ := fun i => fr * Kcg i with hKC_def
  have hKC_nn : ∀ i, 0 ≤ KC i := fun i => mul_nonneg hfr_nn (hKcg_nn i)
  set KPass : ℕ → ℝ := fun n => operatorFieldCompositionGridConstant (E := E) 0 0
    (fun i => KA i * antidiagonalTupleGridWindowShiftConstant Λ (i + 1)) (fun l => KB l * antidiagonalTupleGridWindowShiftConstant Λ (l + 1)) n
    with hKPass_def
  have hKPass_nn : ∀ n, 0 ≤ KPass n := fun n =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0)
      (fun i => mul_nonneg (hKA_nn i) (antidiagonalTupleGridWindowShiftConstant_nonneg hΛ0 _))
      (fun l => mul_nonneg (hKB_nn l) (antidiagonalTupleGridWindowShiftConstant_nonneg hΛ0 _)) n
  refine ⟨fun i => 4 * operatorFieldCompositionGridConstant (E := E) 0 0
      (fun j => KC j * antidiagonalTupleGridWindowShiftConstant Λ (j + 1)) KPass i, ?_, ?_⟩
  · intro i
    refine mul_nonneg (by norm_num) ?_
    exact operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0)
      (fun j => mul_nonneg (hKC_nn j) (antidiagonalTupleGridWindowShiftConstant_nonneg hΛ0 _)) hKPass_nn i
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1 i x
  have hsup : ∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
      (P.toSection y) ≤ Real.sqrt Λ ^ 2 := by
    intro y
    rw [Real.sq_sqrt hΛ0]
    simpa using hP0 y
  have hA : ∀ (m : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (4 + m) y
          ((iteratedCovGrad (I := I) g₀ 1 4 m
            (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)).toSection y) ≤
        KA m * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (m + 2) := by
    intro m y
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g₀ g₁ m y) ?_
    rw [hKA_def, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (hmcd g₁ P htie hδ_le hδ0 hδ hsup m y) hfr_nn
  have hB : ∀ (q : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (1 + q) y
          ((iteratedCovGrad (I := I) g₀ 2 1 q
            (ipLowCc (I := I) (M := M) g₀
              (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀))).toSection y) ≤
        KB q * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (q + 2) := by
    intro q y
    have hbnn := covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y
    refine le_trans (hip (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀) q y) ?_
    rw [hKB_def, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hcip_nn q)
    calc ∑ m ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + m) y
            ((iteratedCovGrad (I := I) g₀ 0 1 m
              (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀)).toSection y)
        ≤ ∑ m ∈ Finset.range (q + 1),
            KΩ m * Combinatorics.antidiagonalTupleGridWindow
              (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (m + 2) :=
          Finset.sum_le_sum (fun m _ => hΩ g₁ P htie hδ_le hδ0 hδ m y)
      _ ≤ ∑ m ∈ Finset.range (q + 1),
            KΩ m * Combinatorics.antidiagonalTupleGridWindow
              (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (q + 2) := by
          refine Finset.sum_le_sum (fun m hm => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (hKΩ_nn m)
          exact Combinatorics.antidiagonalTupleGridWindow_mono _ hbnn
            (by rw [Finset.mem_range] at hm; omega)
      _ = (∑ m ∈ Finset.range (q + 1), KΩ m) *
            Combinatorics.antidiagonalTupleGridWindow
              (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (q + 2) := by
          rw [Finset.sum_mul]
  have hPass : ∀ (n : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + n) y
          ((iteratedCovGrad (I := I) g₀ 2 4 n
            (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁)).toSection y) ≤
        KPass n * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀
            (iteratedCovGrad (I := I) g₀ 0 2 1 P) y) (n + 1) := by
    intro n y
    rw [lieCorrectionZeroVectorBundleLift_eq_ccOperatorFieldComp (I := I) (M := M) g₀ g₁]
    exact antidiagonalTupleGridWindow_covariantDerivative_bound (I := I) (M := M) g₀ P hΛ1 hP0 hP1
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)
      (ipLowCc (I := I) (M := M) g₀ (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀))
      hKA_nn hKB_nn hA hB n y
  have hC : ∀ (m : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) y
          ((iteratedCovGrad (I := I) g₀ 4 2 m
            (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)).toSection y) ≤
        KC m * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (m + 2) := by
    intro m y
    have hbnn := covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_reindexedCometricDoubleTrace_le (I := I) (M := M) g₀ g₁ m y) ?_
    rw [hKC_def, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hfr_nn
    refine le_trans (hcg g₁ P htie hδ_le hδ0 hδ m y) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKcg_nn m)
    exact Combinatorics.antidiagonalTupleGridWindow_mono _ hbnn (by omega)
  have hC' := antidiagonalTupleGridWindow_covariantDerivative_shift (I := I) (M := M) g₀ P hΛ1 hP0 hP1
    (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁) hKC_nn 0
    (fun m y => by simpa using hC m y)
  have houter : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)
          (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁))).toSection x) ≤
      operatorFieldCompositionGridConstant (E := E) 0 0 (fun j => KC j * antidiagonalTupleGridWindowShiftConstant Λ (j + 1)) KPass i *
        Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀
            (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (i + 1) := by
    simpa using operatorFieldComposition_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ (u := 0) (v := 0)
      (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁) (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁)
      (iteratedCovGrad (I := I) g₀ 0 2 1 P)
      (fun j => mul_nonneg (hKC_nn j) (antidiagonalTupleGridWindowShiftConstant_nonneg hΛ0 _)) hKPass_nn
      (fun j y => by simpa using hC' j y) (fun l y => by simpa using hPass l y) i x
  rw [lieCorrectionZeroVectorBundle_eq_ccOperatorFieldComp (I := I) (M := M) g₀ g₁,
    DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real
      (I := I) (M := M) g₀ 2 2 i (2 : ℝ) _,
    SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul (I := I) (M := M) g₀ 2 (2 + i) x (2 : ℝ) _]
  have h4 : ((2 : ℝ) ^ 2) = 4 := by norm_num
  rw [h4, mul_assoc]
  exact mul_le_mul_of_nonneg_left houter (by norm_num)

theorem exists_lieCorrectionZeroVectorBundle_jet_cap_bound (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (_hP1 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 1 ≤ Λ)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
          K i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨Kvb, hKvb_nn, hvb⟩ := exists_lieCorrectionZeroVectorBundle_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ hδ₀ hΛ1
  obtain ⟨Kint, hKint_nn, hint⟩ :=
    antidiagonalTupleGridWindow_bound_to_jet_bound (I := I) (M := M) g₀ (Λ₁ := Real.sqrt Λ) (Real.sqrt_nonneg Λ)
  refine ⟨fun i => Kvb i * ∑ k ∈ Finset.range (i + 1), Kint k,
    fun i => mul_nonneg (hKvb_nn i) (Finset.sum_nonneg (fun k _ => hKint_nn k)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1 i
  have hcap : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Real.sqrt Λ ^ 2 := by
    intro x
    rw [Real.sq_sqrt hΛ0]
    simpa using hP1 x
  exact hint P hcap 2 2 i 1 (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁) (Kvb i) (hKvb_nn i)
    (fun x => hvb g₁ P htie hδ_le hδ0 hδ hP0 hP1 i x)

end DifferentialGeometry.Integral.Connection

end
