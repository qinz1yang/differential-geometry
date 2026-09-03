import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.GridWindow.TermJets
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrection.ZeroOrder.VectorBundle.Expansion

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [SigmaCompactSpace M] in
theorem exists_metricLoweredConnectionDifference_markWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkedGridWindow (I := I) (M := M) g₀ P (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀) 1 K := by
  classical
  obtain ⟨Kcd, hKcd_nn, hcd⟩ := connectionDifferenceMark (I := I) (M := M) g₀ hδ₀
  refine ⟨Kcd, hKcd_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P (metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (I := I) (M := M) g₀ g₁) ?_
  intro i x
  rw [metricLoweredConnectionDifferenceCoefficient_fiber_norm_sq_eq (I := I) (M := M) g₀ g₁ i x]
  exact hcd g₁ P htie hδ_le hδ0 hδ i x

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem mcd_corr_sub (g₀ : SmoothRiemannianMetric I M)
    (ΦA ΦB : SmoothCcTensor g₀ 3 3) (W₁ W₂ : SmoothCcTensor g₀ 0 3) :
    (W₁ +
        ((1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3 ΦA W₁ +
          (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3 ΦB W₁)) -
      (W₂ +
        ((1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3 ΦA W₂ +
          (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3 ΦB W₂)) =
      (W₁ - W₂) +
        ((1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3 ΦA (W₁ - W₂) +
          (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3 ΦB (W₁ - W₂)) := by
  have hA : operatorFieldApply (I := I) (M := M) g₀ 3 3 ΦA (W₁ - W₂) =
      operatorFieldApply (I := I) (M := M) g₀ 3 3 ΦA W₁ -
        operatorFieldApply (I := I) (M := M) g₀ 3 3 ΦA W₂ := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      operatorFieldComposition_sub_right (I := I) (M := M) g₀ 0 3 3 ΦA W₁ W₂
  have hB : operatorFieldApply (I := I) (M := M) g₀ 3 3 ΦB (W₁ - W₂) =
      operatorFieldApply (I := I) (M := M) g₀ 3 3 ΦB W₁ -
        operatorFieldApply (I := I) (M := M) g₀ 3 3 ΦB W₂ := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      operatorFieldComposition_sub_right (I := I) (M := M) g₀ 0 3 3 ΦB W₁ W₂
  rw [hA, hB]
  module

theorem mcdBackgroundAntidiagonalTupleGridWindow (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        (_hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n
              (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ gB -
                metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          K n * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 1) := by
  classical
  let Wfix : SmoothCcTensor g₀ 0 3 :=
    metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₀ - metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gB
  choose KW hKW_nn hKW using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g₀ 0 (3 + i)
        (iteratedCovGrad (I := I) g₀ 0 3 i Wfix))
  choose Kphi hKphi_nn hphi using
    (fun σ : Equiv.Perm (Fin 5) =>
      metricPerturbationLoweringCoefficient_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ σ (Λ₀ := 1))
  set SPhi : ℕ → ℝ := fun i => ∑ σ : Equiv.Perm (Fin 5), Kphi σ i with hSPhi_def
  have hSPhi_nn : ∀ i, 0 ≤ SPhi i := fun i =>
    Finset.sum_nonneg (fun σ _ => hKphi_nn σ i)
  have hsingle : ∀ (σ : Equiv.Perm (Fin 5)) (n : ℕ), Kphi σ n ≤ SPhi n := by
    intro σ n
    simp only [hSPhi_def]
    exact Finset.single_le_sum (f := fun r => Kphi r n)
      (fun r _ => hKphi_nn r n) (Finset.mem_univ σ)
  have hF_nn : ∀ i, 0 ≤ operatorFieldCompositionGridConstant (E := E) 0 0 SPhi KW i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hSPhi_nn hKW_nn i
  refine ⟨fun i => 2 * KW i +
      2 * (2 * ((1 / 2 : ℝ) ^ 2 * operatorFieldCompositionGridConstant (E := E) 0 0 SPhi KW i) +
        2 * ((1 / 2 : ℝ) ^ 2 * operatorFieldCompositionGridConstant (E := E) 0 0 SPhi KW i)), fun i => by
    have := hKW_nn i
    have := hF_nn i
    nlinarith, ?_⟩
  intro g₁ P htie hP0
  have hsup : ∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
      (P.toSection y) ≤ (1 : ℝ) ^ 2 := by
    intro y
    rw [one_pow]
    exact hP0 y
  let WB : SmoothCcTensor g₀ 0 3 := metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB
  let W0 : SmoothCcTensor g₀ 0 3 := metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀
  let W : SmoothCcTensor g₀ 0 3 := WB - W0
  have hW_eq : W = Wfix := by
    dsimp only [W, WB, W0, Wfix, metricLoweredConnectionDifference]
    module
  have hW : HasMarkedGridWindow (I := I) (M := M) g₀ P W 0 KW :=
    hasMarkedGridWindow_congr (I := I) (M := M) g₀ P hW_eq
      (hasMarkedGridWindow_of_pointwise_bound (I := I) (M := M) g₀ P Wfix hKW_nn hKW)
  have hbnn : ∀ y : M, ∀ j, 0 ≤ covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y j :=
    fun y => covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y
  have hcorr : ∀ Φ : SmoothCcTensor g₀ 3 3,
      (∀ (i : ℕ) (y : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + i) y
            ((iteratedCovGrad (I := I) g₀ 3 3 i Φ).toSection y) ≤
          SPhi i * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (i + 1)) →
      HasMarkedGridWindow (I := I) (M := M) g₀ P
        (operatorFieldApply (I := I) (M := M) g₀ 3 3 Φ W) 0
        (operatorFieldCompositionGridConstant (E := E) 0 0 SPhi KW) := by
    intro Φ hwin
    rw [← operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 3 3]
    simpa using hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hSPhi_nn hKW_nn
      (hasMarkedGridWindow_of_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ P _ hwin) hW
  have hmark : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ gB -
        metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) 0
      (fun i => 2 * KW i +
        2 * (2 * ((1 / 2 : ℝ) ^ 2 * operatorFieldCompositionGridConstant (E := E) 0 0 SPhi KW i) +
          2 * ((1 / 2 : ℝ) ^ 2 * operatorFieldCompositionGridConstant (E := E) 0 0 SPhi KW i))) := by
    rw [metricConnectionDifferenceLoweredCoefficient_expansion (I := I) (M := M) g₀ g₁ gB P htie,
      metricConnectionDifferenceLoweredCoefficient_expansion (I := I) (M := M) g₀ g₁ g₀ P htie,
      mcd_corr_sub (I := I) (M := M) g₀]
    refine hasMarkedGridWindow_add (I := I) (M := M) g₀ P hW
      (hasMarkedGridWindow_add (I := I) (M := M) g₀ P
        (hasMarkedGridWindow_smul (I := I) (M := M) g₀ P (1 / 2 : ℝ)
          (hcorr _ (fun i y => le_trans (hphi _ P hsup i y)
            (mul_le_mul_of_nonneg_right (hsingle _ i)
              (Combinatorics.antidiagonalTupleGridWindow_nonneg _ (hbnn y) _)))))
        (hasMarkedGridWindow_smul (I := I) (M := M) g₀ P (1 / 2 : ℝ)
          (hcorr _ (fun i y => le_trans (hphi _ P hsup i y)
            (mul_le_mul_of_nonneg_right (hsingle _ i)
              (Combinatorics.antidiagonalTupleGridWindow_nonneg _ (hbnn y) _))))))
  intro n x
  simpa only [Combinatorics.markGrid_zero] using hmark n x

theorem mcdMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1),
        HasMarkedGridWindow (I := I) (M := M) g₀ P
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) 1 K := by
  classical
  obtain ⟨Kwx, hKwx_nn, hwx⟩ := exists_metricLoweredConnectionDifference_markWindow (I := I) (M := M) g₀ hδ₀
  choose Kphi hKphi_nn hphi using
    (fun σ : Equiv.Perm (Fin 5) =>
      metricPerturbationLoweringCoefficient_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ σ (Λ₀ := 1))
  set SPhi : ℕ → ℝ := fun i => ∑ σ : Equiv.Perm (Fin 5), Kphi σ i with hSPhi_def
  have hSPhi_nn : ∀ i, 0 ≤ SPhi i := fun i =>
    Finset.sum_nonneg (fun σ _ => hKphi_nn σ i)
  have hsingle : ∀ (σ : Equiv.Perm (Fin 5)) (n : ℕ), Kphi σ n ≤ SPhi n := by
    intro σ n
    simp only [hSPhi_def]
    exact Finset.single_le_sum (f := fun r => Kphi r n)
      (fun r _ => hKphi_nn r n) (Finset.mem_univ σ)
  have hF_nn : ∀ i, 0 ≤ operatorFieldCompositionGridConstant (E := E) 0 0 SPhi Kwx i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hSPhi_nn hKwx_nn i
  refine ⟨fun i => 2 * Kwx i +
      2 * (2 * ((1 / 2 : ℝ) ^ 2 * operatorFieldCompositionGridConstant (E := E) 0 0 SPhi Kwx i) +
        2 * ((1 / 2 : ℝ) ^ 2 * operatorFieldCompositionGridConstant (E := E) 0 0 SPhi Kwx i)), fun i => by
    have := hKwx_nn i; have := hF_nn i; nlinarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0
  have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      (P.toSection x) ≤ (1 : ℝ) ^ 2 := by
    intro x; rw [one_pow]; exact hP0 x
  have hWX : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀) 1 Kwx := hwx g₁ P htie hδ_le hδ0 hδ
  have hbnn : ∀ y : M, ∀ j, 0 ≤ covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y j :=
    fun y => covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y
  have hcorr : ∀ Φ : SmoothCcTensor g₀ 3 3,
      (∀ (n : ℕ) (y : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + n) y
            ((iteratedCovGrad (I := I) g₀ 3 3 n Φ).toSection y) ≤
          SPhi n * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (n + 1)) →
      HasMarkedGridWindow (I := I) (M := M) g₀ P
        (operatorFieldApply (I := I) (M := M) g₀ 3 3 Φ (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀)) 1
        (operatorFieldCompositionGridConstant (E := E) 0 0 SPhi Kwx) := by
    intro Φ hwin
    rw [← operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 3 3]
    simpa using hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hSPhi_nn hKwx_nn
      (hasMarkedGridWindow_of_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ P _ hwin) hWX
  refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P
    (metricConnectionDifferenceLoweredCoefficient_expansion (I := I) (M := M) g₀ g₁ g₀ P htie) ?_
  refine hasMarkedGridWindow_add (I := I) (M := M) g₀ P hWX
    (hasMarkedGridWindow_add (I := I) (M := M) g₀ P
      (hasMarkedGridWindow_smul (I := I) (M := M) g₀ P (1 / 2 : ℝ)
        (hcorr _ (fun n y => le_trans (hphi _ P hsup n y)
          (mul_le_mul_of_nonneg_right (hsingle _ n)
            (Combinatorics.antidiagonalTupleGridWindow_nonneg _ (hbnn y) _)))))
      (hasMarkedGridWindow_smul (I := I) (M := M) g₀ P (1 / 2 : ℝ)
        (hcorr _ (fun n y => le_trans (hphi _ P hsup n y)
          (mul_le_mul_of_nonneg_right (hsingle _ n)
            (Combinatorics.antidiagonalTupleGridWindow_nonneg _ (hbnn y) _))))))

theorem exists_deTurckVectorFieldCovector_markWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkedGridWindow (I := I) (M := M) g₀ P
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀) 1 K := by
  classical
  obtain ⟨Kwx, hKwx_nn, hwx⟩ := exists_metricLoweredConnectionDifference_markWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kcg, hKcg_nn, hcg⟩ := riemannianFiberNormSq_iteratedCovGrad_cometricCastG0_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  refine ⟨operatorFieldCompositionGridConstant (E := E) 0 0 Kcg Kwx,
    fun i => operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hKcg_nn hKwx_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  have hCast : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (cometricCastG0 (I := I) g₀ g₁) 0 Kcg :=
    hasMarkedGridWindow_of_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ P _ (fun l y => hcg g₁ P htie hδ_le hδ0 hδ l y)
  refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P
    (show deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 (cometricCastG0 (I := I) g₀ g₁)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀) from by
      rw [operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 3 1, deTurckVectorFieldCovector]) ?_
  simpa using hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hKcg_nn hKwx_nn hCast
    (hwx g₁ P htie hδ_le hδ0 hδ)

theorem ipLowMark (g₀ : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℝ, (∀ l, 0 ≤ c l) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2) {u : ℕ} (om : SmoothCcTensor g₀ 0 1)
        {K : ℕ → ℝ}, (∀ i, 0 ≤ K i) →
        HasMarkedGridWindow (I := I) (M := M) g₀ P om u K →
        HasMarkedGridWindow (I := I) (M := M) g₀ P (ipLowCc (I := I) (M := M) g₀ om) u
          (fun l => c l * ∑ m ∈ Finset.range (l + 1), K m) := by
  classical
  obtain ⟨c, hc_nn, hip⟩ := riemannianFiberNormSq_iteratedCovGrad_ipLow_le (I := I) (M := M) g₀
  refine ⟨c, hc_nn, ?_⟩
  intro P u om K hK hom l x
  refine le_trans (hip om l x) ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hc_nn l)
  have hbnn : ∀ j, 0 ≤ covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x j :=
    covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x
  calc (∑ m ∈ Finset.range (l + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 1 m om).toSection x))
      ≤ ∑ m ∈ Finset.range (l + 1),
          K m * Combinatorics.markGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) u l := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        refine le_trans (hom m x) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hK m)
        exact Combinatorics.markGrid_mono _ hbnn u
          (by rw [Finset.mem_range] at hm; omega)
    _ = (∑ m ∈ Finset.range (l + 1), K m) *
          Combinatorics.markGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) u l := by
        rw [Finset.sum_mul]

theorem exists_lieCorrectionZeroVectorBundle_markWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1),
        HasMarkedGridWindow (I := I) (M := M) g₀ P (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁) 2 K := by
  classical
  obtain ⟨Kmcd, hKmcd_nn, hmcd⟩ := mcdMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨KΩ, hKΩ_nn, hΩ⟩ := exists_deTurckVectorFieldCovector_markWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨cip, hcip_nn, hip⟩ := ipLowMark (I := I) (M := M) g₀
  obtain ⟨Kcg, hKcg_nn, hcg⟩ := riemannianFiberNormSq_iteratedCovGrad_cometricCastG0_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KA : ℕ → ℝ := fun m => fr * Kmcd m with hKA_def
  have hKA_nn : ∀ m, 0 ≤ KA m := fun m => mul_nonneg hfr_nn (hKmcd_nn m)
  set KB : ℕ → ℝ := fun l => cip l * ∑ m ∈ Finset.range (l + 1), KΩ m with hKB_def
  have hKB_nn : ∀ l, 0 ≤ KB l :=
    fun l => mul_nonneg (hcip_nn l) (Finset.sum_nonneg (fun m _ => hKΩ_nn m))
  set KC : ℕ → ℝ := fun m => fr * Kcg m with hKC_def
  have hKC_nn : ∀ m, 0 ≤ KC m := fun m => mul_nonneg hfr_nn (hKcg_nn m)
  set KPass : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 KA KB with hKPass_def
  have hKPass_nn : ∀ n, 0 ≤ KPass n := fun n =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hKA_nn hKB_nn n
  refine ⟨fun i => (2 : ℝ) ^ 2 * operatorFieldCompositionGridConstant (E := E) 0 0 KC KPass i, fun i => by
    have := operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hKC_nn hKPass_nn i; nlinarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0
  have hA : HasMarkedGridWindow (I := I) (M := M) g₀ P (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁) 1 KA := by
    intro m y
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g₀ g₁ m y) ?_
    rw [hKA_def, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (hmcd g₁ P htie hδ_le hδ0 hδ hP0 m y) hfr_nn
  have hB : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (ipLowCc (I := I) (M := M) g₀ (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀)) 1 KB :=
    hip P _ hKΩ_nn (hΩ g₁ P htie hδ_le hδ0 hδ)
  have hC : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁) 0 KC := by
    refine hasMarkedGridWindow_of_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ P _ (fun m y => ?_)
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_reindexedCometricDoubleTrace_le (I := I) (M := M) g₀ g₁ m y) ?_
    rw [hKC_def, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hcg g₁ P htie hδ_le hδ0 hδ m y) hfr_nn
  have hPass : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁) 2 KPass := by
    refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P (lieCorrectionZeroVectorBundleLift_eq_ccOperatorFieldComp (I := I) (M := M) g₀ g₁) ?_
    simpa using hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hKA_nn hKB_nn hA hB
  refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P (lieCorrectionZeroVectorBundle_eq_ccOperatorFieldComp (I := I) (M := M) g₀ g₁) ?_
  refine hasMarkedGridWindow_smul (I := I) (M := M) g₀ P (2 : ℝ) ?_
  simpa using hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hKC_nn hKPass_nn hC hPass

theorem exists_lieCorrectionZeroVectorBundle_iteratedCovGrad_norm_sq_bound (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨KV, hKV_nn, hVB⟩ := exists_lieCorrectionZeroVectorBundle_markWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨K0', hK0'_nn, hjet⟩ := markedGridWindow_jet_bound (I := I) (M := M) g₀
  obtain ⟨cg, hcg_nn, hcg⟩ := gradCapLin (I := I) (M := M) hDim g₀
  refine ⟨fun i => KV i * K0' i, fun i => KV i * K0' i * cg,
    fun i => mul_nonneg (hKV_nn i) (hK0'_nn i),
    fun i => mul_nonneg (mul_nonneg (hKV_nn i) (hK0'_nn i)) hcg_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 i
  set H3 : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2 with hH3_def
  have hH3_nn : 0 ≤ H3 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  set Λ₁ : ℝ := Real.sqrt (cg * H3) with hΛ₁_def
  have hΛ₁0 : 0 ≤ Λ₁ := Real.sqrt_nonneg _
  have hΛ₁sq : Λ₁ ^ 2 = cg * H3 := Real.sq_sqrt (mul_nonneg hcg_nn hH3_nn)
  have hcap : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2 := by
    intro x
    rw [hΛ₁sq]
    exact hcg P x
  have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      (P.toSection x) ≤ (1 : ℝ) ^ 2 := by
    intro x; rw [one_pow]; exact hP0 x
  have hres := hjet P (Λ₀ := 1) zero_le_one (le_refl _) hΛ₁0 hsup hcap
    (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁) hKV_nn
    (hVB g₁ P htie hδ_le hδ0 hδ hP0) i
  refine hres.trans (le_of_eq ?_)
  rw [hΛ₁sq]
  ring

private noncomputable def markOneConst (n : ℕ) : ℝ :=
  ∑ c ∈ Finset.range (n + 1),
    Combinatorics.antidiagonalTupleGridWindowMulConst (c + 1) (n - c)

private lemma markOneConst_nn (n : ℕ) : 0 ≤ markOneConst n :=
  Finset.sum_nonneg (fun c _ =>
    Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg (c + 1) (n - c))

private lemma mark_one_antidiagonalTupleGridWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (n : ℕ) :
    Combinatorics.markGrid b 1 n ≤
      markOneConst n * Combinatorics.antidiagonalTupleGridWindow b (n + 2) := by
  classical
  rw [Combinatorics.markGrid_succ]
  simp only [Combinatorics.markGrid_zero]
  have hterm : ∀ c ∈ Finset.range (n + 1),
      b (c + 1) * Combinatorics.antidiagonalTupleGridWindow b (n - c + 1) ≤
        Combinatorics.antidiagonalTupleGridWindowMulConst (c + 1) (n - c) *
          Combinatorics.antidiagonalTupleGridWindow b (n + 2) := by
    intro c hc
    have hcn : c ≤ n := by
      rw [Finset.mem_range] at hc
      omega
    have hsingle := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le
      b hb 0 (c + 1) (by omega)
    rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one, zero_add] at hsingle
    have hsingle' : b (c + 1) ≤
        Combinatorics.antidiagonalTupleGridWindow b (c + 2) :=
      hsingle.trans (Combinatorics.antidiagonalTupleGrid_le_window b hb (by omega))
    have hright_nn : 0 ≤
        Combinatorics.antidiagonalTupleGridWindow b (n - c + 1) :=
      Combinatorics.antidiagonalTupleGridWindow_nonneg b hb _
    calc
      b (c + 1) * Combinatorics.antidiagonalTupleGridWindow b (n - c + 1)
          ≤ Combinatorics.antidiagonalTupleGridWindow b (c + 2) *
              Combinatorics.antidiagonalTupleGridWindow b (n - c + 1) :=
        mul_le_mul_of_nonneg_right hsingle' hright_nn
      _ ≤ Combinatorics.antidiagonalTupleGridWindowMulConst (c + 1) (n - c) *
            Combinatorics.antidiagonalTupleGridWindow b ((c + 1) + (n - c) + 1) :=
        Combinatorics.antidiagonalTupleGridWindow_mul_le b hb (c + 1) (n - c)
      _ = Combinatorics.antidiagonalTupleGridWindowMulConst (c + 1) (n - c) *
            Combinatorics.antidiagonalTupleGridWindow b (n + 2) := by
        rw [show (c + 1) + (n - c) + 1 = n + 2 by omega]
  calc
    ∑ c ∈ Finset.range (n + 1),
        b (c + 1) * Combinatorics.antidiagonalTupleGridWindow b (n - c + 1)
      ≤ ∑ c ∈ Finset.range (n + 1),
          Combinatorics.antidiagonalTupleGridWindowMulConst (c + 1) (n - c) *
            Combinatorics.antidiagonalTupleGridWindow b (n + 2) :=
        Finset.sum_le_sum hterm
    _ = markOneConst n * Combinatorics.antidiagonalTupleGridWindow b (n + 2) := by
      rw [markOneConst, Finset.sum_mul]

theorem lieCorrectionZeroMixedConnectionMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1),
        HasMarkedGridWindow (I := I) (M := M) g₀ P
          (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g₀) 2 K := by
  classical
  obtain ⟨Kmcd, hKmcd_nn, hmcd⟩ := mcdMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨Ctr2, hCtr2_nn, htr2⟩ := trace_grid_rf (I := I) (M := M) 2 g₀ hδ₀
  obtain ⟨Ctr3, hCtr3_nn, htr3⟩ := trace_grid_rf (I := I) (M := M) 3 g₀ hδ₀
  obtain ⟨Ctr4, hCtr4_nn, htr4⟩ := trace_grid_rf (I := I) (M := M) 4 g₀ hδ₀
  set KM2 : ℕ → ℝ := fun i => (Module.finrank ℝ E : ℝ) ^ 2 * Kmcd i with hKM2_def
  set KM3 : ℕ → ℝ := fun i => (Module.finrank ℝ E : ℝ) ^ 3 * Kmcd i with hKM3_def
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hKM2_nn : ∀ i, 0 ≤ KM2 i := fun i =>
    mul_nonneg (pow_nonneg hfr_nn 2) (hKmcd_nn i)
  have hKM3_nn : ∀ i, 0 ≤ KM3 i := fun i =>
    mul_nonneg (pow_nonneg hfr_nn 3) (hKmcd_nn i)
  set Ktail : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 Ctr3 KM2 with hKtail_def
  have hKtail_nn : ∀ i, 0 ≤ Ktail i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hCtr3_nn hKM2_nn i
  set Kmid : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 KM3 Ktail with hKmid_def
  have hKmid_nn : ∀ i, 0 ≤ Kmid i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hKM3_nn hKtail_nn i
  set Ktr4 : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 Ctr4 Kmid with hKtr4_def
  have hKtr4_nn : ∀ i, 0 ≤ Ktr4 i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hCtr4_nn hKmid_nn i
  set Khalf : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 Ctr2 Ktr4 with hKhalf_def
  have hKhalf_nn : ∀ i, 0 ≤ Khalf i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hCtr2_nn hKtr4_nn i
  refine ⟨fun i => (2 : ℝ) ^ 2 * (2 * Khalf i + 2 * Khalf i), fun i => by
    have := hKhalf_nn i; nlinarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0
  have hmcdP : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) 1 Kmcd :=
    hmcd g₁ P htie hδ_le hδ0 hδ hP0
  have htrace : ∀ (p : ℕ) (C : ℕ → ℝ),
      (∀ (σ : Equiv.Perm (Fin (p + 2))) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + i) x
            ((iteratedCovGrad (I := I) g₀ (p + 2) p i
              (reindexedPureTrace (I := I) (M := M) g₀ g₁ p σ)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 1),
            Combinatorics.antidiagonalTupleGrid
              (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) k) →
      ∀ σ : Equiv.Perm (Fin (p + 2)),
        HasMarkedGridWindow (I := I) (M := M) g₀ P
          (reindexedPureTrace (I := I) (M := M) g₀ g₁ p σ) 0 C := by
    intro p C hbd σ
    exact hasMarkedGridWindow_of_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ P _ (fun i y => hbd σ i y)
  have hT2 : ∀ σ : Equiv.Perm (Fin 4),
      HasMarkedGridWindow (I := I) (M := M) g₀ P
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 σ) 0 Ctr2 :=
    htrace 2 Ctr2 (fun σ i x => htr2 g₁ P htie hδ_le hδ0 hδ σ i x)
  have hT3 : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) 0 Ctr3 :=
    htrace 3 Ctr3 (fun σ i x => htr3 g₁ P htie hδ_le hδ0 hδ σ i x) _
  have hT4 : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) 0 Ctr4 :=
    htrace 4 Ctr4 (fun σ i x => htr4 g₁ P htie hδ_le hδ0 hδ σ i x) _
  have hM2 : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)) 1 KM2 := by
    rw [hKM2_def]
    exact hasMarkedGridWindow_slotExtendIter (I := I) (M := M) g₀ P 2 hmcdP
  have hM3 : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)) 1 KM3 := by
    rw [hKM3_def]
    exact hasMarkedGridWindow_slotExtendIter (I := I) (M := M) g₀ P 3 hmcdP
  have hhalf : ∀ σ : Equiv.Perm (Fin 4),
      HasMarkedGridWindow (I := I) (M := M) g₀ P
        (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g₀ σ) 2 Khalf := by
    intro σ
    have htail := hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀))
      hCtr3_nn hKM2_nn hT3 hM2
    have hmid := hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)) _
      hKM3_nn hKtail_nn hM3 htail
    have htr4' := hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) _
      hCtr4_nn hKmid_nn hT4 hmid
    simpa only [lieCorrectionZeroMixedConnectionHalfExpansion, hKhalf_def] using
      hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 σ) _ hCtr2_nn hKtr4_nn (hT2 σ) htr4'
  refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P
    (lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g₀ g₁ g₀) ?_
  exact hasMarkedGridWindow_smul (I := I) (M := M) g₀ P (2 : ℝ)
    (hasMarkedGridWindow_add (I := I) (M := M) g₀ P (hhalf lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
      (hhalf (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)))

theorem amixBackgroundAntidiagonalTupleGridWindow (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 2 2 n
              (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ gB -
                lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          K n * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) := by
  classical
  obtain ⟨Kbg, hKbg_nn, hbg⟩ := mcdBackgroundAntidiagonalTupleGridWindow (I := I) (M := M) g₀ gB
  obtain ⟨Kmcd, hKmcd_nn, hmcd⟩ := mcdMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨Ctr2, hCtr2_nn, htr2⟩ := trace_grid_rf (I := I) (M := M) 2 g₀ hδ₀
  obtain ⟨Ctr3, hCtr3_nn, htr3⟩ := trace_grid_rf (I := I) (M := M) 3 g₀ hδ₀
  obtain ⟨Ctr4, hCtr4_nn, htr4⟩ := trace_grid_rf (I := I) (M := M) 4 g₀ hδ₀
  set KB3 : ℕ → ℝ := fun i => (Module.finrank ℝ E : ℝ) ^ 3 * Kbg i with hKB3_def
  set KM2 : ℕ → ℝ := fun i => (Module.finrank ℝ E : ℝ) ^ 2 * Kmcd i with hKM2_def
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hKB3_nn : ∀ i, 0 ≤ KB3 i := fun i =>
    mul_nonneg (pow_nonneg hfr_nn 3) (hKbg_nn i)
  have hKM2_nn : ∀ i, 0 ≤ KM2 i := fun i =>
    mul_nonneg (pow_nonneg hfr_nn 2) (hKmcd_nn i)
  set Ktail : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 Ctr3 KM2 with hKtail_def
  have hKtail_nn : ∀ i, 0 ≤ Ktail i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hCtr3_nn hKM2_nn i
  set Kmid : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 KB3 Ktail with hKmid_def
  have hKmid_nn : ∀ i, 0 ≤ Kmid i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hKB3_nn hKtail_nn i
  set Ktr4 : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 Ctr4 Kmid with hKtr4_def
  have hKtr4_nn : ∀ i, 0 ≤ Ktr4 i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hCtr4_nn hKmid_nn i
  set Khalf : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 Ctr2 Ktr4 with hKhalf_def
  have hKhalf_nn : ∀ i, 0 ≤ Khalf i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hCtr2_nn hKtr4_nn i
  set Kmark : ℕ → ℝ := fun i => (2 : ℝ) ^ 2 * (2 * Khalf i + 2 * Khalf i)
    with hKmark_def
  have hKmark_nn : ∀ i, 0 ≤ Kmark i := fun i => by
    have := hKhalf_nn i
    simp only [hKmark_def]
    nlinarith
  refine ⟨fun i => Kmark i * markOneConst i,
    fun i => mul_nonneg (hKmark_nn i) (markOneConst_nn i), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 n x
  have hKappa : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (lieCorrectionZeroMixedConnectionBackgroundDifferenceCoefficient (I := I) (M := M) g₀ g₁ gB) 0 Kbg := by
    refine hasMarkedGridWindow_of_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ P _ ?_
    intro i y
    simpa only [lieCorrectionZeroMixedConnectionBackgroundDifferenceCoefficient] using hbg g₁ P htie hP0 i y
  have hmcdP : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) 1 Kmcd :=
    hmcd g₁ P htie hδ_le hδ0 hδ hP0
  have htrace : ∀ (p : ℕ) (C : ℕ → ℝ),
      (∀ (σ : Equiv.Perm (Fin (p + 2))) (i : ℕ) (y : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + i) y
            ((iteratedCovGrad (I := I) g₀ (p + 2) p i
              (reindexedPureTrace (I := I) (M := M) g₀ g₁ p σ)).toSection y) ≤
          C i * ∑ k ∈ Finset.range (i + 1),
            Combinatorics.antidiagonalTupleGrid
              (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) k) →
      ∀ σ : Equiv.Perm (Fin (p + 2)),
        HasMarkedGridWindow (I := I) (M := M) g₀ P
          (reindexedPureTrace (I := I) (M := M) g₀ g₁ p σ) 0 C := by
    intro p C hbd σ
    exact hasMarkedGridWindow_of_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ P _ (fun i y => hbd σ i y)
  have hT2 : ∀ σ : Equiv.Perm (Fin 4),
      HasMarkedGridWindow (I := I) (M := M) g₀ P
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 σ) 0 Ctr2 :=
    htrace 2 Ctr2 (fun σ i y => htr2 g₁ P htie hδ_le hδ0 hδ σ i y)
  have hT3 : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) 0 Ctr3 :=
    htrace 3 Ctr3 (fun σ i y => htr3 g₁ P htie hδ_le hδ0 hδ σ i y) _
  have hT4 : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) 0 Ctr4 :=
    htrace 4 Ctr4 (fun σ i y => htr4 g₁ P htie hδ_le hδ0 hδ σ i y) _
  have hM2 : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)) 1 KM2 := by
    rw [hKM2_def]
    exact hasMarkedGridWindow_slotExtendIter (I := I) (M := M) g₀ P 2 hmcdP
  have hM3 : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3
        (lieCorrectionZeroMixedConnectionBackgroundDifferenceCoefficient (I := I) (M := M) g₀ g₁ gB)) 0 KB3 := by
    rw [hKB3_def]
    exact hasMarkedGridWindow_slotExtendIter (I := I) (M := M) g₀ P 3 hKappa
  have hhalf : ∀ σ : Equiv.Perm (Fin 4),
      HasMarkedGridWindow (I := I) (M := M) g₀ P
        (lieCorrectionZeroMixedConnectionBackgroundDifferenceHalfExpansion (I := I) (M := M) g₀ g₁ gB σ) 1 Khalf := by
    intro σ
    have htail := hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀))
      hCtr3_nn hKM2_nn hT3 hM2
    have hmid := hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3
        (lieCorrectionZeroMixedConnectionBackgroundDifferenceCoefficient (I := I) (M := M) g₀ g₁ gB)) _
      hKB3_nn hKtail_nn hM3 htail
    have htr4' := hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) _
      hCtr4_nn hKmid_nn hT4 hmid
    simpa only [lieCorrectionZeroMixedConnectionBackgroundDifferenceHalfExpansion,
      hKhalf_def] using
      hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 σ) _
      hCtr2_nn hKtr4_nn (hT2 σ) htr4'
  have hmark : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ gB -
        lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g₀) 1 Kmark := by
    refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P
      (lieCorrectionZeroMixedConnection_sub_reference_eq_backgroundDifferenceExpansion (I := I) (M := M) g₀ g₁ gB) ?_
    simpa only [hKmark_def] using
      hasMarkedGridWindow_smul (I := I) (M := M) g₀ P (2 : ℝ)
        (hasMarkedGridWindow_add (I := I) (M := M) g₀ P (hhalf lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
          (hhalf (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)))
  calc
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ gB -
              lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g₀)).toSection x)
        ≤ Kmark n * Combinatorics.markGrid
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) 1 n := hmark n x
    _ ≤ Kmark n * (markOneConst n * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2)) :=
      mul_le_mul_of_nonneg_left
        (mark_one_antidiagonalTupleGridWindow _ (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x) n) (hKmark_nn n)
    _ = (Kmark n * markOneConst n) * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) := by ring

theorem lieCorrectionZeroMixedConnectionJet (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨KX, hKX_nn, hAM⟩ := lieCorrectionZeroMixedConnectionMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨K0', hK0'_nn, hjet⟩ := markedGridWindow_jet_bound (I := I) (M := M) g₀
  obtain ⟨cg, hcg_nn, hcg⟩ := gradCapLin (I := I) (M := M) hDim g₀
  refine ⟨fun i => KX i * K0' i, fun i => KX i * K0' i * cg,
    fun i => mul_nonneg (hKX_nn i) (hK0'_nn i),
    fun i => mul_nonneg (mul_nonneg (hKX_nn i) (hK0'_nn i)) hcg_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 i
  set H3 : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2 with hH3_def
  have hH3_nn : 0 ≤ H3 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  set Λ₁ : ℝ := Real.sqrt (cg * H3) with hΛ₁_def
  have hΛ₁0 : 0 ≤ Λ₁ := Real.sqrt_nonneg _
  have hΛ₁sq : Λ₁ ^ 2 = cg * H3 := Real.sq_sqrt (mul_nonneg hcg_nn hH3_nn)
  have hcap : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2 := by
    intro x
    rw [hΛ₁sq]
    exact hcg P x
  have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      (P.toSection x) ≤ (1 : ℝ) ^ 2 := by
    intro x; rw [one_pow]; exact hP0 x
  have hres := hjet P (Λ₀ := 1) zero_le_one (le_refl _) hΛ₁0 hsup hcap
    (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g₀) hKX_nn
    (hAM g₁ P htie hδ_le hδ0 hδ hP0) i
  refine hres.trans (le_of_eq ?_)
  rw [hΛ₁sq]
  ring

theorem lieCorrectionZeroMixedConnectionJetBackground (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kd, hKd_nn, hdiff⟩ := amixBackgroundAntidiagonalTupleGridWindow (I := I) (M := M) g₀ gB hδ₀
  obtain ⟨Kint, hKint_nn, hint⟩ :=
    antidiagonalTupleGridWindow_bound_to_covariant_jet_bound (I := I) (M := M) g₀ (Λ₀ := (1 : ℝ)) zero_le_one
  obtain ⟨K0d, K2d, hK0d_nn, hK2d_nn, hdiag⟩ :=
    lieCorrectionZeroMixedConnectionJet (I := I) (M := M) hDim g₀ hδ₀
  set KD : ℕ → ℝ := fun i =>
    Kd i * ∑ k ∈ Finset.range (i + 2), Kint k with hKD_def
  have hKD_nn : ∀ i, 0 ≤ KD i := fun i =>
    mul_nonneg (hKd_nn i) (Finset.sum_nonneg (fun k _ => hKint_nn k))
  refine ⟨fun i => 2 * KD i + 2 * K0d i, fun i => 2 * K2d i,
    fun i => add_nonneg (mul_nonneg zero_le_two (hKD_nn i))
      (mul_nonneg zero_le_two (hK0d_nn i)),
    fun i => mul_nonneg zero_le_two (hK2d_nn i), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 i
  let D : SmoothCcTensor g₀ 2 2 :=
    lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ gB -
      lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g₀
  let A : SmoothCcTensor g₀ 2 2 := lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g₀
  set H3 : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2 with hH3_def
  set JS : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hJS_def
  have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      (P.toSection x) ≤ (1 : ℝ) ^ 2 := by
    intro x
    rw [one_pow]
    exact hP0 x
  have hD : ‖iteratedCovGrad (I := I) g₀ 2 2 i D‖ ^ 2 ≤ KD i * JS := by
    have h := hint P hsup 2 2 i 2 D (Kd i) (hKd_nn i)
      (fun x => by
        simpa only [D] using hdiff g₁ P htie hδ_le hδ0 hδ hP0 i x)
    simpa only [hKD_def, hJS_def] using h
  have hA : ‖iteratedCovGrad (I := I) g₀ 2 2 i A‖ ^ 2 ≤
      (K0d i + K2d i * H3) * JS := by
    simpa only [A, hH3_def, hJS_def] using
      hdiag g₁ P htie hδ_le hδ0 hδ hP0 i
  have hfull : lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ gB = D + A := by
    dsimp only [D, A]
    module
  rw [hfull]
  calc
    ‖iteratedCovGrad (I := I) g₀ 2 2 i (D + A)‖ ^ 2
        ≤ 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i D‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i A‖ ^ 2 :=
      lieFirstOrder_normSq_iteratedCovGrad_add_le (I := I) (M := M) g₀ 2 2 i D A
    _ ≤ 2 * (KD i * JS) + 2 * ((K0d i + K2d i * H3) * JS) :=
      add_le_add (mul_le_mul_of_nonneg_left hD zero_le_two)
        (mul_le_mul_of_nonneg_left hA zero_le_two)
    _ = ((2 * KD i + 2 * K0d i) + (2 * K2d i) * H3) * JS := by ring
    _ = ((2 * KD i + 2 * K0d i) + (2 * K2d i) *
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      rw [← hH3_def, ← hJS_def]

theorem lieCorrectionZeroRiemMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkedGridWindow (I := I) (M := M) g₀ P (lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁) 0 K := by
  classical
  obtain ⟨Kcg, hKcg_nn, hcg⟩ := riemannianFiberNormSq_iteratedCovGrad_cometricCastG0_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  choose SPass hSPass_nn hSPass using
    (fun l : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g₀ 2 (4 + l)
      (iteratedCovGrad (I := I) g₀ 2 4 l (lieCorrectionZeroRiemannLift (I := I) g₀)))
  set KC : ℕ → ℝ := fun m => (Module.finrank ℝ E : ℝ) * Kcg m with hKC_def
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hKC_nn : ∀ m, 0 ≤ KC m := fun m => mul_nonneg hfr_nn (hKcg_nn m)
  refine ⟨operatorFieldCompositionGridConstant (E := E) 0 0 KC SPass,
    fun i => operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hKC_nn hSPass_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  have hLive : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁) 0 KC := by
    refine hasMarkedGridWindow_of_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ P _ (fun m y => ?_)
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_reindexedCometricDoubleTrace_le (I := I) (M := M) g₀ g₁ m y) ?_
    rw [hKC_def, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hcg g₁ P htie hδ_le hδ0 hδ m y) hfr_nn
  have hPass : HasMarkedGridWindow (I := I) (M := M) g₀ P (lieCorrectionZeroRiemannLift (I := I) g₀) 0 SPass :=
    hasMarkedGridWindow_of_pointwise_bound (I := I) (M := M) g₀ P _ hSPass_nn (fun l y => hSPass l y)
  refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P (lieCorrectionZeroRiemann_eq_ccOperatorFieldComp (I := I) (M := M) g₀ g₁) ?_
  refine hasMarkedGridWindow_neg (I := I) (M := M) g₀ P ?_
  simpa using hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hKC_nn hSPass_nn hLive hPass

theorem lieCorrectionZeroRiemJet (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K0 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
          K0 i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨KR, hKR_nn, hRiem⟩ := lieCorrectionZeroRiemMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨K0', hK0'_nn, hjet⟩ := markedGridWindow_zeroOrder_jet_bound (I := I) (M := M) g₀
  refine ⟨fun i => KR i * K0' i,
    fun i => mul_nonneg (hKR_nn i) (hK0'_nn i), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 i
  exact hjet P hP0 (lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁) hKR_nn
    (hRiem g₁ P htie hδ_le hδ0 hδ) i

end DifferentialGeometry.Integral.Connection

end
