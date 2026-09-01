import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.GridWindow.Marked
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.GridWindow.SelfLowCap

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [SigmaCompactSpace M] in
theorem connectionDifferenceMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kcd : ℕ → ℝ, (∀ j, 0 ≤ Kcd j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkedGridWindow (I := I) (M := M) g₀ P
          (connectionDifferenceSection (I := I) g₁ g₀) 1 Kcd := by
  classical
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hts⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_topOrderSeparated_le (I := I) (M := M) g₀ hδ₀
  refine ⟨fun j => 2 * Ktop + (2 * Kc j) * j, fun j => by
    have := hKc_nn j; positivity, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  refine hasMarkedGridWindow_of_top_order_decomposition (I := I) (M := M) g₀ P _ (Ktop := 2 * Ktop) (by linarith)
    (Kc := fun j => 2 * Kc j) (fun j => by have := hKc_nn j; linarith) ?_
  intro j x
  set Hd : SmoothCcTensor g₀ 1 (2 + j) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
      (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) with hHd_def
  obtain ⟨h1, h2⟩ := hts g₁ P htie hδ_le hδ0 hδ j x
  have hsplit_eq :
      (iteratedCovGrad (I := I) g₀ 1 2 j (connectionDifferenceSection (I := I) g₁ g₀)).toSection x =
        Hd.toSection x +
          (iteratedCovGrad (I := I) g₀ 1 2 j (connectionDifferenceSection (I := I) g₁ g₀) -
            Hd).toSection x := by
    simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]; abel
  rw [hsplit_eq]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (2 + j) x
    (Hd.toSection x) _) ?_
  have h1' : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x (Hd.toSection x) ≤
      Ktop * covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (j + 1) := h1
  have h2' : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 2 j (connectionDifferenceSection (I := I) g₁ g₀) -
          Hd).toSection x) ≤
      Kc j * ∑ k ∈ Finset.range j,
        covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (j - k) *
          Combinatorics.antidiagonalTupleGrid
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (k + 1) := h2
  linarith [h1', h2']

theorem exists_ricciConnectionDifferenceQuadraticArm_markWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkedGridWindow (I := I) (M := M) g₀ P
          (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g₀ g₁) 2 K := by
  classical
  obtain ⟨Kcd, hKcd_nn, hcd⟩ := connectionDifferenceMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kft, hKft_nn, hft⟩ := fourTrAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀
  choose S4 hS4_nn hS4 using
    (fun (ρ : Equiv.Perm (Fin 4)) (i : ℕ) =>
      exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (4 + i)
        (iteratedCovGrad (I := I) g₀ 4 4 i (permCoeff (I := I) (M := M) g₀ ρ)))
  choose S3 hS3_nn hS3 using
    (fun (ρ : Equiv.Perm (Fin 3)) (i : ℕ) =>
      exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (3 + i)
        (iteratedCovGrad (I := I) g₀ 3 3 i (permCoeff (I := I) (M := M) g₀ ρ)))
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set SP4 : ℕ → ℝ := fun i => ∑ ρ : Equiv.Perm (Fin 4), S4 ρ i with hSP4_def
  set SP3 : ℕ → ℝ := fun i => ∑ ρ : Equiv.Perm (Fin 3), S3 ρ i with hSP3_def
  have hSP4_nn : ∀ i, 0 ≤ SP4 i := fun i => Finset.sum_nonneg (fun ρ _ => hS4_nn ρ i)
  have hSP3_nn : ∀ i, 0 ≤ SP3 i := fun i => Finset.sum_nonneg (fun ρ _ => hS3_nn ρ i)
  set KInn : ℕ → ℝ := fun i => fr * Kcd i with hKInn_def
  have hKInn_nn : ∀ i, 0 ≤ KInn i := fun i => mul_nonneg hfr_nn (hKcd_nn i)
  set KIns : ℕ → ℝ := fun i => fr * (fr * Kcd i) with hKIns_def
  have hKIns_nn : ∀ i, 0 ≤ KIns i := fun i =>
    mul_nonneg hfr_nn (mul_nonneg hfr_nn (hKcd_nn i))
  set KIC : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 SP3 KInn with hKIC_def
  have hKIC_nn : ∀ i, 0 ≤ KIC i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hSP3_nn hKInn_nn i
  set KMA : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 KIns KIC with hKMA_def
  have hKMA_nn : ∀ i, 0 ≤ KMA i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hKIns_nn hKIC_nn i
  set KMB : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 KIns KInn with hKMB_def
  have hKMB_nn : ∀ i, 0 ≤ KMB i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hKIns_nn hKInn_nn i
  set KA : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 SP4 KMA with hKA_def
  have hKA_nn : ∀ i, 0 ≤ KA i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hSP4_nn hKMA_nn i
  set KB : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 SP4 KMB with hKB_def
  have hKB_nn : ∀ i, 0 ≤ KB i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hSP4_nn hKMB_nn i
  set KQ : ℕ → ℝ := fun i => KA i + KB i with hKQ_def
  have hKQ_nn : ∀ i, 0 ≤ KQ i := fun i => by
    have := hKA_nn i; have := hKB_nn i; simp only [hKQ_def]; linarith
  have hK94_nn : ∀ i, 0 ≤ 94 * KQ i := fun i => by have := hKQ_nn i; linarith
  refine ⟨operatorFieldCompositionGridConstant (E := E) 0 0 Kft (fun i => 94 * KQ i),
    fun i => operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hKft_nn hK94_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  have hcdP := hcd g₁ P htie hδ_le hδ0 hδ
  have hP4 : ∀ ρ : Equiv.Perm (Fin 4),
      HasMarkedGridWindow (I := I) (M := M) g₀ P (permCoeff (I := I) (M := M) g₀ ρ) 0 SP4 := by
    intro ρ
    refine hasMarkedGridWindow_mono (I := I) (M := M) g₀ P (fun i => ?_)
      (hasMarkedGridWindow_of_pointwise_bound (I := I) (M := M) g₀ P _ (fun i => hS4_nn ρ i) (fun i x => hS4 ρ i x))
    exact Finset.single_le_sum (f := fun r => S4 r i)
      (fun r _ => hS4_nn r i) (Finset.mem_univ ρ)
  have hP3 : ∀ ρ : Equiv.Perm (Fin 3),
      HasMarkedGridWindow (I := I) (M := M) g₀ P (permCoeff (I := I) (M := M) g₀ ρ) 0 SP3 := by
    intro ρ
    refine hasMarkedGridWindow_mono (I := I) (M := M) g₀ P (fun i => ?_)
      (hasMarkedGridWindow_of_pointwise_bound (I := I) (M := M) g₀ P _ (fun i => hS3_nn ρ i) (fun i x => hS3 ρ i x))
    exact Finset.single_le_sum (f := fun r => S3 r i)
      (fun r _ => hS3_nn r i) (Finset.mem_univ ρ)
  have hInn : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (connectionDifferenceContrInsertionInnerField (I := I) g₀ g₁) 1 KInn := by
    refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P
      (connectionDifferenceContrInsertionInnerField_eq_reindex_slotExtend (I := I) (M := M) g₀ g₁) ?_
    exact hasMarkedGridWindow_reindex (I := I) (M := M) g₀ P innerCoreInPerm10
      (hasMarkedGridWindow_slotExtend (I := I) (M := M) g₀ P hcdP)
  have hIns : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (connectionDifferenceContravariantInsertionField (I := I) g₀ g₁) 1 KIns := by
    refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P
      (connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two (I := I) (M := M) g₀ g₁) ?_
    exact hasMarkedGridWindow_reindex (I := I) (M := M) g₀ P coreInPerm201
      (hasMarkedGridWindow_slotExtend (I := I) (M := M) g₀ P (hasMarkedGridWindow_slotExtend (I := I) (M := M) g₀ P hcdP))
  have hShapeA : ∀ (ρ : Equiv.Perm (Fin 4)) (ρ' : Equiv.Perm (Fin 3)),
      HasMarkedGridWindow (I := I) (M := M) g₀ P
        (aaCoreP (I := I) (M := M) g₀ g₁ ρ ρ') 2 KA := by
    intro ρ ρ'
    have hinner : HasMarkedGridWindow (I := I) (M := M) g₀ P
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (permCoeff (I := I) (M := M) g₀ ρ')
          (connectionDifferenceContrInsertionInnerField (I := I) g₀ g₁)) 1 KIC := by
      simpa using hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hSP3_nn hKInn_nn (hP3 ρ') hInn
    have hmid : HasMarkedGridWindow (I := I) (M := M) g₀ P
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g₀ g₁)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (permCoeff (I := I) (M := M) g₀ ρ')
            (connectionDifferenceContrInsertionInnerField (I := I) g₀ g₁))) 2 KMA := by
      simpa using hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hKIns_nn hKIC_nn hIns hinner
    simpa only [aaCoreP, hKA_def] using
      hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _
        hSP4_nn hKMA_nn (hP4 ρ) hmid
  have hShapeB : ∀ ρ : Equiv.Perm (Fin 4),
      HasMarkedGridWindow (I := I) (M := M) g₀ P (aaCore (I := I) (M := M) g₀ g₁ ρ) 2 KB := by
    intro ρ
    have hmid : HasMarkedGridWindow (I := I) (M := M) g₀ P
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g₀ g₁)
          (connectionDifferenceContrInsertionInnerField (I := I) g₀ g₁)) 2 KMB := by
      simpa using hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hKIns_nn hKInn_nn hIns hInn
    simpa only [aaCore, hKB_def] using
      hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _
        hSP4_nn hKMB_nn (hP4 ρ) hmid
  have hA' : ∀ (ρ : Equiv.Perm (Fin 4)) (ρ' : Equiv.Perm (Fin 3)),
      HasMarkedGridWindow (I := I) (M := M) g₀ P (aaCoreP (I := I) (M := M) g₀ g₁ ρ ρ') 2 KQ :=
    fun ρ ρ' => hasMarkedGridWindow_mono (I := I) (M := M) g₀ P
      (fun i => by have := hKB_nn i; simp only [hKQ_def]; linarith) (hShapeA ρ ρ')
  have hB' : ∀ ρ : Equiv.Perm (Fin 4),
      HasMarkedGridWindow (I := I) (M := M) g₀ P (aaCore (I := I) (M := M) g₀ g₁ ρ) 2 KQ :=
    fun ρ => hasMarkedGridWindow_mono (I := I) (M := M) g₀ P
      (fun i => by have := hKA_nn i; simp only [hKQ_def]; linarith) (hShapeB ρ)
  have hKer : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g₀ g₁) 2 (fun i => 94 * KQ i) := by
    refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P
      (aaKerSplit (I := I) (M := M) g₀ g₁) ?_
    refine hasMarkedGridWindow_mono (I := I) (M := M) g₀ P ?_
      (hasMarkedGridWindow_add (I := I) (M := M) g₀ P
        (hasMarkedGridWindow_add (I := I) (M := M) g₀ P
          (hasMarkedGridWindow_add (I := I) (M := M) g₀ P
            (hasMarkedGridWindow_add (I := I) (M := M) g₀ P
              (hasMarkedGridWindow_add (I := I) (M := M) g₀ P (hA' _ _)
                (hasMarkedGridWindow_reindex (I := I) (M := M) g₀ P innerCoreInPerm10 (hA' _ _)))
              (hA' _ _))
            (hasMarkedGridWindow_reindex (I := I) (M := M) g₀ P innerCoreInPerm10 (hB' _)))
          (hB' _))
        (hasMarkedGridWindow_reindex (I := I) (M := M) g₀ P innerCoreInPerm10 (hA' _ _)))
    intro i
    exact le_of_eq (by ring)
  have hFT : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (ricciCometricFourTraceCastG0 (I := I) g₀ g₁) 0 Kft :=
    hasMarkedGridWindow_of_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ P _ (fun n y => hft g₁ P htie hδ_le hδ0 hδ n y)
  simpa only [ricciConnectionDifferenceQuadraticArm] using
    hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _
      hKft_nn hK94_nn hFT hKer

theorem exists_ricciConnectionDifferenceQuadraticArm_covariantJetNormSq_bound (hDim : Module.finrank ℝ E = 3)
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
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨KA, hKA_nn, hAA⟩ := exists_ricciConnectionDifferenceQuadraticArm_markWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨K0', hK0'_nn, hjet⟩ := markedGridWindow_jet_bound (I := I) (M := M) g₀
  obtain ⟨cg, hcg_nn, hcg⟩ := gradCapLin (I := I) (M := M) hDim g₀
  refine ⟨fun i => KA i * K0' i, fun i => KA i * K0' i * cg,
    fun i => mul_nonneg (hKA_nn i) (hK0'_nn i),
    fun i => mul_nonneg (mul_nonneg (hKA_nn i) (hK0'_nn i)) hcg_nn, ?_⟩
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
    (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g₀ g₁) hKA_nn
    (hAA g₁ P htie hδ_le hδ0 hδ) i
  refine hres.trans (le_of_eq ?_)
  rw [hΛ₁sq]
  ring

end DifferentialGeometry.Integral.Connection

end
