import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorFieldJetRadiusFree
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroCoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.GridWindow.ArmJets

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open LieCorrectionZeroCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private def insOmegaDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 1 :=
  deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀ -
    deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg

private def insAlphaDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀ -
    deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg

private theorem omegaDiffAntidiagonalTupleGridWindow
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 1 i
              (insOmegaDiff (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          K i * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) := by
  classical
  obtain ⟨Kcg, hKcg_nn, hcg⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_cometricCastG0_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  let Wfix : SmoothCcTensor g₀ 0 3 := metricLoweredConnectionDifference (I := I) (M := M) g₀ g_bg g₀
  choose S hS_nn hS using fun i : ℕ =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g₀ 0 (3 + i)
      (iteratedCovGrad (I := I) g₀ 0 3 i Wfix)
  refine ⟨operatorFieldCompositionGridConstant (E := E) 0 0 Kcg S,
    fun i => operatorFieldCompositionGridConstant_nonneg (u := 0) (v := 0) hKcg_nn hS_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ i x
  have hW : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) y
          ((iteratedCovGrad (I := I) g₀ 0 3 l Wfix).toSection y) ≤
        S l * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (l + 1) := by
    intro l y
    refine (hS l y).trans ?_
    exact le_mul_of_one_le_right (hS_nn l)
      (Combinatorics.one_le_antidiagonalTupleGridWindow _
        (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y) (by omega))
  have hfold := operatorFieldComposition_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ 0 0
    (cometricCastG0 (I := I) g₀ g₁) Wfix P hKcg_nn hS_nn
    (fun l y => hcg g₁ P htie hδ_le hδ0 hδ l y) hW i x
  rw [insOmegaDiff, deTurckVectorFieldCovector_base_sub (I := I) (M := M) g₀ g₁ g_bg,
    show operatorFieldApply (I := I) (M := M) g₀ 3 1
        (cometricCastG0 (I := I) g₀ g₁)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g_bg g₀) =
      operatorFieldApply (I := I) (M := M) g₀ 3 1
        (cometricCastG0 (I := I) g₀ g₁)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g_bg g₀) from rfl,
    ← operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 3 1]
  simpa only [Wfix, Nat.add_zero] using hfold

private theorem alphaDiffAntidiagonalTupleGridWindow
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i
              (insAlphaDiff (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          K i * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 2) := by
  classical
  obtain ⟨Kcd, hKcd_nn, hcd⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kω, hKω_nn, hω⟩ := omegaDiffAntidiagonalTupleGridWindow (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨operatorFieldCompositionGridConstant (E := E) 1 0 Kcd Kω,
    fun i => operatorFieldCompositionGridConstant_nonneg (u := 1) (v := 0) hKcd_nn hKω_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ i x
  have hCA : ∀ (j : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) y
          ((iteratedCovGrad (I := I) g₀ 1 2 j
            (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)).toSection y) ≤
        Kcd j * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (j + 2) := by
    intro j y
    rw [riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceRaisedEndomorphism_eq_connectionDifferenceSection (I := I) (M := M) g₀ g₁ j y]
    exact hcd g₁ P htie hδ_le hδ0 hδ j y
  have hfold := operatorFieldComposition_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ 1 0
    (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
    (insOmegaDiff (I := I) (M := M) g₀ g₁ g_bg) P
    hKcd_nn hKω_nn hCA (fun l y => hω g₁ P htie hδ_le hδ0 hδ l y) i x
  have hform : insAlphaDiff (I := I) (M := M) g₀ g₁ g_bg =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 1 2
        (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
        (insOmegaDiff (I := I) (M := M) g₀ g₁ g_bg) := by
    rw [insAlphaDiff, insOmegaDiff, deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference, deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference,
      show operatorFieldApply (I := I) (M := M) g₀ 1 2
          (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀) =
        operatorFieldApply (I := I) (M := M) g₀ 1 2
          (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀) from rfl,
      show operatorFieldApply (I := I) (M := M) g₀ 1 2
          (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) =
        operatorFieldApply (I := I) (M := M) g₀ 1 2
          (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) from rfl,
      ← operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 1 2,
      ← operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 1 2,
      ccOperatorFieldComp_sub_right]
  rw [hform]
  exact hfold

theorem lieCorrectionZeroInsDiffAntidiagonalTupleGridWindow
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg -
                lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          K i * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 2) := by
  classical
  obtain ⟨Kα, hKα_nn, hα⟩ := alphaDiffAntidiagonalTupleGridWindow (I := I) (M := M) g₀ g_bg hδ₀
  let fr : ℝ := Module.finrank ℝ E
  refine ⟨fun i => 4 * fr * Kα i, fun i => by
    exact mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) (hKα_nn i), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ i x
  let N := endoDiffSection (I := I) (M := M) g₀ g₁ g_bg
  let AD := insAlphaDiff (I := I) (M := M) g₀ g₁ g_bg
  have hraise_sub :
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 AD =
        cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀) -
          cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro y
    apply tensorRSSpace_ext 1 1 y
    intro om
    dsimp only [AD]
    rw [insAlphaDiff, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
      Pi.sub_apply, sub_apply]
    simp only [cometricRaiseSlot0Field_toSection]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      sub_apply]
    rfl
  have hslot : endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 N =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 AD := by
    dsimp only [N]
    change slotInsertEndoCc (I := I) (M := M) g₀ 0
        (connectionDifferenceDeTurckVectorFieldSection (I := I) (M := M) g₀ g₁ g₀ -
          connectionDifferenceDeTurckVectorFieldSection (I := I) (M := M) g₀ g₁ g_bg) = _
    rw [slotInsertEndoCc_sub,
      connectionDifferenceDeTurckVectorFieldInsert_eq_cometricRaise, connectionDifferenceDeTurckVectorFieldInsert_eq_cometricRaise,
      hraise_sub]
  have hslot_bound :
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 N)).toSection x) ≤
        Kα i * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 2) := by
    rw [hslot, riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq
      (I := I) (M := M) g₀ 0 AD i x]
    exact hα g₁ P htie hδ_le hδ0 hδ i x
  let A := endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 N
  let B := reindexCoeffGen (I := I) (M := M) g₀ 2 2
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2
      (Equiv.swap (0 : Fin 2) 1) A) (Equiv.swap (0 : Fin 2) 1)
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i A).toSection x) ≤
        fr * (Kα i * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 2)) := by
    refine (riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
      (I := I) (M := M) g₀ 1 N i x).trans ?_
    rw [pow_one]
    exact mul_le_mul_of_nonneg_left hslot_bound (Nat.cast_nonneg _)
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i B).toSection x) ≤
        fr * (Kα i * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 2)) := by
    dsimp only [B]
    rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongr_both_eq
      (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
        (Equiv.swap (0 : Fin 2) 1) A i x]
    exact hA
  rw [lieCorrectionZeroInsDiff_eq (I := I) (M := M) g₀ g₁ g_bg]
  change riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i (A + B)).toSection x) ≤ _
  rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply]
  refine (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _).trans ?_
  dsimp only [fr] at hA hB ⊢
  linarith only [hA, hB]

end DifferentialGeometry.Integral.Connection

end
