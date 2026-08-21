import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroCoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroCoefficientDecomposition
import DifferentialGeometry.Analysis.Estimates.ProductBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorFieldEndomorphismInsertionTopOrderSeparation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorFieldJetRadiusFree
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroTraceRadiusFreeBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1H2OperatorFieldComposition

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
  (deTurckLieEndoArmField deTurckLieEndoArmField_toSection deTurckLieCovariantDerivativeInsertionFib
    reindexCoeffGen reindexCoeffGen_toSection reindexCoeffFibGen reindexCoeffFibGen_apply
    iteratedCovGrad_reindexCoeffGen norm_reindexCoeffGen_eq
    domDomCongrFibRank domDomCongrFibRank_apply tensor0SProdKappaFib
    metricConnectionDifferenceLoweredFib metricConnectionDifferenceLoweredFib_contMDiff
    symmS cometricRaiseSlot0Field unitModel unitTensor covGrad covGrad_zero
    metricConnectionDifferenceLoweredFib_toModel smoothCcTensor_ext_of_unitModel)
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open LieCorrectionZeroCore
open TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem sq_le_two_add (t u v c1 c2 : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htri : t ≤ u + v) (h1 : u ^ 2 ≤ c1) (h2 : v ^ 2 ≤ c2) : t ^ 2 ≤ 2 * (c1 + c2) := by
  have huv : 0 ≤ u + v := by linarith
  nlinarith only [mul_le_mul htri htri ht huv, sq_nonneg (u - v), h1, h2, hu, hv]

private lemma lieCorrectionZeroBase_perOrder_rf
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Flow : ℕ → ℝ, (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ), i ≤ a →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤
          Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
          Flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kb_top, hKb_top_nn, Kb_flow, hKb_flow_nn, hwalpha⟩ :=
    deTurckVectorFieldCovariantDerivativeLowered_iteratedCovGrad_norm_sq_topOrderSeparated (I := I) (M := M) g₀ g₀ a hδ₀ hΛ₀0
  have h4fr_nn : (0 : ℝ) ≤ 4 * (Module.finrank ℝ E : ℝ) := by positivity
  refine ⟨4 * (Module.finrank ℝ E : ℝ) * Kb_top, mul_nonneg h4fr_nn hKb_top_nn,
    fun i => 4 * (Module.finrank ℝ E : ℝ) * Kb_flow i,
    fun i => mul_nonneg h4fr_nn (hKb_flow_nn i), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i hi
  have hbase : ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖ =
      ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCovariantDerivativeInsertionField (I := I) g₀ g₁ g₀)‖ := by
    rw [lieCorrectionZeroInsertion_base_eq_neg_covariantDerivativeInsertion (I := I) (M := M) g₀ g₁, iteratedCovGrad_neg, norm_neg]
  have hdlb := normSq_iteratedCovGrad_deTurckLieCovariantDerivativeInsertionField_le (I := I) (M := M) g₀ g₁ g₀ i
  rw [norm_iteratedCovGrad_deTurckVectorFieldCovariantDerivativeEndomorphismInsert_eq_deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g₀ i] at hdlb
  have hwa := hwalpha g₁ P htie hδ_le hδ0 hδ hsup i hi
  calc ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2
      = ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCovariantDerivativeInsertionField (I := I) g₀ g₁ g₀)‖ ^ 2 := by
        rw [hbase]
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) *
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 := hdlb
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) *
          (Kb_top * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
            Kb_flow i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hwa h4fr_nn
    _ = 4 * (Module.finrank ℝ E : ℝ) * Kb_top *
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
          4 * (Module.finrank ℝ E : ℝ) * Kb_flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring

private lemma lieCorrectionZeroDiff_perOrder_rf
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Flow : ℕ → ℝ, (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg -
              lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤
          Flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨FB0, hFB0_nn, hB0⟩ :=
    deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference_iteratedCovGrad_norm_sq_le (I := I) (M := M) g₀ g₀ hδ₀ hΛ₀0
  obtain ⟨FBb, hFBb_nn, hBb⟩ :=
    deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference_iteratedCovGrad_norm_sq_le (I := I) (M := M) g₀ g_bg hδ₀ hΛ₀0
  have h4fr_nn : (0 : ℝ) ≤ 4 * (Module.finrank ℝ E : ℝ) := by positivity
  refine ⟨fun i => 4 * (Module.finrank ℝ E : ℝ) * (2 * FB0 i + 2 * FBb i),
    fun i => mul_nonneg h4fr_nn (by have := hFB0_nn i; have := hFBb_nn i; linarith), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i
  have hsplit : slotInsertEndoCc (I := I) (M := M) g₀ 0
      (connectionDifferenceDeTurckVectorFieldSection (I := I) (M := M) g₀ g₁ g₀ -
        connectionDifferenceDeTurckVectorFieldSection (I := I) (M := M) g₀ g₁ g_bg) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀) -
        cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) := by
    rw [slotInsertEndoCc_sub (I := I) (M := M) g₀ 0
        (connectionDifferenceDeTurckVectorFieldSection (I := I) (M := M) g₀ g₁ g₀)
        (connectionDifferenceDeTurckVectorFieldSection (I := I) (M := M) g₀ g₁ g_bg),
      connectionDifferenceDeTurckVectorFieldInsert_eq_cometricRaise (I := I) (M := M) g₀ g₁ g₀,
      connectionDifferenceDeTurckVectorFieldInsert_eq_cometricRaise (I := I) (M := M) g₀ g₁ g_bg]
  have hEDS : slotInsertEndoCc (I := I) (M := M) g₀ 0
      (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀) -
        cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) :=
    hsplit
  have e0 : ‖iteratedCovGrad (I := I) g₀ 1 1 i
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀))‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀)‖ :=
    norm_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
      (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀) i
  have eb : ‖iteratedCovGrad (I := I) g₀ 1 1 i
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg))‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ :=
    norm_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
      (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) i
  have htri : ‖iteratedCovGrad (I := I) g₀ 1 1 i
      (slotInsertEndoCc (I := I) (M := M) g₀ 0
        (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀)‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 2 i (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ := by
    rw [hEDS, iteratedCovGrad_sub]
    refine le_trans (norm_sub_le _ _) ?_
    rw [e0, eb]
  have h0 := hB0 g₁ P htie hδ_le hδ0 hδ hsup i
  have hb := hBb g₁ P htie hδ_le hδ0 hδ hsup i
  have hsq : ‖iteratedCovGrad (I := I) g₀ 1 1 i
      (slotInsertEndoCc (I := I) (M := M) g₀ 0
        (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 ≤
      2 * (FB0 i * (1 + ∑ j ∈ Finset.range (i + 3),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
        FBb i * (1 + ∑ j ∈ Finset.range (i + 3),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
    sq_le_two_add _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) htri h0 hb
  have hred := normSq_iteratedCovGrad_lieCorrectionZeroInsertionDiff_le (I := I) (M := M) g₀ g₁ g_bg i
  refine le_trans hred ?_
  calc 4 * (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2
      ≤ 4 * (Module.finrank ℝ E : ℝ) *
          (2 * (FB0 i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
            FBb i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left hsq h4fr_nn
    _ = 4 * (Module.finrank ℝ E : ℝ) * (2 * FB0 i + 2 * FBb i) *
          (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring

private lemma lieCorrectionZeroRiem_perOrder_rf
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Flow : ℕ → ℝ, (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ), i ≤ a + 1 →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
          Flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Λ, Fcg, hΛ_nn, hFcg_nn, hcom⟩ :=
    cometricCastG0_order0sup_jetL2_radiusFree (I := I) (M := M) g₀ a hδ₀ hΛ₀0
  obtain ⟨KP, hKP_nn, hKP⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 2 4 (lieCorrectionZeroRiemannLift (I := I) g₀)
  choose Cint hCint_nn hCint using
    (fun k : ℕ => exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 4 2 2 4 k)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set NPass : ℕ → ℝ := fun i => ∑ l ∈ Finset.range (i + 1),
    ‖iteratedCovGrad (I := I) g₀ 2 4 l (lieCorrectionZeroRiemannLift (I := I) g₀)‖ ^ 2 with hNPass
  have hNPass_nn : ∀ i, 0 ≤ NPass i := fun i =>
    Finset.sum_nonneg (fun l _ => sq_nonneg _)
  refine ⟨fun i => operatorFieldApplicationGdiag (E := E) i *
    (Cint i * (KP * (fr * Fcg i) + fr * Λ ^ 2 * NPass i)), fun i => ?_, ?_⟩
  · exact mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
      (mul_nonneg (hCint_nn i)
        (add_nonneg (mul_nonneg hKP_nn (mul_nonneg hfr_nn (hFcg_nn i)))
          (mul_nonneg (mul_nonneg hfr_nn (sq_nonneg Λ)) (hNPass_nn i))))
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i hi
  obtain ⟨hsup0, hjet⟩ := hcom g₁ P htie hδ_le hδ0 hδ hsup
  set W1 : ℝ := ∑ j ∈ Finset.range (i + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hW1
  set W3 : ℝ := ∑ j ∈ Finset.range (i + 3),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hW3
  have hW1_nn : 0 ≤ W1 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hW3_nn : 0 ≤ W3 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hW13 : W1 ≤ W3 := by
    rw [hW1, hW3]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => sq_nonneg _)
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hLsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁).toSection x) ≤
      Real.sqrt (fr * Λ ^ 2) ^ 2 := by
    intro x
    have h := riemannianFiberNormSq_iteratedCovGrad_reindexedCometricDoubleTrace_le (I := I) (M := M) g₀ g₁ 0 x
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
    rw [Real.sq_sqrt (mul_nonneg hfr_nn (sq_nonneg Λ))]
    exact le_trans h (mul_le_mul_of_nonneg_left (hsup0 x) hfr_nn)
  have hPsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 4 x
      ((lieCorrectionZeroRiemannLift (I := I) g₀).toSection x) ≤ Real.sqrt KP ^ 2 := by
    intro x
    rw [Real.sq_sqrt hKP_nn]
    exact hKP x
  obtain ⟨hgrid_int, hgrid_bd⟩ := hCint i
    (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁) (lieCorrectionZeroRiemannLift (I := I) g₀)
    (Real.sqrt (fr * Λ ^ 2)) (Real.sqrt KP)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hLsup hPsup
  have hLsum : ∑ m ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 4 2 m (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
      fr * (Fcg i * (1 + W1)) := by
    calc ∑ m ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 m (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)‖ ^ 2
        ≤ ∑ m ∈ Finset.range (i + 1), fr *
            ‖iteratedCovGrad (I := I) g₀ 3 1 m (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2 :=
          Finset.sum_le_sum (fun m _ => norm_iteratedCovGrad_reindexedCometricDoubleTrace_sq_le (I := I) (M := M) g₀ g₁ m)
      _ = fr * ∑ m ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 1 m (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ fr * (Fcg i * (1 + W1)) := by
          refine mul_le_mul_of_nonneg_left ?_ hfr_nn
          simpa [hW1] using hjet i hi
  have hnorm : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁) (lieCorrectionZeroRiemannLift (I := I) g₀))‖ ^ 2 ≤
      operatorFieldApplicationGdiag (E := E) i *
        (Cint i * (Real.sqrt KP ^ 2 * ∑ m ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 m (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)‖ ^ 2
          + Real.sqrt (fr * Λ ^ 2) ^ 2 * ∑ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 4 l (lieCorrectionZeroRiemannLift (I := I) g₀)‖ ^ 2)) := by
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁) (lieCorrectionZeroRiemannLift (I := I) g₀)))
      _ (hgrid_int.const_mul (operatorFieldApplicationGdiag (E := E) i))
      (fun x => riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ i 2 4 2
        (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁) (lieCorrectionZeroRiemannLift (I := I) g₀) x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hgrid_bd (operatorFieldApplicationGdiag_nonneg (E := E) i)
  rw [lieCorrectionZeroRiemann_eq_ccOperatorFieldComp (I := I) (M := M) g₀ g₁, iteratedCovGrad_neg, norm_neg]
  have hKPsq : Real.sqrt KP ^ 2 = KP := Real.sq_sqrt hKP_nn
  have hΛsq : Real.sqrt (fr * Λ ^ 2) ^ 2 = fr * Λ ^ 2 :=
    Real.sq_sqrt (mul_nonneg hfr_nn (sq_nonneg Λ))
  rw [hKPsq, hΛsq] at hnorm
  have hpad : Cint i * (KP * ∑ m ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 m (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)‖ ^ 2
      + fr * Λ ^ 2 * NPass i) ≤
      Cint i * ((KP * (fr * Fcg i) + fr * Λ ^ 2 * NPass i) * (1 + W3)) := by
    refine mul_le_mul_of_nonneg_left ?_ (hCint_nn i)
    have h1 : KP * ∑ m ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 m (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
        KP * (fr * Fcg i) * (1 + W3) := by
      calc KP * ∑ m ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 m (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)‖ ^ 2
          ≤ KP * (fr * (Fcg i * (1 + W1))) := mul_le_mul_of_nonneg_left hLsum hKP_nn
        _ = KP * (fr * Fcg i) * (1 + W1) := by ring
        _ ≤ KP * (fr * Fcg i) * (1 + W3) := by
            refine mul_le_mul_of_nonneg_left (by linarith) ?_
            exact mul_nonneg hKP_nn (mul_nonneg hfr_nn (hFcg_nn i))
    have h2 : fr * Λ ^ 2 * NPass i ≤ fr * Λ ^ 2 * NPass i * (1 + W3) :=
      le_mul_of_one_le_right
        (mul_nonneg (mul_nonneg hfr_nn (sq_nonneg Λ)) (hNPass_nn i)) (by linarith)
    calc KP * ∑ m ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 m (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)‖ ^ 2
        + fr * Λ ^ 2 * NPass i
        ≤ KP * (fr * Fcg i) * (1 + W3) + fr * Λ ^ 2 * NPass i * (1 + W3) := add_le_add h1 h2
      _ = (KP * (fr * Fcg i) + fr * Λ ^ 2 * NPass i) * (1 + W3) := by ring
  calc ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁) (lieCorrectionZeroRiemannLift (I := I) g₀))‖ ^ 2
      ≤ operatorFieldApplicationGdiag (E := E) i *
          (Cint i * (KP * ∑ m ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 m (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)‖ ^ 2
            + fr * Λ ^ 2 * NPass i)) := hnorm
    _ ≤ operatorFieldApplicationGdiag (E := E) i *
          (Cint i * ((KP * (fr * Fcg i) + fr * Λ ^ 2 * NPass i) * (1 + W3))) :=
        mul_le_mul_of_nonneg_left hpad (operatorFieldApplicationGdiag_nonneg (E := E) i)
    _ = operatorFieldApplicationGdiag (E := E) i *
          (Cint i * (KP * (fr * Fcg i) + fr * Λ ^ 2 * NPass i)) * (1 + W3) := by ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem b4_iteratedCovGrad_zero (g : SmoothRiemannianMetric I M) (r s j : ℕ) :
    iteratedCovGrad (I := I) g r s j (0 : SmoothCcTensor g r s) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iteratedCovGrad_succ, ih]
      exact covGrad_zero (I := I) (M := M) (g := g) (r := r) (s := s + j)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem b4_iteratedCovGrad_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma b4_riemannianFiberNormSq_smul (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (x : M) (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

private lemma b4_trace_succ (g : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 5 (3 + (i + 1)) x
        ((iteratedCovGrad (I := I) g 5 3 (i + 1)
          (cometricDoubleTraceField (I := I) g 3)).toSection x) = 0 := by
  rw [← riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g 5 3 i
    (cometricDoubleTraceField (I := I) g 3) x]
  rw [show covGrad (I := I) (M := M) g 5 3 (cometricDoubleTraceField (I := I) g 3) =
      (0 : SmoothCcTensor g 5 4) from
    cometricDoubleTraceField_covGrad_eq_zero (I := I) g 3]
  rw [b4_iteratedCovGrad_zero (I := I) (M := M) g 5 4 i]
  rw [show ((0 : SmoothCcTensor g 5 (4 + i)).toSection x) =
      (0 : TensorRSSpace 5 (4 + i) I x) from rfl]
  exact riemannianFiberNormSq_zero (I := I) (M := M) g 5 (3 + 1 + i) x

private lemma b4_bP_le_grid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (m : ℕ) :
    b (m + 1) ≤ Combinatorics.antidiagonalTupleGrid b (m + 1) := by
  classical
  have hmem : (![m + 1] : Fin 1 → ℕ) ∈ Finset.Nat.antidiagonalTuple 1 (m + 1) := by
    rw [Finset.Nat.mem_antidiagonalTuple]
    simp
  have h1 : b (m + 1) ≤ ∑ e ∈ Finset.Nat.antidiagonalTuple 1 (m + 1),
      ∏ k : Fin 1, b (e k) := by
    have hval : (∏ k : Fin 1, b ((![m + 1] : Fin 1 → ℕ) k)) = b (m + 1) := by
      rw [Fin.prod_univ_one]
      rfl
    rw [← hval]
    exact Finset.single_le_sum (fun e _ => Finset.prod_nonneg (fun k _ => hb (e k))) hmem
  refine le_trans h1 ?_
  have hmem1 : (1 : ℕ) ∈ Finset.range (m + 1 + 1) := Finset.mem_range.mpr (by omega)
  exact Finset.single_le_sum
    (f := fun n => ∑ e ∈ Finset.Nat.antidiagonalTuple n (m + 1), ∏ k : Fin n, b (e k))
    (fun n _ => Finset.sum_nonneg (fun e _ =>
      Finset.prod_nonneg (fun k _ => hb (e k)))) hmem1

private lemma b4_slotIter_le (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (Φ : SmoothCcTensor g r s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (r + w) ((s + w) + i) x
        ((iteratedCovGrad (I := I) g (r + w) (s + w) i
          (slotExtendIter (I := I) (M := M) g r s w Φ)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ w *
        riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
          ((iteratedCovGrad (I := I) g r s i Φ).toSection x) := by
  induction w with
  | zero =>
      simp only [Nat.add_zero, slotExtendIter, pow_zero, one_mul]
      exact le_rfl
  | succ w ih =>
      have hfr : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
      change riemannianFiberNormSq (I := I) (M := M) g ((r + w) + 1)
          (((s + w) + 1) + i) x
          ((iteratedCovGrad (I := I) g ((r + w) + 1) ((s + w) + 1) i
            (slotExtend (I := I) (M := M) g (r + w) (s + w)
              (slotExtendIter (I := I) (M := M) g r s w Φ))).toSection x) ≤ _
      calc
        _ ≤ (Module.finrank ℝ E : ℝ) *
              riemannianFiberNormSq (I := I) (M := M) g (r + w) ((s + w) + i) x
                ((iteratedCovGrad (I := I) g (r + w) (s + w) i
                  (slotExtendIter (I := I) (M := M) g r s w Φ)).toSection x) :=
            riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g (r + w) (s + w)
              (slotExtendIter (I := I) (M := M) g r s w Φ) i x
        _ ≤ (Module.finrank ℝ E : ℝ) *
              ((Module.finrank ℝ E : ℝ) ^ w *
                riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
                  ((iteratedCovGrad (I := I) g r s i Φ).toSection x)) :=
            mul_le_mul_of_nonneg_left ih hfr
        _ = (Module.finrank ℝ E : ℝ) ^ (w + 1) *
              riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
                ((iteratedCovGrad (I := I) g r s i Φ).toSection x) := by
            rw [pow_succ]
            ring

private noncomputable def b4JoinK (u v : ℕ) (A B : ℕ → ℝ) (n : ℕ) : ℝ :=
  operatorFieldApplicationGdiag (E := E) n *
    ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      A i * B j * Combinatorics.antidiagonalTupleGridWindowMulConst (i + u) (j + v)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma b4JoinK_nonneg (u v : ℕ) (A B : ℕ → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) (n : ℕ) :
    0 ≤ b4JoinK (E := E) u v A B n := by
  refine mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) n)
    (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_)))
  exact mul_nonneg (mul_nonneg (hA i) (hB j))
    (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg (i + u) (j + v))

private lemma b4_join_antidiagonalTupleGridWindow (g : SmoothRiemannianMetric I M)
    (p a b u v n : ℕ) (Φ : SmoothCcTensor g a b) (W : SmoothCcTensor g p a)
    (x : M) (grid : ℕ → ℝ) (hgrid : ∀ j, 0 ≤ grid j)
    (A B : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    (hΦ : ∀ j,
      riemannianFiberNormSq (I := I) (M := M) g a (b + j) x
          ((iteratedCovGrad (I := I) g a b j Φ).toSection x) ≤
        A j * Combinatorics.antidiagonalTupleGridWindow grid (j + u + 1))
    (hW : ∀ j,
      riemannianFiberNormSq (I := I) (M := M) g p (a + j) x
          ((iteratedCovGrad (I := I) g p a j W).toSection x) ≤
        B j * Combinatorics.antidiagonalTupleGridWindow grid (j + v + 1)) :
    riemannianFiberNormSq (I := I) (M := M) g p (b + n) x
        ((iteratedCovGrad (I := I) g p b n
          (ccOperatorFieldComp (I := I) (M := M) g p a b Φ W)).toSection x) ≤
      b4JoinK (E := E) u v A B n *
        Combinatorics.antidiagonalTupleGridWindow grid (n + u + v + 1) := by
  classical
  refine le_trans
    (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g n p a b Φ W x) ?_
  rw [b4JoinK, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) n)
  have hterm : ∀ i ∈ Finset.range (n + 1),
      riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
          ((iteratedCovGrad (I := I) g a b i Φ).toSection x) *
        ∑ j ∈ Finset.range (n + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g p (a + j) x
            ((iteratedCovGrad (I := I) g p a j W).toSection x) ≤
      ∑ j ∈ Finset.range (n + 1),
        (A i * B j * Combinatorics.antidiagonalTupleGridWindowMulConst (i + u) (j + v)) *
          Combinatorics.antidiagonalTupleGridWindow grid (n + u + v + 1) := by
    intro i hi
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun j hj => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun j _ _ => ?_))
    swap
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (hA i) (hB j))
          (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg (i + u) (j + v)))
        (Combinatorics.antidiagonalTupleGridWindow_nonneg grid hgrid (n + u + v + 1))
    · have hprod :
          riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
              ((iteratedCovGrad (I := I) g a b i Φ).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g p (a + j) x
              ((iteratedCovGrad (I := I) g p a j W).toSection x) ≤
          (A i * Combinatorics.antidiagonalTupleGridWindow grid (i + u + 1)) *
            (B j * Combinatorics.antidiagonalTupleGridWindow grid (j + v + 1)) :=
        mul_le_mul (hΦ i) (hW j)
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g p (a + j) x _)
          (mul_nonneg (hA i)
            (Combinatorics.antidiagonalTupleGridWindow_nonneg grid hgrid (i + u + 1)))
      calc
        _ ≤ (A i * Combinatorics.antidiagonalTupleGridWindow grid (i + u + 1)) *
              (B j * Combinatorics.antidiagonalTupleGridWindow grid (j + v + 1)) := hprod
        _ = A i * B j *
              (Combinatorics.antidiagonalTupleGridWindow grid ((i + u) + 1) *
                Combinatorics.antidiagonalTupleGridWindow grid ((j + v) + 1)) := by ring
        _ ≤ A i * B j *
              (Combinatorics.antidiagonalTupleGridWindowMulConst (i + u) (j + v) *
                Combinatorics.antidiagonalTupleGridWindow grid
                  ((i + u) + (j + v) + 1)) := by
            refine mul_le_mul_of_nonneg_left
              (Combinatorics.antidiagonalTupleGridWindow_mul_le grid hgrid (i + u) (j + v))
              (mul_nonneg (hA i) (hB j))
        _ ≤ A i * B j *
              (Combinatorics.antidiagonalTupleGridWindowMulConst (i + u) (j + v) *
                Combinatorics.antidiagonalTupleGridWindow grid (n + u + v + 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hA i) (hB j))
            refine mul_le_mul_of_nonneg_left ?_
              (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg (i + u) (j + v))
            exact Combinatorics.antidiagonalTupleGridWindow_mono grid hgrid
              (by rw [Finset.mem_range] at hj; omega)
        _ = (A i * B j *
              Combinatorics.antidiagonalTupleGridWindowMulConst (i + u) (j + v)) *
              Combinatorics.antidiagonalTupleGridWindow grid (n + u + v + 1) := by ring
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (A i * B j * Combinatorics.antidiagonalTupleGridWindowMulConst (i + u) (j + v)) *
            Combinatorics.antidiagonalTupleGridWindow grid (n + u + v + 1) :=
        Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          A i * B j * Combinatorics.antidiagonalTupleGridWindowMulConst (i + u) (j + v)) *
            Combinatorics.antidiagonalTupleGridWindow grid (n + u + v + 1) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_mul])

private def b4PermA : Equiv.Perm (Fin 5) :=
  ⟨![2, 3, 0, 1, 4], ![2, 3, 0, 1, 4], by decide, by decide⟩

private def b4PermB : Equiv.Perm (Fin 5) :=
  ⟨![2, 3, 0, 4, 1], ![2, 4, 0, 1, 3], by decide, by decide⟩

private noncomputable def b4Pk3 (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 3 5 :=
  slotExtend (I := I) (M := M) g₀ 2 4
    (slotExtend (I := I) (M := M) g₀ 1 3 (slotExtend (I := I) (M := M) g₀ 0 2 P))

private noncomputable def b4Phi (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (σ : Equiv.Perm (Fin 5)) : SmoothCcTensor g₀ 3 3 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 3 5 3
    (reindexCoeffGen (I := I) (M := M) g₀ 5 3
      (cometricDoubleTraceField (I := I) g₀ 3) σ)
    (b4Pk3 (I := I) (M := M) g₀ P)

private noncomputable def b4Jet2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) : ℝ :=
  ∑ q ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem b4_jet2_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    0 ≤ b4Jet2 (I := I) (M := M) g r s S :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem b4_jet2_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    b4Jet2 (I := I) (M := M) g r s (S + T) ≤
      2 * (b4Jet2 (I := I) (M := M) g r s S +
        b4Jet2 (I := I) (M := M) g r s T) := by
  unfold b4Jet2
  calc
    ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g r s q (S + T)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 3,
        2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s q T‖ ^ 2) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [iteratedCovGrad_add]
        have htri := norm_add_le
          (iteratedCovGrad (I := I) g r s q S)
          (iteratedCovGrad (I := I) g r s q T)
        calc
          ‖iteratedCovGrad (I := I) g r s q S +
              iteratedCovGrad (I := I) g r s q T‖ ^ 2 ≤
              (‖iteratedCovGrad (I := I) g r s q S‖ +
                ‖iteratedCovGrad (I := I) g r s q T‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) htri 2
          _ ≤ 2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g r s q T‖ ^ 2) := by
            nlinarith only [sq_nonneg
              (‖iteratedCovGrad (I := I) g r s q S‖ -
                ‖iteratedCovGrad (I := I) g r s q T‖)]
    _ = 2 * ((∑ q ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2) +
        ∑ q ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s q T‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem b4_jet2_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) :
    b4Jet2 (I := I) (M := M) g r s (c • S) =
      c ^ 2 * b4Jet2 (I := I) (M := M) g r s S := by
  unfold b4Jet2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [iteratedCovGrad_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]

private theorem b4_slot_l2
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g r s Φ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) *
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
      ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i Φ)).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (r + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
      (slotExtend (I := I) (M := M) g r s Φ))
    F hF (fun x =>
      riemannianFiberNormSq_iteratedCovGrad_slotExtend_le
        (I := I) (M := M) g r s Φ i x)
  have hint : (∫ x,
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g r (s + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private theorem b4_slot_h2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) :
    b4Jet2 (I := I) (M := M) g (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g r s Φ) ≤
      (Module.finrank ℝ E : ℝ) *
        b4Jet2 (I := I) (M := M) g r s Φ := by
  unfold b4Jet2
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
          (slotExtend (I := I) (M := M) g r s Φ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        b4_slot_l2 (I := I) (M := M) g r s i Φ
    _ = (Module.finrank ℝ E : ℝ) *
        ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
      rw [Finset.mul_sum]

omit [NeZero (Module.finrank ℝ E)] in
private theorem b4_reindex_h2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (ρ : Equiv.Perm (Fin r)) :
    b4Jet2 (I := I) (M := M) g r s
        (reindexCoeffGen (I := I) (M := M) g r s Φ ρ) =
      b4Jet2 (I := I) (M := M) g r s Φ := by
  unfold b4Jet2
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedCovGrad_reindexCoeffGen,
    norm_reindexCoeffGen_eq]

private theorem b4_app_h2_mul
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        b4Jet2 (I := I) (M := M) g p c
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
          C * b4Jet2 (I := I) (M := M) g r c Φ *
            b4Jet2 (I := I) (M := M) g p r W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  have hΦ0 : 0 ≤ b4Jet2 (I := I) (M := M) g r c Φ :=
    b4_jet2_nonneg (I := I) (M := M) g r c Φ
  have hW0 : 0 ≤ b4Jet2 (I := I) (M := M) g p r W :=
    b4_jet2_nonneg (I := I) (M := M) g p r W
  have hsΦ :
      Real.sqrt (b4Jet2 (I := I) (M := M) g r c Φ) ^ 2 =
        b4Jet2 (I := I) (M := M) g r c Φ :=
    Real.sq_sqrt hΦ0
  have hsW :
      Real.sqrt (b4Jet2 (I := I) (M := M) g p r W) ^ 2 =
        b4Jet2 (I := I) (M := M) g p r W :=
    Real.sq_sqrt hW0
  have h := happ Φ W
    (Real.sqrt (b4Jet2 (I := I) (M := M) g r c Φ))
    (Real.sqrt (b4Jet2 (I := I) (M := M) g p r W))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by exact le_of_eq hsΦ.symm)
    (by exact le_of_eq hsW.symm)
  calc
    b4Jet2 (I := I) (M := M) g p c
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
      (C₀ *
        Real.sqrt (b4Jet2 (I := I) (M := M) g r c Φ) *
        Real.sqrt (b4Jet2 (I := I) (M := M) g p r W)) ^ 2 := by
      simpa only [b4Jet2] using h
    _ = C₀ ^ 2 * b4Jet2 (I := I) (M := M) g r c Φ *
        b4Jet2 (I := I) (M := M) g p r W := by
      rw [mul_pow, mul_pow, hsΦ, hsW]

private theorem b4_pk3_h2
    (g : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g 0 2) :
    b4Jet2 (I := I) (M := M) g 3 5
        (b4Pk3 (I := I) (M := M) g P) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        b4Jet2 (I := I) (M := M) g 0 2 P := by
  have hfr : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  have h1 := b4_slot_h2 (I := I) (M := M) g 0 2 P
  have h2 := b4_slot_h2 (I := I) (M := M) g 1 3
    (slotExtend (I := I) (M := M) g 0 2 P)
  have h3 := b4_slot_h2 (I := I) (M := M) g 2 4
    (slotExtend (I := I) (M := M) g 1 3
      (slotExtend (I := I) (M := M) g 0 2 P))
  calc
    b4Jet2 (I := I) (M := M) g 3 5
        (b4Pk3 (I := I) (M := M) g P) ≤
      (Module.finrank ℝ E : ℝ) *
        b4Jet2 (I := I) (M := M) g 2 4
          (slotExtend (I := I) (M := M) g 1 3
            (slotExtend (I := I) (M := M) g 0 2 P)) := by
          simpa only [b4Pk3] using h3
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          b4Jet2 (I := I) (M := M) g 1 3
            (slotExtend (I := I) (M := M) g 0 2 P)) :=
      mul_le_mul_of_nonneg_left h2 hfr
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) *
            b4Jet2 (I := I) (M := M) g 0 2 P)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h1 hfr) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 3 *
        b4Jet2 (I := I) (M := M) g 0 2 P := by ring

private theorem b4_phi_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 5)),
        b4Jet2 (I := I) (M := M) g 3 3
            (b4Phi (I := I) (M := M) g P σ) ≤
          C * b4Jet2 (I := I) (M := M) g 0 2 P := by
  obtain ⟨Ca, hCa0, happ⟩ :=
    b4_app_h2_mul (I := I) (M := M) hDim g 3 5 3
  let Jtr : ℝ := b4Jet2 (I := I) (M := M) g 5 3
    (cometricDoubleTraceField (I := I) g 3)
  have hJtr0 : 0 ≤ Jtr :=
    b4_jet2_nonneg (I := I) (M := M) g 5 3
      (cometricDoubleTraceField (I := I) g 3)
  have hfr : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  refine ⟨Ca * Jtr * (Module.finrank ℝ E : ℝ) ^ 3,
    mul_nonneg (mul_nonneg hCa0 hJtr0) (pow_nonneg hfr 3), ?_⟩
  intro P σ
  have hprod := happ
    (reindexCoeffGen (I := I) (M := M) g 5 3
      (cometricDoubleTraceField (I := I) g 3) σ)
    (b4Pk3 (I := I) (M := M) g P)
  rw [b4_reindex_h2 (I := I) (M := M)] at hprod
  have hpk := b4_pk3_h2 (I := I) (M := M) g P
  calc
    b4Jet2 (I := I) (M := M) g 3 3
        (b4Phi (I := I) (M := M) g P σ) ≤
      Ca * Jtr *
        b4Jet2 (I := I) (M := M) g 3 5
          (b4Pk3 (I := I) (M := M) g P) := by
            simpa only [b4Phi, Jtr] using hprod
    _ ≤ Ca * Jtr *
        ((Module.finrank ℝ E : ℝ) ^ 3 *
          b4Jet2 (I := I) (M := M) g 0 2 P) :=
      mul_le_mul_of_nonneg_left hpk (mul_nonneg hCa0 hJtr0)
    _ = (Ca * Jtr * (Module.finrank ℝ E : ℝ) ^ 3) *
        b4Jet2 (I := I) (M := M) g 0 2 P := by ring

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma b4_trace_center (g : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 5 I x) (m : Fin 3 → E) :
    Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g 3 x D) m =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E) m)) := by
  rw [show Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g 3 x D) m =
      modelDoubleTrace (E := E) 3 (cometricLmodel (I := I) g x)
        (Tensor0SSpace.toModel D) m from by
    rw [cometricDoubleTraceFib_toModel (I := I) g 3 x D]]
  rw [modelDoubleTrace_apply (E := E) 3 (cometricLmodel (I := I) g x)
    (Tensor0SSpace.toModel D) m]
  exact cometric_dualTrace_eq_orthoFrame_diag (I := I) g (s := 3) x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel D) m

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma b4_rank0_unit (x : M) (c : Tensor0SSpace 0 I x) :
    c = Tensor0SSpace.toModel c (fun i : Fin 0 => i.elim0) •
      unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have h1 : Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) v = (1 : ℝ) := rfl
  rw [h1, mul_one]
  congr 1
  funext i
  exact i.elim0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma b4_pk3_toModel (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (x : M) (D : Tensor0SSpace 3 I x)
    (u0 u1 u2 u3 u4 : E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
          (b4Pk3 (I := I) (M := M) g₀ P).toSection x) D) ![u0, u1, u2, u3, u4] =
      Tensor0SSpace.toModel D ![u0, u1, u2] *
        unitModel (I := I) (M := M) g₀ 2 P x ![u3, u4] := by
  have h0 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
        (b4Pk3 (I := I) (M := M) g₀ P).toSection x) D) ![u0, u1, u2, u3, u4] =
      Tensor0SSpace.toModel
        (slotExtendFib (I := I) (M := M) 2 4 x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
            (slotExtend (I := I) (M := M) g₀ 1 3
              (slotExtend (I := I) (M := M) g₀ 0 2 P)).toSection x) D)
        (Fin.cons u0 ![u1, u2, u3, u4]) := rfl
  rw [h0]
  rw [slotExtendFib_apply_eval (I := I) (M := M) 2 4 x
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
      (slotExtend (I := I) (M := M) g₀ 1 3
        (slotExtend (I := I) (M := M) g₀ 0 2 P)).toSection x) D u0 ![u1, u2, u3, u4]]
  have h1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtend (I := I) (M := M) g₀ 1 3
          (slotExtend (I := I) (M := M) g₀ 0 2 P)).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D u0)) ![u1, u2, u3, u4] =
      Tensor0SSpace.toModel
        (slotExtendFib (I := I) (M := M) 1 3 x
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
            (slotExtend (I := I) (M := M) g₀ 0 2 P).toSection x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D u0))
        (Fin.cons u1 ![u2, u3, u4]) := rfl
  rw [h1]
  rw [slotExtendFib_apply_eval (I := I) (M := M) 1 3 x
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
      (slotExtend (I := I) (M := M) g₀ 0 2 P).toSection x)
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D u0) u1 ![u2, u3, u4]]
  have h2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtend (I := I) (M := M) g₀ 0 2 P).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D u0) u1)) ![u2, u3, u4] =
      Tensor0SSpace.toModel
        (slotExtendFib (I := I) (M := M) 0 2 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from P.toSection x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D u0) u1))
        (Fin.cons u2 ![u3, u4]) := rfl
  rw [h2]
  rw [slotExtendFib_apply_eval (I := I) (M := M) 0 2 x
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from P.toSection x)
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D u0) u1) u2 ![u3, u4]]
  have hc : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D u0) u1) u2 =
      Tensor0SSpace.toModel D ![u0, u1, u2] • unitTensor (I := I) (M := M) x := by
    have h3 := b4_rank0_unit (I := I) (M := M) x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D u0) u1) u2)
    rw [h3]
    congr 1
  rw [hc, ContinuousLinearMap.map_smul, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [unitModel]

omit [NeZero (Module.finrank ℝ E)] in
private lemma b4_cons_sum_smul {n : ℕ}
    (Zm : Tensor0SModel (n + 1) ℝ E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons (∑ c, t c • u c) rest) =
      ∑ c, t c * Zm (Fin.cons (u c) rest) := by
  classical
  have h1 : ∀ v : E, (Fin.cons v rest : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) rest) 0 v := by
    intro v
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons (0 : E) rest) 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons (0 : E) rest) 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

omit [NeZero (Module.finrank ℝ E)] in
private lemma b4_cons1_sum_smul {n : ℕ}
    (Zm : Tensor0SModel (n + 2) ℝ E) (aa : E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons aa (Fin.cons (∑ c, t c • u c) rest)) =
      ∑ c, t c * Zm (Fin.cons aa (Fin.cons (u c) rest)) := by
  classical
  have h1 : ∀ v : E, (Fin.cons aa (Fin.cons v rest) : Fin (n + 2) → E) =
      Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 v := by
    intro v
    rw [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl]
    rw [← Fin.cons_update]
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem b4_frame_expand (g : SmoothRiemannianMetric I M) (x : M)
    (u : TangentSpace I x) :
    u = ∑ i : Fin (Module.finrank ℝ E),
      g.inner x u (smoothOrthoFrame (I := I) g x i x) •
        smoothOrthoFrame (I := I) g x i x := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x)
        (smoothOrthoFrame (I := I) g x b x) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  have he_li : LinearIndependent ℝ
      (fun i => smoothOrthoFrame (I := I) g x i x) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (smoothOrthoFrame (I := I) g x k x)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g x j x) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (smoothOrthoFrame (I := I) g x k x)
        (c j • smoothOrthoFrame (I := I) g x j x) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (smoothOrthoFrame (I := I) g x k x)).map_smul (c j),
        smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  obtain ⟨bse, hbse⟩ : ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i, bse i = smoothOrthoFrame (I := I) g x i x :=
    ⟨basisOfLinearIndependentOfCardEqFinrank he_li (Fintype.card_fin _),
      fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li (Fintype.card_fin _)) i⟩
  have hcoeff : ∀ j : Fin (Module.finrank ℝ E),
      g.inner x u (smoothOrthoFrame (I := I) g x j x) = bse.repr u j := by
    intro j
    rw [g.symm x u (smoothOrthoFrame (I := I) g x j x)]
    conv_lhs => rw [← bse.sum_repr u]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [(g.inner x (smoothOrthoFrame (I := I) g x j x)).map_smul (bse.repr u i),
        smul_eq_mul, hbse i, horth j i])]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij
      rw [if_neg (fun h => hij h.symm), mul_zero]
  calc u = ∑ i : Fin (Module.finrank ℝ E), bse.repr u i • bse i := (bse.sum_repr u).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
        g.inner x u (smoothOrthoFrame (I := I) g x i x) •
          smoothOrthoFrame (I := I) g x i x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff i, hbse i]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma b4_unitModel_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A + B) x =
      unitModel (I := I) (M := M) g₀ s A x + unitModel (I := I) (M := M) g₀ s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma b4_unitModel_smul (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ)
    (A : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (c • A) x =
      c • unitModel (I := I) (M := M) g₀ s A x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma b4_mcd_unitModel (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g_bg) x m =
      g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g_bg).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g_bg x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnectionDifferenceLoweredFib_toModel (I := I) g₁ g₁ g_bg x m

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma b4_operatorFieldApplication_unitModel (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g₀ r s) (W : SmoothCcTensor g₀ 0 r) (x : M) :
    unitModel (I := I) (M := M) g₀ s (operatorFieldApply (I := I) (M := M) g₀ r s Φ W) x =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
            (unitTensor (I := I) (M := M) x))) := by
  rw [unitModel, operatorFieldApplication_toSection]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma b4_unit_read (g₀ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 3) (x : M) (v : Fin 3 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) v =
      unitModel (I := I) (M := M) g₀ 3 W x v := by
  rw [unitModel]

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem metricConnectionDifferenceLoweredCoefficient_expansion (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g_bg =
      metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg +
        ((1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3
            (b4Phi (I := I) (M := M) g₀ P b4PermA) (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) +
          (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3
            (b4Phi (I := I) (M := M) g₀ P b4PermB) (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)) := by
  classical
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [b4_unitModel_add, b4_unitModel_add, b4_unitModel_smul, b4_unitModel_smul]
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul]
  rw [b4_mcd_unitModel (I := I) (M := M) g₀ g₁ g_bg x m]
  rw [htie x (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (m 0) (m 1)) (m 2)]
  set V : TangentSpace I x := PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (m 0) (m 1) with hV_def
  have hwXi_read : unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) x m =
      g₀.inner x V (m 2) :=
    metricLoweredConnectionDifference_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x m
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) with hD_def
  have hD_read : ∀ v : Fin 3 → E,
      Tensor0SSpace.toModel D v = g₀.inner x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (v 0) (v 1)) (v 2) := by
    intro v
    rw [hD_def, b4_unit_read (I := I) (M := M) g₀ (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) x v]
    exact metricLoweredConnectionDifference_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x v
  have hcommon : ∀ (σ : Equiv.Perm (Fin 5)),
      unitModel (I := I) (M := M) g₀ 3
        (operatorFieldApply (I := I) (M := M) g₀ 3 3 (b4Phi (I := I) (M := M) g₀ P σ)
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)) x m =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
            (b4Pk3 (I := I) (M := M) g₀ P).toSection x) D)
          (fun i : Fin 5 =>
            ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E) m) :
                Fin 5 → E))
            (σ i)) := by
    intro σ
    rw [b4_operatorFieldApplication_unitModel (I := I) (M := M) g₀ 3 3 (b4Phi (I := I) (M := M) g₀ P σ)
      (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) x]
    rw [show ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 3 I x from
        (b4Phi (I := I) (M := M) g₀ P σ).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x))) =
        reindexCoeffFibGen (I := I) 5 3 σ x
          (show Tensor0SSpace 5 I x →L[ℝ] Tensor0SSpace 3 I x from
            (cometricDoubleTraceField (I := I) g₀ 3).toSection x)
          ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
            (b4Pk3 (I := I) (M := M) g₀ P).toSection x) D) from rfl]
    rw [reindexCoeffFibGen_apply]
    rw [show ((show Tensor0SSpace 5 I x →L[ℝ] Tensor0SSpace 3 I x from
        (cometricDoubleTraceField (I := I) g₀ 3).toSection x)
          (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr σ
              (Tensor0SSpace.toModel
                ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
                  (b4Pk3 (I := I) (M := M) g₀ P).toSection x) D))))) =
        cometricDoubleTraceFib (I := I) g₀ 3 x
          (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr σ
              (Tensor0SSpace.toModel
                ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
                  (b4Pk3 (I := I) (M := M) g₀ P).toSection x) D)))) from by
      rw [cometricDoubleTraceField_toSection]]
    rw [b4_trace_center (I := I) (M := M) g₀ x _ m]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  have hA : unitModel (I := I) (M := M) g₀ 3
      (operatorFieldApply (I := I) (M := M) g₀ 3 3 (b4Phi (I := I) (M := M) g₀ P b4PermA)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)) x m =
      unitModel (I := I) (M := M) g₀ 2 P x
        (Fin.cons (show E from V) (fun _ : Fin 1 => m 2)) := by
    rw [hcommon b4PermA]
    have hterm : ∀ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
            (b4Pk3 (I := I) (M := M) g₀ P).toSection x) D)
          (fun i : Fin 5 =>
            ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E) m) :
                Fin 5 → E))
            (b4PermA i)) =
        g₀.inner x V (smoothOrthoFrame (I := I) g₀ x c x) *
          unitModel (I := I) (M := M) g₀ 2 P x
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)
              (fun _ : Fin 1 => m 2)) := by
      intro c
      rw [show (fun i : Fin 5 =>
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E) m) :
              Fin 5 → E))
          (b4PermA i)) =
          (![m 0, m 1, ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E),
            ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E), m 2] :
              Fin 5 → E) from by
        funext i
        fin_cases i <;> rfl]
      rw [b4_pk3_toModel (I := I) (M := M) g₀ P x D _ _ _ _ _]
      rw [hD_read ![m 0, m 1, ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)]]
      rw [show (![((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E), m 2] :
          Fin 2 → E) =
          Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)
            (fun _ : Fin 1 => m 2) from by
        funext k
        fin_cases k <;> rfl]
      rfl
    rw [Finset.sum_congr rfl (fun c _ => hterm c)]
    have hVexp : (show E from V) =
        ∑ c : Fin (Module.finrank ℝ E),
          g₀.inner x V (smoothOrthoFrame (I := I) g₀ x c x) •
            ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E) :=
      b4_frame_expand (I := I) (M := M) g₀ x V
    rw [show unitModel (I := I) (M := M) g₀ 2 P x
        (Fin.cons (show E from V) (fun _ : Fin 1 => m 2)) =
        unitModel (I := I) (M := M) g₀ 2 P x
          (Fin.cons (∑ c : Fin (Module.finrank ℝ E),
            g₀.inner x V (smoothOrthoFrame (I := I) g₀ x c x) •
              ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E))
            (fun _ : Fin 1 => m 2)) from by rw [← hVexp]]
    exact (b4_cons_sum_smul (unitModel (I := I) (M := M) g₀ 2 P x)
      (Module.finrank ℝ E)
      (fun c => g₀.inner x V (smoothOrthoFrame (I := I) g₀ x c x))
      (fun c => ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E))
      (fun _ : Fin 1 => m 2)).symm
  have hB : unitModel (I := I) (M := M) g₀ 3
      (operatorFieldApply (I := I) (M := M) g₀ 3 3 (b4Phi (I := I) (M := M) g₀ P b4PermB)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)) x m =
      unitModel (I := I) (M := M) g₀ 2 P x
        (Fin.cons (m 2) (fun _ : Fin 1 => (show E from V))) := by
    rw [hcommon b4PermB]
    have hterm : ∀ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
            (b4Pk3 (I := I) (M := M) g₀ P).toSection x) D)
          (fun i : Fin 5 =>
            ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E) m) :
                Fin 5 → E))
            (b4PermB i)) =
        g₀.inner x V (smoothOrthoFrame (I := I) g₀ x c x) *
          unitModel (I := I) (M := M) g₀ 2 P x
            (Fin.cons (m 2)
              (fun _ : Fin 1 =>
                ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E))) := by
      intro c
      rw [show (fun i : Fin 5 =>
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E) m) :
              Fin 5 → E))
          (b4PermB i)) =
          (![m 0, m 1, ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E),
            m 2, ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)] :
              Fin 5 → E) from by
        funext i
        fin_cases i <;> rfl]
      rw [b4_pk3_toModel (I := I) (M := M) g₀ P x D _ _ _ _ _]
      rw [hD_read ![m 0, m 1, ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)]]
      rw [show (![m 2, ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)] :
          Fin 2 → E) =
          Fin.cons (m 2)
            (fun _ : Fin 1 =>
              ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E)) from by
        funext k
        fin_cases k <;> rfl]
      rfl
    rw [Finset.sum_congr rfl (fun c _ => hterm c)]
    have hVexp : (show E from V) =
        ∑ c : Fin (Module.finrank ℝ E),
          g₀.inner x V (smoothOrthoFrame (I := I) g₀ x c x) •
            ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E) :=
      b4_frame_expand (I := I) (M := M) g₀ x V
    rw [show unitModel (I := I) (M := M) g₀ 2 P x
        (Fin.cons (m 2) (fun _ : Fin 1 => (show E from V))) =
        unitModel (I := I) (M := M) g₀ 2 P x
          (Fin.cons (m 2) (Fin.cons (∑ c : Fin (Module.finrank ℝ E),
            g₀.inner x V (smoothOrthoFrame (I := I) g₀ x c x) •
              ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E))
            (fun i : Fin 0 => i.elim0))) from by
      rw [← hVexp]
      congr 1
      funext k
      fin_cases k <;> rfl]
    rw [b4_cons1_sum_smul (unitModel (I := I) (M := M) g₀ 2 P x) (m 2)
      (Module.finrank ℝ E)
      (fun c => g₀.inner x V (smoothOrthoFrame (I := I) g₀ x c x))
      (fun c => ((smoothOrthoFrame (I := I) g₀ x c x : TangentSpace I x) : E))
      (fun i : Fin 0 => i.elim0)]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    congr 1
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [hwXi_read, hA, hB]
  have hccb : ∀ v w : TangentSpace I x,
      ccTensorBilin (I := I) g₀ P x v w =
        unitModel (I := I) (M := M) g₀ 2 P x
          (Fin.cons (show E from v) (fun _ : Fin 1 => (show E from w))) := by
    intro v w
    rw [ccTensorBilin_apply]
    rw [show (![v, w] : Fin 2 → TangentSpace I x) =
        (Fin.cons (show E from v) (fun _ : Fin 1 => (show E from w)) : Fin 2 → E) from by
      funext k
      fin_cases k <;> rfl]
    rfl
  rw [ccTensorBilinSymm_apply (I := I) g₀ P x V (m 2)]
  rw [hccb V (m 2), hccb (m 2) V]
  ring

noncomputable def metricLoweredConnectionDifferenceCorrection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 3 :=
  (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3
      (b4Phi (I := I) (M := M) g₀ P b4PermA)
      (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) +
    (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3
      (b4Phi (I := I) (M := M) g₀ P b4PermB)
      (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem metricLoweredConnectionDifferenceCorrection_sub
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (P Q : SmoothCcTensor g₀ 0 2) :
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g₀ g₁ g_bg (P - Q) =
      metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g₀ g₁ g_bg P -
        metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g₀ g₁ g_bg Q := by
  simp only [metricLoweredConnectionDifferenceCorrection, b4Phi, b4Pk3, slotExtend_sub,
    operatorFieldComposition_sub_right, operatorFieldApplication_sub_left]
  module

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem metricConnectionDifferenceLoweredCoefficient_eq_lowered_add_correction
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g_bg =
      metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg +
        metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g₀ g₁ g_bg P := by
  simpa only [metricLoweredConnectionDifferenceCorrection] using
    metricConnectionDifferenceLoweredCoefficient_expansion (I := I) (M := M) g₀ g₁ g_bg P htie

private theorem metricLoweredConnectionDifferenceCorrection_sobolev_two_action_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P : SmoothCcTensor g₀ 0 2)
        (W : SmoothCcTensor g₀ 0 3),
        b4Jet2 (I := I) (M := M) g₀ 0 3
            ((1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3
                (b4Phi (I := I) (M := M) g₀ P b4PermA) W +
              (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3
                (b4Phi (I := I) (M := M) g₀ P b4PermB) W) ≤
          C * b4Jet2 (I := I) (M := M) g₀ 0 2 P *
            b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
  obtain ⟨Cφ, hCφ0, hφ⟩ :=
    b4_phi_h2 (I := I) (M := M) hDim g₀
  obtain ⟨Ca, hCa0, happ⟩ :=
    b4_app_h2_mul (I := I) (M := M) hDim g₀ 0 3 3
  refine ⟨Ca * Cφ, mul_nonneg hCa0 hCφ0, ?_⟩
  intro P W
  let UA : SmoothCcTensor g₀ 0 3 :=
    operatorFieldApply (I := I) (M := M) g₀ 3 3
      (b4Phi (I := I) (M := M) g₀ P b4PermA) W
  let UB : SmoothCcTensor g₀ 0 3 :=
    operatorFieldApply (I := I) (M := M) g₀ 3 3
      (b4Phi (I := I) (M := M) g₀ P b4PermB) W
  have hP0 : 0 ≤ b4Jet2 (I := I) (M := M) g₀ 0 2 P :=
    b4_jet2_nonneg (I := I) (M := M) g₀ 0 2 P
  have hW0 : 0 ≤ b4Jet2 (I := I) (M := M) g₀ 0 3 W :=
    b4_jet2_nonneg (I := I) (M := M) g₀ 0 3 W
  have hA0 : 0 ≤ b4Jet2 (I := I) (M := M) g₀ 0 3 UA :=
    b4_jet2_nonneg (I := I) (M := M) g₀ 0 3 UA
  have hB0 : 0 ≤ b4Jet2 (I := I) (M := M) g₀ 0 3 UB :=
    b4_jet2_nonneg (I := I) (M := M) g₀ 0 3 UB
  have hA :
      b4Jet2 (I := I) (M := M) g₀ 0 3 UA ≤
        Ca * Cφ * b4Jet2 (I := I) (M := M) g₀ 0 2 P *
          b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
    have ha := happ
      (b4Phi (I := I) (M := M) g₀ P b4PermA) W
    have hφA := hφ P b4PermA
    calc
      b4Jet2 (I := I) (M := M) g₀ 0 3 UA ≤
          Ca *
            b4Jet2 (I := I) (M := M) g₀ 3 3
              (b4Phi (I := I) (M := M) g₀ P b4PermA) *
            b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
        simpa only [UA, operatorFieldApply] using ha
      _ ≤ Ca *
            (Cφ * b4Jet2 (I := I) (M := M) g₀ 0 2 P) *
            b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hφA hCa0) hW0
      _ = Ca * Cφ * b4Jet2 (I := I) (M := M) g₀ 0 2 P *
          b4Jet2 (I := I) (M := M) g₀ 0 3 W := by ring
  have hB :
      b4Jet2 (I := I) (M := M) g₀ 0 3 UB ≤
        Ca * Cφ * b4Jet2 (I := I) (M := M) g₀ 0 2 P *
          b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
    have hb := happ
      (b4Phi (I := I) (M := M) g₀ P b4PermB) W
    have hφB := hφ P b4PermB
    calc
      b4Jet2 (I := I) (M := M) g₀ 0 3 UB ≤
          Ca *
            b4Jet2 (I := I) (M := M) g₀ 3 3
              (b4Phi (I := I) (M := M) g₀ P b4PermB) *
            b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
        simpa only [UB, operatorFieldApply] using hb
      _ ≤ Ca *
            (Cφ * b4Jet2 (I := I) (M := M) g₀ 0 2 P) *
            b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hφB hCa0) hW0
      _ = Ca * Cφ * b4Jet2 (I := I) (M := M) g₀ 0 2 P *
          b4Jet2 (I := I) (M := M) g₀ 0 3 W := by ring
  have hadd := b4_jet2_add (I := I) (M := M) g₀ 0 3
    ((1 / 2 : ℝ) • UA) ((1 / 2 : ℝ) • UB)
  rw [b4_jet2_smul, b4_jet2_smul] at hadd
  change b4Jet2 (I := I) (M := M) g₀ 0 3
      ((1 / 2 : ℝ) • UA + (1 / 2 : ℝ) • UB) ≤ _
  calc
    b4Jet2 (I := I) (M := M) g₀ 0 3
        ((1 / 2 : ℝ) • UA + (1 / 2 : ℝ) • UB) ≤
      2 * (((1 / 2 : ℝ) ^ 2 *
          b4Jet2 (I := I) (M := M) g₀ 0 3 UA) +
        (1 / 2 : ℝ) ^ 2 *
          b4Jet2 (I := I) (M := M) g₀ 0 3 UB) := hadd
    _ ≤ Ca * Cφ * b4Jet2 (I := I) (M := M) g₀ 0 2 P *
        b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
      nlinarith

theorem metricLoweredConnectionDifferenceCorrection_sobolev_two_mul_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ g_bg : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g₀ 0 2),
        (∑ q ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g₀ g₁ g_bg P)‖ ^ 2) ≤
          C *
            (∑ q ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) *
            (∑ q ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 3 q
                (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) := by
  obtain ⟨Cφ, hCφ0, hφ⟩ :=
    b4_phi_h2 (I := I) (M := M) hDim g₀
  obtain ⟨Ca, hCa0, happ⟩ :=
    b4_app_h2_mul (I := I) (M := M) hDim g₀ 0 3 3
  refine ⟨Ca * Cφ, mul_nonneg hCa0 hCφ0, ?_⟩
  intro g₁ g_bg P
  let W : SmoothCcTensor g₀ 0 3 :=
    metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg
  let UA : SmoothCcTensor g₀ 0 3 :=
    operatorFieldApply (I := I) (M := M) g₀ 3 3
      (b4Phi (I := I) (M := M) g₀ P b4PermA) W
  let UB : SmoothCcTensor g₀ 0 3 :=
    operatorFieldApply (I := I) (M := M) g₀ 3 3
      (b4Phi (I := I) (M := M) g₀ P b4PermB) W
  have hP0 : 0 ≤ b4Jet2 (I := I) (M := M) g₀ 0 2 P :=
    b4_jet2_nonneg (I := I) (M := M) g₀ 0 2 P
  have hW0 : 0 ≤ b4Jet2 (I := I) (M := M) g₀ 0 3 W :=
    b4_jet2_nonneg (I := I) (M := M) g₀ 0 3 W
  have hA0 : 0 ≤ b4Jet2 (I := I) (M := M) g₀ 0 3 UA :=
    b4_jet2_nonneg (I := I) (M := M) g₀ 0 3 UA
  have hB0 : 0 ≤ b4Jet2 (I := I) (M := M) g₀ 0 3 UB :=
    b4_jet2_nonneg (I := I) (M := M) g₀ 0 3 UB
  have hA :
      b4Jet2 (I := I) (M := M) g₀ 0 3 UA ≤
        Ca * Cφ *
          b4Jet2 (I := I) (M := M) g₀ 0 2 P *
          b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
    have ha := happ
      (b4Phi (I := I) (M := M) g₀ P b4PermA) W
    have hφA := hφ P b4PermA
    calc
      b4Jet2 (I := I) (M := M) g₀ 0 3 UA ≤
          Ca *
            b4Jet2 (I := I) (M := M) g₀ 3 3
              (b4Phi (I := I) (M := M) g₀ P b4PermA) *
            b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
        simpa only [UA, operatorFieldApply] using ha
      _ ≤ Ca *
            (Cφ * b4Jet2 (I := I) (M := M) g₀ 0 2 P) *
            b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hφA hCa0) hW0
      _ = Ca * Cφ *
            b4Jet2 (I := I) (M := M) g₀ 0 2 P *
            b4Jet2 (I := I) (M := M) g₀ 0 3 W := by ring
  have hB :
      b4Jet2 (I := I) (M := M) g₀ 0 3 UB ≤
        Ca * Cφ *
          b4Jet2 (I := I) (M := M) g₀ 0 2 P *
          b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
    have hb := happ
      (b4Phi (I := I) (M := M) g₀ P b4PermB) W
    have hφB := hφ P b4PermB
    calc
      b4Jet2 (I := I) (M := M) g₀ 0 3 UB ≤
          Ca *
            b4Jet2 (I := I) (M := M) g₀ 3 3
              (b4Phi (I := I) (M := M) g₀ P b4PermB) *
            b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
        simpa only [UB, operatorFieldApply] using hb
      _ ≤ Ca *
            (Cφ * b4Jet2 (I := I) (M := M) g₀ 0 2 P) *
            b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hφB hCa0) hW0
      _ = Ca * Cφ *
            b4Jet2 (I := I) (M := M) g₀ 0 2 P *
            b4Jet2 (I := I) (M := M) g₀ 0 3 W := by ring
  have hadd := b4_jet2_add (I := I) (M := M) g₀ 0 3
    ((1 / 2 : ℝ) • UA) ((1 / 2 : ℝ) • UB)
  rw [b4_jet2_smul, b4_jet2_smul] at hadd
  have hcorr :
      b4Jet2 (I := I) (M := M) g₀ 0 3
          (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g₀ g₁ g_bg P) ≤
        Ca * Cφ *
          b4Jet2 (I := I) (M := M) g₀ 0 2 P *
          b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
    rw [show metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g₀ g₁ g_bg P =
        (1 / 2 : ℝ) • UA + (1 / 2 : ℝ) • UB from by
      rfl]
    calc
      b4Jet2 (I := I) (M := M) g₀ 0 3
          ((1 / 2 : ℝ) • UA + (1 / 2 : ℝ) • UB) ≤
        2 * (((1 / 2 : ℝ) ^ 2 *
            b4Jet2 (I := I) (M := M) g₀ 0 3 UA) +
          (1 / 2 : ℝ) ^ 2 *
            b4Jet2 (I := I) (M := M) g₀ 0 3 UB) := hadd
      _ ≤ Ca * Cφ *
          b4Jet2 (I := I) (M := M) g₀ 0 2 P *
          b4Jet2 (I := I) (M := M) g₀ 0 3 W := by
        nlinarith
  simpa only [b4Jet2, W] using hcorr

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem operatorFieldApplication_sub_right_local
    (g₀ : SmoothRiemannianMetric I M)
    (Φ : SmoothCcTensor g₀ 3 3)
    (W V : SmoothCcTensor g₀ 0 3) :
    operatorFieldApply (I := I) (M := M) g₀ 3 3 Φ (W - V) =
      operatorFieldApply (I := I) (M := M) g₀ 3 3 Φ W -
        operatorFieldApply (I := I) (M := M) g₀ 3 3 Φ V := by
  rw [sub_eq_add_neg, operatorFieldApplication_add_right]
  have hneg := operatorFieldApplication_smul_right (I := I) (M := M) g₀ 3 3
    (-1 : ℝ) Φ V
  simp only [neg_one_smul] at hneg
  rw [hneg]
  rfl

theorem metricLoweredConnectionDifferenceCorrection_metric_difference_sobolev_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ g₂ g_bg : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g₀ 0 2),
        (∑ q ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g₀ g₁ g_bg P -
              metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g₀ g₂ g_bg P)‖ ^ 2) ≤
          C *
            (∑ q ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) *
            (∑ q ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 3 q
                (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg -
                  metricLoweredConnectionDifference (I := I) (M := M) g₀ g₂ g_bg)‖ ^ 2) := by
  obtain ⟨C, hC, hact⟩ :=
    metricLoweredConnectionDifferenceCorrection_sobolev_two_action_bound (I := I) (M := M) hDim g₀
  refine ⟨C, hC, ?_⟩
  intro g₁ g₂ g_bg P
  let W₁ : SmoothCcTensor g₀ 0 3 :=
    metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg
  let W₂ : SmoothCcTensor g₀ 0 3 :=
    metricLoweredConnectionDifference (I := I) (M := M) g₀ g₂ g_bg
  let W : SmoothCcTensor g₀ 0 3 := W₁ - W₂
  have hA :
      operatorFieldApply (I := I) (M := M) g₀ 3 3
          (b4Phi (I := I) (M := M) g₀ P b4PermA) W =
        operatorFieldApply (I := I) (M := M) g₀ 3 3
            (b4Phi (I := I) (M := M) g₀ P b4PermA) W₁ -
          operatorFieldApply (I := I) (M := M) g₀ 3 3
            (b4Phi (I := I) (M := M) g₀ P b4PermA) W₂ := by
    simpa only [W] using
      operatorFieldApplication_sub_right_local (I := I) (M := M) g₀
        (b4Phi (I := I) (M := M) g₀ P b4PermA) W₁ W₂
  have hB :
      operatorFieldApply (I := I) (M := M) g₀ 3 3
          (b4Phi (I := I) (M := M) g₀ P b4PermB) W =
        operatorFieldApply (I := I) (M := M) g₀ 3 3
            (b4Phi (I := I) (M := M) g₀ P b4PermB) W₁ -
          operatorFieldApply (I := I) (M := M) g₀ 3 3
            (b4Phi (I := I) (M := M) g₀ P b4PermB) W₂ := by
    simpa only [W] using
      operatorFieldApplication_sub_right_local (I := I) (M := M) g₀
        (b4Phi (I := I) (M := M) g₀ P b4PermB) W₁ W₂
  have heq :
      metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g₀ g₁ g_bg P -
          metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g₀ g₂ g_bg P =
        (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3
            (b4Phi (I := I) (M := M) g₀ P b4PermA) W +
          (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3
            (b4Phi (I := I) (M := M) g₀ P b4PermB) W := by
    change
      ((1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3
            (b4Phi (I := I) (M := M) g₀ P b4PermA) W₁ +
          (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3
            (b4Phi (I := I) (M := M) g₀ P b4PermB) W₁) -
        ((1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3
            (b4Phi (I := I) (M := M) g₀ P b4PermA) W₂ +
          (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 3 3
            (b4Phi (I := I) (M := M) g₀ P b4PermB) W₂) = _
    calc
      _ = (1 / 2 : ℝ) •
            (operatorFieldApply (I := I) (M := M) g₀ 3 3
                (b4Phi (I := I) (M := M) g₀ P b4PermA) W₁ -
              operatorFieldApply (I := I) (M := M) g₀ 3 3
                (b4Phi (I := I) (M := M) g₀ P b4PermA) W₂) +
          (1 / 2 : ℝ) •
            (operatorFieldApply (I := I) (M := M) g₀ 3 3
                (b4Phi (I := I) (M := M) g₀ P b4PermB) W₁ -
              operatorFieldApply (I := I) (M := M) g₀ 3 3
                (b4Phi (I := I) (M := M) g₀ P b4PermB) W₂) := by
        module
      _ = _ := by rw [← hA, ← hB]
  have hraw := hact P W
  rw [heq]
  simpa only [b4Jet2, W, W₁, W₂] using hraw

private lemma b4_pk3_riemannianFiberNormSq_le (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (5 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 5 q (b4Pk3 (I := I) (M := M) g₀ P)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x) := by
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (5 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 5 q (b4Pk3 (I := I) (M := M) g₀ P)).toSection x)
      ≤ (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + q) x
            ((iteratedCovGrad (I := I) g₀ 2 4 q
              (slotExtend (I := I) (M := M) g₀ 1 3
                (slotExtend (I := I) (M := M) g₀ 0 2 P))).toSection x) :=
        riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 4
          (slotExtend (I := I) (M := M) g₀ 1 3 (slotExtend (I := I) (M := M) g₀ 0 2 P)) q x
    _ ≤ (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + q) x
            ((iteratedCovGrad (I := I) g₀ 1 3 q
              (slotExtend (I := I) (M := M) g₀ 0 2 P)).toSection x)) :=
        mul_le_mul_of_nonneg_left
          (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 3
            (slotExtend (I := I) (M := M) g₀ 0 2 P) q x) hfr_nn
    _ ≤ (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
            ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
        exact riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 2 P q x
    _ = (Module.finrank ℝ E : ℝ) ^ 3 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
            ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x) := by ring

lemma metricPerturbationLoweringCoefficient_antidiagonalTupleGridWindow_bound (g₀ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 5))
    {Λ₀ : ℝ} :
    ∃ Kphi : ℕ → ℝ, (∀ l, 0 ≤ Kphi l) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
            ((iteratedCovGrad (I := I) g₀ 3 3 l
              (b4Phi (I := I) (M := M) g₀ P σ)).toSection x) ≤
          Kphi l * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (l + 1) := by
  classical
  have hSΦ_ex : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 5 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 5 3 i
          (cometricDoubleTraceField (I := I) g₀ 3)).toSection x) ≤ K :=
    fun i => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 5 (3 + i)
      (iteratedCovGrad (I := I) g₀ 5 3 i (cometricDoubleTraceField (I := I) g₀ 3))
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  refine ⟨fun l => operatorFieldApplicationGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i') *
      (fr ^ 3 * (((l : ℝ) + 1) * (1 + Λ₀ ^ 2))), fun l => ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) l)
      (Finset.sum_nonneg (fun i' _ => hSΦ_nn i'))) ?_
    refine mul_nonneg (pow_nonneg hfr_nn 3) (mul_nonneg (by positivity) (by positivity))
  intro P hsup l x
  set bP : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) with hbP_def
  have hbP_nn : ∀ j, 0 ≤ bP j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  set antidiagonalTupleGridWindow : ℝ := Combinatorics.antidiagonalTupleGridWindow bP (l + 1) with hantidiagonalTupleGridWindow_def
  have hantidiagonalTupleGridWindow_one : (1 : ℝ) ≤ antidiagonalTupleGridWindow :=
    Combinatorics.one_le_antidiagonalTupleGridWindow bP hbP_nn (by omega)
  have hantidiagonalTupleGridWindow_nn : (0 : ℝ) ≤ antidiagonalTupleGridWindow := le_trans zero_le_one hantidiagonalTupleGridWindow_one
  have hbPw : ∀ q : ℕ, q < l + 1 → bP q ≤ (1 + Λ₀ ^ 2) * antidiagonalTupleGridWindow := by
    intro q hq
    cases q with
    | zero =>
        have h0 : bP 0 ≤ Λ₀ ^ 2 := by
          have h := hsup x
          simpa only [hbP_def, iteratedCovGrad_zero] using h
        calc bP 0 ≤ Λ₀ ^ 2 := h0
          _ = Λ₀ ^ 2 * 1 := by ring
          _ ≤ Λ₀ ^ 2 * antidiagonalTupleGridWindow := mul_le_mul_of_nonneg_left hantidiagonalTupleGridWindow_one (sq_nonneg Λ₀)
          _ ≤ (1 + Λ₀ ^ 2) * antidiagonalTupleGridWindow := by nlinarith only [hantidiagonalTupleGridWindow_nn]
    | succ m =>
        calc bP (m + 1) ≤ Combinatorics.antidiagonalTupleGrid bP (m + 1) :=
              b4_bP_le_grid bP hbP_nn m
          _ ≤ antidiagonalTupleGridWindow := Combinatorics.antidiagonalTupleGrid_le_window bP hbP_nn hq
          _ ≤ (1 + Λ₀ ^ 2) * antidiagonalTupleGridWindow := by nlinarith only [hantidiagonalTupleGridWindow_nn, sq_nonneg Λ₀]
  have hΦarm : ∀ i' : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 5 (3 + i') x
      ((iteratedCovGrad (I := I) g₀ 5 3 i'
        (reindexCoeffGen (I := I) (M := M) g₀ 5 3
          (cometricDoubleTraceField (I := I) g₀ 3) σ)).toSection x) ≤ SΦ i' := by
    intro i'
    rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 5 3
      (cometricDoubleTraceField (I := I) g₀ 3) σ i' x]
    exact hSΦ i' x
  have hqsum : ∀ i' : ℕ, (∑ q ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (5 + q) x
          ((iteratedCovGrad (I := I) g₀ 3 5 q
            (b4Pk3 (I := I) (M := M) g₀ P)).toSection x)) ≤
      fr ^ 3 * (((l : ℝ) + 1) * (1 + Λ₀ ^ 2)) * antidiagonalTupleGridWindow := by
    intro i'
    calc (∑ q ∈ Finset.range (l + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (5 + q) x
            ((iteratedCovGrad (I := I) g₀ 3 5 q
              (b4Pk3 (I := I) (M := M) g₀ P)).toSection x))
        ≤ ∑ q ∈ Finset.range (l + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (5 + q) x
              ((iteratedCovGrad (I := I) g₀ 3 5 q
                (b4Pk3 (I := I) (M := M) g₀ P)).toSection x) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
          exact fun q _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (5 + q) x _
      _ ≤ ∑ q ∈ Finset.range (l + 1), fr ^ 3 * bP q :=
          Finset.sum_le_sum (fun q _ => b4_pk3_riemannianFiberNormSq_le (I := I) (M := M) g₀ P q x)
      _ ≤ ∑ q ∈ Finset.range (l + 1), fr ^ 3 * ((1 + Λ₀ ^ 2) * antidiagonalTupleGridWindow) := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          exact mul_le_mul_of_nonneg_left (hbPw q (Finset.mem_range.mp hq))
            (pow_nonneg hfr_nn 3)
      _ = fr ^ 3 * (((l : ℝ) + 1) * (1 + Λ₀ ^ 2)) * antidiagonalTupleGridWindow := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hleib := riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ l 3 5 3
    (reindexCoeffGen (I := I) (M := M) g₀ 5 3 (cometricDoubleTraceField (I := I) g₀ 3) σ)
    (b4Pk3 (I := I) (M := M) g₀ P) x
  refine le_trans hleib ?_
  rw [show operatorFieldApplicationGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i') *
      (fr ^ 3 * (((l : ℝ) + 1) * (1 + Λ₀ ^ 2))) * antidiagonalTupleGridWindow =
      operatorFieldApplicationGdiag (E := E) l * ((∑ i' ∈ Finset.range (l + 1), SΦ i') *
        (fr ^ 3 * (((l : ℝ) + 1) * (1 + Λ₀ ^ 2)) * antidiagonalTupleGridWindow)) from by ring]
  refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) l)
  calc (∑ i' ∈ Finset.range (l + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 5 (3 + i') x
            ((iteratedCovGrad (I := I) g₀ 5 3 i'
              (reindexCoeffGen (I := I) (M := M) g₀ 5 3
                (cometricDoubleTraceField (I := I) g₀ 3) σ)).toSection x) *
          ∑ q ∈ Finset.range (l + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (5 + q) x
              ((iteratedCovGrad (I := I) g₀ 3 5 q
                (b4Pk3 (I := I) (M := M) g₀ P)).toSection x))
      ≤ ∑ i' ∈ Finset.range (l + 1),
          SΦ i' * (fr ^ 3 * (((l : ℝ) + 1) * (1 + Λ₀ ^ 2)) * antidiagonalTupleGridWindow) := by
        refine Finset.sum_le_sum (fun i' _ => ?_)
        refine mul_le_mul (hΦarm i') (hqsum i') ?_ (hSΦ_nn i')
        exact Finset.sum_nonneg (fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (5 + q) x _)
    _ = (∑ i' ∈ Finset.range (l + 1), SΦ i') *
          (fr ^ 3 * (((l : ℝ) + 1) * (1 + Λ₀ ^ 2)) * antidiagonalTupleGridWindow) := by rw [Finset.sum_mul]

private lemma b4_app_antidiagonalTupleGridWindow (g₀ gb : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 5))
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ₀ : ℝ} :
    ∃ Kap : ℕ → ℝ, (∀ n, 0 ≤ Kap n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n
              (operatorFieldApply (I := I) (M := M) g₀ 3 3 (b4Phi (I := I) (M := M) g₀ P σ)
                (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb))).toSection x) ≤
          Kap n * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2) := by
  classical
  obtain ⟨Kphi, hKphi_nn, hphi⟩ := metricPerturbationLoweringCoefficient_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ σ
  obtain ⟨Kwx, hKwx_nn, hwx⟩ := riemannianFiberNormSq_iteratedCovGrad_metricLoweredConnectionDifference_le_antidiagonalTupleGridWindow (I := I) (M := M) g₀ gb hδ₀
  refine ⟨fun n => operatorFieldApplicationGdiag (E := E) n *
      ∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        Kphi i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1),
    fun n => ?_, ?_⟩
  · refine mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) n) (Finset.sum_nonneg (fun i' _ =>
      Finset.sum_nonneg (fun l _ => ?_)))
    exact mul_nonneg (mul_nonneg (hKphi_nn i') (hKwx_nn l))
      (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (l + 1))
  intro g₁ P htie δ hδ_le hδ0 hδ hsup n x
  set bP : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) with hbP_def
  have hbP_nn : ∀ j, 0 ≤ bP j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hleib := operatorFieldApplication_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 3 3
    (b4Phi (I := I) (M := M) g₀ P σ) (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb) n x
  refine le_trans hleib ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) n)
  have hterm : ∀ i' ∈ Finset.range (n + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + i') x
          ((iteratedCovGrad (I := I) g₀ 3 3 i'
            (b4Phi (I := I) (M := M) g₀ P σ)).toSection x) *
        ∑ l ∈ Finset.range (n + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 3 l
              (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb)).toSection x) ≤
      ∑ l ∈ Finset.range (n + 1),
        (Kphi i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
          Combinatorics.antidiagonalTupleGridWindow bP (n + 2) := by
    intro i' hi'
    have hphii := hphi P hsup i' x
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun l hl => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun l _ _ => ?_))
    swap
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hKphi_nn i') (hKwx_nn l))
        (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (l + 1)))
        (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (n + 2))
    · have hwxl := hwx g₁ P htie hδ_le hδ0 hδ l x
      have hmul := Combinatorics.antidiagonalTupleGridWindow_mul_le bP hbP_nn i' (l + 1)
      have hmono := Combinatorics.antidiagonalTupleGridWindow_mono bP hbP_nn
        (show i' + (l + 1) + 1 ≤ n + 2 by rw [Finset.mem_range] at hl; omega)
      have hprod : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 3 i'
              (b4Phi (I := I) (M := M) g₀ P σ)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 3 l
              (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb)).toSection x) ≤
          (Kphi i' * Combinatorics.antidiagonalTupleGridWindow bP (i' + 1)) *
            (Kwx l * Combinatorics.antidiagonalTupleGridWindow bP (l + 2)) :=
        mul_le_mul hphii hwxl (riemannianFiberNormSq_nonneg _ _ _ _ _)
          (mul_nonneg (hKphi_nn i')
            (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (i' + 1)))
      have hwc_nn : 0 ≤ Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) :=
        Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (l + 1)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + i') x
              ((iteratedCovGrad (I := I) g₀ 3 3 i'
                (b4Phi (I := I) (M := M) g₀ P σ)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 3 l
                (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb)).toSection x)
          ≤ (Kphi i' * Combinatorics.antidiagonalTupleGridWindow bP (i' + 1)) *
              (Kwx l * Combinatorics.antidiagonalTupleGridWindow bP (l + 2)) := hprod
        _ = Kphi i' * Kwx l * (Combinatorics.antidiagonalTupleGridWindow bP (i' + 1) *
              Combinatorics.antidiagonalTupleGridWindow bP (l + 2)) := by ring
        _ ≤ Kphi i' * Kwx l * (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) *
              Combinatorics.antidiagonalTupleGridWindow bP (i' + (l + 1) + 1)) := by
            refine mul_le_mul_of_nonneg_left hmul (mul_nonneg (hKphi_nn i') (hKwx_nn l))
        _ ≤ Kphi i' * Kwx l * (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) *
              Combinatorics.antidiagonalTupleGridWindow bP (n + 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hKphi_nn i') (hKwx_nn l))
            exact mul_le_mul_of_nonneg_left hmono hwc_nn
        _ = (Kphi i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
              Combinatorics.antidiagonalTupleGridWindow bP (n + 2) := by ring
  calc ∑ i' ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 3 i'
              (b4Phi (I := I) (M := M) g₀ P σ)).toSection x) *
          ∑ l ∈ Finset.range (n + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 3 l
                (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb)).toSection x)
      ≤ ∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          (Kphi i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
            Combinatorics.antidiagonalTupleGridWindow bP (n + 2) :=
        Finset.sum_le_sum hterm
    _ = (∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          Kphi i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
          Combinatorics.antidiagonalTupleGridWindow bP (n + 2) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i' _ => by rw [Finset.sum_mul])

theorem metricConnectionDifferenceLoweredCoefficient_antidiagonalTupleGridWindow_bound (g₀ gb : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ₀ : ℝ} :
    ∃ Kmcd : ℕ → ℝ, (∀ n, 0 ≤ Kmcd n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n
              (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ gb)).toSection x) ≤
          Kmcd n * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2) := by
  classical
  obtain ⟨Kwx, hKwx_nn, hwx⟩ := riemannianFiberNormSq_iteratedCovGrad_metricLoweredConnectionDifference_le_antidiagonalTupleGridWindow (I := I) (M := M) g₀ gb hδ₀
  obtain ⟨KapA, hKapA_nn, hapA⟩ := b4_app_antidiagonalTupleGridWindow (I := I) (M := M) g₀ gb b4PermA hδ₀
  obtain ⟨KapB, hKapB_nn, hapB⟩ := b4_app_antidiagonalTupleGridWindow (I := I) (M := M) g₀ gb b4PermB hδ₀
  refine ⟨fun n => 2 * Kwx n + (KapA n + KapB n),
    fun n => by have := hKwx_nn n; have := hKapA_nn n; have := hKapB_nn n; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup n x
  have hwxn := hwx g₁ P htie hδ_le hδ0 hδ n x
  have hUbd := hapA g₁ P htie hδ_le hδ0 hδ hsup n x
  have hVbd := hapB g₁ P htie hδ_le hδ0 hδ hsup n x
  have hsec : ((iteratedCovGrad (I := I) g₀ 0 3 n
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ gb)).toSection x) =
      ((iteratedCovGrad (I := I) g₀ 0 3 n (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb)).toSection x) +
        ((1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 n
            (operatorFieldApply (I := I) (M := M) g₀ 3 3 (b4Phi (I := I) (M := M) g₀ P b4PermA)
              (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb))).toSection x) +
          (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 n
            (operatorFieldApply (I := I) (M := M) g₀ 3 3 (b4Phi (I := I) (M := M) g₀ P b4PermB)
              (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb))).toSection x)) := by
    rw [metricConnectionDifferenceLoweredCoefficient_expansion (I := I) (M := M) g₀ g₁ gb P htie, iteratedCovGrad_add, iteratedCovGrad_add,
      b4_iteratedCovGrad_smul, b4_iteratedCovGrad_smul, SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_add,
      SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_smul]
    rfl
  set WXs := (iteratedCovGrad (I := I) g₀ 0 3 n
    (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb)).toSection x with hWXs_def
  set Us := (iteratedCovGrad (I := I) g₀ 0 3 n
    (operatorFieldApply (I := I) (M := M) g₀ 3 3 (b4Phi (I := I) (M := M) g₀ P b4PermA)
      (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb))).toSection x with hUs_def
  set Vs := (iteratedCovGrad (I := I) g₀ 0 3 n
    (operatorFieldApply (I := I) (M := M) g₀ 3 3 (b4Phi (I := I) (M := M) g₀ P b4PermB)
      (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb))).toSection x with hVs_def
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ gb)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          (WXs + ((1 / 2 : ℝ) • Us + (1 / 2 : ℝ) • Vs)) := by rw [hsec]
    _ ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x WXs +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((1 / 2 : ℝ) • Us + (1 / 2 : ℝ) • Vs) :=
        riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + n) x _ _
    _ ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x WXs +
          2 * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
              ((1 / 2 : ℝ) • Us) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
              ((1 / 2 : ℝ) • Vs)) := by
        have h := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + n) x
          ((1 / 2 : ℝ) • Us) ((1 / 2 : ℝ) • Vs)
        linarith
    _ = 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x WXs +
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x Us +
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x Vs) := by
        rw [b4_riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (3 + n) x (1 / 2) Us,
          b4_riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (3 + n) x (1 / 2) Vs]
        ring
    _ ≤ 2 * (Kwx n * Combinatorics.antidiagonalTupleGridWindow
          (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2)) +
          (KapA n * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2) +
            KapB n * Combinatorics.antidiagonalTupleGridWindow
              (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2)) := by
        refine add_le_add ?_ (add_le_add hUbd hVbd)
        exact mul_le_mul_of_nonneg_left hwxn (by norm_num)
    _ = (2 * Kwx n + (KapA n + KapB n)) * Combinatorics.antidiagonalTupleGridWindow
          (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2) := by ring

theorem metricConnectionDifferenceLoweredCoefficient_l2_radius_free
    (g₀ gb : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ F : ℕ → ℝ, (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w =
            g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ gb)‖ ^ 2 ≤
          F i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kmcd, hKmcd, hmcd⟩ :=
    metricConnectionDifferenceLoweredCoefficient_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ gb hδ₀
  obtain ⟨Krf, hKrf, hgrid⟩ :=
    antidiagonalTupleGrid_integral_radiusFree
      (I := I) (M := M) g₀ hΛ₀0
  refine ⟨fun i => Kmcd i * ∑ k ∈ Finset.range (i + 2), Krf k,
    fun i => mul_nonneg (hKmcd i)
      (Finset.sum_nonneg fun k _ => hKrf k), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i
  have hAG : ∀ k : ℕ,
      MeasureTheory.Integrable
          (fun x => Combinatorics.antidiagonalTupleGrid
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k)
          (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
        (∫ x, Combinatorics.antidiagonalTupleGrid
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          Krf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) := by
    intro k
    have hExpand : (fun x => Combinatorics.antidiagonalTupleGrid
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k) =
        (fun x => ∑ nn ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple nn k,
            ∏ m : Fin nn,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      funext x
      rw [Combinatorics.antidiagonalTupleGrid]
    rw [hExpand]
    exact hgrid P hsup k
  have hwin_int : MeasureTheory.Integrable
      (fun x => Combinatorics.antidiagonalTupleGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 2))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    exact MeasureTheory.integrable_finset_sum _ fun k _ => (hAG k).1
  have hFint : MeasureTheory.Integrable
      (fun x => Kmcd i * Combinatorics.antidiagonalTupleGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 2))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    hwin_int.const_mul _
  have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g₀ 0 (3 + i)
    (iteratedCovGrad (I := I) g₀ 0 3 i
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ gb))
    _ hFint (fun x => hmcd g₁ P htie hδ_le hδ0 hδ hsup i x)
  rw [MeasureTheory.integral_const_mul] at hkey
  refine le_trans hkey ?_
  let S : ℝ := ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
  have hwin_bd : (∫ x, Combinatorics.antidiagonalTupleGridWindow
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 2)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      ∑ k ∈ Finset.range (i + 2),
        Krf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    rw [MeasureTheory.integral_finset_sum _ fun k _ => (hAG k).1]
    exact Finset.sum_le_sum fun k _ => (hAG k).2
  have hinner : (∑ k ∈ Finset.range (i + 2),
      Krf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2)) ≤
      (∑ k ∈ Finset.range (i + 2), Krf k) * (1 + S) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkS : ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2 ≤ S :=
      Finset.single_le_sum (fun j _ => sq_nonneg
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖) hk
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hkS) (hKrf k)
  calc
    Kmcd i * (∫ x, Combinatorics.antidiagonalTupleGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 2)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ Kmcd i * ∑ k ∈ Finset.range (i + 2),
          Krf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hwin_bd (hKmcd i)
    _ ≤ Kmcd i * ((∑ k ∈ Finset.range (i + 2), Krf k) * (1 + S)) :=
      mul_le_mul_of_nonneg_left hinner (hKmcd i)
    _ = (Kmcd i * ∑ k ∈ Finset.range (i + 2), Krf k) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      simp only [S]
      ring

theorem deTurckVectorFieldCovector_antidiagonalTupleGridWindow_bound (g₀ gb : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ KΩ : ℕ → ℝ, (∀ n, 0 ≤ KΩ n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 1 n
              (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gb)).toSection x) ≤
          KΩ n * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2) := by
  classical
  obtain ⟨Kcg, hKcg_nn, hcg⟩ := riemannianFiberNormSq_iteratedCovGrad_cometricCastG0_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kwx, hKwx_nn, hwx⟩ := riemannianFiberNormSq_iteratedCovGrad_metricLoweredConnectionDifference_le_antidiagonalTupleGridWindow (I := I) (M := M) g₀ gb hδ₀
  refine ⟨fun n => operatorFieldApplicationGdiag (E := E) n *
      ∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1),
    fun n => ?_, ?_⟩
  · refine mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) n) (Finset.sum_nonneg (fun i' _ =>
      Finset.sum_nonneg (fun l _ => ?_)))
    exact mul_nonneg (mul_nonneg (hKcg_nn i') (hKwx_nn l))
      (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (l + 1))
  intro g₁ P htie δ hδ_le hδ0 hδ n x
  set bP : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) with hbP_def
  have hbP_nn : ∀ j, 0 ≤ bP j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hleib := operatorFieldApplication_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 3 1
    (cometricCastG0 (I := I) g₀ g₁) (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb) n x
  refine le_trans hleib ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) n)
  have hterm : ∀ i' ∈ Finset.range (n + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
          ((iteratedCovGrad (I := I) g₀ 3 1 i' (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (n + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 3 l
              (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb)).toSection x) ≤
      ∑ l ∈ Finset.range (n + 1),
        (Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
          Combinatorics.antidiagonalTupleGridWindow bP (n + 2) := by
    intro i' hi'
    have hcgi := hcg g₁ P htie hδ_le hδ0 hδ i' x
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun l hl => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun l _ _ => ?_))
    swap
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hKcg_nn i') (hKwx_nn l))
        (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (l + 1)))
        (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (n + 2))
    · have hwxl := hwx g₁ P htie hδ_le hδ0 hδ l x
      have hmul := Combinatorics.antidiagonalTupleGridWindow_mul_le bP hbP_nn i' (l + 1)
      have hmono := Combinatorics.antidiagonalTupleGridWindow_mono bP hbP_nn
        (show i' + (l + 1) + 1 ≤ n + 2 by rw [Finset.mem_range] at hl; omega)
      have hprod : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i' (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 3 l
              (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb)).toSection x) ≤
          (Kcg i' * Combinatorics.antidiagonalTupleGridWindow bP (i' + 1)) *
            (Kwx l * Combinatorics.antidiagonalTupleGridWindow bP (l + 2)) :=
        mul_le_mul hcgi hwxl (riemannianFiberNormSq_nonneg _ _ _ _ _)
          (mul_nonneg (hKcg_nn i')
            (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (i' + 1)))
      have hwc_nn : 0 ≤ Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) :=
        Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (l + 1)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
              ((iteratedCovGrad (I := I) g₀ 3 1 i' (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 3 l
                (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb)).toSection x)
          ≤ (Kcg i' * Combinatorics.antidiagonalTupleGridWindow bP (i' + 1)) *
              (Kwx l * Combinatorics.antidiagonalTupleGridWindow bP (l + 2)) := hprod
        _ = Kcg i' * Kwx l * (Combinatorics.antidiagonalTupleGridWindow bP (i' + 1) *
              Combinatorics.antidiagonalTupleGridWindow bP (l + 2)) := by ring
        _ ≤ Kcg i' * Kwx l * (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) *
              Combinatorics.antidiagonalTupleGridWindow bP (i' + (l + 1) + 1)) := by
            refine mul_le_mul_of_nonneg_left hmul (mul_nonneg (hKcg_nn i') (hKwx_nn l))
        _ ≤ Kcg i' * Kwx l * (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1) *
              Combinatorics.antidiagonalTupleGridWindow bP (n + 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hKcg_nn i') (hKwx_nn l))
            exact mul_le_mul_of_nonneg_left hmono hwc_nn
        _ = (Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
              Combinatorics.antidiagonalTupleGridWindow bP (n + 2) := by ring
  calc ∑ i' ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i' (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
          ∑ l ∈ Finset.range (n + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 3 l
                (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gb)).toSection x)
      ≤ ∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          (Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
            Combinatorics.antidiagonalTupleGridWindow bP (n + 2) :=
        Finset.sum_le_sum hterm
    _ = (∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          Kcg i' * Kwx l * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l + 1)) *
          Combinatorics.antidiagonalTupleGridWindow bP (n + 2) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i' _ => by rw [Finset.sum_mul])

private lemma b4_vbPass_antidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ₀ : ℝ} :
    ∃ Kvp : ℕ → ℝ, (∀ n, 0 ≤ Kvp n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + n) x
            ((iteratedCovGrad (I := I) g₀ 2 4 n
              (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁)).toSection x) ≤
          Kvp n * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 3) := by
  classical
  obtain ⟨Kmcd, hKmcd_nn, hmcd⟩ := metricConnectionDifferenceLoweredCoefficient_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ g₀ hδ₀
  obtain ⟨KΩ, hKΩ_nn, hΩ⟩ := deTurckVectorFieldCovector_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ g₀ hδ₀
  obtain ⟨cip, hcip_nn, hip⟩ := riemannianFiberNormSq_iteratedCovGrad_ipLow_le (I := I) (M := M) g₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  refine ⟨fun n => operatorFieldApplicationGdiag (E := E) n *
      ∑ i' ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1),
        (fr * Kmcd i') * (cip q * ∑ m ∈ Finset.range (q + 1), KΩ m) *
          Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) (q + 1),
    fun n => ?_, ?_⟩
  · refine mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) n) (Finset.sum_nonneg (fun i' _ =>
      Finset.sum_nonneg (fun q _ => ?_)))
    exact mul_nonneg (mul_nonneg (mul_nonneg hfr_nn (hKmcd_nn i'))
      (mul_nonneg (hcip_nn q) (Finset.sum_nonneg (fun m _ => hKΩ_nn m))))
      (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg (i' + 1) (q + 1))
  intro g₁ P htie δ hδ_le hδ0 hδ hsup n x
  set bP : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) with hbP_def
  have hbP_nn : ∀ j, 0 ≤ bP j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  rw [lieCorrectionZeroVectorBundleLift_eq_ccOperatorFieldComp (I := I) (M := M) g₀ g₁]
  have hleib := riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ n 2 1 4 (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)
    (ipLowCc (I := I) (M := M) g₀ (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀)) x
  refine le_trans hleib ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) n)
  have hterm : ∀ i' ∈ Finset.range (n + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (4 + i') x
          ((iteratedCovGrad (I := I) g₀ 1 4 i'
            (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ q ∈ Finset.range (n + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (1 + q) x
            ((iteratedCovGrad (I := I) g₀ 2 1 q
              (ipLowCc (I := I) (M := M) g₀
                (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀))).toSection x) ≤
      ∑ q ∈ Finset.range (n + 1),
        ((fr * Kmcd i') * (cip q * ∑ m ∈ Finset.range (q + 1), KΩ m) *
          Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) (q + 1)) *
          Combinatorics.antidiagonalTupleGridWindow bP (n + 3) := by
    intro i' hi'
    have hheadi : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (4 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 4 i'
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)).toSection x) ≤
        fr * Kmcd i' * Combinatorics.antidiagonalTupleGridWindow bP (i' + 2) := by
      refine le_trans (riemannianFiberNormSq_iteratedCovGrad_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g₀ g₁ i' x) ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (hmcd g₁ P htie hδ_le hδ0 hδ hsup i' x) hfr_nn
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun q hq' => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun q _ _ => ?_))
    swap
    · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hfr_nn (hKmcd_nn i'))
        (mul_nonneg (hcip_nn q) (Finset.sum_nonneg (fun m _ => hKΩ_nn m))))
        (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg (i' + 1) (q + 1)))
        (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (n + 3))
    · have hipq : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (1 + q) x
          ((iteratedCovGrad (I := I) g₀ 2 1 q
            (ipLowCc (I := I) (M := M) g₀
              (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀))).toSection x) ≤
          (cip q * ∑ m ∈ Finset.range (q + 1), KΩ m) *
            Combinatorics.antidiagonalTupleGridWindow bP (q + 2) := by
        refine le_trans (hip (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀) q x) ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (hcip_nn q)
        calc ∑ m ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + m) x
                ((iteratedCovGrad (I := I) g₀ 0 1 m
                  (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀)).toSection x)
            ≤ ∑ m ∈ Finset.range (q + 1),
                KΩ m * Combinatorics.antidiagonalTupleGridWindow bP (m + 2) :=
              Finset.sum_le_sum (fun m _ => hΩ g₁ P htie hδ_le hδ0 hδ m x)
          _ ≤ ∑ m ∈ Finset.range (q + 1),
                KΩ m * Combinatorics.antidiagonalTupleGridWindow bP (q + 2) := by
              refine Finset.sum_le_sum (fun m hm => ?_)
              refine mul_le_mul_of_nonneg_left ?_ (hKΩ_nn m)
              exact Combinatorics.antidiagonalTupleGridWindow_mono bP hbP_nn
                (by rw [Finset.mem_range] at hm; omega)
          _ = (∑ m ∈ Finset.range (q + 1), KΩ m) *
                Combinatorics.antidiagonalTupleGridWindow bP (q + 2) := by
              rw [Finset.sum_mul]
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (4 + i') x
              ((iteratedCovGrad (I := I) g₀ 1 4 i'
                (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (1 + q) x
              ((iteratedCovGrad (I := I) g₀ 2 1 q
                (ipLowCc (I := I) (M := M) g₀
                  (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀))).toSection x)
          ≤ (fr * Kmcd i' * Combinatorics.antidiagonalTupleGridWindow bP (i' + 2)) *
              ((cip q * ∑ m ∈ Finset.range (q + 1), KΩ m) *
                Combinatorics.antidiagonalTupleGridWindow bP (q + 2)) :=
            mul_le_mul hheadi hipq (riemannianFiberNormSq_nonneg _ _ _ _ _)
              (mul_nonneg (mul_nonneg hfr_nn (hKmcd_nn i'))
                (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (i' + 2)))
        _ = (fr * Kmcd i') * (cip q * ∑ m ∈ Finset.range (q + 1), KΩ m) *
              (Combinatorics.antidiagonalTupleGridWindow bP (i' + 2) *
                Combinatorics.antidiagonalTupleGridWindow bP (q + 2)) := by ring
        _ ≤ (fr * Kmcd i') * (cip q * ∑ m ∈ Finset.range (q + 1), KΩ m) *
              (Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) (q + 1) *
                Combinatorics.antidiagonalTupleGridWindow bP ((i' + 1) + (q + 1) + 1)) := by
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (mul_nonneg hfr_nn (hKmcd_nn i'))
                (mul_nonneg (hcip_nn q) (Finset.sum_nonneg (fun m _ => hKΩ_nn m))))
            exact Combinatorics.antidiagonalTupleGridWindow_mul_le bP hbP_nn (i' + 1) (q + 1)
        _ ≤ (fr * Kmcd i') * (cip q * ∑ m ∈ Finset.range (q + 1), KΩ m) *
              (Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) (q + 1) *
                Combinatorics.antidiagonalTupleGridWindow bP (n + 3)) := by
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (mul_nonneg hfr_nn (hKmcd_nn i'))
                (mul_nonneg (hcip_nn q) (Finset.sum_nonneg (fun m _ => hKΩ_nn m))))
            refine mul_le_mul_of_nonneg_left ?_
              (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg (i' + 1) (q + 1))
            exact Combinatorics.antidiagonalTupleGridWindow_mono bP hbP_nn
              (by rw [Finset.mem_range] at hq'; omega)
        _ = ((fr * Kmcd i') * (cip q * ∑ m ∈ Finset.range (q + 1), KΩ m) *
              Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) (q + 1)) *
              Combinatorics.antidiagonalTupleGridWindow bP (n + 3) := by ring
  calc ∑ i' ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (4 + i') x
            ((iteratedCovGrad (I := I) g₀ 1 4 i'
              (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)).toSection x) *
          ∑ q ∈ Finset.range (n + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (1 + q) x
              ((iteratedCovGrad (I := I) g₀ 2 1 q
                (ipLowCc (I := I) (M := M) g₀
                  (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀))).toSection x)
      ≤ ∑ i' ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1),
          ((fr * Kmcd i') * (cip q * ∑ m ∈ Finset.range (q + 1), KΩ m) *
            Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) (q + 1)) *
            Combinatorics.antidiagonalTupleGridWindow bP (n + 3) :=
        Finset.sum_le_sum hterm
    _ = (∑ i' ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1),
          (fr * Kmcd i') * (cip q * ∑ m ∈ Finset.range (q + 1), KΩ m) *
            Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) (q + 1)) *
          Combinatorics.antidiagonalTupleGridWindow bP (n + 3) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i' _ => by rw [Finset.sum_mul])

private lemma b4_vb_antidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ₀ : ℝ} :
    ∃ Kvb : ℕ → ℝ, (∀ i, 0 ≤ Kvb i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁)).toSection x) ≤
          Kvb i * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 3) := by
  classical
  obtain ⟨Kcg, hKcg_nn, hcg⟩ := riemannianFiberNormSq_iteratedCovGrad_cometricCastG0_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kvp, hKvp_nn, hvp⟩ := b4_vbPass_antidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => 4 * (operatorFieldApplicationGdiag (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), ∑ q ∈ Finset.range (i + 1),
        (fr * Kcg i') * Kvp q * Combinatorics.antidiagonalTupleGridWindowMulConst i' (q + 2)),
    fun i => ?_, ?_⟩
  · refine mul_nonneg (by norm_num) (mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg (fun i' _ => Finset.sum_nonneg (fun q _ => ?_))))
    exact mul_nonneg (mul_nonneg (mul_nonneg hfr_nn (hKcg_nn i')) (hKvp_nn q))
      (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (q + 2))
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i x
  set bP : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) with hbP_def
  have hbP_nn : ∀ j, 0 ≤ bP j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  rw [lieCorrectionZeroVectorBundle_eq_ccOperatorFieldComp (I := I) (M := M) g₀ g₁, b4_iteratedCovGrad_smul]
  rw [show (((2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)
        (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁))).toSection x) =
      (2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)
          (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁))).toSection x) from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [b4_riemannianFiberNormSq_smul (I := I) (M := M) g₀ 2 (2 + i) x 2 _]
  have hmain : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)
          (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁))).toSection x) ≤
      (operatorFieldApplicationGdiag (E := E) i *
        ∑ i' ∈ Finset.range (i + 1), ∑ q ∈ Finset.range (i + 1),
          (fr * Kcg i') * Kvp q *
            Combinatorics.antidiagonalTupleGridWindowMulConst i' (q + 2)) *
        Combinatorics.antidiagonalTupleGridWindow bP (i + 3) := by
    have hleib := riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ i 2 4 2 (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)
      (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁) x
    refine le_trans hleib ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) i)
    have hterm : ∀ i' ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
            ((iteratedCovGrad (I := I) g₀ 4 2 i'
              (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)).toSection x) *
          ∑ q ∈ Finset.range (i + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + q) x
              ((iteratedCovGrad (I := I) g₀ 2 4 q
                (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁)).toSection x) ≤
        ∑ q ∈ Finset.range (i + 1),
          ((fr * Kcg i') * Kvp q *
            Combinatorics.antidiagonalTupleGridWindowMulConst i' (q + 2)) *
            Combinatorics.antidiagonalTupleGridWindow bP (i + 3) := by
      intro i' hi'
      have hheadi : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 2 i'
            (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)).toSection x) ≤
          fr * Kcg i' * Combinatorics.antidiagonalTupleGridWindow bP (i' + 1) := by
        refine le_trans (riemannianFiberNormSq_iteratedCovGrad_reindexedCometricDoubleTrace_le (I := I) (M := M) g₀ g₁ i' x) ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hcg g₁ P htie hδ_le hδ0 hδ i' x) hfr_nn
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum (fun q hq' => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun q _ _ => ?_))
      swap
      · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hfr_nn (hKcg_nn i')) (hKvp_nn q))
          (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (q + 2)))
          (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (i + 3))
      · have hvpq := hvp g₁ P htie hδ_le hδ0 hδ hsup q x
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
                ((iteratedCovGrad (I := I) g₀ 4 2 i'
                  (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + q) x
                ((iteratedCovGrad (I := I) g₀ 2 4 q
                  (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁)).toSection x)
            ≤ (fr * Kcg i' * Combinatorics.antidiagonalTupleGridWindow bP (i' + 1)) *
                (Kvp q * Combinatorics.antidiagonalTupleGridWindow bP (q + 3)) :=
              mul_le_mul hheadi hvpq (riemannianFiberNormSq_nonneg _ _ _ _ _)
                (mul_nonneg (mul_nonneg hfr_nn (hKcg_nn i'))
                  (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP_nn (i' + 1)))
          _ = (fr * Kcg i') * Kvp q *
                (Combinatorics.antidiagonalTupleGridWindow bP (i' + 1) *
                  Combinatorics.antidiagonalTupleGridWindow bP (q + 3)) := by ring
          _ ≤ (fr * Kcg i') * Kvp q *
                (Combinatorics.antidiagonalTupleGridWindowMulConst i' (q + 2) *
                  Combinatorics.antidiagonalTupleGridWindow bP (i' + (q + 2) + 1)) := by
              refine mul_le_mul_of_nonneg_left ?_
                (mul_nonneg (mul_nonneg hfr_nn (hKcg_nn i')) (hKvp_nn q))
              exact Combinatorics.antidiagonalTupleGridWindow_mul_le bP hbP_nn i' (q + 2)
          _ ≤ (fr * Kcg i') * Kvp q *
                (Combinatorics.antidiagonalTupleGridWindowMulConst i' (q + 2) *
                  Combinatorics.antidiagonalTupleGridWindow bP (i + 3)) := by
              refine mul_le_mul_of_nonneg_left ?_
                (mul_nonneg (mul_nonneg hfr_nn (hKcg_nn i')) (hKvp_nn q))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg i' (q + 2))
              exact Combinatorics.antidiagonalTupleGridWindow_mono bP hbP_nn
                (by rw [Finset.mem_range] at hq'; omega)
          _ = ((fr * Kcg i') * Kvp q *
                Combinatorics.antidiagonalTupleGridWindowMulConst i' (q + 2)) *
                Combinatorics.antidiagonalTupleGridWindow bP (i + 3) := by ring
    calc ∑ i' ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 4 2 i'
                (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ q ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + q) x
                ((iteratedCovGrad (I := I) g₀ 2 4 q
                  (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁)).toSection x)
        ≤ ∑ i' ∈ Finset.range (i + 1), ∑ q ∈ Finset.range (i + 1),
            ((fr * Kcg i') * Kvp q *
              Combinatorics.antidiagonalTupleGridWindowMulConst i' (q + 2)) *
              Combinatorics.antidiagonalTupleGridWindow bP (i + 3) :=
          Finset.sum_le_sum hterm
      _ = (∑ i' ∈ Finset.range (i + 1), ∑ q ∈ Finset.range (i + 1),
            (fr * Kcg i') * Kvp q *
              Combinatorics.antidiagonalTupleGridWindowMulConst i' (q + 2)) *
            Combinatorics.antidiagonalTupleGridWindow bP (i + 3) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i' _ => by rw [Finset.sum_mul])
  calc (2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)
            (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁))).toSection x)
      ≤ (2 : ℝ) ^ 2 * ((operatorFieldApplicationGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), ∑ q ∈ Finset.range (i + 1),
            (fr * Kcg i') * Kvp q *
              Combinatorics.antidiagonalTupleGridWindowMulConst i' (q + 2)) *
          Combinatorics.antidiagonalTupleGridWindow bP (i + 3)) :=
        mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = 4 * (operatorFieldApplicationGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), ∑ q ∈ Finset.range (i + 1),
            (fr * Kcg i') * Kvp q *
              Combinatorics.antidiagonalTupleGridWindowMulConst i' (q + 2)) *
          Combinatorics.antidiagonalTupleGridWindow bP (i + 3) := by ring

private lemma lieCorrectionZeroVB_perOrder_rf (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Flow : ℕ → ℝ, (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
          Flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kvb, hKvb_nn, hvb⟩ := b4_vb_antidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨K_rf, hK_rf_nn, hK_rf⟩ :=
    antidiagonalTupleGrid_integral_radiusFree (I := I) (M := M) g₀ hΛ₀0
  refine ⟨fun i => Kvb i * ∑ k ∈ Finset.range (i + 3), K_rf k,
    fun i => mul_nonneg (hKvb_nn i) (Finset.sum_nonneg (fun k _ => hK_rf_nn k)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i
  have hAG : ∀ k : ℕ,
      MeasureTheory.Integrable
          (fun x => Combinatorics.antidiagonalTupleGrid
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k)
          (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
        (∫ x, Combinatorics.antidiagonalTupleGrid
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) := by
    intro k
    have hExpand : (fun x => Combinatorics.antidiagonalTupleGrid
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k)
        = (fun x => ∑ nn ∈ Finset.range (k + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple nn k,
            ∏ m : Fin nn, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      funext x; rw [Combinatorics.antidiagonalTupleGrid]
    rw [hExpand]; exact hK_rf P hsup k
  have hwin_int : MeasureTheory.Integrable
      (fun x => Combinatorics.antidiagonalTupleGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    exact MeasureTheory.integrable_finset_sum _ (fun k _ => (hAG k).1)
  have hFint : MeasureTheory.Integrable
      (fun x => Kvb i * Combinatorics.antidiagonalTupleGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := hwin_int.const_mul _
  have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁)) _ hFint
    (fun x => hvb g₁ P htie hδ_le hδ0 hδ hsup i x)
  rw [MeasureTheory.integral_const_mul] at hkey
  refine le_trans hkey ?_
  set S' : ℝ := ∑ j ∈ Finset.range (i + 3),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS'_def
  have hS'_nn : 0 ≤ S' := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hwin_bd : (∫ x, Combinatorics.antidiagonalTupleGridWindow
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 3)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      ∑ k ∈ Finset.range (i + 3),
        K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    rw [MeasureTheory.integral_finset_sum _ (fun k _ => (hAG k).1)]
    exact Finset.sum_le_sum (fun k _ => (hAG k).2)
  have hinner : (∑ k ∈ Finset.range (i + 3),
      K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2)) ≤
      (∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S') := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    have hkS' : ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2 ≤ S' :=
      Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
        (fun j _ => sq_nonneg _) hk
    refine mul_le_mul_of_nonneg_left ?_ (hK_rf_nn k)
    linarith
  calc Kvb i * (∫ x, Combinatorics.antidiagonalTupleGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 3)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
      ≤ Kvb i * ∑ k ∈ Finset.range (i + 3),
          K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hwin_bd (hKvb_nn i)
    _ ≤ Kvb i * ((∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S')) :=
         mul_le_mul_of_nonneg_left hinner (hKvb_nn i)
    _ = (Kvb i * ∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S') := by ring

private lemma b4_amix_antidiagonalTupleGridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ₀ : ℝ} :
    ∃ Kam : ℕ → ℝ, (∀ n, 0 ≤ Kam n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 2 2 n
              (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          Kam n * Combinatorics.antidiagonalTupleGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 3) := by
  classical
  obtain ⟨Ctr2, hCtr2_nn, htr2⟩ := trace_grid_rf (I := I) (M := M) 2 g₀ hδ₀
  obtain ⟨Ctr3, hCtr3_nn, htr3⟩ := trace_grid_rf (I := I) (M := M) 3 g₀ hδ₀
  obtain ⟨Ctr4, hCtr4_nn, htr4⟩ := trace_grid_rf (I := I) (M := M) 4 g₀ hδ₀
  obtain ⟨Km0, hKm0_nn, hm0⟩ := metricConnectionDifferenceLoweredCoefficient_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ g₀ hδ₀
  obtain ⟨KmB, hKmB_nn, hmB⟩ := metricConnectionDifferenceLoweredCoefficient_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ g_bg hδ₀
  let K0 : ℕ → ℝ := fun n => (Module.finrank ℝ E : ℝ) ^ 2 * Km0 n
  let KB : ℕ → ℝ := fun n => (Module.finrank ℝ E : ℝ) ^ 3 * KmB n
  let Ktail : ℕ → ℝ := fun n => b4JoinK (E := E) 0 1 Ctr3 K0 n
  let Kmid : ℕ → ℝ := fun n => b4JoinK (E := E) 1 1 KB Ktail n
  let Ktr4 : ℕ → ℝ := fun n => b4JoinK (E := E) 0 2 Ctr4 Kmid n
  let Khalf : ℕ → ℝ := fun n => b4JoinK (E := E) 0 2 Ctr2 Ktr4 n
  have hK0_nn : ∀ n, 0 ≤ K0 n :=
    fun n => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 2) (hKm0_nn n)
  have hKB_nn : ∀ n, 0 ≤ KB n :=
    fun n => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3) (hKmB_nn n)
  have hKtail_nn : ∀ n, 0 ≤ Ktail n := fun n =>
    b4JoinK_nonneg (E := E) 0 1 Ctr3 K0 hCtr3_nn hK0_nn n
  have hKmid_nn : ∀ n, 0 ≤ Kmid n := fun n =>
    b4JoinK_nonneg (E := E) 1 1 KB Ktail hKB_nn hKtail_nn n
  have hKtr4_nn : ∀ n, 0 ≤ Ktr4 n := fun n =>
    b4JoinK_nonneg (E := E) 0 2 Ctr4 Kmid hCtr4_nn hKmid_nn n
  have hKhalf_nn : ∀ n, 0 ≤ Khalf n := fun n =>
    b4JoinK_nonneg (E := E) 0 2 Ctr2 Ktr4 hCtr2_nn hKtr4_nn n
  refine ⟨fun n => 16 * Khalf n, fun n => mul_nonneg (by norm_num) (hKhalf_nn n), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup n x
  set bP : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) with hbP_def
  have hbP_nn : ∀ j, 0 ≤ bP j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have htr2' (σ : Equiv.Perm (Fin 4)) (j : ℕ) :
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 4 2 j
            (reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 σ)).toSection x) ≤
        Ctr2 j * Combinatorics.antidiagonalTupleGridWindow bP (j + 1) := by
    simpa only [Combinatorics.antidiagonalTupleGridWindow] using
      htr2 g₁ P htie hδ_le hδ0 hδ σ j x
  have htr3' (j : ℕ) :
      riemannianFiberNormSq (I := I) (M := M) g₀ 5 (3 + j) x
          ((iteratedCovGrad (I := I) g₀ 5 3 j
            (reindexedPureTrace (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)).toSection x) ≤
        Ctr3 j * Combinatorics.antidiagonalTupleGridWindow bP (j + 1) := by
    simpa only [Combinatorics.antidiagonalTupleGridWindow] using
      htr3 g₁ P htie hδ_le hδ0 hδ lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour j x
  have htr4' (j : ℕ) :
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + j) x
          ((iteratedCovGrad (I := I) g₀ 6 4 j
            (reindexedPureTrace (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)).toSection x) ≤
        Ctr4 j * Combinatorics.antidiagonalTupleGridWindow bP (j + 1) := by
    simpa only [Combinatorics.antidiagonalTupleGridWindow] using
      htr4 g₁ P htie hδ_le hδ0 hδ lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne j x
  have hK0 (j : ℕ) :
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (5 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 5 j
            (slotExtendIter (I := I) (M := M) g₀ 0 3 2
              (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀))).toSection x) ≤
        K0 j * Combinatorics.antidiagonalTupleGridWindow bP (j + 2) := by
    have hslot := b4_slotIter_le (I := I) (M := M) g₀ 0 3 2
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) j x
    calc
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 3 j
                (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)).toSection x) := by
          simpa only [Nat.zero_add, Nat.reduceAdd] using hslot
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
            (Km0 j * Combinatorics.antidiagonalTupleGridWindow bP (j + 2)) :=
          mul_le_mul_of_nonneg_left
            (hm0 g₁ P htie hδ_le hδ0 hδ hsup j x) (pow_nonneg (Nat.cast_nonneg _) 2)
      _ = K0 j * Combinatorics.antidiagonalTupleGridWindow bP (j + 2) := by
          dsimp only [K0]
          ring
  have hKB (j : ℕ) :
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (6 + j) x
          ((iteratedCovGrad (I := I) g₀ 3 6 j
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3
              (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g_bg))).toSection x) ≤
        KB j * Combinatorics.antidiagonalTupleGridWindow bP (j + 2) := by
    have hslot := b4_slotIter_le (I := I) (M := M) g₀ 0 3 3
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g_bg) j x
    calc
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 3 *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 3 j
                (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
          simpa only [Nat.zero_add, Nat.reduceAdd] using hslot
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 3 *
            (KmB j * Combinatorics.antidiagonalTupleGridWindow bP (j + 2)) :=
          mul_le_mul_of_nonneg_left
            (hmB g₁ P htie hδ_le hδ0 hδ hsup j x) (pow_nonneg (Nat.cast_nonneg _) 3)
      _ = KB j * Combinatorics.antidiagonalTupleGridWindow bP (j + 2) := by
          dsimp only [KB]
          ring
  let tail : SmoothCcTensor g₀ 2 3 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀))
  have htail (j : ℕ) :
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 3 j tail).toSection x) ≤
        Ktail j * Combinatorics.antidiagonalTupleGridWindow bP (j + 2) := by
    simpa only [tail, Ktail, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd] using
      b4_join_antidiagonalTupleGridWindow (I := I) (M := M) (g := g₀) (p := 2) (a := 5) (b := 3)
        (u := 0) (v := 1) (n := j)
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀))
        x bP hbP_nn Ctr3 K0 hCtr3_nn hK0_nn htr3' hK0
  let mid : SmoothCcTensor g₀ 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g_bg)) tail
  have hmid (j : ℕ) :
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 6 j mid).toSection x) ≤
        Kmid j * Combinatorics.antidiagonalTupleGridWindow bP (j + 3) := by
    simpa only [mid, Kmid, Nat.add_assoc, Nat.reduceAdd] using
      b4_join_antidiagonalTupleGridWindow (I := I) (M := M) (g := g₀) (p := 2) (a := 3) (b := 6)
        (u := 1) (v := 1) (n := j)
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g_bg))
        tail x bP hbP_nn KB Ktail hKB_nn hKtail_nn hKB htail
  let traced4 : SmoothCcTensor g₀ 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) mid
  have htraced4 (j : ℕ) :
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 4 j traced4).toSection x) ≤
        Ktr4 j * Combinatorics.antidiagonalTupleGridWindow bP (j + 3) := by
    simpa only [traced4, Ktr4, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd] using
      b4_join_antidiagonalTupleGridWindow (I := I) (M := M) (g := g₀) (p := 2) (a := 6) (b := 4)
        (u := 0) (v := 2) (n := j)
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)
        mid x bP hbP_nn Ctr4 Kmid hCtr4_nn hKmid_nn htr4' hmid
  have hhalf (σ : Equiv.Perm (Fin 4)) (j : ℕ) :
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j
            (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g_bg σ)).toSection x) ≤
        Khalf j * Combinatorics.antidiagonalTupleGridWindow bP (j + 3) := by
    simpa only [lieCorrectionZeroMixedConnectionHalfExpansion, tail, mid, traced4, Khalf, Nat.add_zero, Nat.zero_add,
      Nat.add_assoc, Nat.reduceAdd] using
      b4_join_antidiagonalTupleGridWindow (I := I) (M := M) (g := g₀) (p := 2) (a := 4) (b := 2)
        (u := 0) (v := 2) (n := j)
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 σ)
        traced4 x bP hbP_nn Ctr2 Ktr4 hCtr2_nn hKtr4_nn (htr2' σ) htraced4
  have hsec :
      (iteratedCovGrad (I := I) g₀ 2 2 n
        (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg)).toSection x =
      (2 : ℝ) •
        ((iteratedCovGrad (I := I) g₀ 2 2 n
            (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g_bg lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)).toSection x +
          (iteratedCovGrad (I := I) g₀ 2 2 n
            (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g_bg
              (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))).toSection x) := by
    rw [lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g₀ g₁ g_bg, lieCorrectionZeroMixedConnectionExpansion, b4_iteratedCovGrad_smul,
      iteratedCovGrad_add, SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_add]
    rfl
  set As := (iteratedCovGrad (I := I) g₀ 2 2 n
    (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g_bg lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)).toSection x
  set Bs := (iteratedCovGrad (I := I) g₀ 2 2 n
    (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g_bg
      (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))).toSection x
  have hA := hhalf lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne n
  have hB := hhalf (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) n
  calc
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        = riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
            ((2 : ℝ) • (As + Bs)) := by rw [hsec]
    _ = 4 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x (As + Bs) := by
        rw [b4_riemannianFiberNormSq_smul (I := I) (M := M) g₀ 2 (2 + n) x 2 (As + Bs)]
        norm_num
    _ ≤ 4 * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x As +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x Bs) := by
        exact mul_le_mul_of_nonneg_left
          (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + n) x As Bs)
          (by norm_num)
    _ ≤ 4 * (2 * (Khalf n * Combinatorics.antidiagonalTupleGridWindow bP (n + 3)) +
          2 * (Khalf n * Combinatorics.antidiagonalTupleGridWindow bP (n + 3))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
        · exact mul_le_mul_of_nonneg_left hA (by norm_num)
        · exact mul_le_mul_of_nonneg_left hB (by norm_num)
    _ = (16 * Khalf n) * Combinatorics.antidiagonalTupleGridWindow bP (n + 3) := by ring

private lemma lieCorrectionZeroMixedConnection_perOrder_rf
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Flow : ℕ → ℝ, (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ), i ≤ a →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          Flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kam, hKam_nn, ham⟩ := b4_amix_antidiagonalTupleGridWindow (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨K_rf, hK_rf_nn, hK_rf⟩ :=
    antidiagonalTupleGrid_integral_radiusFree (I := I) (M := M) g₀ hΛ₀0
  refine ⟨fun i => Kam i * ∑ k ∈ Finset.range (i + 3), K_rf k,
    fun i => mul_nonneg (hKam_nn i) (Finset.sum_nonneg (fun k _ => hK_rf_nn k)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i hi
  have hAG : ∀ k : ℕ,
      MeasureTheory.Integrable
          (fun x => Combinatorics.antidiagonalTupleGrid
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k)
          (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
        (∫ x, Combinatorics.antidiagonalTupleGrid
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) := by
    intro k
    have hExpand : (fun x => Combinatorics.antidiagonalTupleGrid
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k)
        = (fun x => ∑ nn ∈ Finset.range (k + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple nn k,
            ∏ m : Fin nn, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      funext x
      rw [Combinatorics.antidiagonalTupleGrid]
    rw [hExpand]
    exact hK_rf P hsup k
  have hwin_int : MeasureTheory.Integrable
      (fun x => Combinatorics.antidiagonalTupleGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    exact MeasureTheory.integrable_finset_sum _ (fun k _ => (hAG k).1)
  have hFint : MeasureTheory.Integrable
      (fun x => Kam i * Combinatorics.antidiagonalTupleGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := hwin_int.const_mul _
  have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg)) _ hFint
    (fun x => ham g₁ P htie hδ_le hδ0 hδ hsup i x)
  rw [MeasureTheory.integral_const_mul] at hkey
  refine le_trans hkey ?_
  set S' : ℝ := ∑ j ∈ Finset.range (i + 3),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS'_def
  have hS'_nn : 0 ≤ S' := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hwin_bd : (∫ x, Combinatorics.antidiagonalTupleGridWindow
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 3)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      ∑ k ∈ Finset.range (i + 3),
        K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    rw [MeasureTheory.integral_finset_sum _ (fun k _ => (hAG k).1)]
    exact Finset.sum_le_sum (fun k _ => (hAG k).2)
  have hinner : (∑ k ∈ Finset.range (i + 3),
      K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2)) ≤
      (∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S') := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    have hkS' : ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2 ≤ S' :=
      Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
        (fun j _ => sq_nonneg _) hk
    refine mul_le_mul_of_nonneg_left ?_ (hK_rf_nn k)
    linarith
  calc
    Kam i * (∫ x, Combinatorics.antidiagonalTupleGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (i + 3)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
      ≤ Kam i * ∑ k ∈ Finset.range (i + 3),
          K_rf k * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hwin_bd (hKam_nn i)
    _ ≤ Kam i * ((∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S')) :=
        mul_le_mul_of_nonneg_left hinner (hKam_nn i)
    _ = (Kam i * ∑ k ∈ Finset.range (i + 3), K_rf k) * (1 + S') := by ring

private lemma lieCorrectionZeroVBAMix_perOrder_rf
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Flow : ℕ → ℝ, (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ), i ≤ a →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁)‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          Flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Fvb, hFvb_nn, hvb⟩ := lieCorrectionZeroVB_perOrder_rf (I := I) (M := M) g₀ hδ₀ hΛ₀0
  obtain ⟨Fam, hFam_nn, ham⟩ :=
    lieCorrectionZeroMixedConnection_perOrder_rf (I := I) (M := M) g₀ g_bg a ha_super hδ₀ hΛ₀0
  refine ⟨fun i => Fvb i + Fam i, fun i => add_nonneg (hFvb_nn i) (hFam_nn i), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup i hi
  have h1 := hvb g₁ P htie hδ_le hδ0 hδ hsup i
  have h2 := ham g₁ P htie hδ_le hδ0 hδ hsup i hi
  calc ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁)‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
      ≤ Fvb i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
          Fam i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := add_le_add h1 h2
    _ = (Fvb i + Fam i) * (1 + ∑ j ∈ Finset.range (i + 3),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring

theorem lieCorrectionZeroField_per_order_l2_radius_free
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Atop : ℕ → ℝ, (∀ i, 0 ≤ Atop i) ∧ ∃ Alow : ℕ → ℝ, (∀ i, 0 ≤ Alow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((symmS (I := I) (M := M) g₀ T).toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ) (_hi : i ≤ a),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          Atop i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
              (symmS (I := I) (M := M) g₀ T)‖ ^ 2 +
          Alow i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) := by
  classical
  obtain ⟨Kb_top, hKb_top_nn, Fb, hFb_nn, hbase⟩ :=
    lieCorrectionZeroBase_perOrder_rf (I := I) (M := M) g₀ a hδ₀ hΛ₀0
  obtain ⟨Fd, hFd_nn, hdiff⟩ :=
    lieCorrectionZeroDiff_perOrder_rf (I := I) (M := M) g₀ g_bg hδ₀ hΛ₀0
  obtain ⟨Fvm, hFvm_nn, hvbamix⟩ :=
    lieCorrectionZeroVBAMix_perOrder_rf (I := I) (M := M) g₀ g_bg a ha_super hδ₀ hΛ₀0
  obtain ⟨Fr, hFr_nn, hriem⟩ :=
    lieCorrectionZeroRiem_perOrder_rf (I := I) (M := M) g₀ a hδ₀ hΛ₀0
  refine ⟨fun i => 5 * Kb_top + 5 * (Fb i + Fd i + Fvm i + Fr i),
    fun i => by
      have := hKb_top_nn; have := hFb_nn i; have := hFd_nn i
      have := hFvm_nn i; have := hFr_nn i
      linarith,
    fun i => 5 * (Fb i + Fd i + Fvm i + Fr i),
    fun i => by
      have := hFb_nn i; have := hFd_nn i; have := hFvm_nn i; have := hFr_nn i
      linarith, ?_⟩
  intro g₁ T δ hδ_le hδ0 hδ htie hsup i hi
  set P : SmoothCcTensor g₀ 0 2 := symmS (I := I) (M := M) g₀ T with hP_def
  have htie' : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    rw [hP_def,
      DifferentialGeometry.Analysis.Spectral.ccTensorBilinSymm_symmS_apply
        (I := I) (M := M) g₀ T y v w]
    exact htie y v w
  have hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ := by
    rw [hP_def]
    exact DifferentialGeometry.Analysis.Spectral.gFibreOpBound_symmS
      (I := I) (M := M) g₀ T hδ
  have hb := hbase g₁ P htie' hδ_le hδ0 hδ' hsup i hi
  have hd := hdiff g₁ P htie' hδ_le hδ0 hδ' hsup i
  have hvm := hvbamix g₁ P htie' hδ_le hδ0 hδ' hsup i hi
  have hr := hriem g₁ P htie' hδ_le hδ0 hδ' hsup i (by omega)
  have hfield : lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg =
      lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀ +
        (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg - lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀) +
        lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁ +
        lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg +
        lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁ := by
    rw [lieCorrectionZero_decomp (I := I) (M := M) g₀ g₁ g_bg]
    abel
  have hgrad : iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg) =
      iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀) +
        iteratedCovGrad (I := I) g₀ 2 2 i
          (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg - lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀) +
        iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁) +
        iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg) +
        iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁) := by
    rw [hfield, iteratedCovGrad_add, iteratedCovGrad_add, iteratedCovGrad_add,
      iteratedCovGrad_add]
  have htri : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖ +
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg - lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖ +
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁)‖ +
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg)‖ +
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁)‖ := by
    rw [hgrad]
    have t1 := norm_add_le
      (iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀) +
        iteratedCovGrad (I := I) g₀ 2 2 i
          (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg - lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀) +
        iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁) +
        iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg))
      (iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁))
    have t2 := norm_add_le
      (iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀) +
        iteratedCovGrad (I := I) g₀ 2 2 i
          (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg - lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀) +
        iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁))
      (iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg))
    have t3 := norm_add_le
      (iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀) +
        iteratedCovGrad (I := I) g₀ 2 2 i
          (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg - lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀))
      (iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁))
    have t4 := norm_add_le
      (iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀))
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg - lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀))
    linarith
  have hsq := (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans
    (DifferentialGeometry.Analysis.sq_sum_five_le
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg -
          lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁)‖
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg)‖
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁)‖)
  have hsplit3 : (∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) =
      (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
    rw [show i + 3 = (i + 2) + 1 from rfl, Finset.sum_range_succ]
  rw [hsplit3] at hb hd hvm hr
  calc ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
      ≤ 5 * (‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg -
              lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁)‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 2 2 i (lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁)‖ ^ 2) := hsq
    _ ≤ 5 * ((Kb_top * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
            Fb i * (1 + ((∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2))) +
          Fd i * (1 + ((∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2)) +
          Fvm i * (1 + ((∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2)) +
          Fr i * (1 + ((∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2))) := by
        linarith
    _ = (5 * Kb_top + 5 * (Fb i + Fd i + Fvm i + Fr i)) *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 +
        (5 * (Fb i + Fd i + Fvm i + Fr i)) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring

theorem lieCorrectionZeroField_summed_l2_radius_free
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Klow : ℝ, 0 ≤ Klow ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w),
        ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          Ktop * (∑ j ∈ Finset.range (a + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) +
          Klow * (1 + ∑ j ∈ Finset.range (a + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) := by
  classical
  obtain ⟨Atop, hAtop_nn, Alow, hAlow_nn, hper⟩ :=
    lieCorrectionZeroField_per_order_l2_radius_free (I := I) (M := M) g₀ g_bg a ha_super hδ₀
      (Λ₀ := max 0 ((Module.finrank ℝ E : ℝ) * δ₀)) (le_max_left _ _)
  refine ⟨∑ i ∈ Finset.range (a + 1), Atop i,
    Finset.sum_nonneg (fun i _ => hAtop_nn i), ?_⟩
  refine ⟨∑ i ∈ Finset.range (a + 1), Alow i,
    Finset.sum_nonneg (fun i _ => hAlow_nn i), ?_⟩
  intro g₁ T δ hδ_le hδ htie
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ T x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hδ₀0 : 0 ≤ δ₀ := le_trans hδ0 hδ_le
    have hmaxeq : max 0 ((Module.finrank ℝ E : ℝ) * δ₀) = (Module.finrank ℝ E : ℝ) * δ₀ :=
      max_eq_right (mul_nonneg (Nat.cast_nonneg _) hδ₀0)
    have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((symmS (I := I) (M := M) g₀ T).toSection x) ≤
        (max 0 ((Module.finrank ℝ E : ℝ) * δ₀)) ^ 2 := by
      intro x
      rw [hmaxeq]
      exact riemannianFiberNormSq_symmS_zero_le_fibreSmall (I := I) (M := M) g₀ hδ₀0 T hδ_le hδ0 hδ x
    have hper' : ∀ i, i ≤ a →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          Atop i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
              (symmS (I := I) (M := M) g₀ T)‖ ^ 2 +
          Alow i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) :=
      fun i hi => hper g₁ T hδ_le hδ0 hδ htie hsup i hi
    set w : ℕ → ℝ := fun j =>
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2 with hw
    have hw_nn : ∀ j, 0 ≤ w j := fun j => sq_nonneg _
    calc ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
        ≤ ∑ i ∈ Finset.range (a + 1),
            (Atop i * w (i + 2) + Alow i * (1 + ∑ j ∈ Finset.range (i + 2), w j)) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact hper' i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      _ = (∑ i ∈ Finset.range (a + 1), Atop i * w (i + 2)) +
            ∑ i ∈ Finset.range (a + 1), Alow i * (1 + ∑ j ∈ Finset.range (i + 2), w j) := by
          rw [Finset.sum_add_distrib]
      _ ≤ (∑ i ∈ Finset.range (a + 1), Atop i) * (∑ j ∈ Finset.range (a + 3), w j) +
            (∑ i ∈ Finset.range (a + 1), Alow i) * (1 + ∑ j ∈ Finset.range (a + 2), w j) := by
          refine add_le_add ?_ ?_
          · calc ∑ i ∈ Finset.range (a + 1), Atop i * w (i + 2)
                ≤ ∑ i ∈ Finset.range (a + 1), Atop i * (∑ j ∈ Finset.range (a + 3), w j) := by
                  refine Finset.sum_le_sum (fun i hi => ?_)
                  have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
                  refine mul_le_mul_of_nonneg_left ?_ (hAtop_nn i)
                  exact Finset.single_le_sum (f := fun j => w j) (fun j _ => hw_nn j)
                    (Finset.mem_range.mpr (by omega))
              _ = (∑ i ∈ Finset.range (a + 1), Atop i) * (∑ j ∈ Finset.range (a + 3), w j) := by
                  rw [Finset.sum_mul]
          · calc ∑ i ∈ Finset.range (a + 1), Alow i * (1 + ∑ j ∈ Finset.range (i + 2), w j)
                ≤ ∑ i ∈ Finset.range (a + 1),
                    Alow i * (1 + ∑ j ∈ Finset.range (a + 2), w j) := by
                  refine Finset.sum_le_sum (fun i hi => ?_)
                  have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
                  refine mul_le_mul_of_nonneg_left ?_ (hAlow_nn i)
                  have hsub : Finset.range (i + 2) ⊆ Finset.range (a + 2) := by
                    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
                  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw_nn j)
                  linarith
              _ = (∑ i ∈ Finset.range (a + 1), Alow i) *
                    (1 + ∑ j ∈ Finset.range (a + 2), w j) := by
                  rw [Finset.sum_mul]
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hL0 : ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (lieCorrectionZeroField (I := I) (M := M) g₀ g₁ g_bg)‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]; ring
    rw [hL0]
    have h1 : 0 ≤ (∑ i ∈ Finset.range (a + 1), Atop i) *
        (∑ j ∈ Finset.range (a + 3),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) :=
      mul_nonneg (Finset.sum_nonneg (fun i _ => hAtop_nn i))
        (Finset.sum_nonneg (fun j _ => sq_nonneg _))
    have h2 : 0 ≤ (∑ i ∈ Finset.range (a + 1), Alow i) *
        (1 + ∑ j ∈ Finset.range (a + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) := by
      refine mul_nonneg (Finset.sum_nonneg (fun i _ => hAlow_nn i)) ?_
      have : 0 ≤ ∑ j ∈ Finset.range (a + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2 :=
        Finset.sum_nonneg (fun j _ => sq_nonneg _)
      linarith
    linarith


end DifferentialGeometry.Integral.Connection

end
