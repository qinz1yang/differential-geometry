import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionTotalDecomposition
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open LieCorr0Core
open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
  (chartRiemannTensor extChartAt_target_subset_interior_of_boundaryless)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad unitModel smoothCcTensor_ext_of_unitModel unitTensor pathIntegralCoeffField
  pathIntegralCoeffField_appCc_eq pathIntegralCoeffField_toSection linearizedRicciThreeArmHjoint
  linearizedRicciThreeArmHcont linearizedRicciThreeArmHjoint_zero
  exists_linearizedRicci_threeArm_coeffFields ricciTensor_realize_sub_eq_threeArm_appCc
  linearizedRicciArm0Field linearizedRicciArm1Field linearizedRicciArm2FieldLichnerowicz
  linearizedRicciArm0BaseCoeff linearizedRicciArm0CorrField linearizedRicciArm1BaseCoeff
  linearizedRicciArm1CorrField ricciArmPrincipalCoeff traceHessianCoeff
  linearizedRicci_arm0Field_jointSmooth linearizedRicci_arm1Field_jointSmooth
  linearizedRicci_arm2FieldLichnerowicz_jointSmooth ricciArmOrder1KoszulCoeff
  exists_arm1Koszul_realizedFam_rfns_ballUniform continuousBilinearMap_basis_expand
  unitModel_basis_expand_two unitModel_eq_ccTensorBilin_local appCc_zero_left_local ccTensor02Symm
  symmS_sub ccTensorBilin_symmS iteratedCovGrad_symmS_eq domDomCongrSection
  riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection)
open DifferentialGeometry.PDE.DeTurck (deTurckVF)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedSmallSet realizedSmallSet_isOpen Icc_subset_realizedSmallSet linearizedRicciAt
  ricciTensor_realized_sub_eq_integral_linearizedRicci linearizedRicciAt_eq_deriv_chartSum_on_Ioo
  realizedRicciChartSum jointContMDiff_toModel_continuous_slice
  hasDerivAt_realizedRicciChartSum_general realizedFam)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (symmAbsorbedCoeff symmAbsorbedCoeff_appCc_eq exists_iteratedCovGrad_unitModel_domDomCongrSection
  symmAbsorbedCoeff_riemannianFiberNormSq_le symmAbsorbedCoeff_jet_le)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private local instance instCompleteSpaceE_tame : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

section LieCorr0BoundsAll

set_option backward.isDefEq.respectTransparency false

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieWEndo deTurckLieWEndo_apply deTurckLieWEndo_homSection_contMDiff deTurckVFCovDeriv
  connDiffOp_homSection_contMDiff metricConnDiffLoweredFib metricConnDiffLoweredFib_toModel
  metricConnDiffLoweredFib_contMDiff domDomCongrFibRank domDomCongrFibRank_apply
  tensor0SProdKappaFib tensor0SProdKappaFib_apply)
open DifferentialGeometry.Analysis.Spectral.DeTurck
  (cometricDoubleTraceFib cometricDoubleTraceFib_toModel cometricDoubleTraceFib_contMDiff)

section LieCorr0BoundsF1

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma lc0b_rfns_neg (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0b_icg_sub (g : SmoothRiemannianMetric I M) (r s q : ℕ)
    (A B : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s q (A - B) =
      iteratedCovGrad (I := I) g r s q A - iteratedCovGrad (I := I) g r s q B := by
  rw [sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_neg, sub_eq_add_neg]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_normSq_icg_sub_le (g : SmoothRiemannianMetric I M) (r s q : ℕ)
    (A B : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r s q (A - B)‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g r s q A‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g r s q B‖ ^ 2 := by
  have h := lc0b_normSq_icg_add_le (I := I) (M := M) g r s q A (-B)
  rw [show A + -B = A - B from (sub_eq_add_neg A B).symm] at h
  rw [iteratedCovGrad_neg, norm_neg] at h
  exact h

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_rfns_toSection_sub_le (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x ((A - B).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x (A.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x (B.toSection x) := by
  rw [show (A - B).toSection x = A.toSection x + (-(B.toSection x)) from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g r s x _ _) ?_
  rw [lc0b_rfns_neg (I := I) (M := M) g r s x (B.toSection x)]

omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_rfns_icg_reindex_eq (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ : Equiv.Perm (Fin r)) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r (s + q) x
        ((iteratedCovGrad (I := I) g₀ r s q
          (reindexCoeffGen (I := I) (M := M) g₀ r s R σ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + q) x
        ((iteratedCovGrad (I := I) g₀ r s q R).toSection x) := by
  rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M) g₀ r s R σ q]
  rw [reindexCoeffGen_toSection]
  exact riemannianFiberNormSq_reindexCoeffFibGen (I := I) (M := M) g₀ r (s + q) x σ _

omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_normSq_icg_reindex_eq (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ : Equiv.Perm (Fin r)) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ r s q (reindexCoeffGen (I := I) (M := M) g₀ r s R σ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ r s q R‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact lc0b_rfns_icg_reindex_eq (I := I) (M := M) g₀ r s R σ q x

lemma lc0b_rfns_icg_slotExtendIter_le (g₀ : SmoothRiemannianMetric I M)
    (b₀ s₀ : ℕ) (w : ℕ) (K : SmoothCcTensor g₀ b₀ s₀) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (b₀ + w) ((s₀ + w) + q) x
        ((iteratedCovGrad (I := I) g₀ (b₀ + w) (s₀ + w) q
          (slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ w *
        riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + q) x
          ((iteratedCovGrad (I := I) g₀ b₀ s₀ q K).toSection x) := by
  induction w with
  | zero =>
      rw [pow_zero, one_mul]
      exact le_rfl
  | succ w ih =>
      have hstep := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ (b₀ + w) (s₀ + w)
        (slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K) q x
      have hmul : (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ (b₀ + w) ((s₀ + w) + q) x
            ((iteratedCovGrad (I := I) g₀ (b₀ + w) (s₀ + w) q
              (slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K)).toSection x) ≤
          (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) ^ w *
            riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + q) x
              ((iteratedCovGrad (I := I) g₀ b₀ s₀ q K).toSection x)) :=
        mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg _)
      refine le_trans hstep (le_trans hmul (le_of_eq ?_))
      rw [pow_succ]
      ring

lemma lc0b_normSq_icg_slotExtendIter_le (g₀ : SmoothRiemannianMetric I M)
    (b₀ s₀ : ℕ) (w : ℕ) (K : SmoothCcTensor g₀ b₀ s₀) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ (b₀ + w) (s₀ + w) q
        (slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ w * ‖iteratedCovGrad (I := I) g₀ b₀ s₀ q K‖ ^ 2 :=
  lc0b_normSq_le_scaled_of_pointwise (I := I) (M := M) g₀ (b₀ + w) ((s₀ + w) + q) b₀ (s₀ + q)
    (iteratedCovGrad (I := I) g₀ (b₀ + w) (s₀ + w) q
      (slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K))
    (iteratedCovGrad (I := I) g₀ b₀ s₀ q K)
    ((Module.finrank ℝ E : ℝ) ^ w) (by positivity)
    (fun x => lc0b_rfns_icg_slotExtendIter_le (I := I) (M := M) g₀ b₀ s₀ w K q x)

lemma lc0b_NEndoIns_decomp (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg) =
      lc0CdVField (I := I) (M := M) g₀ g₁ g₀ - lc0CdVField (I := I) (M := M) g₀ g₁ g_bg
        - DifferentialGeometry.PDE.RicciFlow.deTurckLieWEndoInsert
            (I := I) (M := M) g₀ g₁ g₀ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  beta_reduce
  have hRHS : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
      ((lc0CdVField (I := I) (M := M) g₀ g₁ g₀ - lc0CdVField (I := I) (M := M) g₀ g₁ g_bg
        - DifferentialGeometry.PDE.RicciFlow.deTurckLieWEndoInsert
            (I := I) (M := M) g₀ g₁ g₀).toSection x)) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0CdVField (I := I) (M := M) g₀ g₁ g₀).toSection x) om) -
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0CdVField (I := I) (M := M) g₀ g₁ g_bg).toSection x) om) -
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (DifferentialGeometry.PDE.RicciFlow.deTurckLieWEndoInsert
          (I := I) (M := M) g₀ g₁ g₀).toSection x) om) := rfl
  rw [hRHS]
  rw [lc0b_cdV_fiber (I := I) (M := M) g₀ g₁ g₀ x om,
    lc0b_cdV_fiber (I := I) (M := M) g₀ g₁ g_bg x om]
  have hWfib : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
      (DifferentialGeometry.PDE.RicciFlow.deTurckLieWEndoInsert
        (I := I) (M := M) g₀ g₁ g₀).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x (deTurckLieWEndo (I := I) g₁ g₀ x) om := rfl
  rw [hWfib]
  have hLHS : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (lieCorr0NEndo (I := I) g₀ g₁ g_bg x) om := rfl
  rw [hLHS]
  rw [Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sub_apply]
  rw [slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval,
    slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]
  rw [lc0b_toModel_om_single (I := I) (M := M) x om _,
    lc0b_toModel_om_single (I := I) (M := M) x om _,
    lc0b_toModel_om_single (I := I) (M := M) x om _,
    lc0b_toModel_om_single (I := I) (M := M) x om _]
  rw [Function.update_self, Function.update_self, Function.update_self, Function.update_self]
  rw [show lieCorr0NEndo (I := I) g₀ g₁ g_bg x (w 0) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (w 0)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x) (w 0)
        - deTurckLieWEndo (I := I) g₁ g₀ x (w 0) from by
    rw [lieCorr0NEndo]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]]
  rw [show cotangentToDual (I := I) (x := x) om
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (w 0)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x) (w 0)
        - deTurckLieWEndo (I := I) g₁ g₀ x (w 0)) =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (w 0))
      - cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x) (w 0))
      - cotangentToDual (I := I) (x := x) om
          (deTurckLieWEndo (I := I) g₁ g₀ x (w 0)) from by
    rw [show cotangentToDual (I := I) (x := x) om =
        (cotangentToDualLinear (I := I) (x := x) om : TangentSpace I x →ₗ[ℝ] ℝ) from rfl]
    rw [map_sub, map_sub]]

end LieCorr0BoundsF1

end LieCorr0BoundsAll

end DifferentialGeometry.Analysis.Spectral

end
