import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionMixedFeedBounds
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Spectral
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

section LieCorr0BoundsF4

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound_abs realizedFam_inner_of_mem)

lemma lc0b_normSq_icg_bothCongr_eq (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ' : Equiv.Perm (Fin r)) (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g₀ r s) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ r s q
        (reindexCoeffGen (I := I) (M := M) g₀ r s
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ R) σ')‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ r s q R‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ r s σ' σ R q x

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
lemma lc0b_gFibreOpBound_mono (g₀ : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ δ' : ℝ} (hle : δ ≤ δ')
    (hb : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) :
    metricCauchySchwarzBound (I := I) (M := M) g₀ h δ' := by
  intro x v w
  refine le_trans (hb x v w) ?_
  have h1 : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle h1) h2
  linarith

theorem lieCorr0Field_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ P i := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨Λvb, Fvb, hΛvb_nn, hFvb_nn, hvb⟩ :=
    lc0b_vbField_feed (I := I) (M := M) g₀ a ha_super hR hδ₁_lt
  obtain ⟨Λam, Fam, hΛam_nn, hFam_nn, ham⟩ :=
    lc0b_amixField_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₁_lt
  obtain ⟨Λri, Fri, hΛri_nn, hFri_nn, hri⟩ :=
    lc0b_riemField_feed (I := I) (M := M) g₀ a ha_super hR hδ₁_lt
  obtain ⟨Λc0, Fc0, hΛc0_nn, hFc0_nn, hc0⟩ :=
    lc0b_cdVField_feed (I := I) (M := M) g₀ g₀ a ha_super hR hδ₁_lt
  obtain ⟨Λcb, Fcb, hΛcb_nn, hFcb_nn, hcb⟩ :=
    lc0b_cdVField_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₁_lt
  obtain ⟨PW, hPW_nn, hPW⟩ :=
    deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_ballUniform
      (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => 8 * (4 * (fr * (4 * Fc0 i + 4 * Fcb i + 2 * PW i)))
      + 8 * Fvb i + 4 * Fam i + 2 * Fri i,
    fun i => by
      have h1 := hFc0_nn i
      have h2 := hFcb_nn i
      have h3 := hPW_nn i
      have h4 := hFvb_nn i
      have h5 := hFam_nn i
      have h6 := hFri_nn i
      have hin : 0 ≤ fr * (4 * Fc0 i + 4 * Fcb i + 2 * PW i) := by positivity
      linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁_def
  set Pc : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s with hPc_def
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδs_raw : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc)
      (|1 - s| * δ' + |s| * δ) := by
    rw [hPc_def]
    exact convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  set δP : ℝ := max (|1 - s| * δ' + |s| * δ) 0 with hδP_def
  have hδP_nn : 0 ≤ δP := le_max_right _ _
  have hδP_bound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc)
    δP :=
    lc0b_gFibreOpBound_mono (I := I) (M := M) g₀ _ (le_max_left _ _) hδs_raw
  have hδP_le : δP ≤ δ₁ := by
    refine max_le ?_ hδ₁_nn
    rw [abs_of_nonneg h1ms, abs_of_nonneg hs0]
    have h1 : δ' ≤ δ₁ := le_trans hδ'_le (le_max_left _ _)
    have h2 : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    nlinarith [h1, h2]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ Pc y v w := by
    intro y v w
    rw [hg₁_def, hPc_def]
    exact realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
      (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j Pc
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [hPc_def]
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, lc0b_icg_smul, lc0b_icg_smul]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  obtain ⟨hvb0, hvbL2⟩ := hvb g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨ham0, hamL2⟩ := ham g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨hri0, hriL2⟩ := hri g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨hc00, hc0L2⟩ := hc0 g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨hcb0, hcbL2⟩ := hcb g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  have hWi : ‖iteratedCovGrad (I := I) g₀ 1 1 i
      (DifferentialGeometry.PDE.RicciFlow.deTurckLieWEndoInsert
        (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤ PW i := by
    rw [hg₁_def]
    exact hPW T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  have hdecomp := lc0b_total_decomp (I := I) (M := M) g₀ g₁ g_bg
  have hsplit : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      8 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 +
      8 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (lc0VBField (I := I) (M := M) g₀ g₁)‖ ^ 2 +
      4 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 +
      2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (lc0RiemField (I := I) (M := M) g₀ g₁)‖ ^ 2 := by
    rw [hdecomp]
    have k1 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 2 2 i
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg + lc0VBField (I := I) (M := M) g₀ g₁
        + lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)
      (lc0RiemField (I := I) (M := M) g₀ g₁)
    have k2 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 2 2 i
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg + lc0VBField (I := I) (M := M) g₀ g₁)
      (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)
    have k3 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 2 2 i
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg) (lc0VBField (I := I) (M := M) g₀ g₁)
    linarith [k1, k2, k3]
  have hIns : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      4 * (fr * (4 * Fc0 i + 4 * Fcb i + 2 * PW i)) := by
    have hswapEq : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
          (Equiv.swap (0 : Fin 2) 1))‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 :=
      lc0b_normSq_icg_bothCongr_eq (I := I) (M := M) g₀ 2 2
        (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)) i
    have hsplitI := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 2 2 i
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
        (Equiv.swap (0 : Fin 2) 1))
    have hle_endo : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 ≤
        fr * ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 := by
      refine lc0b_normSq_le_scaled_of_pointwise (I := I) (M := M) g₀ 2 (2 + i) 1 (1 + i)
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
        (iteratedCovGrad (I := I) g₀ 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
        fr hfr_nn ?_
      intro x
      have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
        (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg) i x
      rw [pow_one] at h
      exact h
    have hzero : ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 ≤
        4 * Fc0 i + 4 * Fcb i + 2 * PW i := by
      rw [lc0b_NEndoIns_decomp (I := I) (M := M) g₀ g₁ g_bg]
      have k1 := lc0b_normSq_icg_sub_le (I := I) (M := M) g₀ 1 1 i
        (lc0CdVField (I := I) (M := M) g₀ g₁ g₀ - lc0CdVField (I := I) (M := M) g₀ g₁ g_bg)
        (DifferentialGeometry.PDE.RicciFlow.deTurckLieWEndoInsert
          (I := I) (M := M) g₀ g₁ g₀)
      have k2 := lc0b_normSq_icg_sub_le (I := I) (M := M) g₀ 1 1 i
        (lc0CdVField (I := I) (M := M) g₀ g₁ g₀) (lc0CdVField (I := I) (M := M) g₀ g₁ g_bg)
      have hc0i : ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (lc0CdVField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤ Fc0 i := by
        refine le_trans ?_ (hc0L2 i hi)
        exact Finset.single_le_sum (f := fun q =>
          ‖iteratedCovGrad (I := I) g₀ 1 1 q (lc0CdVField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2)
          (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
      have hcbi : ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (lc0CdVField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ Fcb i := by
        refine le_trans ?_ (hcbL2 i hi)
        exact Finset.single_le_sum (f := fun q =>
          ‖iteratedCovGrad (I := I) g₀ 1 1 q (lc0CdVField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2)
          (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
      linarith [k1, k2, hc0i, hcbi, hWi]
    have hfr_step : fr * ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 ≤
        fr * (4 * Fc0 i + 4 * Fcb i + 2 * PW i) :=
      mul_le_mul_of_nonneg_left hzero hfr_nn
    calc ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
        ≤ 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                  (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1))‖ ^ 2 := hsplitI
      _ = 4 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 := by
          rw [hswapEq]; ring
      _ ≤ 4 * (fr * ‖iteratedCovGrad (I := I) g₀ 1 1 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2) := by
          have := mul_le_mul_of_nonneg_left hle_endo (by norm_num : (0:ℝ) ≤ 4)
          linarith
      _ ≤ 4 * (fr * (4 * Fc0 i + 4 * Fcb i + 2 * PW i)) := by
          have := mul_le_mul_of_nonneg_left hfr_step (by norm_num : (0:ℝ) ≤ 4)
          linarith
  have hVBi : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (lc0VBField (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ Fvb i := by
    refine le_trans ?_ (hvbL2 i hi)
    exact Finset.single_le_sum (f := fun q =>
      ‖iteratedCovGrad (I := I) g₀ 2 2 q (lc0VBField (I := I) (M := M) g₀ g₁)‖ ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
  have hAMi : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ Fam i := by
    refine le_trans ?_ (hamL2 i hi)
    exact Finset.single_le_sum (f := fun q =>
      ‖iteratedCovGrad (I := I) g₀ 2 2 q (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
  have hRIi : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (lc0RiemField (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ Fri i := by
    refine le_trans ?_ (hriL2 i hi)
    exact Finset.single_le_sum (f := fun q =>
      ‖iteratedCovGrad (I := I) g₀ 2 2 q (lc0RiemField (I := I) (M := M) g₀ g₁)‖ ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
  refine le_trans hsplit ?_
  have e1 := mul_le_mul_of_nonneg_left hIns (by norm_num : (0:ℝ) ≤ 8)
  have e2 := mul_le_mul_of_nonneg_left hVBi (by norm_num : (0:ℝ) ≤ 8)
  have e3 := mul_le_mul_of_nonneg_left hAMi (by norm_num : (0:ℝ) ≤ 4)
  have e4 := mul_le_mul_of_nonneg_left hRIi (by norm_num : (0:ℝ) ≤ 2)
  linarith

theorem lieCorr0Field_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨Λvb, Fvb, hΛvb_nn, hFvb_nn, hvb⟩ :=
    lc0b_vbField_feed (I := I) (M := M) g₀ a ha_super hR hδ₁_lt
  obtain ⟨Λam, Fam, hΛam_nn, hFam_nn, ham⟩ :=
    lc0b_amixField_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₁_lt
  obtain ⟨Λri, Fri, hΛri_nn, hFri_nn, hri⟩ :=
    lc0b_riemField_feed (I := I) (M := M) g₀ a ha_super hR hδ₁_lt
  obtain ⟨Λc0, Fc0, hΛc0_nn, hFc0_nn, hc0⟩ :=
    lc0b_cdVField_feed (I := I) (M := M) g₀ g₀ a ha_super hR hδ₁_lt
  obtain ⟨Λcb, Fcb, hΛcb_nn, hFcb_nn, hcb⟩ :=
    lc0b_cdVField_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₁_lt
  obtain ⟨ΛW, hΛW_nn, hΛW⟩ :=
    DifferentialGeometry.Analysis.Sobolev.deTurckLieWEndoInsert_realizedFam_order0_ballUniform
      (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨8 * (4 * (fr * (4 * Λc0 + 4 * Λcb + 2 * ΛW)))
      + 8 * Λvb + 4 * Λam + 2 * Λri,
    by
      have hin : 0 ≤ fr * (4 * Λc0 + 4 * Λcb + 2 * ΛW) := by positivity
      linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁_def
  set Pc : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s with hPc_def
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδs_raw : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc)
      (|1 - s| * δ' + |s| * δ) := by
    rw [hPc_def]
    exact convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  set δP : ℝ := max (|1 - s| * δ' + |s| * δ) 0 with hδP_def
  have hδP_nn : 0 ≤ δP := le_max_right _ _
  have hδP_bound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc)
    δP :=
    lc0b_gFibreOpBound_mono (I := I) (M := M) g₀ _ (le_max_left _ _) hδs_raw
  have hδP_le : δP ≤ δ₁ := by
    refine max_le ?_ hδ₁_nn
    rw [abs_of_nonneg h1ms, abs_of_nonneg hs0]
    have h1 : δ' ≤ δ₁ := le_trans hδ'_le (le_max_left _ _)
    have h2 : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    nlinarith [h1, h2]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ Pc y v w := by
    intro y v w
    rw [hg₁_def, hPc_def]
    exact realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
      (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j Pc
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [hPc_def]
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, lc0b_icg_smul, lc0b_icg_smul]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  obtain ⟨hvb0, hvbL2⟩ := hvb g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨ham0, hamL2⟩ := ham g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨hri0, hriL2⟩ := hri g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨hc00, hc0L2⟩ := hc0 g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨hcb0, hcbL2⟩ := hcb g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  have hWx : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
      ((DifferentialGeometry.PDE.RicciFlow.deTurckLieWEndoInsert
        (I := I) (M := M) g₀ g₁ g₀).toSection x) ≤ ΛW := by
    rw [hg₁_def]
    exact hΛW T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  have hdecomp := lc0b_total_decomp (I := I) (M := M) g₀ g₁ g_bg
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤
      8 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((lc0InsertField (I := I) (M := M) g₀ g₁ g_bg).toSection x) +
      8 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((lc0VBField (I := I) (M := M) g₀ g₁).toSection x) +
      4 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((lc0AMixField (I := I) (M := M) g₀ g₁ g_bg).toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((lc0RiemField (I := I) (M := M) g₀ g₁).toSection x) := by
    rw [hdecomp]
    have k1 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg + lc0VBField (I := I) (M := M) g₀ g₁
        + lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)
      (lc0RiemField (I := I) (M := M) g₀ g₁) x
    have k2 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg + lc0VBField (I := I) (M := M) g₀ g₁)
      (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg) x
    have k3 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg) (lc0VBField (I := I) (M := M) g₀ g₁) x
    linarith [k1, k2, k3]
  have hIns : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((lc0InsertField (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤
      4 * (fr * (4 * Λc0 + 4 * Λcb + 2 * ΛW)) := by
    have hsplitI := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
        (Equiv.swap (0 : Fin 2) 1)) x
    have hswapEq : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
      have h := rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
        (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)) 0 x
      simp only [iteratedCovGrad_zero] at h
      exact h
    have hle_endo : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
          ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
      have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
        (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg) 0 x
      simp only [iteratedCovGrad_zero] at h
      rw [pow_one] at h
      exact h
    have hzero : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        4 * Λc0 + 4 * Λcb + 2 * ΛW := by
      rw [lc0b_NEndoIns_decomp (I := I) (M := M) g₀ g₁ g_bg]
      have k1 := lc0b_rfns_toSection_sub_le (I := I) (M := M) g₀ 1 1
        (lc0CdVField (I := I) (M := M) g₀ g₁ g₀ - lc0CdVField (I := I) (M := M) g₀ g₁ g_bg)
        (DifferentialGeometry.PDE.RicciFlow.deTurckLieWEndoInsert
          (I := I) (M := M) g₀ g₁ g₀) x
      have k2 := lc0b_rfns_toSection_sub_le (I := I) (M := M) g₀ 1 1
        (lc0CdVField (I := I) (M := M) g₀ g₁ g₀) (lc0CdVField (I := I) (M := M) g₀ g₁ g_bg) x
      linarith [k1, k2, hc00 x, hcb0 x, hWx]
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((lc0InsertField (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                  (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) := hsplitI
      _ = 4 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
          rw [hswapEq]; ring
      _ ≤ 4 * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) := by
          have := mul_le_mul_of_nonneg_left hle_endo (by norm_num : (0:ℝ) ≤ 4)
          linarith
      _ ≤ 4 * (fr * (4 * Λc0 + 4 * Λcb + 2 * ΛW)) := by
          have hstep := mul_le_mul_of_nonneg_left hzero hfr_nn
          have := mul_le_mul_of_nonneg_left hstep (by norm_num : (0:ℝ) ≤ 4)
          linarith
  refine le_trans hsplit ?_
  have e1 := mul_le_mul_of_nonneg_left hIns (by norm_num : (0:ℝ) ≤ 8)
  have e2 := mul_le_mul_of_nonneg_left (hvb0 x) (by norm_num : (0:ℝ) ≤ 8)
  have e3 := mul_le_mul_of_nonneg_left (ham0 x) (by norm_num : (0:ℝ) ≤ 4)
  have e4 := mul_le_mul_of_nonneg_left (hri0 x) (by norm_num : (0:ℝ) ≤ 2)
  linarith

end LieCorr0BoundsF4

end LieCorr0BoundsAll

end DifferentialGeometry.Analysis.Spectral

end
