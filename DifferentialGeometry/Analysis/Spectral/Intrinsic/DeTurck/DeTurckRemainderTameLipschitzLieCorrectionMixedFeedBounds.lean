import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionVectorFeedBounds
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic


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

section LieCorr0BoundsF3

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_smul_feed_transfer (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (F : SmoothCcTensor g₀ r s) (Λ : ℝ) (Fn : ℕ → ℝ) (amax : ℕ)
    (h0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (F.toSection x) ≤ Λ)
    (hF : ∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ r s q F‖ ^ 2 ≤ Fn i) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((c • F).toSection x) ≤
      c ^ 2 * Λ) ∧
    (∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ r s q (c • F)‖ ^ 2 ≤
      c ^ 2 * Fn i) := by
  have hc2 : (0 : ℝ) ≤ c ^ 2 := sq_nonneg c
  constructor
  · intro x
    rw [show (c • F).toSection x = c • (F.toSection x) from rfl]
    rw [lc0b_rfns_smul (I := I) (M := M) g₀ r s x c (F.toSection x)]
    exact mul_le_mul_of_nonneg_left (h0 x) hc2
  · intro i hi
    have hstep : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ r s q (c • F)‖ ^ 2 =
        c ^ 2 * ‖iteratedCovGrad (I := I) g₀ r s q F‖ ^ 2 := by
      intro q _
      rw [lc0b_icg_smul (I := I) (M := M) g₀ r s q c F, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs]
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hF i hi) hc2

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_add_feed_transfer (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g₀ r s) (ΛA ΛB : ℝ) (FA FB : ℕ → ℝ) (amax : ℕ)
    (hA0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (A.toSection x) ≤ ΛA)
    (hB0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (B.toSection x) ≤ ΛB)
    (hFA : ∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ r s q A‖ ^ 2 ≤ FA i)
    (hFB : ∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ r s q B‖ ^ 2 ≤ FB i) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((A + B).toSection x) ≤
      2 * ΛA + 2 * ΛB) ∧
    (∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ r s q (A + B)‖ ^ 2 ≤
      2 * FA i + 2 * FB i) := by
  constructor
  · intro x
    refine le_trans (lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ r s A B x) ?_
    have h1 := hA0 x
    have h2 := hB0 x
    linarith
  · intro i hi
    have hstep : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ r s q (A + B)‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ r s q A‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ r s q B‖ ^ 2 :=
      fun q _ => lc0b_normSq_icg_add_le (I := I) (M := M) g₀ r s q A B
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hFA i hi) (by norm_num : (0:ℝ) ≤ 2)
    have h2 := mul_le_mul_of_nonneg_left (hFB i hi) (by norm_num : (0:ℝ) ≤ 2)
    linarith

theorem lc0b_vbField_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((lc0VBField (I := I) (M := M) g₀ g₁).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 q
              (lc0VBField (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λdt2, Fdt2, hΛdt2_nn, hFdt2_nn, hdt2⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ 2 a ha_super hR hδ₀
  obtain ⟨Λκ, Fκ, hΛκ_nn, hFκ_nn, hκ⟩ :=
    lc0b_kappa_feed (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨Λiv, Fiv, hΛiv_nn, hFiv_nn, hiv⟩ :=
    lc0b_iVField_feed (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨C2i, hC2i_nn, hC2i⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 1 2 4 1
  obtain ⟨C2o, hC2o_nn, hC2o⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 4 2 2 4
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set ΛK : ℝ := fr ^ 1 * Λκ with hΛK
  have hΛK_nn : 0 ≤ ΛK := mul_nonneg (by positivity) hΛκ_nn
  set FK : ℕ → ℝ := fun q => fr ^ 1 * Fκ q with hFK
  have hFK_nn : ∀ q, 0 ≤ FK q := fun q => mul_nonneg (by positivity) (hFκ_nn q)
  set Λin : ℝ := ΛK * Λiv with hΛin
  have hΛin_nn : 0 ≤ Λin := mul_nonneg hΛK_nn hΛiv_nn
  set Fin' : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    diagonalGridGrowthFactor (E := E) q * (C2i q * (Λiv * FK q + ΛK * Fiv q)) with hFin'
  have hFin'_nn : ∀ i, 0 ≤ Fin' i := fun i =>
    Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2i_nn q) (add_nonneg (mul_nonneg hΛiv_nn (hFK_nn q))
        (mul_nonneg hΛK_nn (hFiv_nn q))))
  refine ⟨(2 : ℝ) ^ 2 * (Λdt2 * Λin),
    fun i => (2 : ℝ) ^ 2 * ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2o q * (Λin * Fdt2 q + Λdt2 * Fin' q)),
    by positivity,
    fun i => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
        (mul_nonneg (hC2o_nn q) (add_nonneg (mul_nonneg hΛin_nn (hFdt2_nn q))
          (mul_nonneg hΛdt2_nn (hFin'_nn q))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hdt20, hdt2L2⟩ := hdt2 g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hκ0, hκL2⟩ := hκ g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hiv0, hivL2⟩ := hiv g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hK0, hKL2⟩ := lc0b_slotExtendIter_feed_transfer (I := I) (M := M) g₀ 0 3 1
    (lc0Kappa (I := I) (M := M) g₀ g₁ g₀) Λκ Fκ a hκ0 hκL2
  obtain ⟨hin0, hinL2⟩ := lc0b_comp_feed_step (I := I) (M := M) g₀ 2 1 4 a
    (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
    (lc0IVField (I := I) (M := M) g₀ g₁ g₀)
    C2i hC2i_nn hC2i ΛK Λiv FK Fiv hΛK_nn hΛiv_nn hK0 hiv0 hKL2 hivL2
  obtain ⟨htr0, htrL2⟩ := lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 4 2
    (lc0PureDT (I := I) (M := M) g₀ g₁ 2) lieCorr0VBPerm Λdt2 Fdt2 a hdt20 hdt2L2
  obtain ⟨hout0, houtL2⟩ := lc0b_comp_feed_step (I := I) (M := M) g₀ 2 4 2 a
    (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
      (lc0IVField (I := I) (M := M) g₀ g₁ g₀))
    C2o hC2o_nn hC2o Λdt2 Λin Fdt2 Fin' hΛdt2_nn hΛin_nn htr0 hin0 htrL2 hinL2
  obtain ⟨hs0, hsL2⟩ := lc0b_smul_feed_transfer (I := I) (M := M) g₀ 2 2 (2 : ℝ)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
        (lc0IVField (I := I) (M := M) g₀ g₁ g₀)))
    (Λdt2 * Λin)
    (fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2o q * (Λin * Fdt2 q + Λdt2 * Fin' q)))
    a hout0 houtL2
  exact ⟨hs0, hsL2⟩

theorem lc0b_amixHalf_feed (g₀ g_bg : SmoothRiemannianMetric I M)
    (σlast : Equiv.Perm (Fin 4)) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg σlast).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 q
              (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg σlast)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λdt2, Fdt2, hΛdt2_nn, hFdt2_nn, hdt2⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ 2 a ha_super hR hδ₀
  obtain ⟨Λdt3, Fdt3, hΛdt3_nn, hFdt3_nn, hdt3⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ 3 a ha_super hR hδ₀
  obtain ⟨Λdt4, Fdt4, hΛdt4_nn, hFdt4_nn, hdt4⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ 4 a ha_super hR hδ₀
  obtain ⟨Λκ0, Fκ0, hΛκ0_nn, hFκ0_nn, hκ0f⟩ :=
    lc0b_kappa_feed (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨Λκb, Fκb, hΛκb_nn, hFκb_nn, hκbf⟩ :=
    lc0b_kappa_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨C2a, hC2a_nn, hC2a⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 5 2 3 5
  obtain ⟨C2b, hC2b_nn, hC2b⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 3 2 6 3
  obtain ⟨C2c, hC2c_nn, hC2c⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 6 2 4 6
  obtain ⟨C2d, hC2d_nn, hC2d⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 4 2 2 4
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr
  set ΛK0 : ℝ := fr ^ 2 * Λκ0 with hΛK0
  have hΛK0_nn : 0 ≤ ΛK0 := mul_nonneg (by positivity) hΛκ0_nn
  set FK0 : ℕ → ℝ := fun q => fr ^ 2 * Fκ0 q with hFK0
  have hFK0_nn : ∀ q, 0 ≤ FK0 q := fun q => mul_nonneg (by positivity) (hFκ0_nn q)
  set ΛKb : ℝ := fr ^ 3 * Λκb with hΛKb
  have hΛKb_nn : 0 ≤ ΛKb := mul_nonneg (by positivity) hΛκb_nn
  set FKb : ℕ → ℝ := fun q => fr ^ 3 * Fκb q with hFKb
  have hFKb_nn : ∀ q, 0 ≤ FKb q := fun q => mul_nonneg (by positivity) (hFκb_nn q)
  set Λ1 : ℝ := Λdt3 * ΛK0 with hΛ1
  have hΛ1_nn : 0 ≤ Λ1 := mul_nonneg hΛdt3_nn hΛK0_nn
  set F1 : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    diagonalGridGrowthFactor (E := E) q * (C2a q * (ΛK0 * Fdt3 q + Λdt3 * FK0 q)) with hF1
  have hF1_nn : ∀ i, 0 ≤ F1 i := fun i =>
    Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2a_nn q) (add_nonneg (mul_nonneg hΛK0_nn (hFdt3_nn q))
        (mul_nonneg hΛdt3_nn (hFK0_nn q))))
  set Λ2 : ℝ := ΛKb * Λ1 with hΛ2
  have hΛ2_nn : 0 ≤ Λ2 := mul_nonneg hΛKb_nn hΛ1_nn
  set F2 : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    diagonalGridGrowthFactor (E := E) q * (C2b q * (Λ1 * FKb q + ΛKb * F1 q)) with hF2
  have hF2_nn : ∀ i, 0 ≤ F2 i := fun i =>
    Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hΛ1_nn (hFKb_nn q))
        (mul_nonneg hΛKb_nn (hF1_nn q))))
  set Λ3 : ℝ := Λdt4 * Λ2 with hΛ3
  have hΛ3_nn : 0 ≤ Λ3 := mul_nonneg hΛdt4_nn hΛ2_nn
  set F3 : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    diagonalGridGrowthFactor (E := E) q * (C2c q * (Λ2 * Fdt4 q + Λdt4 * F2 q)) with hF3
  have hF3_nn : ∀ i, 0 ≤ F3 i := fun i =>
    Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2c_nn q) (add_nonneg (mul_nonneg hΛ2_nn (hFdt4_nn q))
        (mul_nonneg hΛdt4_nn (hF2_nn q))))
  refine ⟨Λdt2 * Λ3,
    fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2d q * (Λ3 * Fdt2 q + Λdt2 * F3 q)),
    mul_nonneg hΛdt2_nn hΛ3_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2d_nn q) (add_nonneg (mul_nonneg hΛ3_nn (hFdt2_nn q))
        (mul_nonneg hΛdt2_nn (hF3_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hdt20, hdt2L2⟩ := hdt2 g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hdt30, hdt3L2⟩ := hdt3 g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hdt40, hdt4L2⟩ := hdt4 g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hκ00, hκ0L2⟩ := hκ0f g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hκb0, hκbL2⟩ := hκbf g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hK00, hK0L2⟩ := lc0b_slotExtendIter_feed_transfer (I := I) (M := M) g₀ 0 3 2
    (lc0Kappa (I := I) (M := M) g₀ g₁ g₀) Λκ0 Fκ0 a hκ00 hκ0L2
  obtain ⟨hKb0, hKbL2⟩ := lc0b_slotExtendIter_feed_transfer (I := I) (M := M) g₀ 0 3 3
    (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg) Λκb Fκb a hκb0 hκbL2
  obtain ⟨htr30, htr3L2⟩ := lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 5 3
    (lc0PureDT (I := I) (M := M) g₀ g₁ 3) lieCorr0AMixPermQ Λdt3 Fdt3 a hdt30 hdt3L2
  obtain ⟨h10, h1L2⟩ := lc0b_comp_feed_step (I := I) (M := M) g₀ 2 5 3 a
    (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
    (slotExtendIter (I := I) (M := M) g₀ 0 3 2 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
    C2a hC2a_nn hC2a Λdt3 ΛK0 Fdt3 FK0 hΛdt3_nn hΛK0_nn htr30 hK00 htr3L2 hK0L2
  obtain ⟨h20, h2L2⟩ := lc0b_comp_feed_step (I := I) (M := M) g₀ 2 3 6 a
    (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
      (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)))
    C2b hC2b_nn hC2b ΛKb Λ1 FKb F1 hΛKb_nn hΛ1_nn hKb0 h10 hKbL2 h1L2
  obtain ⟨htr40, htr4L2⟩ := lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 6 4
    (lc0PureDT (I := I) (M := M) g₀ g₁ 4) lieCorr0AMixPerm1 Λdt4 Fdt4 a hdt40 hdt4L2
  obtain ⟨h30, h3L2⟩ := lc0b_comp_feed_step (I := I) (M := M) g₀ 2 6 4 a
    (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
        (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))))
    C2c hC2c_nn hC2c Λdt4 Λ2 Fdt4 F2 hΛdt4_nn hΛ2_nn htr40 h20 htr4L2 h2L2
  obtain ⟨htr20, htr2L2⟩ := lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 4 2
    (lc0PureDT (I := I) (M := M) g₀ g₁ 2) σlast Λdt2 Fdt2 a hdt20 hdt2L2
  exact lc0b_comp_feed_step (I := I) (M := M) g₀ 2 4 2 a
    (lc0Tr (I := I) (M := M) g₀ g₁ 2 σlast)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4
      (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
          (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)))))
    C2d hC2d_nn hC2d Λdt2 Λ3 Fdt2 F3 hΛdt2_nn hΛ3_nn htr20 h30 htr2L2 h3L2

theorem lc0b_amixField_feed (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((lc0AMixField (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 q
              (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨ΛhA, FhA, hΛhA_nn, hFhA_nn, hhA⟩ :=
    lc0b_amixHalf_feed (I := I) (M := M) g₀ g_bg lieCorr0AMixPerm2 a ha_super hR hδ₀
  obtain ⟨ΛhB, FhB, hΛhB_nn, hFhB_nn, hhB⟩ :=
    lc0b_amixHalf_feed (I := I) (M := M) g₀ g_bg (lc0SwapOutPerm * lieCorr0AMixPerm2)
      a ha_super hR hδ₀
  refine ⟨(2 : ℝ) ^ 2 * (2 * ΛhA + 2 * ΛhB),
    fun i => (2 : ℝ) ^ 2 * (2 * FhA i + 2 * FhB i),
    by positivity,
    fun i => by
      have := hFhA_nn i
      have := hFhB_nn i
      positivity, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hA0, hAL2⟩ := hhA g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hB0, hBL2⟩ := hhB g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hadd0, haddL2⟩ := lc0b_add_feed_transfer (I := I) (M := M) g₀ 2 2
    (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg lieCorr0AMixPerm2)
    (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg (lc0SwapOutPerm * lieCorr0AMixPerm2))
    ΛhA ΛhB FhA FhB a hA0 hB0 hAL2 hBL2
  exact lc0b_smul_feed_transfer (I := I) (M := M) g₀ 2 2 (2 : ℝ)
    (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg lieCorr0AMixPerm2
      + lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg (lc0SwapOutPerm * lieCorr0AMixPerm2))
    (2 * ΛhA + 2 * ΛhB) (fun i => 2 * FhA i + 2 * FhB i) a hadd0 haddL2

theorem lc0b_riemField_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((lc0RiemField (I := I) (M := M) g₀ g₁).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 q
              (lc0RiemField (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λdt2, Fdt2, hΛdt2_nn, hFdt2_nn, hdt2⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ 2 a ha_super hR hδ₀
  obtain ⟨Λrr, hΛrr_nn, hΛrr⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 4
      (lc0RiemRestField (I := I) (M := M) g₀)
  set Frr : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    ‖iteratedCovGrad (I := I) g₀ 2 4 q (lc0RiemRestField (I := I) (M := M) g₀)‖ ^ 2 with hFrr
  have hFrr_nn : ∀ i, 0 ≤ Frr i := fun i => Finset.sum_nonneg fun q _ => sq_nonneg _
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 4 2 2 4
  refine ⟨(-1 : ℝ) ^ 2 * (Λdt2 * Λrr),
    fun i => (-1 : ℝ) ^ 2 * ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (Λrr * Fdt2 q + Λdt2 * Frr q)),
    by positivity,
    fun i => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
        (mul_nonneg (hC2_nn q) (add_nonneg (mul_nonneg hΛrr_nn (hFdt2_nn q))
          (mul_nonneg hΛdt2_nn (hFrr_nn q))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hdt20, hdt2L2⟩ := hdt2 g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨htr0, htrL2⟩ := lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 4 2
    (lc0PureDT (I := I) (M := M) g₀ g₁ 2) lieCorr0RiemPerm2 Λdt2 Fdt2 a hdt20 hdt2L2
  obtain ⟨hcomp0, hcompL2⟩ := lc0b_comp_feed_step (I := I) (M := M) g₀ 2 4 2 a
    (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2) (lc0RiemRestField (I := I) (M := M) g₀)
    C2 hC2_nn hC2 Λdt2 Λrr Fdt2 Frr hΛdt2_nn hΛrr_nn htr0 hΛrr htrL2 (fun i _ => le_rfl)
  exact lc0b_smul_feed_transfer (I := I) (M := M) g₀ 2 2 (-1 : ℝ)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
      (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)
      (lc0RiemRestField (I := I) (M := M) g₀))
    (Λdt2 * Λrr)
    (fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (Λrr * Fdt2 q + Λdt2 * Frr q)))
    a hcomp0 hcompL2

end LieCorr0BoundsF3

end LieCorr0BoundsAll

end DifferentialGeometry.Analysis.Spectral

end

