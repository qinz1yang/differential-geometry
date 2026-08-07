import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionKappaBounds
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
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

section LieCorr0BoundsC

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (metricComparisonEndo gInvRaisedEndo_apply
  gInvRaisedEndo_eq_diff_add_id inverseMetricSharpFib_g0FlatCLM cotangentToDual_g0FlatCLM
  g0FlatCLM metricComparisonDiffEndo)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
lemma lc0b_toModel_om_single (x : M) (om : Tensor0SSpace 1 I x) (m : Fin 1 → E) :
    Tensor0SSpace.toModel om m = cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [cotangentToDual_apply]
  rw [show (om (fun _ : Fin 1 => (m 0 : TangentSpace I x)) : ℝ) =
      Tensor0SSpace.toModel om (fun _ : Fin 1 => m 0) from rfl]
  congr 1
  funext k
  rw [show k = (0 : Fin 1) from Subsingleton.elim k 0]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma lc0b_g0_inner_sharp_mixed (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (v : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x om) v =
      cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) := by
  have h1 : ∀ w : TangentSpace I x,
      g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
    intro w
    rw [gInvRaisedEndo_apply]
    rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
    rw [cotangentToDualLinear_apply]
    exact cotangentToDual_g0FlatCLM (I := I) g₀ x v w
  have h2 : cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) =
      g₁.inner x (inverseMetricSharpFib (I := I) g₁ x om)
        (metricComparisonEndo (I := I) g₀ g₁ x v) := by
    rw [inverseMetricSharpFib_inner (I := I) g₁ x om (metricComparisonEndo (I := I) g₀ g₁ x v)]
    rfl
  rw [h2]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om) (metricComparisonEndo (I := I) g₀ g₁ x v)]
  rw [h1 (inverseMetricSharpFib (I := I) g₁ x om)]
  exact g₀.symm x (inverseMetricSharpFib (I := I) g₁ x om) v

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
lemma lc0b_sharpFlat_eq_slotInsert_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om) =
      (g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [lc0b_toModel_om_single (I := I) (M := M) x om
    (Function.update m 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x (m 0)))]
  rw [Function.update_self]
  rw [lc0b_toModel_om_single (I := I) (M := M) x
    ((g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om)) m]
  rw [cotangentToDual_g0FlatCLM]
  rw [lc0b_g0_inner_sharp_mixed (I := I) (M := M) g₀ g₁ x om (m 0)]
  rw [fullRaisedEndoField_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
    in
lemma lc0b_fullRaised_diff_split (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) = metricComparisonDiffEndo (I := I) g₀ g₁ x
    from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show metricComparisonEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
lemma lc0b_slotInsert_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ s (A + B) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ s A +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ s A +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x) =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s A).toSection x +
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

theorem lc0b_sharpFlat_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndo_diagGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Km, hKm_nn, hKm⟩ :=
    diagonalProductGrid_riemannianFiberNormSq_integral_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  set IdIns : SmoothCcTensor g₀ 1 1 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀) with hIdIns_def
  obtain ⟨S0, hS0_nn, hS0⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 1 IdIns
  refine ⟨2 * Cb 0 + 2 * S0,
    fun i => ∑ q ∈ Finset.range (i + 1),
      (2 * (Cb q * Km q) + 2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2),
    by have := hCb_nn 0; linarith,
    fun i => Finset.sum_nonneg fun q _ => add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (hCb_nn q) (hKm_nn q)))
      (mul_nonneg (by norm_num) (sq_nonneg _)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  set DiffIns : SmoothCcTensor g₀ 1 1 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁)
    with hDiffIns_def
  have hdecomp : sharpFlatEndoCc (I := I) g₀ g₁ = DiffIns + IdIns := by
    rw [lc0b_sharpFlat_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁,
      lc0b_fullRaised_diff_split (I := I) (M := M) g₀ g₁,
      lc0b_slotInsert_add (I := I) (M := M) g₀ 0]
  refine ⟨?_, ?_⟩
  · intro x
    have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (DiffIns.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (IdIns.toSection x) := by
      rw [hdecomp]
      exact lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 1 1 _ _ x
    have hD0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        (DiffIns.toSection x) ≤ Cb 0 := by
      have h2 := hCb g₁ P htie hδ_le hδ0 hδ 0 x
      simp only [iteratedCovGrad_zero] at h2
      have hgrid0 : (∑ n ∈ Finset.range (0 + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n 0,
          ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = 1 := by
        simp
      rw [hgrid0, mul_one] at h2
      exact h2
    linarith [hsplit, hD0, hS0 x]
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
    obtain ⟨hgi, hgb⟩ := hKm P hPball q hq_le
    have hDq : ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ ^ 2 ≤ Cb q * Km q := by
      have hint : MeasureTheory.Integrable
          (fun x => Cb q *
            (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
              ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        1 (1 + q) (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns) _ hint
        (fun x => hCb g₁ P htie hδ_le hδ0 hδ q x)
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      exact mul_le_mul_of_nonneg_left hgb (hCb_nn q)
    have htri : ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ +
          ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ := by
      rw [hdecomp, iteratedCovGrad_add]
      exact norm_add_le _ _
    nlinarith [htri, hDq,
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q IdIns),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)),
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ -
        ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖)]

theorem lc0b_cds_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
            ((connDiffSection (I := I) g₁ g₀).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 q (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨ΛK, FK, hΛK_nn, hFK_nn, hK⟩ :=
    raisedKoszul_order0sup_jetL2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λsf, Fsf, hΛsf_nn, hFsf_nn, hsf⟩ :=
    lc0b_sharpFlat_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 1 1 2 1
  refine ⟨ΛK ^ 2 * Λsf,
    fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (Λsf * FK q + ΛK ^ 2 * Fsf q)),
    mul_nonneg (sq_nonneg _) hΛsf_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg (mul_nonneg hΛsf_nn (hFK_nn q))
        (mul_nonneg (sq_nonneg _) (hFsf_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hKsup, hKsum⟩ := hK g₁ P hδ_le hδ htie hPball
  obtain ⟨hsfsup, hsfsum⟩ := hsf g₁ P htie hδ_le hδ0 hδ hPball
  have hid : connDiffSection (I := I) g₁ g₀ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 (raisedKoszul (I := I) g₀ g₁)
        (sharpFlatEndoCc (I := I) g₀ g₁) :=
    connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁
  refine ⟨?_, ?_⟩
  · intro x
    rw [hid, appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
      (show TensorRSSpace 1 2 I x from (raisedKoszul (I := I) g₀ g₁).toSection x)
      (show TensorRSSpace 1 1 I x from (sharpFlatEndoCc (I := I) g₀ g₁).toSection x)) ?_
    exact mul_le_mul (hKsup x) (hsfsup x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) (sq_nonneg ΛK)
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
    rw [hid]
    exact lc0b_appCcRS_normSq_le (I := I) (M := M) g₀ 1 1 2
      (raisedKoszul (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) q
      (C2 q) (ΛK ^ 2) Λsf (FK q) (Fsf q)
      (hC2_nn q) (sq_nonneg ΛK) hΛsf_nn hKsup hsfsup (hKsum q hq_le) (hsfsum q hq_le)
      (hC2 q)

theorem lc0b_kappa_feed (g₀ gB : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
    lc0b_cds_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λlow, hΛlow_nn, hΛlow⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 3
      (lc0LowFix (I := I) (M := M) g₀ gB)
  obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
      (lc0FixCd (I := I) (M := M) g₀ gB)
  obtain ⟨C2b, hC2b_nn, hC2b⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 1 1 2 1
  set nQ : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * max δ₀ 0 ^ 2 with hnQ_def
  have hnQ_nn : 0 ≤ nQ := by rw [hnQ_def]; positivity
  set FB : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2
    with hFB_def
  have hFB_nn : ∀ i, 0 ≤ FB i := fun i => Finset.sum_nonneg fun q _ => sq_nonneg _
  set Ffx : ℕ → ℝ := fun q => ∑ l ∈ Finset.range (q + 1),
    ‖iteratedCovGrad (I := I) g₀ 1 2 l (lc0FixCd (I := I) (M := M) g₀ gB)‖ ^ 2
    with hFfx_def
  have hFfx_nn : ∀ q, 0 ≤ Ffx q := fun q => Finset.sum_nonneg fun l _ => sq_nonneg _
  set FC : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    diagonalGridGrowthFactor (E := E) q * (C2b q * (nQ * Fcd q + Λcd * (((q : ℝ) + 1) * R ^ 2)))
    with hFC_def
  have hFC_nn : ∀ i, 0 ≤ FC i := by
    intro i
    refine Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hnQ_nn (hFcd_nn q))
        (mul_nonneg hΛcd_nn (by positivity))))
  set FD : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    diagonalGridGrowthFactor (E := E) q * (C2b q * (nQ * Ffx q + Λfx * (((q : ℝ) + 1) * R ^ 2)))
    with hFD_def
  have hFD_nn : ∀ i, 0 ≤ FD i := by
    intro i
    refine Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hnQ_nn (hFfx_nn q))
        (mul_nonneg hΛfx_nn (by positivity))))
  refine ⟨8 * Λcd + 8 * Λlow + 4 * (Λcd * nQ) + 2 * (Λfx * nQ),
    fun i => 8 * Fcd i + 8 * FB i + 4 * FC i + 2 * FD i,
    by
      have e1 := mul_nonneg hΛcd_nn hnQ_nn
      have e2 := mul_nonneg hΛfx_nn hnQ_nn
      linarith [hΛcd_nn, hΛlow_nn, e1, e2],
    fun i => by
      have := hFcd_nn i
      have := hFB_nn i
      have := hFC_nn i
      have := hFD_nn i
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hWB0, hWBL2⟩ :=
    lc0b_WB_feed (I := I) (M := M) g₀ a P hδ_le hδ0 hδ hPball
  obtain ⟨hcd0, hcdL2⟩ := hcd g₁ P htie hδ_le hδ0 hδ hPball
  have hκeq := lc0b_kappa_decomp (I := I) (M := M) g₀ g₁ gB P htie
  have hΨcC : ∀ x : M, (connDiffSection (I := I) g₁ g₀).toSection x =
      connDiffFib (I := I) g₁ g₀ x := fun x => rfl
  have hΨcD : ∀ x : M, (lc0FixCd (I := I) (M := M) g₀ gB).toSection x =
      connDiffFib (I := I) g₀ gB x := fun x => rfl
  have hWBsum : ∀ q : ℕ, q ≤ a →
      ∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 l
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P))‖ ^ 2 ≤ ((q : ℝ) + 1) * R ^ 2 := by
    intro q hq
    refine le_trans (Finset.sum_le_sum fun l hl =>
      hWBL2 l (le_trans (by have := Finset.mem_range.mp hl; omega : l ≤ q) hq)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    exact le_refl _
  refine ⟨?_, ?_⟩
  · intro x
    have hsec : (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x =
        ((connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
          + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀
          + lc0PbLow (I := I) (M := M) g₀ P g₀ gB).toSection x) := by
      rw [hκeq]
    rw [hsec]
    have h1 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
        + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)
      (lc0PbLow (I := I) (M := M) g₀ P g₀ gB) x
    have h2 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB)
      (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀) x
    have h3 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁) (lc0LowFix (I := I) (M := M) g₀ gB) x
    have hA0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((connDiffLoweredCc (I := I) g₀ g₁).toSection x) ≤ Λcd := by
      have h := lc0b_rfns_icg_lowered_eq_connDiff (I := I) (M := M) g₀ g₁ 0 x
      simp only [iteratedCovGrad_zero] at h
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((connDiffLoweredCc (I := I) g₀ g₁).toSection x)
          = riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
              ((connDiffSection (I := I) g₁ g₀).toSection x) := h
        _ ≤ Λcd := hcd0 x
    have hB0 := hΛlow x
    have hC0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((lc0PbLow (I := I) (M := M) g₀ P g₁ g₀).toSection x) ≤ Λcd * nQ := by
      have h := lc0b_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P g₁ g₀
        (connDiffSection (I := I) g₁ g₀) hΨcC 0 x
      simp only [iteratedCovGrad_zero] at h
      rw [h, appCcRS_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
        (show TensorRSSpace 1 2 I x from (connDiffSection (I := I) g₁ g₀).toSection x)
        (show TensorRSSpace 1 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x)) ?_
      exact mul_le_mul (hcd0 x) (hWB0 x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) hΛcd_nn
    have hD0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((lc0PbLow (I := I) (M := M) g₀ P g₀ gB).toSection x) ≤ Λfx * nQ := by
      have h := lc0b_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P g₀ gB
        (lc0FixCd (I := I) (M := M) g₀ gB) hΨcD 0 x
      simp only [iteratedCovGrad_zero] at h
      rw [h, appCcRS_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
        (show TensorRSSpace 1 2 I x from
          (lc0FixCd (I := I) (M := M) g₀ gB).toSection x)
        (show TensorRSSpace 1 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x)) ?_
      exact mul_le_mul (hΛfx x) (hWB0 x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) hΛfx_nn
    linarith [h1, h2, h3, hA0, hB0, hC0, hD0]
  · intro i hi
    have hstep : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤
        8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2 +
          4 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2 := by
      intro q _
      have hnorm : ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
              + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀
              + lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2 := by
        rw [hκeq]
      rw [hnorm]
      have k1 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
          + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)
        (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)
      have k2 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB)
        (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)
      have k3 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁) (lc0LowFix (I := I) (M := M) g₀ gB)
      linarith [k1, k2, k3]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    have hsplit : ∑ q ∈ Finset.range (i + 1),
        (8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2 +
          4 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2) =
        8 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2 +
          4 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsplit]
    have hBsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2 ≤ FB i := le_rfl
    have hAsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 ≤ Fcd i := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun q _ =>
        lc0b_normSq_icg_lowered_eq (I := I) (M := M) g₀ g₁ q)) ?_
      exact hcdL2 i hi
    have hCsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 ≤ FC i := by
      rw [hFC_def]
      refine Finset.sum_le_sum fun q hq => ?_
      have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
      rw [lc0b_normSq_icg_pbLow_eq (I := I) (M := M) g₀ P g₁ g₀
        (connDiffSection (I := I) g₁ g₀) hΨcC q]
      exact lc0b_appCcRS_normSq_le (I := I) (M := M) g₀ 1 1 2
        (connDiffSection (I := I) g₁ g₀)
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ P)) q
        (C2b q) Λcd nQ (Fcd q) (((q : ℝ) + 1) * R ^ 2)
        (hC2b_nn q) hΛcd_nn hnQ_nn hcd0 hWB0 (hcdL2 q hq_le) (hWBsum q hq_le)
        (hC2b q)
    have hDsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2 ≤ FD i := by
      rw [hFD_def]
      refine Finset.sum_le_sum fun q hq => ?_
      have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
      rw [lc0b_normSq_icg_pbLow_eq (I := I) (M := M) g₀ P g₀ gB
        (lc0FixCd (I := I) (M := M) g₀ gB) hΨcD q]
      refine lc0b_appCcRS_normSq_le (I := I) (M := M) g₀ 1 1 2
        (lc0FixCd (I := I) (M := M) g₀ gB)
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ P)) q
        (C2b q) Λfx nQ (Ffx q) (((q : ℝ) + 1) * R ^ 2)
        (hC2b_nn q) hΛfx_nn hnQ_nn hΛfx hWB0 le_rfl (hWBsum q hq_le)
        (hC2b q)
    linarith [hAsum, hCsum, hDsum, hBsum]

end LieCorr0BoundsC

end LieCorr0BoundsAll

end DifferentialGeometry.Analysis.Spectral

end

