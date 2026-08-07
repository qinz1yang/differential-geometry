import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionTensorTransferBounds
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature


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

section LieCorr0BoundsF2

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

theorem lc0b_comp_feed_step (g₀ : SmoothRiemannianMetric I M)
    (p a b : ℕ) (amax : ℕ)
    (Φ : SmoothCcTensor g₀ a b) (W : SmoothCcTensor g₀ p a)
    (C2 : ℕ → ℝ) (hC2_nn : ∀ k, 0 ≤ C2 k)
    (htwo : ∀ k : ℕ,
      ∀ (S : SmoothCcTensor g₀ a b) (T : SmoothCcTensor g₀ p a)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ a b x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p a x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ a (b + n) x
                  ((iteratedCovGrad (I := I) g₀ a b n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
                      ((iteratedCovGrad (I := I) g₀ p a l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ a (b + n) x
                  ((iteratedCovGrad (I := I) g₀ a b n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
                      ((iteratedCovGrad (I := I) g₀ p a l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C2 k * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ a b n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ p a l T‖ ^ 2))
    (ΛΦ ΛW : ℝ) (FΦ FW : ℕ → ℝ) (hΛΦ : 0 ≤ ΛΦ) (hΛW : 0 ≤ ΛW)
    (hΦ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ a b x (Φ.toSection x) ≤ ΛΦ)
    (hW0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p a x (W.toSection x) ≤ ΛW)
    (hFΦ : ∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ a b q Φ‖ ^ 2 ≤ FΦ i)
    (hFW : ∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ p a q W‖ ^ 2 ≤ FW i) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p b x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ W).toSection x) ≤ ΛΦ * ΛW) ∧
    (∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ p b q (ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ W)‖ ^ 2
          ≤
      ∑ q ∈ Finset.range (i + 1),
        diagonalGridGrowthFactor (E := E) q * (C2 q * (ΛW * FΦ q + ΛΦ * FW q))) := by
  constructor
  · intro x
    rw [appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ p a b x
      (show TensorRSSpace a b I x from Φ.toSection x)
      (show TensorRSSpace p a I x from W.toSection x)) ?_
    exact mul_le_mul (hΦ0 x) (hW0 x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ p a x _) hΛΦ
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ amax := by have := Finset.mem_range.mp hq; omega
    exact lc0b_appCcRS_normSq_le (I := I) (M := M) g₀ p a b Φ W q
      (C2 q) ΛΦ ΛW (FΦ q) (FW q) (hC2_nn q) hΛΦ hΛW hΦ0 hW0
      (hFΦ q hq_le) (hFW q hq_le) (htwo q)

omit [NeZero (Module.finrank ℝ E)] in
theorem lc0b_reindex_feed_transfer (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ : Equiv.Perm (Fin r)) (Λ : ℝ) (F : ℕ → ℝ) (amax : ℕ)
    (h0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (R.toSection x) ≤ Λ)
    (hF : ∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ r s q R‖ ^ 2 ≤ F i) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x
        ((reindexCoeffGen (I := I) (M := M) g₀ r s R σ).toSection x) ≤ Λ) ∧
    (∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ r s q
          (reindexCoeffGen (I := I) (M := M) g₀ r s R σ)‖ ^ 2 ≤ F i) := by
  constructor
  · intro x
    have h := lc0b_rfns_icg_reindex_eq (I := I) (M := M) g₀ r s R σ 0 x
    simp only [iteratedCovGrad_zero] at h
    exact le_of_eq_of_le h (h0 x)
  · intro i hi
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun q _ =>
      lc0b_normSq_icg_reindex_eq (I := I) (M := M) g₀ r s R σ q)) (hF i hi)

theorem lc0b_slotExtendIter_feed_transfer (g₀ : SmoothRiemannianMetric I M)
    (b₀ s₀ w : ℕ) (K : SmoothCcTensor g₀ b₀ s₀) (Λ : ℝ) (F : ℕ → ℝ) (amax : ℕ)
    (h0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (K.toSection x) ≤ Λ)
    (hF : ∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ b₀ s₀ q K‖ ^ 2 ≤ F i) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (b₀ + w) (s₀ + w) x
        ((slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ w * Λ) ∧
    (∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ (b₀ + w) (s₀ + w) q
          (slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ w * F i) := by
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ w := by positivity
  constructor
  · intro x
    have h := lc0b_rfns_icg_slotExtendIter_le (I := I) (M := M) g₀ b₀ s₀ w K 0 x
    simp only [iteratedCovGrad_zero] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left (h0 x) hfr_nn
  · intro i hi
    have hstep : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ (b₀ + w) (s₀ + w) q
          (slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K)‖ ^ 2 ≤
        (Module.finrank ℝ E : ℝ) ^ w * ‖iteratedCovGrad (I := I) g₀ b₀ s₀ q K‖ ^ 2 :=
      fun q _ => lc0b_normSq_icg_slotExtendIter_le (I := I) (M := M) g₀ b₀ s₀ w K q
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hF i hi) hfr_nn

theorem lc0b_vflat_feed (g₀ gB : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 1 x
            ((lc0VFlat (I := I) (M := M) g₀ g₁ gB).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 1 q
              (lc0VFlat (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λdt, Fdt, hΛdt_nn, hFdt_nn, hdt⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ 1 a ha_super hR hδ₀
  obtain ⟨Λκ, Fκ, hΛκ_nn, hFκ_nn, hκ⟩ :=
    lc0b_kappa_feed (I := I) (M := M) g₀ gB a ha_super hR hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 3 0 1 3
  refine ⟨Λdt * Λκ,
    fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (Λκ * Fdt q + Λdt * Fκ q)),
    mul_nonneg hΛdt_nn hΛκ_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg (mul_nonneg hΛκ_nn (hFdt_nn q))
        (mul_nonneg hΛdt_nn (hFκ_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hdt0, hdtL2⟩ := hdt g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hκ0, hκL2⟩ := hκ g₁ P htie hδ_le hδ0 hδ hPball
  exact lc0b_comp_feed_step (I := I) (M := M) g₀ 0 3 1 a
    (lc0PureDT (I := I) (M := M) g₀ g₁ 1) (lc0Kappa (I := I) (M := M) g₀ g₁ gB)
    C2 hC2_nn hC2 Λdt Λκ Fdt Fκ hΛdt_nn hΛκ_nn hdt0 hκ0 hdtL2 hκL2

theorem lc0b_iVField_feed (g₀ gB : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 1 x
            ((lc0IVField (I := I) (M := M) g₀ g₁ gB).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 1 q
              (lc0IVField (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λdt, Fdt, hΛdt_nn, hFdt_nn, hdt⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ 1 a ha_super hR hδ₀
  obtain ⟨Λvf, Fvf, hΛvf_nn, hFvf_nn, hvf⟩ :=
    lc0b_vflat_feed (I := I) (M := M) g₀ gB a ha_super hR hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 3 2 1 3
  set fr2 : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 with hfr2
  have hfr2_nn : 0 ≤ fr2 := by positivity
  refine ⟨Λdt * (fr2 * Λvf),
    fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * ((fr2 * Λvf) * Fdt q + Λdt * (fr2 * Fvf q))),
    mul_nonneg hΛdt_nn (mul_nonneg hfr2_nn hΛvf_nn),
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg
        (mul_nonneg (mul_nonneg hfr2_nn hΛvf_nn) (hFdt_nn q))
        (mul_nonneg hΛdt_nn (mul_nonneg hfr2_nn (hFvf_nn q))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hdt0, hdtL2⟩ := hdt g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hvf0, hvfL2⟩ := hvf g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hre0, hreL2⟩ := lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 3 1
    (lc0PureDT (I := I) (M := M) g₀ g₁ 1) lc0IVPerm Λdt Fdt a hdt0 hdtL2
  obtain ⟨hse0, hseL2⟩ := lc0b_slotExtendIter_feed_transfer (I := I) (M := M) g₀ 0 1 2
    (lc0VFlat (I := I) (M := M) g₀ g₁ gB) Λvf Fvf a hvf0 hvfL2
  exact lc0b_comp_feed_step (I := I) (M := M) g₀ 2 3 1 a
    (reindexCoeffGen (I := I) (M := M) g₀ 3 1 (lc0PureDT (I := I) (M := M) g₀ g₁ 1) lc0IVPerm)
    (slotExtendIter (I := I) (M := M) g₀ 0 1 2 (lc0VFlat (I := I) (M := M) g₀ g₁ gB))
    C2 hC2_nn hC2 Λdt (fr2 * Λvf) Fdt (fun q => fr2 * Fvf q) hΛdt_nn
    (mul_nonneg hfr2_nn hΛvf_nn) hre0 hse0 hreL2 hseL2

theorem lc0b_cdVField_feed (g₀ gB : SmoothRiemannianMetric I M) (a : ℕ)
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
            ((lc0CdVField (I := I) (M := M) g₀ g₁ gB).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 1 q
              (lc0CdVField (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λiv, Fiv, hΛiv_nn, hFiv_nn, hiv⟩ :=
    lc0b_iVField_feed (I := I) (M := M) g₀ gB a ha_super hR hδ₀
  obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
    lc0b_cds_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 2 1 1 2
  refine ⟨Λiv * Λcd,
    fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (Λcd * Fiv q + Λiv * Fcd q)),
    mul_nonneg hΛiv_nn hΛcd_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg (mul_nonneg hΛcd_nn (hFiv_nn q))
        (mul_nonneg hΛiv_nn (hFcd_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hiv0, hivL2⟩ := hiv g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hcd0, hcdL2⟩ := hcd g₁ P htie hδ_le hδ0 hδ hPball
  exact lc0b_comp_feed_step (I := I) (M := M) g₀ 1 2 1 a
    (lc0IVField (I := I) (M := M) g₀ g₁ gB) (connDiffSection (I := I) g₁ g₀)
    C2 hC2_nn hC2 Λiv Λcd Fiv Fcd hΛiv_nn hΛcd_nn hiv0 hcd0 hivL2 hcdL2

end LieCorr0BoundsF2

end LieCorr0BoundsAll

end DifferentialGeometry.Analysis.Spectral

end

