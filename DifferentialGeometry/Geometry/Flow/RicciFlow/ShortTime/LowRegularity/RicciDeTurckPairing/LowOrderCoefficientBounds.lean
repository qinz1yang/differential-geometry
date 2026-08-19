import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.LowOrderCoefficientJointSmoothness
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJetNaturality
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorFieldJetProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis (sq_add_sq_le_sq_add_of_nonneg)
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Elliptic
  (integrable_riemannianFiberNormSq_toSection riemannianFiberNormSq)
open DifferentialGeometry.Analysis.Sobolev
  (cometricCastG0 covariantJetNormSq covariantJetNormSq_add_le covariantJetNormSq_nonneg
    covariantJetNormSq_reindexCoeffGen covariantJetNormSq_rsDomDomCongrSection
    covariantJetNormSq_slotExtend_le covariantJetNormSq_smul covariantJetNormSq_sub_le
    covariantJetNormSq_sum_six_le exists_covariantJetNormSq_two_operatorFieldComposition_le iteratedCovGrad
    normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo rsDomDomCongrSection
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs)
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply operatorFieldApplication_add_left operatorFieldApplication_smul_left operatorFieldApplication_smul_right operatorFieldApplication_sub_left ccOperatorFieldComp
    operatorFieldComposition_sub_left operatorFieldComposition_sub_right ccTensorToHs ccTensorToHs_smul deTurckLieTopOrderPairingFamily
    metricComparisonEndomorphismField
    iteratedCovGrad_neg lieCorrectionZeroRiemann norm_iteratedCovGrad_domDomCongrSection permCoeff pureTrace
    pureTrace_toSection riemannianFiberNormSq_symmS_zero_le_fibreSmall slotExtend slotExtend_sub slotExtendIter
    symmS_eq_self_of_ccTensorBilin_symm)
open DifferentialGeometry.Geometry.Connection (slotInsertEndoCc)
open DifferentialGeometry.Geometry.Curvature
  (connectionDifferenceFib_apply_eval connectionDifferenceSection connectionDifferenceSection_self connectionDifferenceSection_toSection
    slotInsertEndoFib)

private lemma mul_le_one_add_mul_sum
    (R D N : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hN : 0 ≤ N) :
    N * R ≤ (1 + R) * (D + N) := by
  calc
    N * R ≤ (D + N) * R :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hD) hR
    _ ≤ (D + N) * (1 + R) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (add_nonneg hD hN)
    _ = (1 + R) * (D + N) := mul_comm _ _

private lemma le_one_add_mul_sum
    (R D N : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hN : 0 ≤ N) :
    D ≤ (1 + R) * (D + N) := by
  calc
    D ≤ D + N := le_add_of_nonneg_right hN
    _ = 1 * (D + N) := (one_mul _).symm
    _ ≤ (1 + R) * (D + N) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hR) (add_nonneg hD hN)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

noncomputable def lowOrderZeroCoefficientPath
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g -
      deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
        lieDecompositionQ lieDecompositionEps s) +
    lieCorrectionZeroRiemann (I := I) (M := M) g gm

noncomputable def lowOrderFirstDerivativeCoefficientPath
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 3 2 :=
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  (-2 * s : ℝ) • ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm T +
    s • lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm T +
    s • lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm g T

noncomputable def affineLowOrderZeroCoefficientPath
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  lowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ s -
    lieCorrectionQuadraticZeroCoefficient (I := I) (M := M) g gm

noncomputable def affineLowOrderFirstDerivativeCoefficientPath
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 3 2 :=
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ s +
    s • lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm T

theorem affineLowOrderZeroCoefficientPath_eq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
    affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ s =
      lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gm T s +
        lieCorrectionZeroRiemann (I := I) (M := M) g gm := by
  dsimp only
  rw [affineLowOrderZeroCoefficientPath, lowOrderZeroCoefficientPath]
  calc
    (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
          lieDecompositionQ lieDecompositionEps s) +
          lieCorrectionZeroRiemann (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
        lieCorrectionQuadraticZeroCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) =
      ((deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g -
          deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
            lieDecompositionQ lieDecompositionEps s) -
        lieCorrectionQuadraticZeroCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s)) +
        lieCorrectionZeroRiemann (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) := by abel
    _ = _ := by
      rw [deTurckLieCovariantDerivative_affineZero_decomposition (I := I) (M := M)
        g T hT hδ_lt hδ hδZ hs]

theorem exists_cometricCastG0_covariantJetNormSq_two_low_bound
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (cometricCastG0 (I := I) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  classical
  let aStar : ℕ := 2 * Module.finrank ℝ E + 10
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Λ, F, hΛ, hF, hcast⟩ :=
    cometricCastG0_order0sup_jetL2_radiusFree
      (I := I) (M := M) g aStar le_rfl hδ₀ hΛ₀0
  refine ⟨F 2, hF 2, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact riemannianFiberNormSq_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  have hraw := (hcast g₁ P htie hδ_le hδ0 hδ hsup).2 2 (by
    dsimp only [aStar]
    omega)
  simpa only [covariantJetNormSq, Nat.reduceAdd] using hraw

theorem exists_reindexedCometricDoubleTrace_covariantJetNormSq_two_low_bound
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  obtain ⟨Kc, hKc, hc⟩ :=
    exists_cometricCastG0_covariantJetNormSq_two_low_bound (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr * Kc
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg hfr hKc
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 i
          (reindexedCometricDoubleTrace (I := I) (M := M) g g₁)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, fr *
        ‖iteratedCovGrad (I := I) g 3 1 i
          (cometricCastG0 (I := I) g g₁)‖ ^ 2 := by
        exact Finset.sum_le_sum fun i _ => by
          simpa only [fr] using
            norm_iteratedCovGrad_reindexedCometricDoubleTrace_sq_le (I := I) (M := M) g g₁ i
    _ = fr * covariantJetNormSq (I := I) (M := M) g 2
        (cometricCastG0 (I := I) g g₁) := by
      rw [← Finset.mul_sum]
    _ ≤ fr * (Kc *
        (1 + covariantJetNormSq (I := I) (M := M) g 2 P)) :=
      mul_le_mul_of_nonneg_left
        (hc g₁ P hP htie hδ_le hδ0 hδ) hfr
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
      simp only [K]
      ring

theorem exists_lieCorrectionZeroRiemann_covariantJetNormSq_two_low_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroRiemann (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  obtain ⟨Kl, hKl, hlive⟩ :=
    exists_reindexedCometricDoubleTrace_covariantJetNormSq_two_low_bound (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 4 2
  let B : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (lieCorrectionZeroRiemannLift (I := I) g)
  let K : ℝ := Ca * Kl * B
  have hB : 0 ≤ B :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
      (lieCorrectionZeroRiemannLift (I := I) g)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hCa hKl) hB
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hLive := hlive g₁ P hP htie hδ_le hδ0 hδ
  have hApp := happ
    (reindexedCometricDoubleTrace (I := I) (M := M) g g₁)
    (lieCorrectionZeroRiemannLift (I := I) g)
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (lieCorrectionZeroRiemann (I := I) (M := M) g g₁) =
      covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 2 4 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g g₁)
          (lieCorrectionZeroRiemannLift (I := I) g)) := by
        rw [lieCorrectionZeroRiemann_eq_ccOperatorFieldComp (I := I) (M := M) g g₁]
        unfold covariantJetNormSq
        apply Finset.sum_congr rfl
        intro q _
        rw [iteratedCovGrad_neg, norm_neg]
    _ ≤ Ca *
        covariantJetNormSq (I := I) (M := M) g 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g g₁) *
        covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroRiemannLift (I := I) g) := hApp
    _ ≤ Ca * (Kl *
        (1 + covariantJetNormSq (I := I) (M := M) g 2 P)) * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLive hCa) hB
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
      simp only [K]
      ring

theorem exists_lieCorrectionCurvatureZeroCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) T s) ≤
        K * R ^ 2 := by
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 6 2
  obtain ⟨ρ, Bp, hρ, hBp, hpair⟩ :=
    RicciDeTurckLowOrder.pair_trace_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Cc, hCc, hcurv⟩ :=
    exists_riemannCurvatureCoefficientField_covariantJetNormSq_bound (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  let K : ℝ := Ca * Bp ^ 2 * (fr ^ 2 * Cc)
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg hCa (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) hCc)
  refine ⟨ρ, K, hρ, hK, ?_⟩
  intro T δ hδ_le hδT hδZ R hR hT2 hTn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgm
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs22 : (s / 2) ^ 2 ≤ (1 : ℝ) := by
    nlinarith [hs.1, hs.2]
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgm, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hPn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTn)
  have hPair : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm) ≤ Bp ^ 2 :=
    hpair P gm hPtie hPn
  let V : SmoothCcTensor g 0 4 :=
    (-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g T
  have hV : covariantJetNormSq (I := I) (M := M) g 2 V ≤ Cc * R ^ 2 := by
    have hbase : covariantJetNormSq (I := I) (M := M) g 2
        (riemannCurvatureCoefficientField (I := I) (M := M) g T) ≤ Cc * R ^ 2 :=
      (hcurv T).trans (mul_le_mul_of_nonneg_left hT2 hCc)
    simp only [V, covariantJetNormSq_smul]
    calc
      (-(s / 2)) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (riemannCurvatureCoefficientField (I := I) (M := M) g T) =
          (s / 2) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
            (riemannCurvatureCoefficientField (I := I) (M := M) g T) := by ring
      _ ≤ covariantJetNormSq (I := I) (M := M) g 2
          (riemannCurvatureCoefficientField (I := I) (M := M) g T) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hs22
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
            (riemannCurvatureCoefficientField (I := I) (M := M) g T))
      _ ≤ Cc * R ^ 2 := hbase
  have hIter : slotExtendIter (I := I) (M := M) g 0 4 2 V =
      slotExtend (I := I) (M := M) g 1 5
        (slotExtend (I := I) (M := M) g 0 4 V) := rfl
  have hX : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 6
        (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
        (slotExtendIter (I := I) (M := M) g 0 4 2 V)) ≤
      fr ^ 2 * (Cc * R ^ 2) := by
    rw [operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2 V)) =
        covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 5
            (slotExtend (I := I) (M := M) g 0 4 V)) := by
          rw [hIter, covariantJetNormSq_rsDomDomCongrSection]
      _ ≤ fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 4 V) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 V) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 4 _) hfr
      _ ≤ fr * (fr * (Cc * R ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hV hfr) hfr
      _ = fr ^ 2 * (Cc * R ^ 2) := by ring
  rw [hgm, lieCorrectionCurvatureZeroCoefficient, covariantJetNormSq_smul, neg_one_sq, one_mul]
  refine (happ _ _).trans ?_
  have hstep := mul_le_mul (mul_le_mul_of_nonneg_left hPair hCa) hX
    (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
    (mul_nonneg hCa (sq_nonneg _))
  refine hstep.trans ?_
  simp only [K]
  exact le_of_eq (by ring)

theorem exists_lieCorrectionCurvatureZeroCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R D2 N : ℝ), 0 ≤ R → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) T s -
            lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) U s) ≤
        (B * (1 + R) * (D2 + N)) ^ 2 := by
  obtain ⟨ρp, Cp, hρp, hCp, hpair⟩ :=
    RicciDeTurckLowOrder.pairTrace_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Bp, hρb, hBp, hbdd⟩ :=
    RicciDeTurckLowOrder.pair_trace_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Cc, hCc, hcurv⟩ :=
    exists_riemannCurvatureCoefficientField_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 6 2
  let ρ : ℝ := min ρp ρb
  let fr : ℝ := Module.finrank ℝ E
  let K0 : ℝ := fr ^ 2 * Cc
  let S : ℝ := Real.sqrt (2 * Ca * K0)
  let B : ℝ := S * (Cp + Bp)
  have hρ : 0 < ρ := lt_min hρp hρb
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK0 : 0 ≤ K0 := mul_nonneg (sq_nonneg _) hCc
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = 2 * Ca * K0 := by
    simpa only [S] using Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) hCa) hK0)
  have hB : 0 ≤ B := mul_nonneg hS (add_nonneg hCp hBp)
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T U δ hδ_le hδT hδU hδZ R D2 N hR hD2 hN
    hT2 hU2 hTU2 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s
  let gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s
  let P : SmoothCcTensor g 0 2 := s • T
  let Q : SmoothCcTensor g 0 2 := s • U
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by nlinarith [hs.1, hs.2]
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [gmT, P, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [gmU, Q, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hPn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρp := by
    simp only [P, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTn.trans (min_le_left _ _))
  have hQn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρp := by
    simp only [Q, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hUn.trans (min_le_left _ _))
  have hQnb :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρb := by
    simp only [Q, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hUn.trans (min_le_right _ _))
  have hPQn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    rw [show P - Q = s • (T - U) by simp only [P, Q, smul_sub],
      ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTUn)
  let AT : SmoothCcTensor g 6 2 := cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT
  let AU : SmoothCcTensor g 6 2 := cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU
  have hAD : covariantJetNormSq (I := I) (M := M) g 2 (AT - AU) ≤ (Cp * N) ^ 2 := by
    have hraw := hpair P Q gmT gmU hPtie hQtie hPn hQn
    refine hraw.trans (pow_le_pow_left₀
      (mul_nonneg hCp (norm_nonneg _)) ?_ 2)
    exact mul_le_mul_of_nonneg_left hPQn hCp
  have hAU : covariantJetNormSq (I := I) (M := M) g 2 AU ≤ Bp ^ 2 := by
    simpa only [AU] using hbdd Q gmU hQtie hQnb
  have htransfer : ∀ Z : SmoothCcTensor g 0 4,
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 6 6
            (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
            (slotExtendIter (I := I) (M := M) g 0 4 2 Z)) ≤
        fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 Z := by
    intro Z
    have hIter : slotExtendIter (I := I) (M := M) g 0 4 2 Z =
        slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4 Z) := rfl
    rw [operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2 Z)) =
        covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 5
            (slotExtend (I := I) (M := M) g 0 4 Z)) := by
              rw [hIter, covariantJetNormSq_rsDomDomCongrSection]
      _ ≤ fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 4 Z) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 Z) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 4 _) hfr
      _ = fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 Z := by ring
  let ZT : SmoothCcTensor g 0 4 :=
    (-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g T
  let ZU : SmoothCcTensor g 0 4 :=
    (-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g U
  let ZD : SmoothCcTensor g 0 4 := ZT - ZU
  have hs22 : (s / 2) ^ 2 ≤ (1 : ℝ) := by nlinarith [hs.1, hs.2]
  have hZT : covariantJetNormSq (I := I) (M := M) g 2 ZT ≤ Cc * R ^ 2 := by
    have hbase := (hcurv T).trans (mul_le_mul_of_nonneg_left hT2 hCc)
    simp only [ZT, covariantJetNormSq_smul]
    have hcoef : (-(s / 2) : ℝ) ^ 2 ≤ 1 := by nlinarith
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _) hcoef).trans hbase
  have hZD : covariantJetNormSq (I := I) (M := M) g 2 ZD ≤ Cc * D2 ^ 2 := by
    have hbase : covariantJetNormSq (I := I) (M := M) g 2
        (riemannCurvatureCoefficientField (I := I) (M := M) g T -
          riemannCurvatureCoefficientField (I := I) (M := M) g U) ≤ Cc * D2 ^ 2 := by
      rw [riemannCurvatureCoefficientField_sub (I := I) (M := M) g T U]
      exact (hcurv (T - U)).trans
        (mul_le_mul_of_nonneg_left hTU2 hCc)
    rw [show ZD = (-(s / 2) : ℝ) •
        (riemannCurvatureCoefficientField (I := I) (M := M) g T -
          riemannCurvatureCoefficientField (I := I) (M := M) g U) by
          simp only [ZD, ZT, ZU, smul_sub], covariantJetNormSq_smul]
    have hcoef : (-(s / 2) : ℝ) ^ 2 ≤ 1 := by nlinarith
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _) hcoef).trans hbase
  let XT : SmoothCcTensor g 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
      (slotExtendIter (I := I) (M := M) g 0 4 2 ZT)
  let XU : SmoothCcTensor g 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
      (slotExtendIter (I := I) (M := M) g 0 4 2 ZU)
  let XD : SmoothCcTensor g 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
      (slotExtendIter (I := I) (M := M) g 0 4 2 ZD)
  have hXD_eq : XT - XU = XD := by
    simp only [XT, XU, XD, ZD, slotExtendIter]
    rw [slotExtend_sub, slotExtend_sub]
    rw [operatorFieldComposition_sub_right]
  have hXT : covariantJetNormSq (I := I) (M := M) g 2 XT ≤ K0 * R ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 XT ≤
          fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 ZT := by
            simpa only [XT] using htransfer ZT
      _ ≤ fr ^ 2 * (Cc * R ^ 2) :=
        mul_le_mul_of_nonneg_left hZT (sq_nonneg _)
      _ = K0 * R ^ 2 := by simp only [K0]; ring
  have hXD : covariantJetNormSq (I := I) (M := M) g 2 (XT - XU) ≤
      K0 * D2 ^ 2 := by
    rw [hXD_eq]
    calc
      covariantJetNormSq (I := I) (M := M) g 2 XD ≤
          fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 ZD := by
            simpa only [XD] using htransfer ZD
      _ ≤ fr ^ 2 * (Cc * D2 ^ 2) :=
        mul_le_mul_of_nonneg_left hZD (sq_nonneg _)
      _ = K0 * D2 ^ 2 := by simp only [K0]; ring
  have hsplit :
      lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmT T s -
          lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmU U s =
        (-1 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g 2 6 2 (AT - AU) XT +
            ccOperatorFieldComp (I := I) (M := M) g 2 6 2 AU (XT - XU)) := by
    simp only [lieCorrectionCurvatureZeroCoefficient, AT, AU, XT, XU, ZT, ZU]
    rw [operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  let x : ℝ := S * Cp * N * R
  let y : ℝ := S * Bp * D2
  have hx : 0 ≤ x :=
    mul_nonneg (mul_nonneg (mul_nonneg hS hCp) hN) hR
  have hy : 0 ≤ y := mul_nonneg (mul_nonneg hS hBp) hD2
  have hterm1 : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2 (AT - AU) XT) ≤
      Ca * (Cp * N) ^ 2 * (K0 * R ^ 2) := by
    refine (happ (AT - AU) XT).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hAD hCa) hXT
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g XT)
      (mul_nonneg hCa (sq_nonneg _))
  have hterm2 : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2 AU (XT - XU)) ≤
      Ca * Bp ^ 2 * (K0 * D2 ^ 2) := by
    refine (happ AU (XT - XU)).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hAU hCa) hXD
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g (XT - XU))
      (mul_nonneg hCa (sq_nonneg _))
  have hxSq : 2 * (Ca * (Cp * N) ^ 2 * (K0 * R ^ 2)) = x ^ 2 := by
    simp only [x, mul_pow, hSsq]
    ring
  have hySq : 2 * (Ca * Bp ^ 2 * (K0 * D2 ^ 2)) = y ^ 2 := by
    simp only [y, mul_pow, hSsq]
    ring
  have hsum : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2 (AT - AU) XT +
        ccOperatorFieldComp (I := I) (M := M) g 2 6 2 AU (XT - XU)) ≤
      (x + y) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g 2 6 2 (AT - AU) XT) +
          covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g 2 6 2 AU (XT - XU))) ≤
        2 * (Ca * (Cp * N) ^ 2 * (K0 * R ^ 2) +
          Ca * Bp ^ 2 * (K0 * D2 ^ 2)) :=
            mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by norm_num)
      _ = x ^ 2 + y ^ 2 := by rw [← hxSq, ← hySq]; ring
      _ ≤ (x + y) ^ 2 := sq_add_sq_le_sq_add_of_nonneg hx hy
  have hF1 : N * R ≤ (1 + R) * (D2 + N) := by
    exact mul_le_one_add_mul_sum R D2 N hR hD2 hN
  have hF2 : D2 ≤ (1 + R) * (D2 + N) := by
    exact le_one_add_mul_sum R D2 N hR hD2 hN
  have hxy : x + y ≤ B * (1 + R) * (D2 + N) := by
    calc
      x + y ≤ S * Cp * ((1 + R) * (D2 + N)) +
          S * Bp * ((1 + R) * (D2 + N)) :=
        by
          simpa only [x, y, mul_assoc] using
            (add_le_add
              (mul_le_mul_of_nonneg_left hF1 (mul_nonneg hS hCp))
              (mul_le_mul_of_nonneg_left hF2 (mul_nonneg hS hBp)))
      _ = B * (1 + R) * (D2 + N) := by simp only [B]; ring
  change covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmT T s -
        lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmU U s) ≤
    (B * (1 + R) * (D2 + N)) ^ 2
  rw [hsplit, covariantJetNormSq_smul]
  norm_num
  exact hsum.trans
    (pow_le_pow_left₀ (add_nonneg hx hy) hxy 2)

theorem exists_affineLowOrderZeroCoefficientPath_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R D2 N : ℝ), 0 ≤ R → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδT hδZ s -
            affineLowOrderZeroCoefficientPath (I := I) (M := M) g U hδU hδZ s) ≤
        (B * (1 + R) * (D2 + N)) ^ 2 := by
  obtain ⟨ρc, Bc, hρc, hBc, hcurv⟩ :=
    exists_lieCorrectionCurvatureZeroCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρr, Cr, hρr, hCr, hriem⟩ :=
    exists_lieCorrectionZeroRiemann_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  let ρ : ℝ := min ρc ρr
  let B : ℝ := 2 * (Bc + Cr)
  have hρ : 0 < ρ := lt_min hρc hρr
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (add_nonneg hBc hCr)
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T U hT hU δ hδ_le hδT hδU hδZ R D2 N hR hD2 hN
    hT2 hU2 hTU2 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s
  let gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s
  let P : SmoothCcTensor g 0 2 := s • T
  let Q : SmoothCcTensor g 0 2 := s • U
  let Z : ℝ := (1 + R) * (D2 + N)
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [gmT, P, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [gmU, Q, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hPn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρr := by
    simp only [P, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTn.trans (min_le_right _ _))
  have hQn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρr := by
    simp only [Q, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hUn.trans (min_le_right _ _))
  have hPQn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    rw [show P - Q = s • (T - U) by simp only [P, Q, smul_sub],
      ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTUn)
  have hc : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmT T s -
        lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmU U s) ≤
      (Bc * Z) ^ 2 := by
    simpa only [gmT, gmU, Z, mul_assoc] using
      hcurv T U hδ_le hδT hδU hδZ R D2 N hR hD2 hN
        hT2 hU2 hTU2
        (hTn.trans (min_le_left _ _))
        (hUn.trans (min_le_left _ _)) hTUn hs
  have hr0 : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroRiemann (I := I) (M := M) g gmT -
        lieCorrectionZeroRiemann (I := I) (M := M) g gmU) ≤
      (Cr * N) ^ 2 :=
    (hriem P Q gmT gmU hPtie hQtie hPn hQn).trans
      (pow_le_pow_left₀ (mul_nonneg hCr (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hPQn hCr) 2)
  have hZ : 0 ≤ Z :=
    mul_nonneg (add_nonneg (by norm_num) hR) (add_nonneg hD2 hN)
  have hNZ : N ≤ Z := by
    simp only [Z]
    nlinarith [mul_nonneg hR (add_nonneg hD2 hN)]
  have hr : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroRiemann (I := I) (M := M) g gmT -
        lieCorrectionZeroRiemann (I := I) (M := M) g gmU) ≤
      (Cr * Z) ^ 2 :=
    hr0.trans (pow_le_pow_left₀ (mul_nonneg hCr hN)
      (mul_le_mul_of_nonneg_left hNZ hCr) 2)
  rw [affineLowOrderZeroCoefficientPath_eq (I := I) (M := M) g T hT hδ_lt hδT hδZ hs,
    affineLowOrderZeroCoefficientPath_eq (I := I) (M := M) g U hU hδ_lt hδU hδZ hs]
  change covariantJetNormSq (I := I) (M := M) g 2
      ((lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmT T s +
          lieCorrectionZeroRiemann (I := I) (M := M) g gmT) -
        (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmU U s +
          lieCorrectionZeroRiemann (I := I) (M := M) g gmU)) ≤
    (B * (1 + R) * (D2 + N)) ^ 2
  rw [show
    (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmT T s +
        lieCorrectionZeroRiemann (I := I) (M := M) g gmT) -
      (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmU U s +
        lieCorrectionZeroRiemann (I := I) (M := M) g gmU) =
      (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmT T s -
        lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmU U s) +
      (lieCorrectionZeroRiemann (I := I) (M := M) g gmT -
        lieCorrectionZeroRiemann (I := I) (M := M) g gmU) by module]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmT T s -
            lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmU U s) +
        covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroRiemann (I := I) (M := M) g gmT -
            lieCorrectionZeroRiemann (I := I) (M := M) g gmU)) ≤
      2 * ((Bc * Z) ^ 2 + (Cr * Z) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hc hr) (by norm_num)
    _ ≤ 2 * ((Bc * Z + Cr * Z) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (sq_add_sq_le_sq_add_of_nonneg (mul_nonneg hBc hZ) (mul_nonneg hCr hZ)) (by norm_num)
    _ ≤ (2 * (Bc + Cr) * Z) ^ 2 := by
      nlinarith [sq_nonneg (Bc * Z + Cr * Z)]
    _ = (B * (1 + R) * (D2 + N)) ^ 2 := by
      simp only [B, Z]
      ring

theorem exists_affineLowOrderZeroCoefficientPath_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδT hδZ s) ≤
        (B R) ^ 2 := by
  obtain ⟨ρ, Kc, hρ, hKc, hcurv⟩ :=
    exists_lieCorrectionCurvatureZeroCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Kr, hKr, hriem⟩ :=
    exists_lieCorrectionZeroRiemann_covariantJetNormSq_two_low_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let X : ℝ → ℝ := fun R =>
    2 * (Kc * R ^ 2 + Kr * (1 + R ^ 2))
  let B : ℝ → ℝ := fun R => Real.sqrt (X R)
  have hX : ∀ R : ℝ, 0 ≤ R → 0 ≤ X R := by
    intro R hR
    have hc : 0 ≤ Kc * R ^ 2 := mul_nonneg hKc (sq_nonneg _)
    have hr : 0 ≤ Kr * (1 + R ^ 2) :=
      mul_nonneg hKr (by positivity)
    simp only [X]
    linarith
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R hR hT2 hTn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgm
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by nlinarith [hs.1, hs.2]
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgm, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hc : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gm T s) ≤ Kc * R ^ 2 := by
    rw [hgm]
    exact hcurv T hδ_le hδT hδZ R hR hT2 hTn hs
  have hr : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroRiemann (I := I) (M := M) g gm) ≤ Kr * (1 + R ^ 2) := by
    refine (hriem gm P hPsymm hPtie hδ_le hδ0 hδP).trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hP2]) hKr
  rw [affineLowOrderZeroCoefficientPath_eq (I := I) (M := M) g T hT hδ_lt hδT hδZ hs]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
  rw [show (B R) ^ 2 = X R from Real.sq_sqrt (hX R hR)]
  simp only [X]
  linarith

theorem lowOrderFirstDerivativeCoefficientPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ) := by
  have hR := ricciConnectionDifferenceDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T T hδ hδZ
  have hR' : linearizedRicciThreeArmHjoint (I := I) (M := M) g 3
      (fun t => ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) T)
      (δ := δ) (δ' := δ) := hR
  have hRN := threeArmJoint_smul (I := I) (M := M) (r := 3) g (-2 : ℝ) _ hR'
  have hRN' : JointlySmoothCcTensorFamily (I := I) g 3 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => (-2 : ℝ) • ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) T) := hRN
  have hRNP := jointlySmoothCcTensorFamily_parameter_smul (I := I) (M := M) g hRN'
  have hV := lieCorrectionZeroVectorBundleDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T T hδ hδZ
  have hVP := jointlySmoothCcTensorFamily_parameter_smul (I := I) (M := M) g hV
  have hA := lieCorrectionZeroMixedConnectionDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T T hδ hδZ
  have hAP := jointlySmoothCcTensorFamily_parameter_smul (I := I) (M := M) g hA
  have hsum := jointlySmoothCcTensorFamily_add (I := I) (M := M) g
    (jointlySmoothCcTensorFamily_add (I := I) (M := M) g hRNP hVP) hAP
  refine hsum.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (TensorRSModel 3 2 ℝ E)
    (E := fun x : M => TensorRSSpace 3 2 I x) q.1 z) ?_
  rw [lowOrderFirstDerivativeCoefficientPath]
  simp only [smul_smul]
  congr 2
  ring_nf

theorem lieCorrectionZeroRiemann_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 2 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => lieCorrectionZeroRiemann (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  have hLive := reindexedCometricDoubleTrace_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hPass := jointlySmoothCcTensorFamily_const (I := I) (M := M) g
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
    (lieCorrectionZeroRiemannLift (I := I) g)
  have happ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hLive hPass
  have happ' : linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ccOperatorFieldComp (I := I) (M := M) g 2 4 2
        (reindexedCometricDoubleTrace (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ t))
        (lieCorrectionZeroRiemannLift (I := I) g))
      (δ := δ) (δ' := δ) := happ
  have hs := threeArmJoint_smul (I := I) (M := M) (r := 2) g (-1 : ℝ) _ happ'
  simpa only [linearizedRicciThreeArmHjoint, lieCorrectionZeroRiemann_eq_ccOperatorFieldComp,
    neg_one_smul] using hs

theorem lowOrderZeroCoefficientPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 2 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (lowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ) := by
  have hLie : JointlySmoothCcTensorFamily (I := I) g 2 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => lieDecomposition0 (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) g T hδ hδZ t) :=
    lieDecomposition_joint (I := I) (M := M) g g T hδ hδZ
  have hR := lieCorrectionZeroRiemann_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  simpa only [lowOrderZeroCoefficientPath, lieDecomposition0] using
    jointlySmoothCcTensorFamily_add (I := I) (M := M) g hLie hR

theorem affineLowOrderZeroCoefficientPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 2 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ) := by
  have hL := lowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hQ := lieCorrectionQuadraticZeroCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hT hδ hδZ
  simpa only [affineLowOrderZeroCoefficientPath] using
    jointlySmoothCcTensorFamily_sub (I := I) (M := M) g hL hQ

theorem affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ) := by
  have hL := lowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hQ := lieCorrectionQuadraticFirstDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hQP := jointlySmoothCcTensorFamily_parameter_smul (I := I) (M := M) g hQ
  simpa only [affineLowOrderFirstDerivativeCoefficientPath] using
    jointlySmoothCcTensorFamily_add (I := I) (M := M) g hL hQP

theorem lowerScalePathIntegrand_apply_decomposition
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
          g g T hδ hδZ s) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (lowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ s) T +
        operatorFieldApply (I := I) (M := M) g 3 2
          (lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ s)
          (covGrad (I := I) (M := M) g 0 2 T) := by
  let P : SmoothCcTensor g 0 2 := s • T
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 s = P by
      simp only [P, convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hric := ricciConnectionDifferenceDerivativeCoefficient_apply (I := I) (M := M) g gm P T hP htie
  have hvb := lieCorrectionZeroVectorBundleDerivativeCoefficient_apply (I := I) (M := M) g gm P T hP htie
  have hamix := lieCorrectionZeroMixedConnectionDerivativeCoefficient_apply (I := I) (M := M) g gm g P T hP htie
  rw [lowerScalePathIntegrand_decomposition (I := I) (M := M) g T hT hδ_lt hδ hδZ hs]
  simp only [operatorFieldApplication_add_left, operatorFieldApplication_smul_left]
  rw [lieCorrectionZeroVectorBundle_eq_expansion (I := I) (M := M) g gm,
    lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g gm g]
  rw [hric, hvb, hamix]
  rw [show covGrad (I := I) (M := M) g 0 2 P =
      s • covGrad (I := I) (M := M) g 0 2 T by
    exact covGrad_smul (I := I) (M := M) g 0 2 s T]
  simp only [operatorFieldApplication_smul_right, lowOrderZeroCoefficientPath, lowOrderFirstDerivativeCoefficientPath, gm,
    operatorFieldApplication_add_left, operatorFieldApplication_smul_left, smul_smul]
  abel

theorem lowerScalePathIntegrand_apply_affine_decomposition
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
          g g T hδ hδZ s) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ s) T +
        operatorFieldApply (I := I) (M := M) g 3 2
          (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ s)
          (covGrad (I := I) (M := M) g 0 2 T) := by
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g (s • T) x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 s = s • T by
      simp only [convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ
        (Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs) x u v
  have hsT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (s • T) x u v =
        ccTensorBilin (I := I) g (s • T) x v u := by
    intro x u v
    simp only [ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hq := lieCorrectionQuadraticFirstDerivativeCoefficient_apply (I := I) (M := M) g gm (s • T) T hsT htie
  have hqT : operatorFieldApply (I := I) (M := M) g 2 2
      (lieCorrectionQuadraticZeroCoefficient (I := I) (M := M) g gm) T =
      s • operatorFieldApply (I := I) (M := M) g 3 2
        (lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm T)
          (covGrad (I := I) (M := M) g 0 2 T) := by
    rw [hq]
    rw [show covGrad (I := I) (M := M) g 0 2 (s • T) =
        s • covGrad (I := I) (M := M) g 0 2 T by
      exact covGrad_smul (I := I) (M := M) g 0 2 s T]
    simp only [operatorFieldApplication_smul_right]
  rw [lowerScalePathIntegrand_apply_decomposition (I := I) (M := M) g T hT hδ_lt hδ hδZ hs]
  simp only [affineLowOrderZeroCoefficientPath, affineLowOrderFirstDerivativeCoefficientPath, operatorFieldApplication_sub_left, operatorFieldApplication_add_left,
    operatorFieldApplication_smul_left]
  rw [hqT]
  abel

noncomputable def lowOrderZeroCoefficientPathIntegral
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 2 2
    (lowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (lowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ)

noncomputable def lowOrderFirstDerivativeCoefficientPathIntegral
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 3 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 3 2
    (lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (lowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ)

noncomputable def affineLowOrderZeroCoefficientPathIntegral
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 2 2
    (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hT hδ hδZ)

noncomputable def affineLowOrderZeroCoefficientPathIntegralDifference
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (hU : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g U x u v =
        ccTensorBilin (I := I) g U x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 2 2
    (fun s =>
      affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδT hδZ s -
        affineLowOrderZeroCoefficientPath (I := I) (M := M) g U hδU hδZ s)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (jointlySmoothCcTensorFamily_sub (I := I) (M := M) g
      (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hT hδT hδZ)
      (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g U hU hδU hδZ))

theorem lowOrderZeroCoefficientPathIntegral_sub
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (hU : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g U x u v =
        ccTensorBilin (I := I) g U x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M) g T hT hδ_lt hδT hδZ -
        affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M) g U hU hδ_lt hδU hδZ =
      affineLowOrderZeroCoefficientPathIntegralDifference (I := I) (M := M)
        g T U hT hU hδ_lt hδT hδU hδZ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply TensorRSSpace.toModel_injective
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hTcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2
      (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδT hδZ)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hT hδT hδZ) x
  have hUcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2
      (affineLowOrderZeroCoefficientPath (I := I) (M := M) g U hδU hδZ)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g U hU hδU hδZ) x
  have hTint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδT hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hTcont.mono hSI).intervalIntegrable
  have hUint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((affineLowOrderZeroCoefficientPath (I := I) (M := M) g U hδU hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hUcont.mono hSI).intervalIntegrable
  simp only [affineLowOrderZeroCoefficientPathIntegral, affineLowOrderZeroCoefficientPathIntegralDifference, pathIntegralCoeffField_toModel,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    TensorRSSpace.toModel_sub]
  rw [intervalIntegral.integral_sub hTint hUint]

theorem exists_affineLowOrderZeroCoefficientPathIntegral_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R D2 N : ℝ), 0 ≤ R → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M) g T hT
              (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ -
            affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M) g U hU
              (lt_of_le_of_lt hδ_le (by norm_num)) hδU hδZ) ≤
        (B * (1 + R) * (D2 + N)) ^ 2 := by
  obtain ⟨ρ, B, hρ, hB, hpoint⟩ :=
    exists_affineLowOrderZeroCoefficientPath_pairing_secondOrder_bound (I := I) (M := M) hDim g
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T U hT hU δ hδ_le hδT hδU hδZ R D2 N hR hD2 hN
    hT2 hU2 hTU2 hTn hUn hTUn
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  let Φ : ℝ → SmoothCcTensor g 2 2 := fun s =>
    affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδT hδZ s -
      affineLowOrderZeroCoefficientPath (I := I) (M := M) g U hδU hδZ s
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjoint : JointlySmoothCcTensorFamily (I := I) g 2 2 S Φ := by
    dsimp only [S, Φ]
    exact jointlySmoothCcTensorFamily_sub (I := I) (M := M) g
      (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hT hδT hδZ)
      (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g U hU hδU hδZ)
  have hBtot : 0 ≤ B * (1 + R) * (D2 + N) :=
    mul_nonneg (mul_nonneg hB (add_nonneg (by norm_num) hR))
      (add_nonneg hD2 hN)
  have hpath := path_jetL2_le (I := I) (M := M) g 2 2 2
    Φ S metricPerturbationPathDomain_isOpen hSI hjoint hBtot
    (fun s hs => by
      simpa only [Φ, covariantJetNormSq, Nat.reduceAdd] using
        hpoint T U hT hU hδ_le hδT hδU hδZ R D2 N
          hR hD2 hN hT2 hU2 hTU2 hTn hUn hTUn hs)
  rw [lowOrderZeroCoefficientPathIntegral_sub (I := I) (M := M)
    g T U hT hU hδ_lt hδT hδU hδZ]
  simpa only [affineLowOrderZeroCoefficientPathIntegralDifference, Φ, S, covariantJetNormSq, Nat.reduceAdd] using hpath

theorem exists_affineLowOrderZeroCoefficientPathIntegral_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M) g T hT
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ) ≤
        (B R) ^ 2 := by
  obtain ⟨ρ, B, hρ, hB, hpoint⟩ :=
    exists_affineLowOrderZeroCoefficientPath_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R hR hT2 hTn
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hpath := path_jetL2_le (I := I) (M := M) g 2 2 2
    (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδT hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen hSI
    (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hT hδT hδZ)
    (B := B R) (hB R hR)
    (fun s hs => by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using
        hpoint T hT hδ_le hδ0 hδT hδZ R hR hT2 hTn hs)
  simpa only [affineLowOrderZeroCoefficientPathIntegral, covariantJetNormSq, Nat.reduceAdd] using hpath

theorem exists_connectionDifferenceLowOrderOperator_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨C0, C1, hC0, hC1, hpair⟩ :=
    connSec_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let B : ℝ → ℝ := fun R => C0 0 + C1 0 * R
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact add_nonneg (hC0 0 (by norm_num))
      (mul_nonneg (hC1 0 (by norm_num)) hR)
  intro gm T hT htie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  have hzeroSymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  have hzeroTie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  have h02 :
      covariantJetNormSq (I := I) (M := M) g 2
          (0 : SmoothCcTensor g 0 2) ≤ (0 : ℝ) ^ 2 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • T by simp, covariantJetNormSq_smul]
    norm_num
  have hraw :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g -
            connectionDifferenceSection (I := I) g g) ≤
        (C0 0 * A + C1 0 * R + C1 0 * A * R) ^ 2 :=
    hpair gm g T (0 : SmoothCcTensor g 0 2) hT hzeroSymm
      htie hzeroTie hδ_le hδ0 hδT hδ_le hδ0 hδZ
      0 A R A (by norm_num) hA hR hA h02 hT3
      (by simpa only [sub_zero] using hT2)
      (by simpa only [sub_zero] using hT3)
  rw [connectionDifferenceSection_self (I := I) (M := M) g, sub_zero] at hraw
  have hc0 : 0 ≤ C0 0 := hC0 0 (by norm_num)
  have hc1 : 0 ≤ C1 0 := hC1 0 (by norm_num)
  have hold : 0 ≤ C0 0 * A + C1 0 * R + C1 0 * A * R :=
    add_nonneg (add_nonneg (mul_nonneg hc0 hA) (mul_nonneg hc1 hR))
      (mul_nonneg (mul_nonneg hc1 hA) hR)
  have hlin :
      C0 0 * A + C1 0 * R + C1 0 * A * R ≤
        B R * (1 + A) := by
    dsimp only [B]
    nlinarith [mul_nonneg hc0 (by norm_num : (0 : ℝ) ≤ 1),
      mul_nonneg hc1 hR]
  exact hraw.trans (pow_le_pow_left₀ hold hlin 2)

theorem exists_connectionDifferenceInsertionInnerDerivativeCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContrInsertionInnerField (I := I) g gm) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨C, hC, hsec⟩ := exists_connectionDifferenceLowOrderOperator_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => 3 * C R
  refine ⟨B, fun R hR => mul_nonneg (by norm_num) (hC R hR), ?_⟩
  intro gm T hT htie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  have hs := hsec gm T hT htie hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  rw [connectionDifferenceContrInsertionInnerField_eq_reindex_slotExtend
      (I := I) (M := M) g gm,
    covariantJetNormSq_reindexCoeffGen (I := I) (M := M) g]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 2
          (connectionDifferenceSection (I := I) gm g)) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _
    _ = 3 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g) := by rw [hDim]; norm_num
    _ ≤ 3 * (C R * (1 + A)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ (B R * (1 + A)) ^ 2 := by
      simp only [B]
      nlinarith [sq_nonneg (C R * (1 + A))]

theorem exists_connectionDifferenceContravariantInsertionField_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gm) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨C, hC, hsec⟩ := exists_connectionDifferenceLowOrderOperator_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => 3 * C R
  refine ⟨B, fun R hR => mul_nonneg (by norm_num) (hC R hR), ?_⟩
  intro gm T hT htie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  have hs := hsec gm T hT htie hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  rw [connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two
      (I := I) (M := M) g gm,
    covariantJetNormSq_reindexCoeffGen (I := I) (M := M) g]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 2 3
          (slotExtend (I := I) (M := M) g 1 2
            (connectionDifferenceSection (I := I) gm g))) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 2
            (connectionDifferenceSection (I := I) gm g)) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 3 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceSection (I := I) gm g)) :=
      mul_le_mul_of_nonneg_left
        (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _)
        (Nat.cast_nonneg _)
    _ = 9 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g) := by
      rw [hDim]
      ring
    _ ≤ 9 * (C R * (1 + A)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = (B R * (1 + A)) ^ 2 := by simp only [B]; ring

theorem iteratedCovGrad_slotInsertEndoCc_normSq_le
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) ^ s *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
      ((iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 1 (1 + i)
      (iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ))).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (s + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (s + 1) (s + 1) i
      (slotInsertEndoCc (I := I) (M := M) g s Λ))
    F hF (fun x =>
      riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
        (I := I) (M := M) g s Λ i x)
  have hint :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
          ((iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

theorem covariantJetNormSq_slotInsertEndoCc_le
    (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    covariantJetNormSq (I := I) (M := M) g m
        (slotInsertEndoCc (I := I) (M := M) g s Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        covariantJetNormSq (I := I) (M := M) g m
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range (m + 1), (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        iteratedCovGrad_slotInsertEndoCc_normSq_le (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

theorem covariantJetNormSq_slotInsertEndoCc_symmRaiseEndo_le
    (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (D : SmoothCcTensor g 0 2)
    (hD : symmS (I := I) (M := M) g D = D) :
    covariantJetNormSq (I := I) (M := M) g m
        (slotInsertEndoCc (I := I) (M := M) g s
          (symmRaiseEndo (I := I) (M := M) g D)) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        covariantJetNormSq (I := I) (M := M) g m D := by
  have h0 :
      covariantJetNormSq (I := I) (M := M) g m
          (slotInsertEndoCc (I := I) (M := M) g 0
            (symmRaiseEndo (I := I) (M := M) g D)) =
        covariantJetNormSq (I := I) (M := M) g m D := by
    rw [insert_symmRaise_eq (I := I) (M := M) g D]
    calc
      covariantJetNormSq (I := I) (M := M) g m
          (cometricRaiseSlot0Field (I := I) (M := M) g 0
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1)
              (symmS (I := I) (M := M) g D))) =
        covariantJetNormSq (I := I) (M := M) g m
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (symmS (I := I) (M := M) g D)) := by
          unfold covariantJetNormSq
          apply Finset.sum_congr rfl
          intro q _
          rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
            (I := I) (M := M) g 0
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1)
              (symmS (I := I) (M := M) g D)) q]
      _ = covariantJetNormSq (I := I) (M := M) g m
          (symmS (I := I) (M := M) g D) := by
        unfold covariantJetNormSq
        apply Finset.sum_congr rfl
        intro q _
        rw [norm_iteratedCovGrad_domDomCongrSection
          (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g D) q]
      _ = covariantJetNormSq (I := I) (M := M) g m D := by rw [hD]
  have hslot := covariantJetNormSq_slotInsertEndoCc_le (I := I) (M := M) g s m
    (symmRaiseEndo (I := I) (M := M) g D)
  rw [h0] at hslot
  exact hslot

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem sharpFlatEndoCc_eq_slotInsertEndoCc_zero
    (g gm : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g gm =
      slotInsertEndoCc (I := I) (M := M) g 0
        (metricComparisonEndomorphismField (I := I) (M := M) g gm) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g 0
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (metricComparisonEndomorphism (I := I) g gm x) om from rfl]
  rw [cotangentToDual_slotInsertEndoFib' (I := I) (M := M) x
    (metricComparisonEndomorphism (I := I) g gm x) om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g gm).toSection x) om =
      g0FlatCLM (I := I) g x (inverseMetricSharpFib (I := I) gm x om) from rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I) om
      (metricComparisonEndomorphism (I := I) g gm x w) =
      gm.inner x (inverseMetricSharpFib (I := I) gm x om)
        (metricComparisonEndomorphism (I := I) g gm x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) gm x om
      (metricComparisonEndomorphism (I := I) g gm x w)).symm]
  rw [show metricComparisonEndomorphism (I := I) g gm x w =
      inverseMetricSharpFib (I := I) gm x (g0FlatCLM (I := I) g x w) from by
    rw [metricComparisonEndomorphism_apply]]
  rw [gm.symm x (inverseMetricSharpFib (I := I) gm x om)
    (inverseMetricSharpFib (I := I) gm x (g0FlatCLM (I := I) g x w))]
  rw [inverseMetricSharpFib_inner (I := I) gm x
    (g0FlatCLM (I := I) g x w) (inverseMetricSharpFib (I := I) gm x om)]
  rw [cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [g.symm x w (inverseMetricSharpFib (I := I) gm x om)]

theorem exists_sharpFlatEndoCc_covariantJetNormSq_two_bound
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gm) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  classical
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Λ, Flow, hΛ, hFlow0, hFlow⟩ :=
    sharpFlatEndoCc_lowOrder_jetL2_radiusFree
      (I := I) (M := M) g
        (2 * Module.finrank ℝ E + 10) le_rfl hδ₀ hΛ₀0
  refine ⟨Flow 2, hFlow0 2, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact riemannianFiberNormSq_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  simpa only [covariantJetNormSq, Nat.reduceAdd] using
    (hFlow gm P htie hδ_le hδ0 hδ hsup).2 2 (by omega)

theorem exists_metricComparisonSlotInsertion_covariantJetNormSq_two_low_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g s
            (metricComparisonEndomorphismField (I := I) (M := M) g gm)) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  obtain ⟨K₀, hK₀, hsharp⟩ :=
    exists_sharpFlatEndoCc_covariantJetNormSq_two_bound (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr ^ s * K₀
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg hfr s) hK₀
  refine ⟨K, hK, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g s
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)) ≤
      fr ^ s * covariantJetNormSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 0
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)) := by
      simpa only [fr] using covariantJetNormSq_slotInsertEndoCc_le (I := I) (M := M) g s 2
        (metricComparisonEndomorphismField (I := I) (M := M) g gm)
    _ = fr ^ s * covariantJetNormSq (I := I) (M := M) g 2
        (sharpFlatEndoCc (I := I) g gm) := by
      rw [sharpFlatEndoCc_eq_slotInsertEndoCc_zero (I := I) (M := M) g gm]
    _ ≤ fr ^ s * (K₀ *
        (1 + covariantJetNormSq (I := I) (M := M) g 2 P)) :=
      mul_le_mul_of_nonneg_left
        (hsharp gm P hP htie hδ_le hδ0 hδ) (pow_nonneg hfr s)
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
      simp only [K]
      ring

theorem exists_connectionDifferenceInsertionInnerActionCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_hW : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g W x u v =
            ccTensorBilin (I := I) g W x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W) ≤
        (B * R) ^ 2 := by
  obtain ⟨ρ, Cc, hρ, hCc, hconn⟩ :=
    RicciDeTurckLowOrder.low_connection_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ci, hCi, hi⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 3
  obtain ⟨Ca, hCa, ha⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 3
  let JP : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g (finRotate 3))
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := Ca * Ci * fr ^ 2 * JP * Cc ^ 2
  let B : ℝ := Real.sqrt K
  have hJP : 0 ≤ JP := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = K := by
    simpa only [B] using Real.sq_sqrt hK
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro gm P W hP hW htie R hR hW2 hPn
  have hsymm : symmS (I := I) (M := M) g W = W :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g W hW
  have hins := covariantJetNormSq_slotInsertEndoCc_symmRaiseEndo_le (I := I) (M := M) g 2 2 W hsymm
  have hone :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W) ≤
        Ci * (fr ^ 2 * R ^ 2) * JP := by
    rw [connectionDifferenceInsertionInnerDerivativeCoefficient]
    have hraw := hi
      (slotInsertEndoCc (I := I) (M := M) g 2
        (symmRaiseEndo (I := I) (M := M) g W))
      (permCoeff (I := I) (M := M) g (finRotate 3))
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
            (slotInsertEndoCc (I := I) (M := M) g 2
              (symmRaiseEndo (I := I) (M := M) g W))
            (permCoeff (I := I) (M := M) g (finRotate 3))) ≤
        Ci * covariantJetNormSq (I := I) (M := M) g 2
            (slotInsertEndoCc (I := I) (M := M) g 2
              (symmRaiseEndo (I := I) (M := M) g W)) * JP := by
          simpa only [JP] using hraw
      _ ≤ Ci * (fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 W) * JP :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hins hCi) hJP
      _ ≤ Ci * (fr ^ 2 * R ^ 2) * JP :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hW2 (pow_nonneg hfr 2)) hCi) hJP
  have hc := hconn P gm htie hPn
  rw [connectionDifferenceInsertionInnerActionCoefficient]
  have hraw := ha
    (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W)
    (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W)
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)) ≤
      Ca * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W) *
        covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm) := hraw
    _ ≤ Ca * (Ci * (fr ^ 2 * R ^ 2) * JP) * Cc ^ 2 :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hone hCa) hc
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hCa
          (mul_nonneg
            (mul_nonneg hCi
              (mul_nonneg (pow_nonneg hfr 2) (sq_nonneg R))) hJP))
    _ = K * R ^ 2 := by simp only [K]; ring
    _ = (B * R) ^ 2 := by rw [mul_pow, hBsq]

noncomputable def ricciQuadraticPermutationJetCap
    (g : SmoothRiemannianMetric I M) : ℝ :=
  covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroThreeOneTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapBlocks) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroThreeTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroOneThreeTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroOneTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapZeroTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapZeroOne) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_rotateInputs)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciQuadraticPermutationJetCap_nonneg (g : SmoothRiemannianMetric I M) :
    0 ≤ ricciQuadraticPermutationJetCap (I := I) (M := M) g := by
  unfold ricciQuadraticPermutationJetCap
  have h1 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroThreeOneTwo)
  have h2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapBlocks)
  have h3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroThreeTwo)
  have h4 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroOneThreeTwo)
  have h5 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroOneTwo)
  have h6 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapZeroTwo)
  have h7 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapZeroOne)
  have h8 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_rotateInputs)
  linarith

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covariantJetNormSq_ricciQuadraticPermutation_four_le
    (g : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
    (hpm : pm = ricciQuadraticPermutation_cycleZeroThreeOneTwo ∨ pm = ricciQuadraticPermutation_swapBlocks ∨ pm = ricciQuadraticPermutation_cycleZeroThreeTwo ∨
      pm = ricciQuadraticPermutation_cycleZeroOneThreeTwo ∨ pm = ricciQuadraticPermutation_cycleZeroOneTwo ∨ pm = ricciQuadraticPermutation_swapZeroTwo) :
    covariantJetNormSq (I := I) (M := M) g 2
        (permCoeff (I := I) (M := M) g pm) ≤
      ricciQuadraticPermutationJetCap (I := I) (M := M) g := by
  have h1 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroThreeOneTwo)
  have h2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapBlocks)
  have h3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroThreeTwo)
  have h4 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroOneThreeTwo)
  have h5 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroOneTwo)
  have h6 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapZeroTwo)
  have h7 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapZeroOne)
  have h8 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_rotateInputs)
  unfold ricciQuadraticPermutationJetCap
  rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl <;> linarith

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covariantJetNormSq_ricciQuadraticPermutation_three_le
    (g : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 3))
    (hpm : pm = ricciQuadraticPermutation_swapZeroOne ∨ pm = ricciQuadraticPermutation_rotateInputs) :
    covariantJetNormSq (I := I) (M := M) g 2
        (permCoeff (I := I) (M := M) g pm) ≤
      ricciQuadraticPermutationJetCap (I := I) (M := M) g := by
  have h1 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroThreeOneTwo)
  have h2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapBlocks)
  have h3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroThreeTwo)
  have h4 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroOneThreeTwo)
  have h5 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroOneTwo)
  have h6 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapZeroTwo)
  have h7 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapZeroOne)
  have h8 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_rotateInputs)
  unfold ricciQuadraticPermutationJetCap
  rcases hpm with rfl | rfl <;> linarith

theorem exists_ricciQuadraticKernelDerivativeCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_hW : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g W x u v =
            ccTensorBilin (I := I) g W x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gm W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨Co, hCo, hoapp⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 4 4
  obtain ⟨Cc, hCc, hcapp⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 4
  obtain ⟨Cm, hCm, hmapp⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 3
  obtain ⟨Bo, hBo, hout⟩ := exists_connectionDifferenceContravariantInsertionField_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρ, Bi, hρ, hBi, hinn⟩ := exists_connectionDifferenceInsertionInnerActionCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let J : ℝ := ricciQuadraticPermutationJetCap (I := I) (M := M) g
  let KZ : ℝ → ℝ := fun R => (1 + Cm * J) * (Bi * R) ^ 2
  let L : ℝ → ℝ := fun R =>
    94 * Co * J * (Cc * Bo R ^ 2 * KZ R)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hJ : 0 ≤ J := ricciQuadraticPermutationJetCap_nonneg (I := I) (M := M) g
  have hKZ : ∀ R : ℝ, 0 ≤ R → 0 ≤ KZ R := by
    intro R hR
    exact mul_nonneg
      (add_nonneg (by norm_num) (mul_nonneg hCm hJ))
      (sq_nonneg (Bi * R))
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCo) hJ)
      (mul_nonneg (mul_nonneg hCc (sq_nonneg (Bo R))) (hKZ R hR))
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P W hP hW htie δ hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPn
  let S : ℝ := (1 + A) ^ 2
  let Q : ℝ := Co * J * (Cc * (Bo R ^ 2 * S) * KZ R)
  have hS : 0 ≤ S := sq_nonneg _
  have hO :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gm) ≤
        Bo R ^ 2 * S := by
    calc
      _ ≤ (Bo R * (1 + A)) ^ 2 :=
        hout gm P hP htie hδ_le hδ0 hδP hδZ
          R A hR hA hP2 hP3
      _ = Bo R ^ 2 * S := by simp only [S]; ring
  have hI :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W) ≤
        (Bi * R) ^ 2 := hinn gm P W hP hW htie R hR hW2 hPn
  have hZdir :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W) ≤ KZ R := by
    refine hI.trans ?_
    simp only [KZ]
    have hz : 0 ≤ (Bi * R) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hCm hJ]
  have hZmid : ∀ pm : Equiv.Perm (Fin 3),
      (pm = ricciQuadraticPermutation_swapZeroOne ∨ pm = ricciQuadraticPermutation_rotateInputs) →
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
            (permCoeff (I := I) (M := M) g pm)
            (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W)) ≤ KZ R := by
    intro pm hpm
    have hp := covariantJetNormSq_ricciQuadraticPermutation_three_le (I := I) (M := M) g pm hpm
    have hraw := hmapp
      (permCoeff (I := I) (M := M) g pm)
      (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W)
    refine hraw.trans ?_
    have hmul :
        Cm * covariantJetNormSq (I := I) (M := M) g 2
              (permCoeff (I := I) (M := M) g pm) *
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W) ≤
          Cm * J * (Bi * R) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp hCm) hI
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hCm hJ)
    refine hmul.trans ?_
    simp only [KZ]
    have hz : 0 ≤ (Bi * R) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hCm hJ]
  have hQ : 0 ≤ Q := by
    exact mul_nonneg (mul_nonneg hCo hJ)
      (mul_nonneg
        (mul_nonneg hCc (mul_nonneg (sq_nonneg (Bo R)) hS))
        (hKZ R hR))
  have hblk : ∀ pm : Equiv.Perm (Fin 4),
      (pm = ricciQuadraticPermutation_cycleZeroThreeOneTwo ∨ pm = ricciQuadraticPermutation_swapBlocks ∨ pm = ricciQuadraticPermutation_cycleZeroThreeTwo ∨
        pm = ricciQuadraticPermutation_cycleZeroOneThreeTwo ∨ pm = ricciQuadraticPermutation_cycleZeroOneTwo ∨ pm = ricciQuadraticPermutation_swapZeroTwo) →
      ∀ Z : SmoothCcTensor g 3 3,
      covariantJetNormSq (I := I) (M := M) g 2 Z ≤ KZ R →
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
            (permCoeff (I := I) (M := M) g pm)
            (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
              (connectionDifferenceContravariantInsertionField (I := I) g gm) Z)) ≤ Q := by
    intro pm hpm Z hZ
    have hp := covariantJetNormSq_ricciQuadraticPermutation_four_le (I := I) (M := M) g pm hpm
    have hmraw := hcapp
      (connectionDifferenceContravariantInsertionField (I := I) g gm) Z
    have hm :
        covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
              (connectionDifferenceContravariantInsertionField (I := I) g gm) Z) ≤
          Cc * (Bo R ^ 2 * S) * KZ R := by
      refine hmraw.trans ?_
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hO hCc) hZ
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g Z)
        (mul_nonneg hCc (mul_nonneg (sq_nonneg (Bo R)) hS))
    have horaw := hoapp
      (permCoeff (I := I) (M := M) g pm)
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gm) Z)
    refine horaw.trans ?_
    have hfin := mul_le_mul
      (mul_le_mul_of_nonneg_left hp hCo) hm
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hCo hJ)
    simpa only [Q] using hfin
  have hx0 := hblk ricciQuadraticPermutation_cycleZeroThreeOneTwo (Or.inl rfl) _
    (hZmid ricciQuadraticPermutation_swapZeroOne (Or.inl rfl))
  have hx1 := hblk ricciQuadraticPermutation_swapBlocks (Or.inr (Or.inl rfl)) _
    (hZmid ricciQuadraticPermutation_swapZeroOne (Or.inl rfl))
  have hx2 := hblk ricciQuadraticPermutation_cycleZeroThreeTwo (Or.inr (Or.inr (Or.inl rfl))) _
    (hZmid ricciQuadraticPermutation_rotateInputs (Or.inr rfl))
  have hx3 := hblk ricciQuadraticPermutation_cycleZeroOneThreeTwo
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _ hZdir
  have hx4 := hblk ricciQuadraticPermutation_cycleZeroOneTwo
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) _ hZdir
  have hx5 := hblk ricciQuadraticPermutation_swapZeroTwo
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _
    (hZmid ricciQuadraticPermutation_rotateInputs (Or.inr rfl))
  rw [ricciQuadraticKernelDerivativeCoefficient]
  refine (covariantJetNormSq_sum_six_le (I := I) (M := M) g 2 _ _ _ _ _ _
    hx0 hx1 hx2 hx3 hx4 hx5).trans ?_
  calc
    94 * Q = L R * S := by simp only [Q, L]; ring
    _ = (B R * (1 + A)) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      simpa only [S, mul_pow] using
        congrArg (fun x : ℝ => x * (1 + A) ^ 2) hBR.symm
    _ ≤ (B R * (1 + A)) ^ 2 := le_rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem cometricDoubleTraceCoefficient_eq_pureTrace
    (g gm : SmoothRiemannianMetric I M) :
    cometricDoubleTraceCoefficient (I := I) (M := M) g gm =
      pureTrace (I := I) (M := M) g gm 2 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricDoubleTraceCoefficient_toSection, pureTrace_toSection]

omit [NeZero (Module.finrank ℝ E)] in
theorem covariantJetNormSq_ricciFourTraceCombination_le
    (g : SmoothRiemannianMetric I M) (F : SmoothCcTensor g 4 2) :
    covariantJetNormSq (I := I) (M := M) g 2
        (((1 : ℝ) / 2) •
          (reindexCoeffGen (I := I) (M := M) g 4 2 F
                fourTraceArgPerm0231 +
            reindexCoeffGen (I := I) (M := M) g 4 2 F
                fourTraceArgPerm0321 -
            F -
            reindexCoeffGen (I := I) (M := M) g 4 2 F
                fourTraceArgPerm2301)) ≤
      22 * covariantJetNormSq (I := I) (M := M) g 2 F := by
  have h0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g F
  have h1 := covariantJetNormSq_add_le (I := I) (M := M) g 2
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0231)
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0321)
  have h2 := covariantJetNormSq_sub_le (I := I) (M := M) g 2
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0231 +
      reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0321) F
  have h3 := covariantJetNormSq_sub_le (I := I) (M := M) g 2
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0231 +
        reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0321 - F)
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm2301)
  rw [covariantJetNormSq_reindexCoeffGen, covariantJetNormSq_reindexCoeffGen] at h1
  rw [covariantJetNormSq_reindexCoeffGen] at h3
  rw [covariantJetNormSq_smul]
  norm_num at h1 h2 h3 ⊢
  linarith

theorem exists_ricciCometricFourTraceCastG0_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (P : SmoothCcTensor g 0 2)
        (gm : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 2
            (ricciCometricFourTraceCastG0 (I := I) g gm) ≤ B ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hbdd⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  let L : ℝ := 22 * C ^ 2
  let B : ℝ := Real.sqrt L
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (sq_nonneg C)
  refine ⟨ρ, B, hρ, Real.sqrt_nonneg _, ?_⟩
  intro P gm htie hPn
  have hF : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoubleTraceCoefficient (I := I) (M := M) g gm) ≤ C ^ 2 := by
    rw [cometricDoubleTraceCoefficient_eq_pureTrace]
    exact hbdd P gm htie hPn
  rw [ricciCometricFourTraceCastG0_eq_reindex_combination
    (I := I) (M := M) g gm]
  refine (covariantJetNormSq_ricciFourTraceCombination_le (I := I) (M := M) g _).trans ?_
  rw [show B ^ 2 = L by simpa only [B] using Real.sq_sqrt hL]
  simp only [L]
  exact mul_le_mul_of_nonneg_left hF (by norm_num)

theorem exists_ricciConnectionDifferenceQuadraticDerivativeCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_hW : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g W x u v =
            ccTensorBilin (I := I) g W x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gm W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρk, Bk, hρk, hBk, hker⟩ :=
    exists_ricciQuadraticKernelDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρt, Bt, hρt, hBt, htrace⟩ :=
    exists_ricciCometricFourTraceCastG0_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 4 2
  let ρ : ℝ := min ρk ρt
  let L : ℝ → ℝ := fun R => Ca * Bt ^ 2 * Bk R ^ 2
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hρ : 0 < ρ := lt_min hρk hρt
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg hCa (sq_nonneg Bt)) (sq_nonneg (Bk R))
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P W hP hW htie δ hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPn
  have hPnk : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) P‖ ≤ ρk := hPn.trans (min_le_left _ _)
  have hPnt : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) P‖ ≤ ρt := hPn.trans (min_le_right _ _)
  have hk := hker gm P W hP hW htie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPnk
  have ht := htrace P gm htie hPnt
  rw [ricciConnectionDifferenceQuadraticDerivativeCoefficient]
  have hraw := happ
    (ricciCometricFourTraceCastG0 (I := I) g gm)
    (ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gm W)
  refine hraw.trans ?_
  calc
    Ca * covariantJetNormSq (I := I) (M := M) g 2
          (ricciCometricFourTraceCastG0 (I := I) g gm) *
        covariantJetNormSq (I := I) (M := M) g 2
          (ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gm W) ≤
      Ca * Bt ^ 2 * (Bk R * (1 + A)) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left ht hCa) hk
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCa (sq_nonneg Bt))
    _ = L R * (1 + A) ^ 2 := by simp only [L]; ring
    _ = (B R * (1 + A)) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      simpa only [mul_pow] using
        congrArg (fun x : ℝ => x * (1 + A) ^ 2) hBR.symm
    _ ≤ (B R * (1 + A)) ^ 2 := le_rfl

theorem exists_ricciConnectionDifferenceDerivativeCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_hW : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g W x u v =
            ccTensorBilin (I := I) g W x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρ, Ba, hρ, hBa, haa⟩ := exists_ricciConnectionDifferenceQuadraticDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Bd, hBd, hda⟩ :=
    exists_ricciConnectionDerivativeTransposedCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let L : ℝ → ℝ := fun R => 2 * (Ba R ^ 2 + Bd R ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg (Ba R)) (sq_nonneg (Bd R)))
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P W hP hW htie δ hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPn
  have hsymm : symmS (I := I) (M := M) g W = W :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g W hW
  have hW2' : covariantJetNormSq (I := I) (M := M) g 2
      (symmS (I := I) (M := M) g W) ≤ R ^ 2 := by
    simpa only [hsymm] using hW2
  have ha := haa gm P W hP hW htie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPn
  have hd := hda gm P (symmS (I := I) (M := M) g W)
    hP htie hδ_le hδ0 hδP R A hR hA hP2 hP3 hW2'
  rw [ricciConnectionDifferenceDerivativeCoefficient]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gm W) +
        covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gm
            (symmS (I := I) (M := M) g W))) ≤
      2 * ((Ba R * (1 + A)) ^ 2 + (Bd R * (1 + A)) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add ha hd) (by norm_num)
    _ = L R * (1 + A) ^ 2 := by simp only [L]; ring
    _ = (B R * (1 + A)) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      simpa only [mul_pow] using
        congrArg (fun x : ℝ => x * (1 + A) ^ 2) hBR.symm

omit [NeZero (Module.finrank ℝ E)] in
theorem covariantJetNormSq_cometricRaiseSlot0Field
    (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (W : SmoothCcTensor g 0 (s + 2)) :
    covariantJetNormSq (I := I) (M := M) g m
        (cometricRaiseSlot0Field (I := I) (M := M) g s W) =
      covariantJetNormSq (I := I) (M := M) g m W := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
    (I := I) (M := M) g s W q]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem cometricRaiseSlot0Field_zero_sub
    (g : SmoothRiemannianMetric I M)
    (W W' : SmoothCcTensor g 0 2) :
    cometricRaiseSlot0Field (I := I) (M := M) g 0 (W - W') =
      cometricRaiseSlot0Field (I := I) (M := M) g 0 W -
        cometricRaiseSlot0Field (I := I) (M := M) g 0 W' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  simp only [SmoothCcTensor.toSection_sub,
    cometricRaiseSlot0Field_toSection]
  rfl

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
