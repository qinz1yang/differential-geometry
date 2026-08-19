import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.LowOrderDerivativeBounds

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq
  covariantJetNormSq_add_le covariantJetNormSq_nonneg
  exists_covariantJetNormSq_two_operatorFieldComposition_le)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral
  (ccOperatorFieldComp operatorFieldComposition_sub_left operatorFieldComposition_sub_right ccTensorToHs permCoeff
    symmS_eq_self_of_ccTensorBilin_symm)
open DifferentialGeometry.Geometry.Connection (slotInsertEndoCc)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

noncomputable def lowOrderFirstDerivativePathIntegral
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 3 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 3 2
    (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ)

noncomputable def lowOrderFirstDerivativePathIntegralDifference
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 3 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 3 2
    (fun s =>
      affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s -
        affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g U hδU hδZ s)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (jointlySmoothCcTensorFamily_sub (I := I) (M := M) g
      (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδT hδZ)
      (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g U hδU hδZ))

theorem lowOrderFirstDerivativePathIntegral_sub
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    lowOrderFirstDerivativePathIntegral (I := I) (M := M) g T hδ_lt hδT hδZ -
        lowOrderFirstDerivativePathIntegral (I := I) (M := M) g U hδ_lt hδU hδZ =
      lowOrderFirstDerivativePathIntegralDifference (I := I) (M := M)
        g T U hδ_lt hδT hδU hδZ := by
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
      (I := I) g 3 2
      (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδT hδZ) x
  have hUcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2
      (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g U hδU hδZ)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g U hδU hδZ) x
  have hTint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hTcont.mono hSI).intervalIntegrable
  have hUint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g U hδU hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hUcont.mono hSI).intervalIntegrable
  simp only [lowOrderFirstDerivativePathIntegral, lowOrderFirstDerivativePathIntegralDifference, pathIntegralCoeffField_toModel,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    TensorRSSpace.toModel_sub]
  rw [intervalIntegral.integral_sub hTint hUint]

theorem exists_connectionDifferenceInsertionInnerDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (D2 : ℝ), 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g T -
            connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g U) ≤
        (C * D2) ^ 2 := by
  obtain ⟨K, hK, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 3
  let P : SmoothCcTensor g 3 3 :=
    permCoeff (I := I) (M := M) g (finRotate 3)
  let J : ℝ := covariantJetNormSq (I := I) (M := M) g 2 P
  let fr : ℝ := Module.finrank ℝ E
  let L : ℝ := K * fr ^ 2 * J
  let C : ℝ := Real.sqrt L
  have hJ : 0 ≤ J := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g P
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCsq : C ^ 2 = L := by
    simpa only [C] using Real.sq_sqrt hL
  refine ⟨C, hC, ?_⟩
  intro T U hT hU D2 hD2 hTU2
  let D : SmoothCcTensor g 0 2 := T - U
  have hDsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g D x u v =
        ccTensorBilin (I := I) g D x v u := by
    intro x u v
    simpa only [D, ccTensorBilin_apply, ccTensorModel_sub,
      ContinuousMultilinearMap.sub_apply] using
        congrArg₂ (fun a b : ℝ => a - b) (hT x u v) (hU x u v)
  have hDself : symmS (I := I) (M := M) g D = D :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g D hDsymm
  have hraise :
      symmRaiseEndo (I := I) (M := M) g T -
          symmRaiseEndo (I := I) (M := M) g U =
        symmRaiseEndo (I := I) (M := M) g D := by
    have hneg : symmRaiseEndo (I := I) (M := M) g (-U) =
        -symmRaiseEndo (I := I) (M := M) g U := by
      rw [show -U = (-1 : ℝ) • U by simp, symmRaiseEndo_smul]
      exact neg_one_smul ℝ
        (symmRaiseEndo (I := I) (M := M) g U)
    calc
      symmRaiseEndo (I := I) (M := M) g T -
          symmRaiseEndo (I := I) (M := M) g U =
        symmRaiseEndo (I := I) (M := M) g T +
          -symmRaiseEndo (I := I) (M := M) g U := sub_eq_add_neg _ _
      _ = symmRaiseEndo (I := I) (M := M) g T +
          symmRaiseEndo (I := I) (M := M) g (-U) := by rw [hneg]
      _ = symmRaiseEndo (I := I) (M := M) g (T + -U) :=
        (symmRaiseEndo_add (I := I) (M := M) g T (-U)).symm
      _ = symmRaiseEndo (I := I) (M := M) g D := by rfl
  have hins : covariantJetNormSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 2
        (symmRaiseEndo (I := I) (M := M) g D)) ≤
        fr ^ 2 * D2 ^ 2 := by
    refine (covariantJetNormSq_slotInsertEndoCc_symmRaiseEndo_le (I := I) (M := M) g 2 2 D hDself).trans ?_
    exact mul_le_mul_of_nonneg_left
      (by simpa only [D] using hTU2) (pow_nonneg hfr 2)
  have hform :
      connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g T -
          connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g U =
        ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (slotInsertEndoCc (I := I) (M := M) g 2
            (symmRaiseEndo (I := I) (M := M) g D)) P := by
    rw [connectionDifferenceInsertionInnerDerivativeCoefficient, connectionDifferenceInsertionInnerDerivativeCoefficient, ← operatorFieldComposition_sub_left,
      ← slotInsertEndoCc_sub, hraise]
  rw [hform]
  refine (happ _ _).trans ?_
  calc
    K * covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 2
            (symmRaiseEndo (I := I) (M := M) g D)) * J ≤
        K * (fr ^ 2 * D2 ^ 2) * J :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hins hK) hJ
    _ = L * D2 ^ 2 := by simp only [L]; ring
    _ = (C * D2) ^ 2 := by rw [mul_pow, hCsq]

theorem exists_connectionDifferenceInsertionInnerDerivativeCoefficient_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SmoothCcTensor g 0 2)
        (_hW : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g W x u v =
            ccTensorBilin (I := I) g W x v u)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W) ≤
        (C * R) ^ 2 := by
  obtain ⟨K, hK, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 3
  let P : SmoothCcTensor g 3 3 :=
    permCoeff (I := I) (M := M) g (finRotate 3)
  let J : ℝ := covariantJetNormSq (I := I) (M := M) g 2 P
  let fr : ℝ := Module.finrank ℝ E
  let L : ℝ := K * fr ^ 2 * J
  let C : ℝ := Real.sqrt L
  have hJ : 0 ≤ J := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g P
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCsq : C ^ 2 = L := by
    simpa only [C] using Real.sq_sqrt hL
  refine ⟨C, hC, ?_⟩
  intro W hW R hR hW2
  have hWself : symmS (I := I) (M := M) g W = W :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g W hW
  have hins : covariantJetNormSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 2
        (symmRaiseEndo (I := I) (M := M) g W)) ≤
        fr ^ 2 * R ^ 2 := by
    refine (covariantJetNormSq_slotInsertEndoCc_symmRaiseEndo_le (I := I) (M := M) g 2 2 W hWself).trans ?_
    exact mul_le_mul_of_nonneg_left hW2 (pow_nonneg hfr 2)
  rw [connectionDifferenceInsertionInnerDerivativeCoefficient]
  refine (happ _ _).trans ?_
  calc
    K * covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 2
            (symmRaiseEndo (I := I) (M := M) g W)) * J ≤
        K * (fr ^ 2 * R ^ 2) * J :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hins hK) hJ
    _ = L * R ^ 2 := by simp only [L]; ring
    _ = (C * R) ^ 2 := by rw [mul_pow, hCsq]

theorem exists_connectionDifferenceInsertionInnerActionCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R D2 N : ℝ), 0 ≤ R → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gT T -
            connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gU U) ≤
        (B * (D2 + R * N)) ^ 2 := by
  obtain ⟨ρp, Cp, hρp, hCp, hpair⟩ :=
    RicciDeTurckLowOrder.connLow_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Cb, hρb, hCb, hbdd⟩ :=
    RicciDeTurckLowOrder.low_connection_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ci, hCi, hinPair⟩ :=
    exists_connectionDifferenceInsertionInnerDerivativeCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Cib, hCib, hinBdd⟩ :=
    exists_connectionDifferenceInsertionInnerDerivativeCoefficient_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 3
  let ρ : ℝ := min ρp ρb
  let B : ℝ := 2 * Ca * (Ci * Cb + Cib * Cp)
  have hρ : 0 < ρ := lt_min hρp hρb
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie hTn hUn
    R D2 N hR hD2 hN hU2 hTU2 hTUn
  let IT : SmoothCcTensor g 3 3 := connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g T
  let IU : SmoothCcTensor g 3 3 := connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g U
  let CT : SmoothCcTensor g 3 3 :=
    RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT
  let CU : SmoothCcTensor g 3 3 :=
    RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gU
  let X : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 3 (IT - IU) CT
  let Y : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 3 IU (CT - CU)
  let x : ℝ := Ca * (Ci * D2) * Cb
  let y : ℝ := Ca * (Cib * R) * (Cp * N)
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hTnp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρp := hTn.trans (min_le_left _ _)
  have hUnp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρp := hUn.trans (min_le_left _ _)
  have hTnb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρb := hTn.trans (min_le_right _ _)
  have hITdiff : covariantJetNormSq (I := I) (M := M) g 2 (IT - IU) ≤
      (Ci * D2) ^ 2 := by
    simpa only [IT, IU] using hinPair T U hT hU D2 hD2 hTU2
  have hIU : covariantJetNormSq (I := I) (M := M) g 2 IU ≤
      (Cib * R) ^ 2 := by
    simpa only [IU] using hinBdd U hU R hR hU2
  have hCT : covariantJetNormSq (I := I) (M := M) g 2 CT ≤ Cb ^ 2 := by
    simpa only [CT] using hbdd T gT hTtie hTnb
  have hCdiff : covariantJetNormSq (I := I) (M := M) g 2 (CT - CU) ≤
      (Cp * N) ^ 2 := by
    have hp := hpair T U gT gU hTtie hUtie hTnp hUnp
    exact hp.trans
      (pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hTUn hCp) 2)
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ x ^ 2 := by
    simpa only [X, x] using
      happ (IT - IU) CT (Ci * D2) Cb
        (mul_nonneg hCi hD2) hCb hITdiff hCT
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ y ^ 2 := by
    simpa only [Y, y] using
      happ IU (CT - CU) (Cib * R) (Cp * N)
        (mul_nonneg hCib hR) (mul_nonneg hCp hN) hIU hCdiff
  have hsplit :
      connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gT T -
          connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gU U = X + Y := by
    simp only [connectionDifferenceInsertionInnerActionCoefficient, X, Y, IT, IU, CT, CU,
      operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  have hlead : 2 * (x + y) ≤ B * (D2 + R * N) := by
    have hgap : B * (D2 + R * N) =
        2 * (x + y) +
          2 * Ca * (Cib * Cp * D2 + Ci * Cb * R * N) := by
      simp only [B, x, y]
      ring
    rw [hgap]
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg (by norm_num) hCa)
        (add_nonneg
          (mul_nonneg (mul_nonneg hCib hCp) hD2)
          (mul_nonneg
            (mul_nonneg (mul_nonneg hCi hCb) hR) hN)))
  rw [hsplit]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
        covariantJetNormSq (I := I) (M := M) g 2 Y) ≤
      2 * (x ^ 2 + y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ (2 * (x + y)) ^ 2 := by
      nlinarith [mul_nonneg hx0 hy0]
    _ ≤ (B * (D2 + R * N)) ^ 2 :=
      pow_le_pow_left₀
        (mul_nonneg (by norm_num) (add_nonneg hx0 hy0)) hlead 2

noncomputable def ricciQuadraticKernelDerivativeBlock
    (g gm : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
    (Z : SmoothCcTensor g 3 3) : SmoothCcTensor g 3 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 4
    (permCoeff (I := I) (M := M) g pm)
    (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm) Z)

theorem exists_ricciQuadraticKernelDerivativeBlock_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (pm : Equiv.Perm (Fin 4)) (ZT ZU : SmoothCcTensor g 3 3)
        (P OD OU ZB ZD : ℝ),
        0 ≤ P → 0 ≤ OD → 0 ≤ OU → 0 ≤ ZB → 0 ≤ ZD →
        covariantJetNormSq (I := I) (M := M) g 2
            (permCoeff (I := I) (M := M) g pm) ≤ P ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceContravariantInsertionField (I := I) g gT -
              connectionDifferenceContravariantInsertionField (I := I) g gU) ≤ OD ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceContravariantInsertionField (I := I) g gU) ≤ OU ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 ZT ≤ ZB ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (ZT - ZU) ≤ ZD ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciQuadraticKernelDerivativeBlock (I := I) (M := M) g gT pm ZT -
            ricciQuadraticKernelDerivativeBlock (I := I) (M := M) g gU pm ZU) ≤
        (C * P * (OD * ZB + OU * ZD)) ^ 2 := by
  obtain ⟨C4, hC4, hout⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 4
  obtain ⟨C3, hC3, hinn⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 4
  let C : ℝ := 2 * C4 * C3
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro gT gU pm ZT ZU P OD OU ZB ZD
    hP hOD hOU hZB hZD hp hoDiff hoU hZT hZdiff
  let OT : SmoothCcTensor g 3 4 :=
    connectionDifferenceContravariantInsertionField (I := I) g gT
  let OUf : SmoothCcTensor g 3 4 :=
    connectionDifferenceContravariantInsertionField (I := I) g gU
  let X : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 4 (OT - OUf) ZT
  let Y : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 4 OUf (ZT - ZU)
  let x : ℝ := C3 * OD * ZB
  let y : ℝ := C3 * OU * ZD
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ x ^ 2 := by
    simpa only [X, x, OT, OUf] using
      hinn (connectionDifferenceContravariantInsertionField (I := I) g gT -
          connectionDifferenceContravariantInsertionField (I := I) g gU) ZT
        OD ZB hOD hZB hoDiff hZT
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ y ^ 2 := by
    simpa only [Y, y, OUf] using
      hinn (connectionDifferenceContravariantInsertionField (I := I) g gU) (ZT - ZU)
        OU ZD hOU hZD hoU hZdiff
  have hinner :
      ccOperatorFieldComp (I := I) (M := M) g 3 3 4 OT ZT -
          ccOperatorFieldComp (I := I) (M := M) g 3 3 4 OUf ZU = X + Y := by
    simp only [X, Y, OT, OUf, operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  have hsum : covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤
      (2 * (x + y)) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
          covariantJetNormSq (I := I) (M := M) g 2 Y) ≤
        2 * (x ^ 2 + y ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
      _ ≤ (2 * (x + y)) ^ 2 := by
        nlinarith [mul_nonneg hx0 hy0]
  have hform :
      ricciQuadraticKernelDerivativeBlock (I := I) (M := M) g gT pm ZT -
          ricciQuadraticKernelDerivativeBlock (I := I) (M := M) g gU pm ZU =
        ccOperatorFieldComp (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g pm) (X + Y) := by
    rw [ricciQuadraticKernelDerivativeBlock, ricciQuadraticKernelDerivativeBlock, ← operatorFieldComposition_sub_right, hinner]
  rw [hform]
  have hxy0 : 0 ≤ 2 * (x + y) :=
    mul_nonneg (by norm_num) (add_nonneg hx0 hy0)
  refine (hout _ _ P (2 * (x + y)) hP hxy0 hp hsum).trans_eq ?_
  simp only [C, x, y]
  ring

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
