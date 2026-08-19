import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.LowOrderCoefficientPairingBounds

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

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
open DifferentialGeometry.Analysis.Sobolev
  (covariantJetNormSq iteratedCovGrad iteratedCovGrad_succ iteratedCovGrad_zero)
open DifferentialGeometry.Analysis.Spectral (operatorFieldApply ccTensorToHs)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

theorem exists_lowOrderFirstDerivativePathIntegral_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (lowOrderFirstDerivativePathIntegral (I := I) (M := M) g T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρ, B, hρ, hB, hpoint⟩ :=
    exists_affineLowOrderFirstDerivativeCoefficientPath_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hpath := path_jetL2_le (I := I) (M := M) g 3 2 2
    (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen hSI
    (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδT hδZ)
    (B := B R * (1 + A))
    (mul_nonneg (hB R hR) (add_nonneg (by norm_num) hA))
    (fun s hs => by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using
        hpoint T hT hδ_le hδ0 hδT hδZ
          R A hR hA hT2 hT3 hTn hs)
  simpa only [lowOrderFirstDerivativePathIntegral, covariantJetNormSq, Nat.reduceAdd] using hpath

theorem lowerScalePathIntegral_apply_decomposition
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
    operatorFieldApply (I := I) (M := M) g 2 2
        (RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδ hδZ) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (lowOrderZeroCoefficientPathIntegral (I := I) (M := M) g T hδ_lt hδ hδZ) T +
        operatorFieldApply (I := I) (M := M) g 3 2
          (lowOrderFirstDerivativeCoefficientPathIntegral (I := I) (M := M) g T hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 1 T) := by
  classical
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  let Ψ : ℝ → SmoothCcTensor g 2 2 :=
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M) g g T hδ hδZ
  let L : ℝ → SmoothCcTensor g 2 2 :=
    lowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ
  let Q : ℝ → SmoothCcTensor g 3 2 :=
    lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjΨ : JointlySmoothCcTensorFamily (I := I) g 2 2 S Ψ := by
    simpa only [JointlySmoothCcTensorFamily, S, Ψ] using
      RicciDeTurckLowOrder.selfLow_joint (I := I) (M := M)
        g g T hδ hδZ
  have hjL : JointlySmoothCcTensorFamily (I := I) g 2 2 S L := by
    simpa only [S, L] using
      lowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hjQ : JointlySmoothCcTensorFamily (I := I) g 3 2 S Q := by
    simpa only [S, Q] using
      lowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hcΨ : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((Ψ s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 Ψ S hjΨ x
  have hcL : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((L s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 L S hjL x
  have hcQ : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((Q s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2 Q S hjQ x
  have hPiΨ :
      RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 Ψ
          S metricPerturbationPathDomain_isOpen hSI hjΨ := rfl
  have hPiL :
      lowOrderZeroCoefficientPathIntegral (I := I) (M := M) g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 L
          S metricPerturbationPathDomain_isOpen hSI hjL := rfl
  have hPiQ :
      lowOrderFirstDerivativeCoefficientPathIntegral (I := I) (M := M) g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 3 2 Q
          S metricPerturbationPathDomain_isOpen hSI hjQ := rfl
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [hPiΨ, hPiL, hPiQ]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 2 2 Ψ T S
      metricPerturbationPathDomain_isOpen hSI hjΨ hcΨ x v]
  rw [unitModel_add (I := I) (M := M) g]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 2 2 L T S
      metricPerturbationPathDomain_isOpen hSI hjL hcL x v]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 3 2 Q
      (iteratedCovGrad (I := I) g 0 2 1 T) S
      metricPerturbationPathDomain_isOpen hSI hjQ hcQ x v]
  have hIL := coeffApp_integrable (I := I) (M := M)
    g 2 2 L T S hSI hcL x v
  have hIQ := coeffApp_integrable (I := I) (M := M)
    g 3 2 Q (iteratedCovGrad (I := I) g 0 2 1 T)
    S hSI hcQ x v
  rw [← intervalIntegral.integral_add hIL hIQ]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hone := lowerScalePathIntegrand_apply_decomposition (I := I) (M := M)
    g T hT hδ_lt hδ hδZ hs
  change
    unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
            g g T hδ hδZ s) T) x v =
      unitModel (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (lowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ s) T) x v +
        unitModel (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 3 2
            (lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ s)
            (iteratedCovGrad (I := I) g 0 2 1 T)) x v
  rw [hone, unitModel_add (I := I) (M := M) g,
    iteratedCovGrad_succ, iteratedCovGrad_zero]

theorem lowerScalePathIntegral_apply_affine_decomposition
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
    operatorFieldApply (I := I) (M := M) g 2 2
        (RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδ hδZ) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M)
            g T hT hδ_lt hδ hδZ) T +
        operatorFieldApply (I := I) (M := M) g 3 2
          (lowOrderFirstDerivativePathIntegral (I := I) (M := M)
            g T hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 1 T) := by
  classical
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  let Ψ : ℝ → SmoothCcTensor g 2 2 :=
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M) g g T hδ hδZ
  let L : ℝ → SmoothCcTensor g 2 2 :=
    affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ
  let Q : ℝ → SmoothCcTensor g 3 2 :=
    affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjΨ : JointlySmoothCcTensorFamily (I := I) g 2 2 S Ψ := by
    simpa only [JointlySmoothCcTensorFamily, S, Ψ] using
      RicciDeTurckLowOrder.selfLow_joint (I := I) (M := M)
        g g T hδ hδZ
  have hjL : JointlySmoothCcTensorFamily (I := I) g 2 2 S L := by
    simpa only [S, L] using
      affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hT hδ hδZ
  have hjQ : JointlySmoothCcTensorFamily (I := I) g 3 2 S Q := by
    simpa only [S, Q] using
      affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hcΨ : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((Ψ s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 Ψ S hjΨ x
  have hcL : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((L s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 L S hjL x
  have hcQ : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((Q s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2 Q S hjQ x
  have hPiΨ :
      RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 Ψ
          S metricPerturbationPathDomain_isOpen hSI hjΨ := rfl
  have hPiL :
      affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M)
          g T hT hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 L
          S metricPerturbationPathDomain_isOpen hSI hjL := rfl
  have hPiQ :
      lowOrderFirstDerivativePathIntegral (I := I) (M := M) g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 3 2 Q
          S metricPerturbationPathDomain_isOpen hSI hjQ := rfl
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [hPiΨ, hPiL, hPiQ]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 2 2 Ψ T S
      metricPerturbationPathDomain_isOpen hSI hjΨ hcΨ x v]
  rw [unitModel_add (I := I) (M := M) g]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 2 2 L T S
      metricPerturbationPathDomain_isOpen hSI hjL hcL x v]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 3 2 Q
      (iteratedCovGrad (I := I) g 0 2 1 T) S
      metricPerturbationPathDomain_isOpen hSI hjQ hcQ x v]
  have hIL := coeffApp_integrable (I := I) (M := M)
    g 2 2 L T S hSI hcL x v
  have hIQ := coeffApp_integrable (I := I) (M := M)
    g 3 2 Q (iteratedCovGrad (I := I) g 0 2 1 T)
    S hSI hcQ x v
  rw [← intervalIntegral.integral_add hIL hIQ]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hone := lowerScalePathIntegrand_apply_affine_decomposition (I := I) (M := M)
    g T hT hδ_lt hδ hδZ hs
  change
    unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
            g g T hδ hδZ s) T) x v =
      unitModel (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ s) T) x v +
        unitModel (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 3 2
            (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ s)
            (iteratedCovGrad (I := I) g 0 2 1 T)) x v
  rw [hone, unitModel_add (I := I) (M := M) g,
    iteratedCovGrad_succ, iteratedCovGrad_zero]

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
