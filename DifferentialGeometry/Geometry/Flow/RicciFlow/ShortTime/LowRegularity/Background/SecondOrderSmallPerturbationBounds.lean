import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SecondOrderCoefficientJetBounds

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq
  covariantJetNormSq_add_le covariantJetNormSq_sub_le)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Elliptic
  (riemannianFiberNormSq riemannianFiberNormSq_add_le
    riemannianFiberNormSq_sub_le)
open DifferentialGeometry.Analysis.Spectral
  (ccTensorToHs ccTensorToHs_smul deTurckMetricPrincipalDefectTotal phi_dev_h2)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
theorem topOrderKernel_backgroundDifference_eq
    (g gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    (rhsDecompositionTop (I := I) (M := M) g gB T hδ hδZ s +
          RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s -
          deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB g) -
        (rhsDecompositionTop (I := I) (M := M) g g T hδ hδZ s +
          RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s -
          deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g g) =
      (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB
            (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
          deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB g) -
        (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
          deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g g) := by
  rw [show rhsDecompositionTop (I := I) (M := M) g gB T hδ hδZ s +
        RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s -
        deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB g = _ from
      RicciDeTurckLowOrder.topKernel_eq (I := I) (M := M) g gB T hδ hδZ s,
    show rhsDecompositionTop (I := I) (M := M) g g T hδ hδZ s +
        RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s -
        deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g g = _ from
      RicciDeTurckLowOrder.topKernel_eq (I := I) (M := M) g g T hδ hδZ s]
  abel

private theorem c2BackgroundPath
    (g gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ) (δ' := δ))
    (hK : linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (fun s => rhsDecompositionTop (I := I) (M := M) g gB T hδ hδZ s +
          RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s -
          deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB g)
      (δ := δ) (δ' := δ)) :
    (lowerScaleActionCoefficients (I := I) (M := M) g gB T hδ_lt hδ hδZ).secondOrderCoefficient =
      pathIntegralCoeffField (I := I) (M := M) g 4 2
        (fun s => rhsDecompositionTop (I := I) (M := M) g gB T hδ hδZ s +
            RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s -
            deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB g)
        (metricPerturbationPathDomain (δ := δ) (δ' := δ))
        metricPerturbationPathDomain_isOpen hSI hK := by
  rw [RicciDeTurckLowOrder.secondOrderCoefficient_eq (I := I) (M := M) g gB T hδ_lt hδ hδZ]
  exact path_add_sub_eq (I := I) (M := M) g 4 hSI _ _ _
    (rhsDecompositionTop_joint (I := I) (M := M) g gB T hδ_lt hδ hδZ)
    (RicciDeTurckLowOrder.selfTop_joint (I := I) (M := M) g T hδ hδZ) hK

private theorem devBackgroundCap
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2) {δ : ℝ} (_hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            (((deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB
                  (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB g) -
              (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
                  (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g g)).toSection x) ≤
            (C * R) ^ 2) ∧
          covariantJetNormSq (I := I) (M := M) g 2
            ((deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB
                  (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB g) -
              (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
                  (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g g)) ≤ (C * R) ^ 2 := by
  obtain ⟨ρ1, C1, hρ1, hC1, hphiB⟩ := phi_dev_h2 (I := I) (M := M) hDim g gB
  obtain ⟨ρ2, C2, hρ2, hC2, hphiG⟩ := phi_dev_h2 (I := I) (M := M) hDim g g
  refine ⟨min ρ1 ρ2, 2 * (C1 + C2), lt_min hρ1 hρ2, by positivity, ?_⟩
  intro T δ hδ_lt hδ hδZ R hR0 hRρ hTHs s hs
  have hRρ1 : R ≤ ρ1 := hRρ.trans (min_le_left _ _)
  have hRρ2 : R ≤ ρ2 := hRρ.trans (min_le_right _ _)
  have hzeroHs :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (0 : SmoothCcTensor g 0 2)‖ ≤ R := by
    have hz :
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (0 : SmoothCcTensor g 0 2) = 0 := by
      rw [show (0 : SmoothCcTensor g 0 2) =
          (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
        ccTensorToHs_smul, zero_smul]
    rw [hz, norm_zero]
    exact hR0
  have hkey : 2 * (C1 * R) ^ 2 + 2 * (C2 * R) ^ 2 ≤ (2 * (C1 + C2) * R) ^ 2 := by
    have hexp : (2 * (C1 + C2) * R) ^ 2 = 4 * (C1 + C2) ^ 2 * R ^ 2 := by ring
    rw [hexp]
    nlinarith [sq_nonneg (C1 * R), sq_nonneg (C2 * R),
      mul_nonneg (mul_nonneg hC1 hC2) (sq_nonneg R)]
  have hB := hphiB T (0 : SmoothCcTensor g 0 2) hδ_lt hδ hδ_lt hδZ
    hR0 hRρ1 hTHs hzeroHs hs.1 hs.2
  have hG := hphiG T (0 : SmoothCcTensor g 0 2) hδ_lt hδ hδ_lt hδZ
    hR0 hRρ2 hTHs hzeroHs hs.1 hs.2
  constructor
  · intro x
    have hBx := hB.1 x
    have hGx := hG.1 x
    have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g 4 2 x
      ((deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
        deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB g).toSection x)
      ((deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
        deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g g).toSection x)
    simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
      Pi.sub_apply] at hsub hBx hGx ⊢
    linarith [hsub, hBx, hGx, hkey]
  · have hBj : covariantJetNormSq (I := I) (M := M) g 2
        (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB
            (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
          deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB g) ≤ (C1 * R) ^ 2 := by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using hB.2
    have hGj : covariantJetNormSq (I := I) (M := M) g 2
        (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
          deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g g) ≤ (C2 * R) ^ 2 := by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using hG.2
    have hsub := covariantJetNormSq_sub_le (I := I) (M := M) g 2
      (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
        deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB g)
      (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
        deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g g)
    linarith [hsub, hBj, hGj, hkey]

omit [NeZero (Module.finrank ℝ E)] in
private theorem pathBoth
    (g : SmoothRiemannianMetric I M) {δ : ℝ}
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ) (δ' := δ))
    (D : ℝ → SmoothCcTensor g 4 2)
    (hD : linearizedRicciThreeArmHjoint (I := I) (M := M) g 4 D
      (δ := δ) (δ' := δ))
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hpt : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((D s).toSection x) ≤ Λ ^ 2)
    (hjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      covariantJetNormSq (I := I) (M := M) g 2 (D s) ≤ Λ ^ 2) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((pathIntegralCoeffField (I := I) (M := M) g 4 2 D
          (metricPerturbationPathDomain (δ := δ) (δ' := δ))
          metricPerturbationPathDomain_isOpen hSI hD).toSection x) ≤ Λ ^ 2) ∧
      covariantJetNormSq (I := I) (M := M) g 2
        (pathIntegralCoeffField (I := I) (M := M) g 4 2 D
          (metricPerturbationPathDomain (δ := δ) (δ' := δ))
          metricPerturbationPathDomain_isOpen hSI hD) ≤ Λ ^ 2 := by
  have hIcc : Set.Icc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    simpa only [Set.uIcc_of_le zero_le_one] using hSI
  constructor
  · intro x
    have hcont := (jointContMDiff_toModel_continuous_slice
      (I := I) g 4 2 D (metricPerturbationPathDomain (δ := δ) (δ' := δ)) hD x).mono hIcc
    refine riemannianFiberNormSq_pathIntegralCoeffField_le_sq
      (I := I) (M := M) g 4 2 D (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      metricPerturbationPathDomain_isOpen hSI hD x Λ hΛ hcont ?_
    intro s hs
    have hsqrt := Real.sqrt_le_sqrt (hpt s hs x)
    simpa only [Real.sqrt_sq hΛ] using hsqrt
  · exact path_jetL2_le (I := I) (M := M) g 4 2 2 D
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      metricPerturbationPathDomain_isOpen hSI hD hΛ (fun s hs => hjet s hs)

theorem exists_lowerScaleSecondOrderCoefficient_background_smallPerturbation_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
      let A := lowerScaleActionCoefficients (I := I) (M := M) g gB T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            (A.secondOrderCoefficient.toSection x) ≤ (C * R) ^ 2) ∧
        covariantJetNormSq (I := I) (M := M) g 2 A.secondOrderCoefficient ≤ (C * R) ^ 2 := by
  classical
  obtain ⟨ρ0, C0, hρ0, hC0, hdiag⟩ := exists_lowerScaleSecondOrderCoefficient_smallPerturbation_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρd, Cd, hρd, hCd, hdev⟩ := devBackgroundCap (I := I) (M := M) hDim g gB
  let C : ℝ := 2 * (Cd + C0)
  have hC : 0 ≤ C := by positivity
  refine ⟨min ρ0 ρd, C, lt_min hρ0 hρd, hC, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R hR0 hRρ hTHs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hRρ0 : R ≤ ρ0 := hRρ.trans (min_le_left _ _)
  have hRρd : R ≤ ρd := hRρ.trans (min_le_right _ _)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjΦB := rhsDecompositionTop_joint (I := I) (M := M) g gB T hδ_lt hδ hδZ
  have hjΦG := rhsDecompositionTop_joint (I := I) (M := M) g g T hδ_lt hδ hδZ
  have hjΨ := RicciDeTurckLowOrder.selfTop_joint (I := I) (M := M) g T hδ hδZ
  have hjKerB := threeArmJoint_sub (I := I) (M := M) g _ _
    (threeArmJoint_add (I := I) (M := M) g _ _ hjΦB hjΨ)
    (armConst (I := I) (M := M) g (δ := δ) (δ' := δ)
      (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB g))
  have hjKerG := threeArmJoint_sub (I := I) (M := M) g _ _
    (threeArmJoint_add (I := I) (M := M) g _ _ hjΦG hjΨ)
    (armConst (I := I) (M := M) g (δ := δ) (δ' := δ)
      (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g g))
  have hjD := threeArmJoint_sub (I := I) (M := M) g _ _ hjKerB hjKerG
  have hcB := c2BackgroundPath (I := I) (M := M) g gB T hδ_lt hδ hδZ hSI hjKerB
  have hcG := c2BackgroundPath (I := I) (M := M) g g T hδ_lt hδ hδZ hSI hjKerG
  have hdiff :
      (lowerScaleActionCoefficients (I := I) (M := M) g gB T hδ_lt hδ hδZ).secondOrderCoefficient -
          (lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ).secondOrderCoefficient =
        pathIntegralCoeffField (I := I) (M := M) g 4 2
          (fun s =>
            (rhsDecompositionTop (I := I) (M := M) g gB T hδ hδZ s +
                RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s -
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB g) -
              (rhsDecompositionTop (I := I) (M := M) g g T hδ hδZ s +
                RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s -
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g g))
          (metricPerturbationPathDomain (δ := δ) (δ' := δ))
          metricPerturbationPathDomain_isOpen hSI hjD := by
    rw [hcB, hcG]
    exact path_sub_eq (I := I) (M := M) g 4 hSI _ _ hjKerB hjKerG hjD
  have hcapPt : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (((rhsDecompositionTop (I := I) (M := M) g gB T hδ hδZ s +
                RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s -
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB g) -
              (rhsDecompositionTop (I := I) (M := M) g g T hδ hδZ s +
                RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s -
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g g)).toSection x) ≤
        (Cd * R) ^ 2 := by
    intro s hs x
    rw [topOrderKernel_backgroundDifference_eq (I := I) (M := M) g gB T hδ hδZ s]
    exact (hdev T hδ_lt hδ hδZ hR0 hRρd hTHs s hs).1 x
  have hcapJet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      covariantJetNormSq (I := I) (M := M) g 2
          ((rhsDecompositionTop (I := I) (M := M) g gB T hδ hδZ s +
              RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s -
              deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gB g) -
            (rhsDecompositionTop (I := I) (M := M) g g T hδ hδZ s +
              RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδ hδZ s -
              deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g g)) ≤
        (Cd * R) ^ 2 := by
    intro s hs
    rw [topOrderKernel_backgroundDifference_eq (I := I) (M := M) g gB T hδ hδZ s]
    exact (hdev T hδ_lt hδ hδZ hR0 hRρd hTHs s hs).2
  have hCdR0 : 0 ≤ Cd * R := mul_nonneg hCd hR0
  obtain ⟨hdPt, hdJet⟩ := pathBoth (I := I) (M := M) g hSI _ hjD hCdR0
    hcapPt hcapJet
  rw [← hdiff] at hdPt hdJet
  have hdg :
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ).secondOrderCoefficient.toSection x) ≤
            (C0 * R) ^ 2) ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ).secondOrderCoefficient ≤ (C0 * R) ^ 2 :=
    hdiag T hT hδ_le hδ0 hδ hδZ hR0 hRρ0 hTHs
  have hsplit :
      (lowerScaleActionCoefficients (I := I) (M := M) g gB T hδ_lt hδ hδZ).secondOrderCoefficient =
        ((lowerScaleActionCoefficients (I := I) (M := M) g gB T hδ_lt hδ hδZ).secondOrderCoefficient -
            (lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ).secondOrderCoefficient) +
          (lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ).secondOrderCoefficient := by
    abel
  have hkey2 : 2 * (Cd * R) ^ 2 + 2 * (C0 * R) ^ 2 ≤ (C * R) ^ 2 := by
    have hCR : (C * R) ^ 2 = 4 * (Cd + C0) ^ 2 * R ^ 2 := by
      simp only [C]; ring
    rw [hCR]
    nlinarith [sq_nonneg (Cd * R), sq_nonneg (C0 * R),
      mul_nonneg (mul_nonneg hCd hC0) (sq_nonneg R)]
  change
    (∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((lowerScaleActionCoefficients (I := I) (M := M) g gB T hδ_lt hδ hδZ).secondOrderCoefficient.toSection x) ≤
        (C * R) ^ 2) ∧
      covariantJetNormSq (I := I) (M := M) g 2
        (lowerScaleActionCoefficients (I := I) (M := M) g gB T hδ_lt hδ hδZ).secondOrderCoefficient ≤ (C * R) ^ 2
  constructor
  · intro x
    have hd := hdPt x
    have hg := hdg.1 x
    rw [hsplit]
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g 4 2 x
      (((lowerScaleActionCoefficients (I := I) (M := M) g gB T hδ_lt hδ hδZ).secondOrderCoefficient -
        (lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ).secondOrderCoefficient).toSection x)
      ((lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ).secondOrderCoefficient.toSection x)
    simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
      ContMDiffSection.coe_add, ContMDiffSection.coe_sub,
      Pi.add_apply, Pi.sub_apply] at hadd hd ⊢
    linarith [hadd, hd, hg, hkey2]
  · rw [hsplit]
    have hadd := covariantJetNormSq_add_le (I := I) (M := M) g 2
      ((lowerScaleActionCoefficients (I := I) (M := M) g gB T hδ_lt hδ hδZ).secondOrderCoefficient -
        (lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ).secondOrderCoefficient)
      (lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδ hδZ).secondOrderCoefficient
    linarith [hadd, hdJet, hdg.2, hkey2]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
