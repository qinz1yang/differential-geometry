import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.CoefficientDeviationSecondOrderBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalPathDecomposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Manifold Set Filter Topology DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE : CompleteSpace E :=
  FiniteDimensional.complete ℝ E


theorem top_path_dev_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T T' : SmoothCcTensor g 0 2)
          {δ : ℝ} (hδ_lt : δ < 1)
          (hδ : gFibreOpBound g (ccTensorBilinSymm (I := I) g T) δ)
          {δ' : ℝ} (hδ'_lt : δ' < 1)
          (hδ' : gFibreOpBound g (ccTensorBilinSymm (I := I) g T') δ')
          {R : ℝ}, 0 ≤ R → R ≤ ρ →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g 4 2 x
                  ((rhsTopPathIntegral (I := I) (M := M) g T T'
                      hδ_lt hδ hδ'_lt hδ' -
                    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g).toSection x) ≤
                (C * R) ^ 2) ∧
              (∑ i ∈ Finset.range 3,
                ‖iteratedCovGrad (I := I) g 4 2 i
                  (rhsTopPathIntegral (I := I) (M := M) g T T'
                      hδ_lt hδ hδ'_lt hδ' -
                    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g)‖ ^ 2) ≤
                (C * R) ^ 2 := by
  classical
  obtain ⟨ρ, C, hρ, hC, hdev⟩ :=
    phi_dev_h2_uniform (I := I) (M := M) hDim gBase hΛ
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro g hEq hjet T T' δ hδ_lt hδ δ' hδ'_lt hδ' R hR hRρ hT hT'
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt
  have hSopen : IsOpen (metricPerturbationPathDomain (δ := δ) (δ' := δ')) :=
    metricPerturbationPathDomain_isOpen
  let Φ : ℝ → SmoothCcTensor g 4 2 := fun s =>
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T T' hδ hδ' s) -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
  have hjpath := rhs_top_path_joint (I := I) (M := M) g T T' hδ hδ'
  have hjdev : linearizedRicciThreeArmHjoint (I := I) (M := M) g 4 Φ
      (δ := δ) (δ' := δ') := by
    simpa [Φ] using phi_dev_joint (I := I) (M := M) g T T' hδ hδ'
  let Pdev : SmoothCcTensor g 4 2 :=
    pathIntegralCoeffField (I := I) (M := M) g 4 2 Φ
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hSopen hSI hjdev
  have hcpath : ∀ x : M, ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel
        ((deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T T' hδ hδ' t)).toSection x))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
    intro x
    have h := hjpath
    rw [linearizedRicciThreeArmHjoint] at h
    exact jointContMDiff_toModel_continuous_slice (I := I) g 4 2
      (fun s => deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T T' hδ hδ' s))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) h x
  have hcdev : ∀ x : M, ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel ((Φ t).toSection x))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g 4 2 Φ
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hjdev x
  have heq : rhsTopPathIntegral (I := I) (M := M) g T T'
      hδ_lt hδ hδ'_lt hδ' -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g = Pdev := by
    have hPeq : rhsTopPathIntegral (I := I) (M := M) g T T'
        hδ_lt hδ hδ'_lt hδ' =
        pathIntegralCoeffField (I := I) (M := M) g 4 2
          (fun s => deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T T' hδ hδ' s))
          (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hSopen hSI hjpath := rfl
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    apply TensorRSSpace.toModel_injective
    change TensorRSSpace.toModel
        ((rhsTopPathIntegral (I := I) (M := M) g T T'
          hδ_lt hδ hδ'_lt hδ' -
            deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g).toSection x) =
      TensorRSSpace.toModel (Pdev.toSection x)
    rw [show (rhsTopPathIntegral (I := I) (M := M) g T T'
          hδ_lt hδ hδ'_lt hδ' -
            deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g).toSection x =
        (rhsTopPathIntegral (I := I) (M := M) g T T'
          hδ_lt hδ hδ'_lt hδ').toSection x -
          (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g).toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [TensorRSSpace.toModel_sub, hPeq]
    dsimp [Pdev]
    rw [pathIntegralFib_toModel, pathIntegralFib_toModel]
    have hint : IntervalIntegrable (fun t : ℝ =>
        TensorRSSpace.toModel
          ((deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T T' hδ hδ' t)).toSection x))
        MeasureTheory.volume 0 1 :=
      ((hcpath x).mono hSI).intervalIntegrable
    rw [show (∫ t in (0 : ℝ)..1, TensorRSSpace.toModel ((Φ t).toSection x)) =
        ∫ t in (0 : ℝ)..1,
          (TensorRSSpace.toModel
              ((deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
                (metricPerturbationPath (I := I) g T T' hδ hδ' t)).toSection x) -
            TensorRSSpace.toModel
              ((deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g).toSection x)) from
      intervalIntegral.integral_congr (fun t _ => by
        simp only [Φ]
        rw [show (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T T' hδ hδ' t) -
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g).toSection x =
              (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
                (metricPerturbationPath (I := I) g T T' hδ hδ' t)).toSection x -
              (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g).toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [TensorRSSpace.toModel_sub])]
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const]
    norm_num
  have hCR : 0 ≤ C * R := mul_nonneg hC hR
  have hper : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((Φ s).toSection x) ≤ (C * R) ^ 2) ∧
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 2 i (Φ s)‖ ^ 2) ≤ (C * R) ^ 2 := by
    intro s hs
    simpa [Φ] using hdev g hEq hjet T T' hδ_lt hδ hδ'_lt hδ'
      hR hRρ hT hT' hs.1 hs.2
  refine ⟨?_, ?_⟩
  · intro x
    rw [heq]
    dsimp [Pdev]
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((Φ t).toSection x)) ≤ C * R := by
      intro t ht
      calc
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            ((Φ t).toSection x)) ≤ Real.sqrt ((C * R) ^ 2) :=
          Real.sqrt_le_sqrt ((hper t ht).1 x)
        _ = C * R := Real.sqrt_sq hCR
    exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq
      (I := I) (M := M) g 4 2 Φ
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hSopen hSI hjdev x
      (C * R) ((hcdev x).mono (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt)) hsup
  · rw [heq]
    dsimp [Pdev]
    exact path_jetL2_le (I := I) (M := M) g 4 2 2 Φ
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hSopen hSI hjdev
      (fun t ht => by simpa using (hper t ht).2)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
