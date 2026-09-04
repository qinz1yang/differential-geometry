import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.Remainder
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Remainder.MoserTameBounds

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem termConst
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A : SmoothCcTensor g r 2) {δ δ' : ℝ} :
    linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g r
      (fun _ => A) (δ := δ) (δ' := δ') :=
  (A.toSection.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem path_sub_eq
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    {δ δ' : ℝ}
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (Φ Ψ : ℝ → SmoothCcTensor g r 2)
    (hΦ : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g r Φ
      (δ := δ) (δ' := δ'))
    (hΨ : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g r Ψ
      (δ := δ) (δ' := δ'))
    (hD : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g r
      (fun t => Φ t - Ψ t) (δ := δ) (δ' := δ')) :
    pathIntegralCoeffField (I := I) (M := M) g r 2 Φ
          (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
          metricPerturbationPathDomain_isOpen hSI hΦ -
        pathIntegralCoeffField (I := I) (M := M) g r 2 Ψ
          (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
          metricPerturbationPathDomain_isOpen hSI hΨ =
      pathIntegralCoeffField (I := I) (M := M) g r 2
        (fun t => Φ t - Ψ t)
        (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
        metricPerturbationPathDomain_isOpen hSI hD := by
  rw [linearizedRicciCovariantJetJointSmoothness] at hΦ hΨ hD
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro y
  apply TensorRSSpace.toModel_injective
  have hcΦ := jointContMDiff_toModel_continuous_slice
    (I := I) g r 2 Φ (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hΦ y
  have hcΨ := jointContMDiff_toModel_continuous_slice
    (I := I) g r 2 Ψ (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hΨ y
  have hIΦ : IntervalIntegrable (fun t : ℝ =>
      TensorRSSpace.toModel ((Φ t).toSection y))
      MeasureTheory.volume 0 1 :=
    (hcΦ.mono hSI).intervalIntegrable
  have hIΨ : IntervalIntegrable (fun t : ℝ =>
      TensorRSSpace.toModel ((Ψ t).toSection y))
      MeasureTheory.volume 0 1 :=
    (hcΨ.mono hSI).intervalIntegrable
  have hΦmodel := pathIntegralCoeffField_toModel (I := I) (M := M) g r 2 Φ
    (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    metricPerturbationPathDomain_isOpen hSI hΦ y
  have hΨmodel := pathIntegralCoeffField_toModel (I := I) (M := M) g r 2 Ψ
    (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    metricPerturbationPathDomain_isOpen hSI hΨ y
  have hDmodel := pathIntegralCoeffField_toModel (I := I) (M := M) g r 2
    (fun t => Φ t - Ψ t) (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    metricPerturbationPathDomain_isOpen hSI hD y
  simp only [SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply, TensorRSSpace.toModel_sub]
  rw [hΦmodel, hΨmodel, hDmodel]
  simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
    Pi.sub_apply, TensorRSSpace.toModel_sub]
  rw [intervalIntegral.integral_sub hIΦ hIΨ]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem path_add_sub_eq
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    {δ δ' : ℝ}
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (Φ Ψ : ℝ → SmoothCcTensor g r 2) (C : SmoothCcTensor g r 2)
    (hΦ : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g r Φ
      (δ := δ) (δ' := δ'))
    (hΨ : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g r Ψ
      (δ := δ) (δ' := δ'))
    (hK : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g r
      (fun t => Φ t + Ψ t - C) (δ := δ) (δ' := δ')) :
    pathIntegralCoeffField (I := I) (M := M) g r 2 Φ
          (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
          metricPerturbationPathDomain_isOpen hSI hΦ +
        pathIntegralCoeffField (I := I) (M := M) g r 2 Ψ
          (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
          metricPerturbationPathDomain_isOpen hSI hΨ -
        C =
      pathIntegralCoeffField (I := I) (M := M) g r 2
        (fun t => Φ t + Ψ t - C)
        (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
        metricPerturbationPathDomain_isOpen hSI hK := by
  rw [linearizedRicciCovariantJetJointSmoothness] at hΦ hΨ hK
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro y
  apply TensorRSSpace.toModel_injective
  have hcΦ := jointContMDiff_toModel_continuous_slice
    (I := I) g r 2 Φ (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hΦ y
  have hcΨ := jointContMDiff_toModel_continuous_slice
    (I := I) g r 2 Ψ (metricPerturbationPathDomain (δ := δ) (δ' := δ')) hΨ y
  have hIΦ : IntervalIntegrable (fun t : ℝ =>
      TensorRSSpace.toModel ((Φ t).toSection y))
      MeasureTheory.volume 0 1 :=
    (hcΦ.mono hSI).intervalIntegrable
  have hIΨ : IntervalIntegrable (fun t : ℝ =>
      TensorRSSpace.toModel ((Ψ t).toSection y))
      MeasureTheory.volume 0 1 :=
    (hcΨ.mono hSI).intervalIntegrable
  have hΦmodel := pathIntegralCoeffField_toModel (I := I) (M := M) g r 2 Φ
    (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    metricPerturbationPathDomain_isOpen hSI hΦ y
  have hΨmodel := pathIntegralCoeffField_toModel (I := I) (M := M) g r 2 Ψ
    (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    metricPerturbationPathDomain_isOpen hSI hΨ y
  have hKmodel := pathIntegralCoeffField_toModel (I := I) (M := M) g r 2
    (fun t => Φ t + Ψ t - C) (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    metricPerturbationPathDomain_isOpen hSI hK y
  simp only [SmoothCcTensor.toSection_add,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_add,
    ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply,
    TensorRSSpace.toModel_add, TensorRSSpace.toModel_sub]
  rw [hΦmodel, hΨmodel, hKmodel]
  simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_add, ContMDiffSection.coe_sub, Pi.add_apply,
    Pi.sub_apply, TensorRSSpace.toModel_add, TensorRSSpace.toModel_sub]
  rw [intervalIntegral.integral_sub (hIΦ.add hIΨ) intervalIntegrable_const,
    intervalIntegral.integral_add hIΦ hIΨ, intervalIntegral.integral_const]
  norm_num

omit [NeZero (Module.finrank ℝ E)] in
theorem path_add_sub_jet
    (g : SmoothRiemannianMetric I M) (r n : ℕ)
    {δ δ' : ℝ}
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (Φ Ψ : ℝ → SmoothCcTensor g r 2) (C : SmoothCcTensor g r 2)
    (hΦ : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g r Φ
      (δ := δ) (δ' := δ'))
    (hΨ : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g r Ψ
      (δ := δ) (δ' := δ'))
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hcap : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      covariantJetNormSq (I := I) (M := M) g n (Φ t + Ψ t - C) ≤ Λ) :
    covariantJetNormSq (I := I) (M := M) g n
        (pathIntegralCoeffField (I := I) (M := M) g r 2 Φ
              (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
              metricPerturbationPathDomain_isOpen hSI hΦ +
          pathIntegralCoeffField (I := I) (M := M) g r 2 Ψ
              (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
              metricPerturbationPathDomain_isOpen hSI hΨ -
          C) ≤ Λ := by
  classical
  have hK : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g r
      (fun t => Φ t + Ψ t - C) (δ := δ) (δ' := δ') :=
    covariantJetJoint_sub (I := I) (M := M) g _ _
      (covariantJetJoint_add (I := I) (M := M) g _ _ hΦ hΨ)
      (termConst (I := I) (M := M) g C)
  have heq := path_add_sub_eq (I := I) (M := M) g r hSI Φ Ψ C hΦ hΨ hK
  have hsq : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hΛ
  have hcap' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∑ q ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g r 2 q (Φ t + Ψ t - C)‖ ^ 2) ≤
        Real.sqrt Λ ^ 2 := by
    intro t ht
    rw [hsq]
    exact hcap t ht
  have hmain := path_jetL2_le (I := I) (M := M) g r 2 n
    (fun t => Φ t + Ψ t - C) (metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    metricPerturbationPathDomain_isOpen hSI hK hcap'
  rw [heq]
  exact le_of_le_of_eq hmain hsq

theorem topKerJetSharp
    (g : SmoothRiemannianMetric I M) :
    ∃ Kk : ℕ → ℝ, (∀ i, 0 ≤ Kk i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ0 : 0 ≤ δ) (_hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        covariantJetNormSq (I := I) (M := M) g i
            (rhsDecompositionTop (I := I) (M := M) g T hδg hδZ s +
              RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδg hδZ s -
              deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g) ≤
          Kk i * (1 + ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  have h30 : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have h31 : (1 / 3 : ℝ) < 1 := by norm_num
  obtain ⟨AL, SL, hL⟩ := HasMoserTameBounds.lieDecomposition2 (I := I) (M := M) g (δ₀ := 1 / 3) h30 h31
  obtain ⟨AP, SP, hP⟩ :=
    HasMoserTameBounds.deTurckMetricPrincipalDefectDifference (I := I) (M := M) g (δ₀ := 1 / 3) h30 h31
  obtain ⟨AR, SR, hR⟩ :=
    HasMoserTameBounds.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g (δ₀ := 1 / 3) h30 h31
  refine ⟨fun i => |2 * (2 * (AL i + AP i) + 4 * AR i)|,
    fun i => abs_nonneg _, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le h31
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hTsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * (1 / 3)) ^ 2 := by
    intro x
    have h := riemannianFiberNormSq_ccTensor02Symm_zero_le_fibreSmall
      (I := I) (M := M) g h30 T hδ_le hδ0 hδg x
    change riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      ((ccTensor02Symm (I := I) (M := M) g T).toSection x) ≤ _ at h
    rwa [ccTensor02Symm_eq_self (I := I) (M := M) g T hT] at h
  have hpert := metricPerturbationPath_isControlledMetricPerturbation (I := I) (M := M) g T hδ0 hδ_le hδ_lt hδg hδZ hTsup hs
  have hLw := hL T hTsup hδ0 hδ_le hδ_lt hδg hδZ hs
  have hPw := hP T (metricPerturbationPath (I := I) g T 0 hδg hδZ s)
    (convexPerturbation (I := I) g T 0 s) hpert
  have hRw := hR T hTsup (metricPerturbationPath (I := I) g T 0 hδg hδZ s)
    (convexPerturbation (I := I) g T 0 s) hpert
  have hAR : ∀ n, 0 ≤ AR n := fun n => HasMoserTameBounds.coefficient_nonneg (I := I) (M := M) hRw n
  have hSR : 0 ≤ SR := hRw.1
  have hRs : HasMoserTameBounds (I := I) (M := M) g T (fun n => 4 * AR n) (2 * SR)
      ((-2 * s : ℝ) • RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδg hδZ s) T) := by
    refine HasMoserTameBounds.mono (I := I) (M := M)
      (HasMoserTameBounds.smul (I := I) (M := M) (-2 * s : ℝ) hRw) (fun n => ?_) ?_
    · have hexp : (-2 * s : ℝ) ^ 2 = 4 * s ^ 2 := by ring
      rw [hexp]
      nlinarith [mul_nonneg (by nlinarith : (0 : ℝ) ≤ 1 - s ^ 2) (hAR n)]
    · rw [abs_mul, abs_of_nonneg hs0, show |(-2 : ℝ)| = 2 from by norm_num]
      nlinarith [hSR]
  have hfin := HasMoserTameBounds.add (I := I) (M := M)
    (HasMoserTameBounds.add (I := I) (M := M) hLw hPw) hRs
  rw [RicciDeTurckLowOrder.topKernel_eq (I := I) (M := M) g T hδg hδZ s]
  refine (hfin.2.2 i).trans ?_
  have hjetT : (0 : ℝ) ≤ covariantJetNormSq (I := I) (M := M) g i T :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := i) g T
  have hwin : covariantJetNormSq (I := I) (M := M) g i T =
      ∑ j ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := rfl
  rw [← hwin]
  exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith only [hjetT])

theorem topKer_jet
    (g : SmoothRiemannianMetric I M) :
    ∃ Kk : ℕ → ℝ, (∀ i, 0 ≤ Kk i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ0 : 0 ≤ δ) (_hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        covariantJetNormSq (I := I) (M := M) g i
            (rhsDecompositionTop (I := I) (M := M) g T hδg hδZ s +
              RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδg hδZ s -
              deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g) ≤
          Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  obtain ⟨Kk, hKk_nn, hker⟩ := topKerJetSharp (I := I) (M := M) g
  refine ⟨Kk, hKk_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i s hs
  refine (hker T hT hδ0 hδ_le hδg hδZ i s hs).trans ?_
  have hsub : Finset.range (i + 1) ⊆ Finset.range (i + 2) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hmono : ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤
      ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (by linarith only [hmono]) (hKk_nn i)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
