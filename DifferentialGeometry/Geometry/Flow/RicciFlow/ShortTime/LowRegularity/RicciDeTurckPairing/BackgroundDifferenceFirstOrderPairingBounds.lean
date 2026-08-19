import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.BackgroundDifferenceFirstDerivativePairingBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SecondOrderCoefficientLipschitzBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.LinearTerms

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open LieCorrectionZeroCore

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_mono
    (g : SmoothRiemannianMetric I M) {r s m n : ℕ}
    (hmn : m ≤ n) (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m S ≤
      covariantJetNormSq (I := I) (M := M) g n S := by
  unfold covariantJetNormSq
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.add_le_add_right hmn 1))
    (fun _ _ _ => sq_nonneg _)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_zero_section
    (g : SmoothRiemannianMetric I M) (r s m : ℕ) :
    iteratedCovGrad (I := I) g r s m
        (0 : SmoothCcTensor g r s) = 0 := by
  induction m with
  | zero => rw [iteratedCovGrad_zero]
  | succ m ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_zero
    (g : SmoothRiemannianMetric I M) {r s m : ℕ} :
    covariantJetNormSq (I := I) (M := M) g m
        (0 : SmoothCcTensor g r s) = 0 := by
  unfold covariantJetNormSq
  apply Finset.sum_eq_zero
  intro q hq
  rw [iteratedCovGrad_zero_section, norm_zero, zero_pow (by norm_num)]

omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_one_domDomCongrSection
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    covariantJetNormSq (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g σ S) =
      covariantJetNormSq (I := I) (M := M) g 1 S := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ S q x

omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_two_domDomCongrSection
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g σ S) =
      covariantJetNormSq (I := I) (M := M) g 2 S := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ S q x

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem domDomCongrSection_sub
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g σ (A - B) =
      domDomCongrSection (I := I) g σ A -
        domDomCongrSection (I := I) g σ B := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  have hsub : ∀ (P Q : SmoothCcTensor g 0 s),
      unitModel (I := I) (M := M) g s (P - Q) x =
        unitModel (I := I) (M := M) g s P x -
          unitModel (I := I) (M := M) g s Q x := by
    intro P Q
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [domDomCongrSection_unitModel, hsub A B]
  rw [hsub
    (domDomCongrSection (I := I) g σ A)
    (domDomCongrSection (I := I) g σ B)]
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

private theorem exists_operatorFieldComposition_covariantJetNormSq_one_le_two_one
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        covariantJetNormSq (I := I) (M := M) g 1
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2 Φ *
            covariantJetNormSq (I := I) (M := M) g 1 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    operator_field_composition_h2_h1_to_h1_bound (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  let A : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 Φ)
  let B : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 1 W)
  have hΦ0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g Φ
  have hW0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 1) g W
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 Φ := by
    simpa only [A] using Real.sq_sqrt hΦ0
  have hBsq : B ^ 2 = covariantJetNormSq (I := I) (M := M) g 1 W := by
    simpa only [B] using Real.sq_sqrt hW0
  have hnorm := happ Φ W A B hA hB
    (by simpa only [covariantJetNormSq, Nat.reduceAdd] using le_of_eq hAsq.symm)
    (by simpa only [covariantJetNormSq, Nat.reduceAdd] using le_of_eq hBsq.symm)
  have hsq := pow_le_pow_left₀
    (norm_nonneg (⟨ccOperatorFieldComp (I := I) (M := M) g p r c Φ W⟩ :
      SmoothCcTensorH1 g p c)) hnorm 2
  rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g p c
    (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)] at hsq
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
      (C₀ * A * B) ^ 2 := by
        simpa only [covariantJetNormSq, Finset.sum_range_succ,
          Finset.sum_range_zero, zero_add, Nat.reduceAdd,
          iteratedCovGrad_zero_section, iteratedCovGrad_succ] using hsq
    _ = C₀ ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 Φ *
        covariantJetNormSq (I := I) (M := M) g 1 W := by
      rw [mul_pow, mul_pow, hAsq, hBsq]

private theorem exists_operatorFieldComposition_covariantJetNormSq_one_le_one_two
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        covariantJetNormSq (I := I) (M := M) g 1
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
          C * covariantJetNormSq (I := I) (M := M) g 1 Φ *
            covariantJetNormSq (I := I) (M := M) g 2 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    operator_field_composition_h1_h2_to_h1_bound (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  let A : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 1 Φ)
  let B : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W)
  have hΦ0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 1) g Φ
  have hW0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g W
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = covariantJetNormSq (I := I) (M := M) g 1 Φ := by
    simpa only [A] using Real.sq_sqrt hΦ0
  have hBsq : B ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 W := by
    simpa only [B] using Real.sq_sqrt hW0
  have hnorm := happ Φ W A B hA hB
    (by simpa only [covariantJetNormSq, Nat.reduceAdd] using le_of_eq hAsq.symm)
    (by simpa only [covariantJetNormSq, Nat.reduceAdd] using le_of_eq hBsq.symm)
  have hsq := pow_le_pow_left₀
    (norm_nonneg (⟨ccOperatorFieldComp (I := I) (M := M) g p r c Φ W⟩ :
      SmoothCcTensorH1 g p c)) hnorm 2
  rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g p c
    (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)] at hsq
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
      (C₀ * A * B) ^ 2 := by
        simpa only [covariantJetNormSq, Finset.sum_range_succ,
          Finset.sum_range_zero, zero_add, Nat.reduceAdd,
          iteratedCovGrad_zero_section, iteratedCovGrad_succ] using hsq
    _ = C₀ ^ 2 * covariantJetNormSq (I := I) (M := M) g 1 Φ *
        covariantJetNormSq (I := I) (M := M) g 2 W := by
      rw [mul_pow, mul_pow, hAsq, hBsq]

private theorem deTurckLieCovariantDerivativeArmTwoCoefficient_difference_covariantJetNormSq_one_le
    (g gT gU : SmoothRiemannianMetric I M) :
    covariantJetNormSq (I := I) (M := M) g 1
        (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT -
          deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 1
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g) := by
  let fr : ℝ := Module.finrank ℝ E
  have hper : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 q
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT -
            deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU)‖ ^ 2 ≤
        fr ^ 2 *
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g)‖ ^ 2 := by
    intro q
    let F : M → ℝ := fun x => fr ^ 2 *
      riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
        ((iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g)).toSection x)
    have hF : MeasureTheory.Integrable F
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [F]
      exact (integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g 1 (2 + q)
        (iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g))).const_mul _
    have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g 3 (4 + q)
      (iteratedCovGrad (I := I) g 3 4 q
        (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT -
          deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU))
      F hF (fun x => by
        simpa only [F, fr] using
          deTurckLieCovariantDerivativeArmTwoCoefficient_sub_l2 (I := I) (M := M) g gT gU q x)
    have hint : (∫ x,
        riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
          ((iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g)‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    dsimp only [F] at hsq
    rw [MeasureTheory.integral_const_mul, hint] at hsq
    exact hsq
  unfold covariantJetNormSq
  calc
    ∑ q ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 3 4 q
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT -
            deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 2, fr ^ 2 *
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g)‖ ^ 2 :=
      Finset.sum_le_sum fun q _ => hper q
    _ = fr ^ 2 * ∑ q ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g)‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem iteratedCovGrad_slotInsertEndoCc_norm_sq_le
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

private theorem covariantJetNormSq_two_slotInsertEndoCc_le
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    covariantJetNormSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g s Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        iteratedCovGrad_slotInsertEndoCc_norm_sq_le (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem symmS_eq_self
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (hS : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g S x u v =
        ccTensorBilin (I := I) g S x v u) :
    symmS (I := I) (M := M) g S = S := by
  have hswap :
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext fun v => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g 2 S x ![u, w] =
          unitModel (I := I) (M := M) g 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x w u]
      exact hS x u w
    have hveta :
        (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  unfold symmS ccTensor02Symm
  rw [hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_two_slotInsert_symmRaiseEndo_eq
    (g : SmoothRiemannianMetric I M) (D : SmoothCcTensor g 0 2)
    (hD : symmS (I := I) (M := M) g D = D) :
    covariantJetNormSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 0
          (symmRaiseEndo (I := I) (M := M) g D)) =
      covariantJetNormSq (I := I) (M := M) g 2 D := by
  rw [insert_symmRaise_eq (I := I) (M := M) g D]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 0
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (symmS (I := I) (M := M) g D))) =
      covariantJetNormSq (I := I) (M := M) g 2
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
    _ = covariantJetNormSq (I := I) (M := M) g 2
          (symmS (I := I) (M := M) g D) :=
      covariantJetNormSq_two_domDomCongrSection (I := I) (M := M) g
        (Equiv.swap (0 : Fin 2) 1)
        (symmS (I := I) (M := M) g D)
    _ = covariantJetNormSq (I := I) (M := M) g 2 D := by rw [hD]

private theorem metricComparisonEndomorphism_third_slot_difference_covariantJetNormSq_two_le
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (hU : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g U x u v =
        ccTensorBilin (I := I) g U x v u)
    (hTtie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
    (hUtie : ∀ (x : M) (u v : TangentSpace I x),
      gU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    covariantJetNormSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 3
            (metricComparisonEndomorphismField (I := I) (M := M) gT g) -
          slotInsertEndoCc (I := I) (M := M) g 3
            (metricComparisonEndomorphismField (I := I) (M := M) gU g)) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
  have hsymm : symmS (I := I) (M := M) g (T - U) = T - U := by
    have hTs := symmS_eq_self (I := I) (M := M) g T hT
    have hUs := symmS_eq_self (I := I) (M := M) g U hU
    change ccTensor02Symm (I := I) (M := M) g T = T at hTs
    change ccTensor02Symm (I := I) (M := M) g U = U at hUs
    change ccTensor02Symm (I := I) (M := M) g (T - U) = T - U
    rw [symmS_sub, hTs, hUs]
  rw [← slotInsertEndoCc_sub,
    RicciDeTurckLowOrder.fullRev_sub (I := I) (M := M)
      g gT gU T U hTtie hUtie]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 3
          (symmRaiseEndo (I := I) (M := M) g (T - U))) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0
            (symmRaiseEndo (I := I) (M := M) g (T - U))) :=
      covariantJetNormSq_two_slotInsertEndoCc_le (I := I) (M := M) g 3
        (symmRaiseEndo (I := I) (M := M) g (T - U))
    _ = (Module.finrank ℝ E : ℝ) ^ 3 *
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
      rw [covariantJetNormSq_two_slotInsert_symmRaiseEndo_eq (I := I) (M := M) g (T - U) hsymm]

private theorem exists_metricComparisonEndomorphism_third_slot_covariantJetNormSq_two_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 3
            (metricComparisonEndomorphismField (I := I) (M := M) gm g)) ≤
        (C * (1 + R)) ^ 2 := by
  let A0 : SmoothCcTensor g 4 4 :=
    slotInsertEndoCc (I := I) (M := M) g 3
      (metricComparisonEndomorphismField (I := I) (M := M) g g)
  let J0 : ℝ := covariantJetNormSq (I := I) (M := M) g 2 A0
  let fr : ℝ := Module.finrank ℝ E
  let Z : ℝ := 2 * (fr ^ 3 + J0)
  let C : ℝ := Real.sqrt Z
  have hJ0 : 0 ≤ J0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g A0
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact mul_nonneg (by norm_num)
      (add_nonneg (by positivity) hJ0)
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro gm P hP htie R hR hP2
  have hzero : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  have hzeroTie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v = g.inner x u v +
        ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  let A : SmoothCcTensor g 4 4 :=
    slotInsertEndoCc (I := I) (M := M) g 3
      (metricComparisonEndomorphismField (I := I) (M := M) gm g)
  have hpair : covariantJetNormSq (I := I) (M := M) g 2 (A - A0) ≤
      fr ^ 3 * covariantJetNormSq (I := I) (M := M) g 2 P := by
    simpa only [A, A0, fr, sub_zero] using
      metricComparisonEndomorphism_third_slot_difference_covariantJetNormSq_two_le (I := I) (M := M) g gm g P
        (0 : SmoothCcTensor g 0 2) hP hzero htie hzeroTie
  have hpairR : covariantJetNormSq (I := I) (M := M) g 2 (A - A0) ≤
      fr ^ 3 * R ^ 2 :=
    hpair.trans (mul_le_mul_of_nonneg_left hP2 (by positivity))
  have hRdom : R ^ 2 ≤ (1 + R) ^ 2 := by nlinarith
  have hone : (1 : ℝ) ≤ (1 + R) ^ 2 := by
    nlinarith [sq_nonneg R]
  have hdom : 2 * (fr ^ 3 * R ^ 2 + J0) ≤
      Z * (1 + R) ^ 2 := by
    calc
      2 * (fr ^ 3 * R ^ 2 + J0) ≤
          2 * (fr ^ 3 * (1 + R) ^ 2 + J0 * (1 + R) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (add_le_add
            (mul_le_mul_of_nonneg_left hRdom (by positivity))
            (by simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hone hJ0))
          (by norm_num)
      _ = Z * (1 + R) ^ 2 := by
        simp only [Z]
        ring
  have hCsq : C ^ 2 = Z := by
    simpa only [C] using Real.sq_sqrt hZ
  have hAeq : A = (A - A0) + A0 := by module
  change covariantJetNormSq (I := I) (M := M) g 2 A ≤ (C * (1 + R)) ^ 2
  rw [hAeq]
  calc
    covariantJetNormSq (I := I) (M := M) g 2 ((A - A0) + A0) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 (A - A0) +
          covariantJetNormSq (I := I) (M := M) g 2 A0) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 (A - A0) A0
    _ ≤ 2 * (fr ^ 3 * R ^ 2 + J0) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hpairR le_rfl) (by norm_num)
    _ ≤ Z * (1 + R) ^ 2 := hdom
    _ = (C * (1 + R)) ^ 2 := by
      rw [mul_pow, hCsq]

private theorem exists_deTurckLieBackgroundDifferenceLoweredCoefficient_difference_raw_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ C21 C12 : ℝ, 0 ≤ C21 ∧ 0 ≤ C12 ∧
      ∀ gT gU : SmoothRiemannianMetric I M,
      covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg -
            deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gU g_bg) ≤
        4 * C21 *
            covariantJetNormSq (I := I) (M := M) g 2
              (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g_bg) *
            covariantJetNormSq (I := I) (M := M) g 1
              (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
                metricLoweredConnectionDifferenceCoefficient (I := I) g gU) +
          6 * C12 *
            covariantJetNormSq (I := I) (M := M) g 2
              (metricLoweredConnectionDifferenceCoefficient (I := I) g g_bg) *
            covariantJetNormSq (I := I) (M := M) g 1
              (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT -
                deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU) := by
  obtain ⟨C21, hC21, h21⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_one_le_two_one (I := I) (M := M) hDim g 0 3 4
  obtain ⟨C12, hC12, h12⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_one_le_one_two (I := I) (M := M) hDim g 0 3 4
  refine ⟨C21, C12, hC21, hC12, ?_⟩
  intro gT gU
  let X1 : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g (deTurckLieBackgroundDifferencePermutations 0)
      (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
        (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g_bg)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
          metricLoweredConnectionDifferenceCoefficient (I := I) g gU))
  let X2 : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g (deTurckLieBackgroundDifferencePermutations 1)
      (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
        (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT -
          deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g g_bg))
  let X3 : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g (deTurckLieBackgroundDifferencePermutations 2)
      (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
        (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT -
          deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g g_bg))
  have hX1 : covariantJetNormSq (I := I) (M := M) g 1 X1 ≤
      C21 * covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g_bg) *
        covariantJetNormSq (I := I) (M := M) g 1
          (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
            metricLoweredConnectionDifferenceCoefficient (I := I) g gU) := by
    dsimp only [X1]
    rw [covariantJetNormSq_one_domDomCongrSection]
    exact h21 _ _
  have hX2 : covariantJetNormSq (I := I) (M := M) g 1 X2 ≤
      C12 * covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT -
            deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU) *
        covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifferenceCoefficient (I := I) g g_bg) := by
    dsimp only [X2]
    rw [covariantJetNormSq_one_domDomCongrSection]
    exact h12 _ _
  have hX3 : covariantJetNormSq (I := I) (M := M) g 1 X3 ≤
      C12 * covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT -
            deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU) *
        covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifferenceCoefficient (I := I) g g_bg) := by
    dsimp only [X3]
    rw [covariantJetNormSq_one_domDomCongrSection]
    exact h12 _ _
  have h12sum := covariantJetNormSq_add_le (I := I) (M := M) g 1
    ((-1 : ℝ) • X1) X2
  have h123sum := covariantJetNormSq_add_le (I := I) (M := M) g 1
    ((-1 : ℝ) • X1 + X2) X3
  have hneg : covariantJetNormSq (I := I) (M := M) g 1 ((-1 : ℝ) • X1) =
      covariantJetNormSq (I := I) (M := M) g 1 X1 := by
    rw [covariantJetNormSq_smul]
    norm_num
  have hsum : covariantJetNormSq (I := I) (M := M) g 1
      (((-1 : ℝ) • X1 + X2) + X3) ≤
        4 * covariantJetNormSq (I := I) (M := M) g 1 X1 +
          4 * covariantJetNormSq (I := I) (M := M) g 1 X2 +
          2 * covariantJetNormSq (I := I) (M := M) g 1 X3 := by
    rw [hneg] at h12sum
    nlinarith
  rw [deTurckLieBackgroundDifferenceLoweredCoefficient_sub (I := I) (M := M) g gT gU g_bg]
  change covariantJetNormSq (I := I) (M := M) g 1
      (((-1 : ℝ) • X1 + X2) + X3) ≤ _
  nlinarith [hsum, hX1, hX2, hX3]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem connectionDifferenceLoweredCc_sub_eq_metricLoweredConnectionDifference_sub
    (g gT gU : SmoothRiemannianMetric I M) :
    metricLoweredConnectionDifferenceCoefficient (I := I) g gT - metricLoweredConnectionDifferenceCoefficient (I := I) g gU =
      metricLoweredConnectionDifference (I := I) (M := M) g gT g - metricLoweredConnectionDifference (I := I) (M := M) g gU g := by
  simp only [metricLoweredConnectionDifference]
  module

private lemma sq_add_sq_le_sum_sq
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ 2 + y ^ 2 ≤ (x + y) ^ 2 := by
  nlinarith only [mul_nonneg hx hy]

private lemma low_order_pairing_envelope_eq
    (k0 k1 w0 w1 s0 s1 A D : ℝ) :
    k0 * (w0 * D + w1 * A * D) + k1 * (s0 * D + s1 * A * D) =
      (k0 * w0 + k1 * s0) * D + (k0 * w1 + k1 * s1) * A * D := by
  ring

private lemma neg_smul_sub {V : Type*} [AddCommGroup V] [Module ℝ V]
    (X Y : V) :
    (-1 : ℝ) • X - (-1 : ℝ) • Y = (-1 : ℝ) • (X - Y) := by
  module

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] in
private theorem operatorFieldComposition_sub_apply_bilinear
    (g : SmoothRiemannianMetric I M)
    (PT PU : SmoothCcTensor g 6 2) (XT XU : SmoothCcTensor g 2 6) :
    ccOperatorFieldComp (I := I) (M := M) g 2 6 2 PT XT -
        ccOperatorFieldComp (I := I) (M := M) g 2 6 2 PU XU =
      ccOperatorFieldComp (I := I) (M := M) g 2 6 2 PU (XT - XU) +
        ccOperatorFieldComp (I := I) (M := M) g 2 6 2 (PT - PU) XT := by
  rw [ccOperatorFieldComp_sub_right, operatorFieldComposition_sub_left]
  module

private lemma pairing_product_bound_split
    (C Pb fr Bc Cp N Bt D : ℝ) :
    2 * (C * Pb ^ 2 * (fr * Bc * D) ^ 2 +
        C * (Cp * N) ^ 2 * (fr * Bt) ^ 2) =
      (2 * C * Pb ^ 2 * (fr * Bc) ^ 2) * D ^ 2 +
        (2 * C * Cp ^ 2 * (fr * Bt) ^ 2) * N ^ 2 := by
  ring

private lemma pairing_product_coefficient_nonneg
    {P B D C A : ℝ} (hP : 0 ≤ P) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hC : 0 ≤ C) (hA : 0 ≤ A) :
    0 ≤ P * (B * D + C * A) :=
  mul_nonneg hP (add_nonneg (mul_nonneg hB hD) (mul_nonneg hC hA))

private lemma pairing_product_coefficient_mul
    (P B D C A N : ℝ) :
    P * (B * (D * N) + (C * N) * A) =
      (P * (B * D + C * A)) * N := by
  ring

private theorem exists_deTurckLieBackgroundDifferenceLoweredCoefficient_difference_first_order_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg -
            deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gU g_bg) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C21, C12, hC21, hC12, hraw⟩ :=
    exists_deTurckLieBackgroundDifferenceLoweredCoefficient_difference_raw_bound (I := I) (M := M) hDim g g_bg
  obtain ⟨W0, W1, hW0, hW1, hw⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_one_sub_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨S0, S1, hS0, hS1, hs⟩ :=
    connSec_pair_h1 (I := I) (M := M) hDim g hδ₀0 hδ₀
  let JA : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g g_bg)
  let JC : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (metricLoweredConnectionDifferenceCoefficient (I := I) g g_bg)
  let fr : ℝ := Module.finrank ℝ E
  let Q0 : ℝ := 4 * C21 * JA
  let Q1 : ℝ := 6 * C12 * JC * fr ^ 2
  let K0 : ℝ := Real.sqrt Q0
  let K1 : ℝ := Real.sqrt Q1
  let B0 : ℝ → ℝ := fun R => K0 * W0 R + K1 * S0 R
  let B1 : ℝ → ℝ := fun R => K0 * W1 R + K1 * S1 R
  have hJA : 0 ≤ JA := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hJC : 0 ≤ JC := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hQ0 : 0 ≤ Q0 := by
    dsimp only [Q0]
    exact mul_nonneg (mul_nonneg (by norm_num) hC21) hJA
  have hQ1 : 0 ≤ Q1 := by
    dsimp only [Q1]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hC12) hJC) (sq_nonneg fr)
  have hK0 : 0 ≤ K0 := Real.sqrt_nonneg _
  have hK1 : 0 ≤ K1 := Real.sqrt_nonneg _
  have hK0sq : K0 ^ 2 = Q0 := by
    simpa only [K0] using Real.sq_sqrt hQ0
  have hK1sq : K1 ^ 2 = Q1 := by
    simpa only [K1] using Real.sq_sqrt hQ1
  refine ⟨B0, B1, ?_, ?_, ?_⟩
  · intro R hR
    dsimp only [B0]
    exact add_nonneg (mul_nonneg hK0 (hW0 R hR))
      (mul_nonneg hK1 (hS0 R hR))
  · intro R hR
    dsimp only [B1]
    exact add_nonneg (mul_nonneg hK0 (hW1 R hR))
      (mul_nonneg hK1 (hS1 R hR))
  · intro gT gU T U hT hU hTtie hUtie
      δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
      R A D2 hR hA hD2 hU2 hT3 hTU2
    let X : ℝ := W0 R * D2 + W1 R * A * D2
    let Y : ℝ := S0 R * D2 + S1 R * A * D2
    have hX : 0 ≤ X := by
      dsimp only [X]
      exact add_nonneg
        (mul_nonneg (hW0 R hR) hD2)
        (mul_nonneg (mul_nonneg (hW1 R hR) hA) hD2)
    have hY : 0 ≤ Y := by
      dsimp only [Y]
      exact add_nonneg
        (mul_nonneg (hS0 R hR) hD2)
        (mul_nonneg (mul_nonneg (hS1 R hR) hA) hD2)
    have hlow : covariantJetNormSq (I := I) (M := M) g 1
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
          metricLoweredConnectionDifferenceCoefficient (I := I) g gU) ≤ X ^ 2 := by
      calc
        covariantJetNormSq (I := I) (M := M) g 1
            (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
              metricLoweredConnectionDifferenceCoefficient (I := I) g gU) =
          covariantJetNormSq (I := I) (M := M) g 1
            (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
              metricLoweredConnectionDifference (I := I) (M := M) g gU g) := by
          rw [connectionDifferenceLoweredCc_sub_eq_metricLoweredConnectionDifference_sub (I := I) (M := M) g gT gU]
        _ ≤ X ^ 2 := by
          simpa only [X] using
            hw gT gU g T U hT hU hTtie hUtie
              hδT_le hδT0 hδT hδU_le hδU0 hδU
              R A D2 hR hA hD2 hU2 hT3 hTU2
    have hsec : covariantJetNormSq (I := I) (M := M) g 1
        (connectionDifferenceSection (I := I) gT g -
          connectionDifferenceSection (I := I) gU g) ≤ Y ^ 2 := by
      simpa only [Y] using
        hs gT gU T U hT hU hTtie hUtie
          hδT_le hδT0 hδT hδU_le hδU0 hδU
          R A D2 hR hA hD2 hU2 hT3 hTU2
    have harm : covariantJetNormSq (I := I) (M := M) g 1
        (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT -
          deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU) ≤
        fr ^ 2 * Y ^ 2 :=
      (deTurckLieCovariantDerivativeArmTwoCoefficient_difference_covariantJetNormSq_one_le (I := I) (M := M) g gT gU).trans
        (mul_le_mul_of_nonneg_left hsec (sq_nonneg fr))
    have hout := hraw gT gU
    have hpart0 : Q0 * covariantJetNormSq (I := I) (M := M) g 1
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
          metricLoweredConnectionDifferenceCoefficient (I := I) g gU) ≤ Q0 * X ^ 2 :=
      mul_le_mul_of_nonneg_left hlow hQ0
    have hbase1 : 0 ≤ 6 * C12 * JC :=
      mul_nonneg (mul_nonneg (by norm_num) hC12) hJC
    have hpart1 : (6 * C12 * JC) *
        covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT -
            deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU) ≤
        Q1 * Y ^ 2 := by
      calc
        (6 * C12 * JC) * covariantJetNormSq (I := I) (M := M) g 1
            (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT -
              deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU) ≤
          (6 * C12 * JC) * (fr ^ 2 * Y ^ 2) :=
            mul_le_mul_of_nonneg_left harm hbase1
        _ = Q1 * Y ^ 2 := by
          simp only [Q1, mul_assoc]
    have hquad : covariantJetNormSq (I := I) (M := M) g 1
        (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg -
          deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gU g_bg) ≤
        Q0 * X ^ 2 + Q1 * Y ^ 2 := by
      have hout' : covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg -
            deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gU g_bg) ≤
          Q0 * covariantJetNormSq (I := I) (M := M) g 1
              (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
                metricLoweredConnectionDifferenceCoefficient (I := I) g gU) +
            (6 * C12 * JC) * covariantJetNormSq (I := I) (M := M) g 1
              (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT -
                deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU) := by
        simpa only [Q0, JA, JC] using hout
      exact hout'.trans (add_le_add hpart0 hpart1)
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg -
            deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gU g_bg) ≤
        Q0 * X ^ 2 + Q1 * Y ^ 2 := hquad
      _ = (K0 * X) ^ 2 + (K1 * Y) ^ 2 := by
        rw [mul_pow, mul_pow, hK0sq, hK1sq]
      _ ≤ (K0 * X + K1 * Y) ^ 2 := by
        exact sq_add_sq_le_sum_sq (K0 * X) (K1 * Y)
          (mul_nonneg hK0 hX) (mul_nonneg hK1 hY)
      _ = (B0 R * D2 + B1 R * A * D2) ^ 2 := by
        rw [low_order_pairing_envelope_eq]

private theorem exists_deTurckLieBackgroundDifferenceLoweredCoefficient_first_order_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δT : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (A : ℝ), 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg) ≤
        2 * ((B0 0 * A + B1 0 * A * A) ^ 2 +
          covariantJetNormSq (I := I) (M := M) g 1
            (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g g g_bg)) := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    exists_deTurckLieBackgroundDifferenceLoweredCoefficient_difference_first_order_bound (I := I) (M := M) hDim g g_bg hδ₀0 hδ₀
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro gT T hT hTtie δT hδT_le hδT0 hδT A hA hT3
  have hzero : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  have hzeroTie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v = g.inner x u v +
        ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  have hT2 : covariantJetNormSq (I := I) (M := M) g 2 T ≤ A ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by omega) T).trans hT3
  have hzeroOp : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) 0 := by
    intro x v w
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    norm_num
  have hpair0 : covariantJetNormSq (I := I) (M := M) g 1
      (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg -
        deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g g g_bg) ≤
      (B0 0 * A + B1 0 * A * A) ^ 2 := by
    have hz2 : covariantJetNormSq (I := I) (M := M) g 2
        (0 : SmoothCcTensor g 0 2) ≤ (0 : ℝ) ^ 2 := by
      rw [covariantJetNormSq_zero]
      norm_num
    have hTU2 : covariantJetNormSq (I := I) (M := M) g 2
        (T - (0 : SmoothCcTensor g 0 2)) ≤ A ^ 2 := by
      simpa only [sub_zero] using hT2
    exact hpair gT g T (0 : SmoothCcTensor g 0 2)
        hT hzero hTtie hzeroTie
        hδT_le hδT0 hδT hδ₀0 (by norm_num)
        hzeroOp
        0 A A (by norm_num) hA hA hz2 hT3 hTU2
  have hdecomp : deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg =
      (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg -
        deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g g g_bg) +
      deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g g g_bg := by
    module
  rw [hdecomp]
  exact (covariantJetNormSq_add_le (I := I) (M := M) g 1 _ _).trans
    (mul_le_mul_of_nonneg_left (add_le_add hpair0 le_rfl) (by norm_num))

private theorem exists_deTurckLieBackgroundDifferenceCoefficient_difference_raw_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ gT gU : SmoothRiemannianMetric I M,
      covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg -
            deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gU g_bg) ≤
        8 * C *
          (covariantJetNormSq (I := I) (M := M) g 2
              (slotInsertEndoCc (I := I) (M := M) g 3
                (metricComparisonEndomorphismField (I := I) (M := M) gU g)) *
            covariantJetNormSq (I := I) (M := M) g 1
              (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg -
                deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gU g_bg) +
           covariantJetNormSq (I := I) (M := M) g 2
              (slotInsertEndoCc (I := I) (M := M) g 3
                  (metricComparisonEndomorphismField (I := I) (M := M) gT g) -
                slotInsertEndoCc (I := I) (M := M) g 3
                  (metricComparisonEndomorphismField (I := I) (M := M) gU g)) *
            covariantJetNormSq (I := I) (M := M) g 1
              (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg)) := by
  obtain ⟨C, hC, happ⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_one_le_two_one (I := I) (M := M) hDim g 0 4 4
  refine ⟨C, hC, ?_⟩
  intro gT gU
  let ST : SmoothCcTensor g 4 4 :=
    slotInsertEndoCc (I := I) (M := M) g 3
      (metricComparisonEndomorphismField (I := I) (M := M) gT g)
  let SU : SmoothCcTensor g 4 4 :=
    slotInsertEndoCc (I := I) (M := M) g 3
      (metricComparisonEndomorphismField (I := I) (M := M) gU g)
  let LT : SmoothCcTensor g 0 4 :=
    deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg
  let LU : SmoothCcTensor g 0 4 :=
    deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gU g_bg
  let HT : SmoothCcTensor g 0 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 0 4 4 ST LT
  let HU : SmoothCcTensor g 0 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 0 4 4 SU LU
  have hhalf : HT - HU =
      ccOperatorFieldComp (I := I) (M := M) g 0 4 4 SU (LT - LU) +
        ccOperatorFieldComp (I := I) (M := M) g 0 4 4 (ST - SU) LT := by
    dsimp only [HT, HU]
    rw [ccOperatorFieldComp_sub_right, operatorFieldComposition_sub_left]
    module
  have hterm0 : covariantJetNormSq (I := I) (M := M) g 1
      (ccOperatorFieldComp (I := I) (M := M) g 0 4 4 SU (LT - LU)) ≤
      C * covariantJetNormSq (I := I) (M := M) g 2 SU *
        covariantJetNormSq (I := I) (M := M) g 1 (LT - LU) :=
    happ SU (LT - LU)
  have hterm1 : covariantJetNormSq (I := I) (M := M) g 1
      (ccOperatorFieldComp (I := I) (M := M) g 0 4 4 (ST - SU) LT) ≤
      C * covariantJetNormSq (I := I) (M := M) g 2 (ST - SU) *
        covariantJetNormSq (I := I) (M := M) g 1 LT :=
    happ (ST - SU) LT
  have hhalfJ : covariantJetNormSq (I := I) (M := M) g 1 (HT - HU) ≤
      2 * (C * covariantJetNormSq (I := I) (M := M) g 2 SU *
          covariantJetNormSq (I := I) (M := M) g 1 (LT - LU) +
        C * covariantJetNormSq (I := I) (M := M) g 2 (ST - SU) *
          covariantJetNormSq (I := I) (M := M) g 1 LT) := by
    rw [hhalf]
    exact (covariantJetNormSq_add_le (I := I) (M := M) g 1 _ _).trans
      (mul_le_mul_of_nonneg_left (add_le_add hterm0 hterm1) (by norm_num))
  have hcore : deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg -
      deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gU g_bg =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) (HT - HU) +
        (HT - HU) := by
    rw [deTurckLieBackgroundDifferenceCoefficient, deTurckLieBackgroundDifferenceCoefficient]
    change (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) HT + HT) -
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) HU + HU) = _
    rw [domDomCongrSection_sub]
    module
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg -
          deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gU g_bg) =
      covariantJetNormSq (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) (HT - HU) +
          (HT - HU)) := by rw [hcore]
    _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) (HT - HU)) +
        covariantJetNormSq (I := I) (M := M) g 1 (HT - HU)) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 1 _ _
    _ = 4 * covariantJetNormSq (I := I) (M := M) g 1 (HT - HU) := by
      rw [covariantJetNormSq_one_domDomCongrSection]
      ring
    _ ≤ 4 * (2 * (C * covariantJetNormSq (I := I) (M := M) g 2 SU *
          covariantJetNormSq (I := I) (M := M) g 1 (LT - LU) +
        C * covariantJetNormSq (I := I) (M := M) g 2 (ST - SU) *
          covariantJetNormSq (I := I) (M := M) g 1 LT)) :=
      mul_le_mul_of_nonneg_left hhalfJ (by norm_num)
    _ = 8 * C *
        (covariantJetNormSq (I := I) (M := M) g 2 SU *
            covariantJetNormSq (I := I) (M := M) g 1 (LT - LU) +
          covariantJetNormSq (I := I) (M := M) g 2 (ST - SU) *
            covariantJetNormSq (I := I) (M := M) g 1 LT) := by ring

private theorem exists_deTurckLieBackgroundDifferenceCoefficient_difference_first_order_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ → ℝ,
      (∀ R A : ℝ, 0 ≤ B R A) ∧
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
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg -
            deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gU g_bg) ≤
        (B R A * D2) ^ 2 := by
  obtain ⟨C, hC, hraw⟩ :=
    exists_deTurckLieBackgroundDifferenceCoefficient_difference_raw_bound (I := I) (M := M) hDim g g_bg
  obtain ⟨Cr, hCr, hrev⟩ := exists_metricComparisonEndomorphism_third_slot_covariantJetNormSq_two_bound (I := I) (M := M) g
  obtain ⟨P0, P1, hP0, hP1, hpair⟩ :=
    exists_deTurckLieBackgroundDifferenceLoweredCoefficient_difference_first_order_bound (I := I) (M := M) hDim g g_bg hδ₀0 hδ₀
  obtain ⟨D0, D1, hD0, hD1, hbdd⟩ :=
    exists_deTurckLieBackgroundDifferenceLoweredCoefficient_first_order_bound (I := I) (M := M) hDim g g_bg hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let J0 : ℝ := covariantJetNormSq (I := I) (M := M) g 1
    (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g g g_bg)
  let Q : ℝ → ℝ → ℝ → ℝ := fun R A D2 =>
    8 * C *
      ((Cr * (1 + R)) ^ 2 *
          (P0 R * D2 + P1 R * A * D2) ^ 2 +
        fr ^ 3 * D2 ^ 2 *
          (2 * ((D0 0 * A + D1 0 * A * A) ^ 2 + J0)))
  let K : ℝ → ℝ → ℝ := fun R A =>
    8 * C *
      ((Cr * (1 + R)) ^ 2 * (P0 R + P1 R * A) ^ 2 +
        fr ^ 3 *
          (2 * ((D0 0 * A + D1 0 * A * A) ^ 2 + J0)))
  let B : ℝ → ℝ → ℝ := fun R A => Real.sqrt (K R A)
  refine ⟨B, fun R A => Real.sqrt_nonneg _, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  have hSU : covariantJetNormSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 3
        (metricComparisonEndomorphismField (I := I) (M := M) gU g)) ≤
      (Cr * (1 + R)) ^ 2 :=
    hrev gU U hU hUtie R hR hU2
  have hSD : covariantJetNormSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 3
          (metricComparisonEndomorphismField (I := I) (M := M) gT g) -
        slotInsertEndoCc (I := I) (M := M) g 3
          (metricComparisonEndomorphismField (I := I) (M := M) gU g)) ≤
      fr ^ 3 * D2 ^ 2 :=
    (metricComparisonEndomorphism_third_slot_difference_covariantJetNormSq_two_le (I := I) (M := M) g gT gU T U
      hT hU hTtie hUtie).trans
      (mul_le_mul_of_nonneg_left hTU2 (by positivity))
  have hLP : covariantJetNormSq (I := I) (M := M) g 1
      (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg -
        deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gU g_bg) ≤
      (P0 R * D2 + P1 R * A * D2) ^ 2 :=
    hpair gT gU T U hT hU hTtie hUtie
      hδT_le hδT0 hδT hδU_le hδU0 hδU
      R A D2 hR hA hD2 hU2 hT3 hTU2
  have hLT : covariantJetNormSq (I := I) (M := M) g 1
      (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg) ≤
      2 * ((D0 0 * A + D1 0 * A * A) ^ 2 + J0) := by
    simpa only [J0] using
      hbdd gT T hT hTtie hδT_le hδT0 hδT A hA hT3
  have hSU0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 3
        (metricComparisonEndomorphismField (I := I) (M := M) gU g)) :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hLP0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1
      (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg -
        deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gU g_bg) :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 1) g _
  have hSD0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 3
          (metricComparisonEndomorphismField (I := I) (M := M) gT g) -
        slotInsertEndoCc (I := I) (M := M) g 3
          (metricComparisonEndomorphismField (I := I) (M := M) gU g)) :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hLT0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1
      (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg) :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 1) g _
  have hRU : 0 ≤ (Cr * (1 + R)) ^ 2 := sq_nonneg _
  have hRP : 0 ≤ (P0 R * D2 + P1 R * A * D2) ^ 2 := sq_nonneg _
  have hRD : 0 ≤ fr ^ 3 * D2 ^ 2 := by positivity
  have hRL : 0 ≤ 2 * ((D0 0 * A + D1 0 * A * A) ^ 2 + J0) := by
    have hJ0 : 0 ≤ J0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 1) g _
    exact mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) hJ0)
  have hprod0 :
      covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 3
            (metricComparisonEndomorphismField (I := I) (M := M) gU g)) *
        covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg -
            deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gU g_bg) ≤
      (Cr * (1 + R)) ^ 2 *
        (P0 R * D2 + P1 R * A * D2) ^ 2 :=
    (mul_le_mul_of_nonneg_right hSU hLP0).trans
      (mul_le_mul_of_nonneg_left hLP hRU)
  have hprod1 :
      covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 3
              (metricComparisonEndomorphismField (I := I) (M := M) gT g) -
            slotInsertEndoCc (I := I) (M := M) g 3
              (metricComparisonEndomorphismField (I := I) (M := M) gU g)) *
        covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieBackgroundDifferenceLoweredCoefficient (I := I) (M := M) g gT g_bg) ≤
      fr ^ 3 * D2 ^ 2 *
        (2 * ((D0 0 * A + D1 0 * A * A) ^ 2 + J0)) :=
    (mul_le_mul_of_nonneg_right hSD hLT0).trans
      (mul_le_mul_of_nonneg_left hLT hRD)
  have hout := hraw gT gU
  have hcoef : 0 ≤ 8 * C := mul_nonneg (by norm_num) hC
  have hmain : covariantJetNormSq (I := I) (M := M) g 1
      (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg -
        deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gU g_bg) ≤ Q R A D2 := by
    exact hout.trans
      (mul_le_mul_of_nonneg_left (add_le_add hprod0 hprod1) hcoef)
  have hK : 0 ≤ K R A := by
    dsimp only [K]
    exact mul_nonneg hcoef
      (add_nonneg (mul_nonneg hRU (sq_nonneg _))
        (mul_nonneg (by positivity) hRL))
  have hBsq : (B R A) ^ 2 = K R A := by
    simpa only [B] using Real.sq_sqrt hK
  have hQeq : Q R A D2 = K R A * D2 ^ 2 := by
    dsimp only [Q, K]
    ring
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg -
          deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gU g_bg) ≤ Q R A D2 := hmain
    _ = K R A * D2 ^ 2 := hQeq
    _ = (B R A * D2) ^ 2 := by rw [mul_pow, hBsq]

private noncomputable def deTurckLieBackgroundDifferencePairTrace
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 4) :
    SmoothCcTensor g 2 6 :=
  rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
    (slotExtendIter (I := I) (M := M) g 0 4 2 S)

private theorem covariantJetNormSq_one_slotExtend_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 1
        (slotExtend (I := I) (M := M) g r s S) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 1 S := by
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
          (slotExtend (I := I) (M := M) g r s S)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 2, (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i S‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        iteratedCovGrad_slotExtend_norm_sq_le (I := I) (M := M) g r s i S
    _ = (Module.finrank ℝ E : ℝ) *
        ∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g r s i S‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem covariantJetNormSq_one_slotExtendIter_two_le
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 4) :
    covariantJetNormSq (I := I) (M := M) g 1
        (slotExtendIter (I := I) (M := M) g 0 4 2 S) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 1 S := by
  change covariantJetNormSq (I := I) (M := M) g 1
      (slotExtend (I := I) (M := M) g 1 5
        (slotExtend (I := I) (M := M) g 0 4 S)) ≤ _
  have hfr : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  calc
    _ ≤ (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 0 4 S) :=
      covariantJetNormSq_one_slotExtend_le (I := I) (M := M) g 1 5 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          covariantJetNormSq (I := I) (M := M) g 1 S) :=
      mul_le_mul_of_nonneg_left
        (covariantJetNormSq_one_slotExtend_le (I := I) (M := M) g 0 4 S) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 1 S := by ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem slotExtendIter_two_sub
    (g : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g 0 4) :
    slotExtendIter (I := I) (M := M) g 0 4 2 (A - B) =
      slotExtendIter (I := I) (M := M) g 0 4 2 A -
        slotExtendIter (I := I) (M := M) g 0 4 2 B := by
  change slotExtend (I := I) (M := M) g 1 5
      (slotExtend (I := I) (M := M) g 0 4 (A - B)) =
    slotExtend (I := I) (M := M) g 1 5
        (slotExtend (I := I) (M := M) g 0 4 A) -
      slotExtend (I := I) (M := M) g 1 5
        (slotExtend (I := I) (M := M) g 0 4 B)
  rw [slotExtend_sub, slotExtend_sub]

private theorem covariantJetNormSq_one_rsDomDomCongrSection
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 1
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S) =
      covariantJetNormSq (I := I) (M := M) g 1 S := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro i _
  exact iteratedCovGrad_rsDomDomCongrSection_norm_sq (I := I) (M := M) g σ S i

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem deTurckLieBackgroundDifferencePairTrace_sub
    (g : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g 0 4) :
    deTurckLieBackgroundDifferencePairTrace (I := I) (M := M) g (A - B) =
      deTurckLieBackgroundDifferencePairTrace (I := I) (M := M) g A -
        deTurckLieBackgroundDifferencePairTrace (I := I) (M := M) g B := by
  unfold deTurckLieBackgroundDifferencePairTrace
  rw [slotExtendIter_two_sub, rsDomDomCongrSection_sub]

private theorem covariantJetNormSq_one_deTurckLieBackgroundDifferencePairTrace_le
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 4) :
    covariantJetNormSq (I := I) (M := M) g 1
        (deTurckLieBackgroundDifferencePairTrace (I := I) (M := M) g S) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 1 S := by
  unfold deTurckLieBackgroundDifferencePairTrace
  rw [covariantJetNormSq_one_rsDomDomCongrSection]
  exact covariantJetNormSq_one_slotExtendIter_two_le (I := I) (M := M) g S

private theorem exists_deTurckLieBackgroundDifferenceCoefficient_first_order_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δT : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (A : ℝ), 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg) ≤
        (B A) ^ 2 := by
  obtain ⟨P, hP, hpair⟩ :=
    exists_deTurckLieBackgroundDifferenceCoefficient_difference_first_order_bound (I := I) (M := M) hDim g g_bg hδ₀0 hδ₀
  let J0 : ℝ := covariantJetNormSq (I := I) (M := M) g 1
    (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g g g_bg)
  let Q : ℝ → ℝ := fun A => 2 * ((P 0 A * A) ^ 2 + J0)
  let B : ℝ → ℝ := fun A => Real.sqrt (Q A)
  have hJ0 : 0 ≤ J0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 1) g _
  have hQ : ∀ A : ℝ, 0 ≤ Q A := by
    intro A
    exact mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) hJ0)
  refine ⟨B, fun A _ => Real.sqrt_nonneg _, ?_⟩
  intro gT T hT hTtie δT hδT_le hδT0 hδT A hA hT3
  have hzero : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  have hzeroTie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v = g.inner x u v +
        ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  have hzeroOp : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) 0 := by
    intro x v w
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    norm_num
  have hT2 : covariantJetNormSq (I := I) (M := M) g 2 T ≤ A ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by omega) T).trans hT3
  have hz2 : covariantJetNormSq (I := I) (M := M) g 2
      (0 : SmoothCcTensor g 0 2) ≤ (0 : ℝ) ^ 2 := by
    rw [covariantJetNormSq_zero]
    norm_num
  have hTU2 : covariantJetNormSq (I := I) (M := M) g 2
      (T - (0 : SmoothCcTensor g 0 2)) ≤ A ^ 2 := by
    simpa only [sub_zero] using hT2
  have hpair0 : covariantJetNormSq (I := I) (M := M) g 1
      (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg -
        deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g g g_bg) ≤
      (P 0 A * A) ^ 2 :=
    hpair gT g T (0 : SmoothCcTensor g 0 2)
      hT hzero hTtie hzeroTie
      hδT_le hδT0 hδT hδ₀0 (by norm_num) hzeroOp
      0 A A (by norm_num) hA hA hz2 hT3 hTU2
  have hdecomp : deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg =
      (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg -
        deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g g g_bg) +
      deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g g g_bg := by
    module
  have hmain : covariantJetNormSq (I := I) (M := M) g 1
      (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg) ≤ Q A := by
    rw [hdecomp]
    exact (covariantJetNormSq_add_le (I := I) (M := M) g 1 _ _).trans
      (mul_le_mul_of_nonneg_left (add_le_add hpair0 le_rfl) (by norm_num))
  have hBsq : (B A) ^ 2 = Q A := by
    simpa only [B] using Real.sq_sqrt (hQ A)
  rw [hBsq]
  exact hmain

theorem exists_deTurckLieConnectionDifferenceDerivativeCoefficient_backgroundDifference_pairing_firstOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ ρ : ℝ, ∃ B0 : ℝ → ℝ → ℝ, ∃ B1 : ℝ → ℝ,
      0 < ρ ∧
      (∀ R A : ℝ, 0 ≤ B0 R A) ∧
      (∀ A : ℝ, 0 ≤ B1 A) ∧
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
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      let N := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      covariantJetNormSq (I := I) (M := M) g 1
          ((deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gT g_bg -
              deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gT g) -
            (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gU g_bg -
              deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gU g)) ≤
        (B0 R A * D2 + B1 A * N) ^ 2 := by
  obtain ⟨C, hC, happ⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_one_le_two_one (I := I) (M := M) hDim g 2 6 2
  obtain ⟨Bc, hBc, hcore⟩ :=
    exists_deTurckLieBackgroundDifferenceCoefficient_difference_first_order_bound (I := I) (M := M) hDim g g_bg hδ₀0 hδ₀
  obtain ⟨Bt, hBt, hcoreBdd⟩ :=
    exists_deTurckLieBackgroundDifferenceCoefficient_first_order_bound (I := I) (M := M) hDim g g_bg hδ₀0 hδ₀
  obtain ⟨ρp, Cp, hρp, hCp, htracePair⟩ :=
    RicciDeTurckLowOrder.pairTrace_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Pb, hρb, hPb, htraceBdd⟩ :=
    RicciDeTurckLowOrder.pair_trace_sobolev_two_bound (I := I) (M := M) hDim g
  let fr : ℝ := Module.finrank ℝ E
  let ρ : ℝ := min ρp ρb
  let K0 : ℝ → ℝ → ℝ := fun R A =>
    2 * C * Pb ^ 2 * (fr * Bc R A) ^ 2
  let K1 : ℝ → ℝ := fun A =>
    2 * C * Cp ^ 2 * (fr * Bt A) ^ 2
  let B0 : ℝ → ℝ → ℝ := fun R A => Real.sqrt (K0 R A)
  let B1 : ℝ → ℝ := fun A => Real.sqrt (K1 A)
  have hρ : 0 < ρ := lt_min hρp hρb
  refine ⟨ρ, B0, B1, hρ, fun R A => Real.sqrt_nonneg _,
    fun A => Real.sqrt_nonneg _, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    hTHs hUHs R A D2 hR hA hD2 hU2 hT3 hTU2
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let PT : SmoothCcTensor g 6 2 :=
    cometricDoublePairTraceCoefficient (I := I) (M := M) g gT
  let PU : SmoothCcTensor g 6 2 :=
    cometricDoublePairTraceCoefficient (I := I) (M := M) g gU
  let XT : SmoothCcTensor g 2 6 :=
    deTurckLieBackgroundDifferencePairTrace (I := I) (M := M) g
      (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg)
  let XU : SmoothCcTensor g 2 6 :=
    deTurckLieBackgroundDifferencePairTrace (I := I) (M := M) g
      (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gU g_bg)
  let YT : SmoothCcTensor g 2 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 2 PT XT
  let YU : SmoothCcTensor g 2 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 2 PU XU
  let FT : SmoothCcTensor g 2 2 :=
    deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gT g_bg -
      deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gT g
  let FU : SmoothCcTensor g 2 2 :=
    deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gU g_bg -
      deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gU g
  have hFT : FT = (-1 : ℝ) • YT := by
    dsimp only [FT, YT, PT, XT]
    simpa only [deTurckLieBackgroundDifferencePairTrace] using
      (deTurckLieConnectionDifferenceDerivative_backgroundDifference_eq (I := I) (M := M) g g_bg gT)
  have hFU : FU = (-1 : ℝ) • YU := by
    dsimp only [FU, YU, PU, XU]
    simpa only [deTurckLieBackgroundDifferencePairTrace] using
      (deTurckLieConnectionDifferenceDerivative_backgroundDifference_eq (I := I) (M := M) g g_bg gU)
  have hFsub : FT - FU = (-1 : ℝ) • (YT - YU) := by
    rw [hFT, hFU]
    exact neg_smul_sub YT YU
  have hYsub : YT - YU =
      ccOperatorFieldComp (I := I) (M := M) g 2 6 2 PU (XT - XU) +
        ccOperatorFieldComp (I := I) (M := M) g 2 6 2 (PT - PU) XT := by
    dsimp only [YT, YU]
    exact operatorFieldComposition_sub_apply_bilinear (I := I) (M := M) g PT PU XT XU
  have hXsub : XT - XU =
      deTurckLieBackgroundDifferencePairTrace (I := I) (M := M) g
        (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg -
          deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gU g_bg) := by
    simpa only [XT, XU] using
      (deTurckLieBackgroundDifferencePairTrace_sub (I := I) (M := M) g
        (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg)
        (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gU g_bg)).symm
  have hTHsp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρp := hTHs.trans (min_le_left _ _)
  have hUHsp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρp := hUHs.trans (min_le_left _ _)
  have hTHsb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρb := hTHs.trans (min_le_right _ _)
  have hUHsb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρb := hUHs.trans (min_le_right _ _)
  have hPU : covariantJetNormSq (I := I) (M := M) g 2 PU ≤ Pb ^ 2 := by
    simpa only [PU] using htraceBdd U gU hUtie hUHsb
  have hPD : covariantJetNormSq (I := I) (M := M) g 2 (PT - PU) ≤
      (Cp * N) ^ 2 := by
    simpa only [PT, PU, N] using
      htracePair T U gT gU hTtie hUtie hTHsp hUHsp
  have hcoreD : covariantJetNormSq (I := I) (M := M) g 1
      (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg -
        deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gU g_bg) ≤
      (Bc R A * D2) ^ 2 :=
    hcore gT gU T U hT hU hTtie hUtie
      hδT_le hδT0 hδT hδU_le hδU0 hδU
      R A D2 hR hA hD2 hU2 hT3 hTU2
  have hcoreT : covariantJetNormSq (I := I) (M := M) g 1
      (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg) ≤ (Bt A) ^ 2 :=
    hcoreBdd gT T hT hTtie hδT_le hδT0 hδT A hA hT3
  have hXD : covariantJetNormSq (I := I) (M := M) g 1 (XT - XU) ≤
      (fr * Bc R A * D2) ^ 2 := by
    rw [hXsub]
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieBackgroundDifferencePairTrace (I := I) (M := M) g
            (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg -
              deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gU g_bg)) ≤
        fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg -
            deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gU g_bg) :=
        covariantJetNormSq_one_deTurckLieBackgroundDifferencePairTrace_le (I := I) (M := M) g _
      _ ≤ fr ^ 2 * (Bc R A * D2) ^ 2 :=
        mul_le_mul_of_nonneg_left hcoreD (sq_nonneg _)
      _ = (fr * Bc R A * D2) ^ 2 := by
        simp only [mul_pow, mul_assoc]
  have hXT : covariantJetNormSq (I := I) (M := M) g 1 XT ≤
      (fr * Bt A) ^ 2 := by
    dsimp only [XT]
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieBackgroundDifferencePairTrace (I := I) (M := M) g
            (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg)) ≤
        fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 1
          (deTurckLieBackgroundDifferenceCoefficient (I := I) (M := M) g gT g_bg) :=
        covariantJetNormSq_one_deTurckLieBackgroundDifferencePairTrace_le (I := I) (M := M) g _
      _ ≤ fr ^ 2 * (Bt A) ^ 2 :=
        mul_le_mul_of_nonneg_left hcoreT (sq_nonneg _)
      _ = (fr * Bt A) ^ 2 := by rw [mul_pow]
  have hPU0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 PU :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hPD0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 (PT - PU) :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hXD0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1 (XT - XU) :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 1) g _
  have hXT0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1 XT :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 1) g _
  have hprod0 : C * covariantJetNormSq (I := I) (M := M) g 2 PU *
        covariantJetNormSq (I := I) (M := M) g 1 (XT - XU) ≤
      C * Pb ^ 2 * (fr * Bc R A * D2) ^ 2 :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPU hC) hXD0).trans
      (mul_le_mul_of_nonneg_left hXD
        (mul_nonneg hC (sq_nonneg _)))
  have hprod1 : C * covariantJetNormSq (I := I) (M := M) g 2 (PT - PU) *
        covariantJetNormSq (I := I) (M := M) g 1 XT ≤
      C * (Cp * N) ^ 2 * (fr * Bt A) ^ 2 :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPD hC) hXT0).trans
      (mul_le_mul_of_nonneg_left hXT
        (mul_nonneg hC (sq_nonneg _)))
  have hYraw : covariantJetNormSq (I := I) (M := M) g 1 (YT - YU) ≤
      2 * (C * covariantJetNormSq (I := I) (M := M) g 2 PU *
            covariantJetNormSq (I := I) (M := M) g 1 (XT - XU) +
        C * covariantJetNormSq (I := I) (M := M) g 2 (PT - PU) *
            covariantJetNormSq (I := I) (M := M) g 1 XT) := by
    rw [hYsub]
    exact (covariantJetNormSq_add_le (I := I) (M := M) g 1 _ _).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add (happ PU (XT - XU)) (happ (PT - PU) XT))
        (by norm_num))
  have hY : covariantJetNormSq (I := I) (M := M) g 1 (YT - YU) ≤
      2 * (C * Pb ^ 2 * (fr * Bc R A * D2) ^ 2 +
        C * (Cp * N) ^ 2 * (fr * Bt A) ^ 2) :=
    hYraw.trans
      (mul_le_mul_of_nonneg_left (add_le_add hprod0 hprod1) (by norm_num))
  have hK0 : 0 ≤ K0 R A := by
    dsimp only [K0]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg _))
      (sq_nonneg _)
  have hK1 : 0 ≤ K1 A := by
    dsimp only [K1]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg _))
      (sq_nonneg _)
  have hB0sq : (B0 R A) ^ 2 = K0 R A := by
    simpa only [B0] using Real.sq_sqrt hK0
  have hB1sq : (B1 A) ^ 2 = K1 A := by
    simpa only [B1] using Real.sq_sqrt hK1
  have hsplitSq :
      2 * (C * Pb ^ 2 * (fr * Bc R A * D2) ^ 2 +
          C * (Cp * N) ^ 2 * (fr * Bt A) ^ 2) =
        (B0 R A * D2) ^ 2 + (B1 A * N) ^ 2 := by
    calc
      2 * (C * Pb ^ 2 * (fr * Bc R A * D2) ^ 2 +
          C * (Cp * N) ^ 2 * (fr * Bt A) ^ 2) =
        K0 R A * D2 ^ 2 + K1 A * N ^ 2 := by
          simpa only [K0, K1] using
            pairing_product_bound_split C Pb fr (Bc R A) Cp N (Bt A) D2
      _ = (B0 R A) ^ 2 * D2 ^ 2 + (B1 A) ^ 2 * N ^ 2 := by
        rw [hB0sq, hB1sq]
      _ = (B0 R A * D2) ^ 2 + (B1 A * N) ^ 2 := by
        rw [mul_pow, mul_pow]
  have hN : 0 ≤ N := norm_nonneg _
  have hZ0 : 0 ≤ B0 R A * D2 :=
    mul_nonneg (Real.sqrt_nonneg _) hD2
  have hZ1 : 0 ≤ B1 A * N :=
    mul_nonneg (Real.sqrt_nonneg _) hN
  have hFjet : covariantJetNormSq (I := I) (M := M) g 1 (FT - FU) =
      covariantJetNormSq (I := I) (M := M) g 1 (YT - YU) := by
    rw [hFsub]
    simpa only [neg_one_sq, one_mul] using
      (covariantJetNormSq_smul (I := I) (M := M) g 1 (-1 : ℝ) (YT - YU))
  change covariantJetNormSq (I := I) (M := M) g 1 (FT - FU) ≤
    (B0 R A * D2 + B1 A * N) ^ 2
  rw [hFjet]
  calc
    covariantJetNormSq (I := I) (M := M) g 1 (YT - YU) ≤
        2 * (C * Pb ^ 2 * (fr * Bc R A * D2) ^ 2 +
          C * (Cp * N) ^ 2 * (fr * Bt A) ^ 2) := hY
    _ = (B0 R A * D2) ^ 2 + (B1 A * N) ^ 2 := hsplitSq
    _ ≤ (B0 R A * D2 + B1 A * N) ^ 2 := by
      exact sq_add_sq_le_sum_sq _ _ hZ0 hZ1

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iteratedCovGrad_covGrad_norm_sq_eq
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (S : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r (s + 1) i
        (covGrad (I := I) (M := M) g r s S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s (i + 1) S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs
    (I := I) (M := M) g r s i S x

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem covariantJetNormSq_one_covGrad_le_two
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 1
        (covGrad (I := I) (M := M) g r s S) ≤
      covariantJetNormSq (I := I) (M := M) g 2 S := by
  have h0 := iteratedCovGrad_covGrad_norm_sq_eq (I := I) (M := M) g r s 0 S
  have h1 := iteratedCovGrad_covGrad_norm_sq_eq (I := I) (M := M) g r s 1 S
  unfold covariantJetNormSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 ⊢
  rw [h0, h1]
  nlinarith [sq_nonneg ‖S‖]

private theorem covariantJetNormSq_one_slotInsertEndoCc_le
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    covariantJetNormSq (I := I) (M := M) g 1
        (slotInsertEndoCc (I := I) (M := M) g s Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        covariantJetNormSq (I := I) (M := M) g 1
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 2, (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        iteratedCovGrad_slotInsertEndoCc_norm_sq_le (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

private noncomputable def endomorphismInsertionPair
    (g : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    SmoothCcTensor g 2 2 :=
  let X := slotInsertEndoCc (I := I) (M := M) g 1 Λ
  X + reindexCoeffGen (I := I) (M := M) g 2 2
    (rsDomDomCongrSection (I := I) (M := M) g 2 2
      (Equiv.swap (0 : Fin 2) 1) X)
    (Equiv.swap (0 : Fin 2) 1)

private theorem covariantJetNormSq_one_endomorphismInsertionPair_le
    (g : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    covariantJetNormSq (I := I) (M := M) g 1
        (endomorphismInsertionPair (I := I) (M := M) g Λ) ≤
      4 * (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 1
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
  let X : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1 Λ
  let Y : SmoothCcTensor g 2 2 :=
    reindexCoeffGen (I := I) (M := M) g 2 2
      (rsDomDomCongrSection (I := I) (M := M) g 2 2
        (Equiv.swap (0 : Fin 2) 1) X)
      (Equiv.swap (0 : Fin 2) 1)
  have hY : covariantJetNormSq (I := I) (M := M) g 1 Y =
      covariantJetNormSq (I := I) (M := M) g 1 X := by
    dsimp only [Y]
    rw [covariantJetNormSq_reindexCoeffGen, covariantJetNormSq_one_rsDomDomCongrSection]
  have hX : covariantJetNormSq (I := I) (M := M) g 1 X ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 1
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
    simpa only [X, pow_one] using
      covariantJetNormSq_one_slotInsertEndoCc_le (I := I) (M := M) g 1 Λ
  change covariantJetNormSq (I := I) (M := M) g 1 (X + Y) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 1 (X + Y) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 1 X +
          covariantJetNormSq (I := I) (M := M) g 1 Y) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 1 X Y
    _ = 4 * covariantJetNormSq (I := I) (M := M) g 1 X := by
      rw [hY]
      ring
    _ ≤ 4 * ((Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 1
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)) :=
      mul_le_mul_of_nonneg_left hX (by norm_num)
    _ = 4 * (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 1
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem endomorphismInsertionPair_sub
    (g : SmoothRiemannianMetric I M)
    (Λ Γ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endomorphismInsertionPair (I := I) (M := M) g (Λ - Γ) =
      endomorphismInsertionPair (I := I) (M := M) g Λ -
        endomorphismInsertionPair (I := I) (M := M) g Γ := by
  unfold endomorphismInsertionPair
  dsimp only
  rw [slotInsertEndoCc_sub]
  rw [rsDomDomCongrSection_sub, reindexCoeffGen_sub]
  module

private noncomputable def deTurckInsertionCorrectionEndomorphism
    (g gm g_bg : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  (deTurckVectorFieldCovariantDerivativeEndomorphismSection (I := I) (M := M) gm g_bg -
      deTurckVectorFieldCovariantDerivativeEndomorphismSection (I := I) (M := M) gm g) +
    endoDiffSection (I := I) (M := M) g gm g_bg

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma deTurckInsertionCorrectionEndomorphism_apply
    (g gm g_bg : SmoothRiemannianMetric I M) (x : M) :
    deTurckInsertionCorrectionEndomorphism (I := I) (M := M) g gm g_bg x =
      (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) gm g_bg x -
        deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) gm g x) +
      (lieCorrectionZeroNEndo (I := I) g gm g_bg x -
        lieCorrectionZeroNEndo (I := I) g gm g x) := by
  rw [deTurckInsertionCorrectionEndomorphism]
  change (_ - _) + endoDiffSection (I := I) (M := M) g gm g_bg x = _
  have hdiff : endoDiffSection (I := I) (M := M) g gm g_bg x =
      lieCorrectionZeroNEndo (I := I) g gm g_bg x -
        lieCorrectionZeroNEndo (I := I) g gm g x := by
    simpa only [endoDiffSection, connectionDifferenceDeTurckVectorFieldSection,
      ContMDiffSection.coe_sub, Pi.sub_apply] using
      (nEndo_diff (I := I) (M := M) g gm g_bg x).symm
  rw [hdiff]
  simp only [deTurckVectorFieldCovariantDerivativeEndomorphismSection_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem deTurckLieInsertionCorrection_eq_endomorphismInsertionPair
    (g gm g_bg : SmoothRiemannianMetric I M) :
    (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g_bg -
        deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g) +
      (lieCorrectionZeroInsertion (I := I) (M := M) g gm g_bg -
        lieCorrectionZeroInsertion (I := I) (M := M) g gm g) =
      endomorphismInsertionPair (I := I) (M := M) g
        (deTurckInsertionCorrectionEndomorphism (I := I) (M := M) g gm g_bg) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  let Λ := deTurckInsertionCorrectionEndomorphism (I := I) (M := M) g gm g_bg
  let X := slotInsertEndoCc (I := I) (M := M) g 1 Λ
  let Y := reindexCoeffGen (I := I) (M := M) g 2 2
    (rsDomDomCongrSection (I := I) (M := M) g 2 2
      (Equiv.swap (0 : Fin 2) 1) X)
    (Equiv.swap (0 : Fin 2) 1)
  have hsum :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (X + Y).toSection x) D =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        X.toSection x) D +
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        Y.toSection x) D := rfl
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g_bg -
            deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g) +
          (lieCorrectionZeroInsertion (I := I) (M := M) g gm g_bg -
            lieCorrectionZeroInsertion (I := I) (M := M) g gm g)).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (X + Y).toSection x) D) m
  rw [hsum, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]
  rw [show
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g_bg -
            deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g) +
          (lieCorrectionZeroInsertion (I := I) (M := M) g gm g_bg -
            lieCorrectionZeroInsertion (I := I) (M := M) g gm g)).toSection x) D =
        (deTurckLieCovariantDerivativeInsertionFib (I := I) gm g_bg x D -
          deTurckLieCovariantDerivativeInsertionFib (I := I) gm g x D) +
        (lieCorrectionZeroInsertionFib (I := I) g gm g_bg x D -
          lieCorrectionZeroInsertionFib (I := I) g gm g x D) from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
    Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [deTurckLieCovariantDerivativeInsertionFib_toModel (I := I) gm g_bg x D m,
    deTurckLieCovariantDerivativeInsertionFib_toModel (I := I) gm g x D m,
    lieCorrectionZeroInsertionFib_toModel (I := I) g gm g_bg x D m,
    lieCorrectionZeroInsertionFib_toModel (I := I) g gm g x D m]
  have hX :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        X.toSection x) D =
      slotInsertEndoFib (I := I) (M := M) 2 0 x (Λ x) D := rfl
  rw [hX, slotInsertEndoFib_apply_eval]
  have hY :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        Y.toSection x) D =
      reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (rsDomDomCongrSection (I := I) (M := M) g 2 2
            (Equiv.swap (0 : Fin 2) 1) X).toSection x) D := rfl
  rw [hY, reindexCoeffFibGen_apply]
  rw [show
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g 2 2
          (Equiv.swap (0 : Fin 2) 1) X).toSection x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        rsDomDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
          (X.toSection x)) from by
        rw [rsDomDomCongrSection_toSection]]
  rw [toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hX' :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        X.toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr
            (Equiv.swap (0 : Fin 2) 1) (Tensor0SSpace.toModel D))) =
      slotInsertEndoFib (I := I) (M := M) 2 0 x (Λ x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr
            (Equiv.swap (0 : Fin 2) 1) (Tensor0SSpace.toModel D))) := rfl
  rw [hX', slotInsertEndoFib_apply_eval,
    Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have harg :
      (fun k => Function.update
        (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
        (Λ x ((fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0))
        ((Equiv.swap (0 : Fin 2) 1) k)) =
      Function.update m 1 (Λ x (m 1)) := by
    funext k
    have hswap0 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 :=
      Equiv.swap_apply_left 0 1
    have hswap1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 :=
      Equiv.swap_apply_right 0 1
    simp only [Function.update_apply]
    rw [hswap0, Equiv.swap_apply_self]
    have hcond : ((Equiv.swap (0 : Fin 2) 1) k = 0) = (k = 1) := by
      apply propext
      constructor
      · intro h
        have h2 := congrArg (Equiv.swap (0 : Fin 2) 1) h
        rwa [Equiv.swap_apply_self, hswap0] at h2
      · intro h
        rw [h, hswap1]
    simp only [hcond]
  rw [harg]
  have hΛ := deTurckInsertionCorrectionEndomorphism_apply (I := I) (M := M) g gm g_bg x
  dsimp only [Λ] at hΛ ⊢
  rw [hΛ]
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,
    ContinuousMultilinearMap.map_update_add,
    ContinuousMultilinearMap.map_update_sub]
  simp only [sub_eq_add_neg, neg_add_rev]
  ac_rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem cometricRaiseSlot0Field_zero_sub
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

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem cometricRaiseSlot0Field_zero_add
    (g : SmoothRiemannianMetric I M)
    (W W' : SmoothCcTensor g 0 2) :
    cometricRaiseSlot0Field (I := I) (M := M) g 0 (W + W') =
      cometricRaiseSlot0Field (I := I) (M := M) g 0 W +
        cometricRaiseSlot0Field (I := I) (M := M) g 0 W' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  simp only [SmoothCcTensor.toSection_add,
    cometricRaiseSlot0Field_toSection]
  rfl

private theorem slotInsertEndoCc_zero_deTurckInsertionCorrectionEndomorphism
    (g gm g_bg : SmoothRiemannianMetric I M) :
    slotInsertEndoCc (I := I) (M := M) g 0
        (deTurckInsertionCorrectionEndomorphism (I := I) (M := M) g gm g_bg) =
      cometricRaiseSlot0Field (I := I) (M := M) g 0
        (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gm g_bg -
          deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gm g) := by
  rw [deTurckInsertionCorrectionEndomorphism, slotInsertEndoCc_add, slotInsertEndoCc_sub]
  change (deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g gm g_bg -
      deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g gm g) +
    slotInsertEndoCc (I := I) (M := M) g 0
      (endoDiffSection (I := I) (M := M) g gm g_bg) = _
  rw [endoDiffSection, slotInsertEndoCc_sub,
    deTurckVectorFieldCovariantDerivativeEndomorphismInsert_eq_cometricRaise_deTurckVectorFieldCovariantDerivativeLowered,
    deTurckVectorFieldCovariantDerivativeEndomorphismInsert_eq_cometricRaise_deTurckVectorFieldCovariantDerivativeLowered,
    connectionDifferenceDeTurckVectorFieldInsert_eq_cometricRaise,
    connectionDifferenceDeTurckVectorFieldInsert_eq_cometricRaise]
  rw [deTurckVectorFieldCovariantDerivativeLowered, deTurckVectorFieldCovariantDerivativeLowered, cometricRaiseSlot0Field_zero_add, cometricRaiseSlot0Field_zero_add, cometricRaiseSlot0Field_zero_sub]
  module

omit [NeZero (Module.finrank ℝ E)] in
private theorem deTurckVectorFieldCovector_backgroundDifference_sub
    (g g_bg gT gU : SmoothRiemannianMetric I M) :
    (deTurckVectorFieldCovector (I := I) (M := M) g gT g_bg -
        deTurckVectorFieldCovector (I := I) (M := M) g gT g) -
      (deTurckVectorFieldCovector (I := I) (M := M) g gU g_bg -
        deTurckVectorFieldCovector (I := I) (M := M) g gU g) =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 1
        (reindexedPureTrace (I := I) (M := M) g gT 1 (Equiv.refl _) -
          reindexedPureTrace (I := I) (M := M) g gU 1 (Equiv.refl _))
        (metricLoweredConnectionDifferenceCoefficient (I := I) g g -
          metricLoweredConnectionDifferenceCoefficient (I := I) g g_bg) := by
  rw [deTurckVectorFieldCovector_sub_eq_reindexedPureTrace_ccOperatorFieldComp (I := I) (M := M) g gT g_bg g,
    deTurckVectorFieldCovector_sub_eq_reindexedPureTrace_ccOperatorFieldComp (I := I) (M := M) g gU g_bg g]
  rw [operatorFieldComposition_sub_left]

private theorem exists_deTurckVectorFieldCovector_backgroundDifference_pairing_second_order_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 2
            ((deTurckVectorFieldCovector (I := I) (M := M) g gT g_bg -
                deTurckVectorFieldCovector (I := I) (M := M) g gT g) -
              (deTurckVectorFieldCovector (I := I) (M := M) g gU g_bg -
                deTurckVectorFieldCovector (I := I) (M := M) g gU g)) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 0 3 1
  obtain ⟨ρ, Ct, hρ, _hCt, htrace⟩ :=
    RicciDeTurckLowOrder.trace1_pair_h2 (I := I) (M := M) hDim g
  let P : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCoefficient (I := I) g g -
      metricLoweredConnectionDifferenceCoefficient (I := I) g g_bg
  let JP : ℝ := covariantJetNormSq (I := I) (M := M) g 2 P
  let K : ℝ := Ca * Ct ^ 2 * JP
  let C : ℝ := Real.sqrt K
  have hJP : 0 ≤ JP := by
    dsimp only [JP]
    exact covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g P
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (mul_nonneg hCa (sq_nonneg _)) hJP
  have hCsq : C ^ 2 = K := by
    simpa only [C] using Real.sq_sqrt hK
  refine ⟨ρ, C, hρ, Real.sqrt_nonneg _, ?_⟩
  intro T U gT gU hTtie hUtie hTHs hUHs
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let Φ : SmoothCcTensor g 3 1 :=
    reindexedPureTrace (I := I) (M := M) g gT 1 (Equiv.refl _) -
      reindexedPureTrace (I := I) (M := M) g gU 1 (Equiv.refl _)
  have hΦ : covariantJetNormSq (I := I) (M := M) g 2 Φ ≤
      (Ct * N) ^ 2 := by
    dsimp only [Φ, N]
    rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
    exact htrace T U gT gU hTtie hUtie hTHs hUHs
  have hprod : Ca * covariantJetNormSq (I := I) (M := M) g 2 Φ * JP ≤
      Ca * (Ct * N) ^ 2 * JP :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hΦ hCa) hJP
  rw [deTurckVectorFieldCovector_backgroundDifference_sub (I := I) (M := M) g g_bg gT gU]
  change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 0 3 1 Φ P) ≤
    (C * N) ^ 2
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 0 3 1 Φ P) ≤
      Ca * covariantJetNormSq (I := I) (M := M) g 2 Φ * JP := by
        simpa only [JP] using happ Φ P
    _ ≤ Ca * (Ct * N) ^ 2 * JP := hprod
    _ = (C * N) ^ 2 := by
      simp only [mul_pow, hCsq]
      dsimp only [K]
      ring

omit [NeZero (Module.finrank ℝ E)] in
private theorem deTurckVectorFieldCovariantDerivativeLoweredBase_backgroundDifference_eq
    (g g_bg gm : SmoothRiemannianMetric I M) :
    deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gm g_bg -
        deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gm g =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (covGrad (I := I) (M := M) g 0 1
          (deTurckVectorFieldCovector (I := I) (M := M) g gm g_bg -
            deTurckVectorFieldCovector (I := I) (M := M) g gm g)) := by
  unfold deTurckVectorFieldCovariantDerivativeLoweredBase
  rw [← domDomCongrSection_sub, ← covGrad_sub]

omit [NeZero (Module.finrank ℝ E)] in
private theorem deTurckVectorFieldCovariantDerivativeLoweredBase_backgroundDifference_sub
    (g g_bg gT gU : SmoothRiemannianMetric I M) :
    (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gT g_bg -
        deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gT g) -
      (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gU g_bg -
        deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gU g) =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (covGrad (I := I) (M := M) g 0 1
          ((deTurckVectorFieldCovector (I := I) (M := M) g gT g_bg -
              deTurckVectorFieldCovector (I := I) (M := M) g gT g) -
            (deTurckVectorFieldCovector (I := I) (M := M) g gU g_bg -
              deTurckVectorFieldCovector (I := I) (M := M) g gU g))) := by
  rw [deTurckVectorFieldCovariantDerivativeLoweredBase_backgroundDifference_eq (I := I) (M := M) g g_bg gT,
    deTurckVectorFieldCovariantDerivativeLoweredBase_backgroundDifference_eq (I := I) (M := M) g g_bg gU,
    ← domDomCongrSection_sub, ← covGrad_sub]

private theorem exists_deTurckVectorFieldCovariantDerivativeLoweredBase_backgroundDifference_pairing_first_order_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 1
            ((deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gT g_bg -
                deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gT g) -
              (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gU g_bg -
                deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gU g)) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hω⟩ :=
    exists_deTurckVectorFieldCovector_backgroundDifference_pairing_second_order_bound (I := I) (M := M) hDim g g_bg
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hTHs hUHs
  rw [deTurckVectorFieldCovariantDerivativeLoweredBase_backgroundDifference_sub (I := I) (M := M) g g_bg gT gU,
    covariantJetNormSq_one_domDomCongrSection]
  exact (covariantJetNormSq_one_covGrad_le_two (I := I) (M := M) g
    ((deTurckVectorFieldCovector (I := I) (M := M) g gT g_bg -
        deTurckVectorFieldCovector (I := I) (M := M) g gT g) -
      (deTurckVectorFieldCovector (I := I) (M := M) g gU g_bg -
        deTurckVectorFieldCovector (I := I) (M := M) g gU g))).trans
    (hω T U gT gU hTtie hUtie hTHs hUHs)

omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_one_cometricRaiseSlot0Field_eq
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    covariantJetNormSq (I := I) (M := M) g 1
        (cometricRaiseSlot0Field (I := I) (M := M) g 0 W) =
      covariantJetNormSq (I := I) (M := M) g 1 W := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq]

theorem exists_deTurckLieInsertionCorrection_pairing_firstOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 1
            (((deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gT g_bg -
                  deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gT g) +
                (lieCorrectionZeroInsertion (I := I) (M := M) g gT g_bg -
                  lieCorrectionZeroInsertion (I := I) (M := M) g gT g)) -
              ((deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gU g_bg -
                  deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gU g) +
                (lieCorrectionZeroInsertion (I := I) (M := M) g gU g_bg -
                  lieCorrectionZeroInsertion (I := I) (M := M) g gU g))) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, Ca, hρ, _hCa, hα⟩ :=
    exists_deTurckVectorFieldCovariantDerivativeLoweredBase_backgroundDifference_pairing_first_order_bound (I := I) (M := M) hDim g g_bg
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := 4 * fr * Ca ^ 2
  let C : ℝ := Real.sqrt K
  have hfr : 0 ≤ fr := by positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (mul_nonneg (by norm_num) hfr) (sq_nonneg _)
  have hCsq : C ^ 2 = K := by
    simpa only [C] using Real.sq_sqrt hK
  refine ⟨ρ, C, hρ, Real.sqrt_nonneg _, ?_⟩
  intro T U gT gU hTtie hUtie hTHs hUHs
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let ΛT := deTurckInsertionCorrectionEndomorphism (I := I) (M := M) g gT g_bg
  let ΛU := deTurckInsertionCorrectionEndomorphism (I := I) (M := M) g gU g_bg
  let AT : SmoothCcTensor g 0 2 :=
    deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gT g_bg -
      deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gT g
  let AU : SmoothCcTensor g 0 2 :=
    deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gU g_bg -
      deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gU g
  let FT : SmoothCcTensor g 2 2 :=
    (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gT g_bg -
        deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gT g) +
      (lieCorrectionZeroInsertion (I := I) (M := M) g gT g_bg -
        lieCorrectionZeroInsertion (I := I) (M := M) g gT g)
  let FU : SmoothCcTensor g 2 2 :=
    (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gU g_bg -
        deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gU g) +
      (lieCorrectionZeroInsertion (I := I) (M := M) g gU g_bg -
        lieCorrectionZeroInsertion (I := I) (M := M) g gU g)
  have hFT : FT = endomorphismInsertionPair (I := I) (M := M) g ΛT := by
    simpa only [FT, ΛT] using
      deTurckLieInsertionCorrection_eq_endomorphismInsertionPair (I := I) (M := M) g gT g_bg
  have hFU : FU = endomorphismInsertionPair (I := I) (M := M) g ΛU := by
    simpa only [FU, ΛU] using
      deTurckLieInsertionCorrection_eq_endomorphismInsertionPair (I := I) (M := M) g gU g_bg
  have hFsub : FT - FU =
      endomorphismInsertionPair (I := I) (M := M) g (ΛT - ΛU) := by
    rw [hFT, hFU, endomorphismInsertionPair_sub]
  have hslot :
      slotInsertEndoCc (I := I) (M := M) g 0 (ΛT - ΛU) =
        cometricRaiseSlot0Field (I := I) (M := M) g 0 (AT - AU) := by
    dsimp only [ΛT, ΛU, AT, AU]
    rw [slotInsertEndoCc_sub,
      slotInsertEndoCc_zero_deTurckInsertionCorrectionEndomorphism (I := I) (M := M) g gT g_bg,
      slotInsertEndoCc_zero_deTurckInsertionCorrectionEndomorphism (I := I) (M := M) g gU g_bg,
      ← cometricRaiseSlot0Field_zero_sub]
  have hslotJet : covariantJetNormSq (I := I) (M := M) g 1
      (slotInsertEndoCc (I := I) (M := M) g 0 (ΛT - ΛU)) =
        covariantJetNormSq (I := I) (M := M) g 1 (AT - AU) := by
    rw [hslot, covariantJetNormSq_one_cometricRaiseSlot0Field_eq]
  have hA : covariantJetNormSq (I := I) (M := M) g 1 (AT - AU) ≤
      (Ca * N) ^ 2 := by
    simpa only [AT, AU, N] using
      hα T U gT gU hTtie hUtie hTHs hUHs
  change covariantJetNormSq (I := I) (M := M) g 1 (FT - FU) ≤
    (C * N) ^ 2
  rw [hFsub]
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (endomorphismInsertionPair (I := I) (M := M) g (ΛT - ΛU)) ≤
      4 * fr * covariantJetNormSq (I := I) (M := M) g 1
        (slotInsertEndoCc (I := I) (M := M) g 0 (ΛT - ΛU)) := by
        simpa only [fr] using
          covariantJetNormSq_one_endomorphismInsertionPair_le (I := I) (M := M) g (ΛT - ΛU)
    _ = 4 * fr * covariantJetNormSq (I := I) (M := M) g 1 (AT - AU) := by
      rw [hslotJet]
    _ ≤ 4 * fr * (Ca * N) ^ 2 :=
      mul_le_mul_of_nonneg_left hA (mul_nonneg (by norm_num) hfr)
    _ = (C * N) ^ 2 := by
      simp only [mul_pow, hCsq]
      dsimp only [K]
      ring

private theorem exists_operatorFieldComposition_covariantJetNormSq_one_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r)
        (A B : ℝ), 0 ≤ A → 0 ≤ B →
        covariantJetNormSq (I := I) (M := M) g 2 Φ ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 1 W ≤ B ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 1
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
          (C * A * B) ^ 2 := by
  obtain ⟨K, hK, happ⟩ := exists_operatorFieldComposition_covariantJetNormSq_one_le_two_one (I := I) (M := M) hDim g p r c
  let C : ℝ := Real.sqrt K
  have hCsq : C ^ 2 = K := by
    simpa only [C] using Real.sq_sqrt hK
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro Φ W A B _hA _hB hΦ hW
  have hW0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1 W :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 1) g W
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
      K * covariantJetNormSq (I := I) (M := M) g 2 Φ *
        covariantJetNormSq (I := I) (M := M) g 1 W := happ Φ W
    _ ≤ K * A ^ 2 * covariantJetNormSq (I := I) (M := M) g 1 W :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hΦ hK) hW0
    _ ≤ K * A ^ 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_left hW (mul_nonneg hK (sq_nonneg _))
    _ = (C * A * B) ^ 2 := by
      simp only [mul_pow, hCsq]

private theorem exists_operatorFieldComposition_difference_covariantJetNormSq_one_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ΦT ΦU : SmoothCcTensor g r c)
        (WT WU : SmoothCcTensor g p r)
        (A DA B DB : ℝ),
        0 ≤ A → 0 ≤ DA → 0 ≤ B → 0 ≤ DB →
        covariantJetNormSq (I := I) (M := M) g 2 ΦU ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (ΦT - ΦU) ≤ DA ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 1 WT ≤ B ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 1 (WT - WU) ≤ DB ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 1
            (ccOperatorFieldComp (I := I) (M := M) g p r c ΦT WT -
              ccOperatorFieldComp (I := I) (M := M) g p r c ΦU WU) ≤
          (C * (A * DB + DA * B)) ^ 2 := by
  obtain ⟨K, hK, happ⟩ := exists_operatorFieldComposition_covariantJetNormSq_one_le_two_one (I := I) (M := M) hDim g p r c
  let Q : ℝ := 2 * K
  let C : ℝ := Real.sqrt Q
  have hQ : 0 ≤ Q := mul_nonneg (by norm_num) hK
  have hCsq : C ^ 2 = Q := by
    simpa only [C] using Real.sq_sqrt hQ
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro ΦT ΦU WT WU A DA B DB hA hDA hB hDB
    hΦU hΦD hWT hWD
  have hform :
      ccOperatorFieldComp (I := I) (M := M) g p r c ΦT WT -
          ccOperatorFieldComp (I := I) (M := M) g p r c ΦU WU =
        ccOperatorFieldComp (I := I) (M := M) g p r c ΦU (WT - WU) +
          ccOperatorFieldComp (I := I) (M := M) g p r c (ΦT - ΦU) WT := by
    rw [ccOperatorFieldComp_sub_right, operatorFieldComposition_sub_left]
    module
  have hWD0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1 (WT - WU) :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 1) g (WT - WU)
  have hWT0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1 WT :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 1) g WT
  have h0 : K * covariantJetNormSq (I := I) (M := M) g 2 ΦU *
        covariantJetNormSq (I := I) (M := M) g 1 (WT - WU) ≤
      K * A ^ 2 * DB ^ 2 := by
    calc
      _ ≤ K * A ^ 2 * covariantJetNormSq (I := I) (M := M) g 1 (WT - WU) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hΦU hK) hWD0
      _ ≤ K * A ^ 2 * DB ^ 2 :=
        mul_le_mul_of_nonneg_left hWD (mul_nonneg hK (sq_nonneg _))
  have h1 : K * covariantJetNormSq (I := I) (M := M) g 2 (ΦT - ΦU) *
        covariantJetNormSq (I := I) (M := M) g 1 WT ≤
      K * DA ^ 2 * B ^ 2 := by
    calc
      _ ≤ K * DA ^ 2 * covariantJetNormSq (I := I) (M := M) g 1 WT :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hΦD hK) hWT0
      _ ≤ K * DA ^ 2 * B ^ 2 :=
        mul_le_mul_of_nonneg_left hWT (mul_nonneg hK (sq_nonneg _))
  have hcross : 0 ≤ 2 * (A * DB) * (DA * B) := by positivity
  rw [hform]
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g p r c ΦU (WT - WU) +
          ccOperatorFieldComp (I := I) (M := M) g p r c (ΦT - ΦU) WT) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g p r c ΦU (WT - WU)) +
        covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g p r c (ΦT - ΦU) WT)) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 1 _ _
    _ ≤ 2 * (K * A ^ 2 * DB ^ 2 + K * DA ^ 2 * B ^ 2) := by
      have hs := add_le_add
        ((happ ΦU (WT - WU)).trans h0)
        ((happ (ΦT - ΦU) WT).trans h1)
      exact mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ 2 * K * (A * DB + DA * B) ^ 2 := by
      nlinarith
    _ = (C * (A * DB + DA * B)) ^ 2 := by
      simp only [mul_pow, hCsq]
      dsimp only [Q]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem symmSCovGrad3_sub
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2) :
    symmSCovGrad3 (I := I) (M := M) g (T - U) =
      symmSCovGrad3 (I := I) (M := M) g T -
        symmSCovGrad3 (I := I) (M := M) g U := by
  rw [symmSCovGrad3_def, symmSCovGrad3_def, symmSCovGrad3_def,
    symmS_sub, covGrad_sub]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem koszulCovecCc_sub
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2) :
    koszulCovecCc (I := I) g (T - U) =
      koszulCovecCc (I := I) g T - koszulCovecCc (I := I) g U := by
  unfold koszulCovecCc
  rw [symmSCovGrad3_sub]
  rw [domDomCongrSection_sub, domDomCongrSection_sub, domDomCongrSection_sub]
  module

omit [NeZero (Module.finrank ℝ E)] in
private theorem lieCorrectionZeroKappa_self_sub
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
    (hUtie : ∀ (x : M) (u v : TangentSpace I x),
      gU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    lieCorrectionZeroKappa (I := I) (M := M) g gT g -
        lieCorrectionZeroKappa (I := I) (M := M) g gU g =
      domDomCongrSection (I := I) g (finRotate 3).symm
        (koszulCovecCc (I := I) g (T - U)) := by
  rw [kappa_self (I := I) (M := M) g gT T hTtie,
    kappa_self (I := I) (M := M) g gU U hUtie,
    ← domDomCongrSection_sub, ← koszulCovecCc_sub]

omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_one_lieCorrectionZeroKappa_self_le
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) :
    covariantJetNormSq (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (finRotate 3).symm
          (koszulCovecCc (I := I) g P)) ≤
      10 * covariantJetNormSq (I := I) (M := M) g 2 P := by
  have hterm : ∀ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g 0 3 i
        (domDomCongrSection (I := I) g (finRotate 3).symm
          (koszulCovecCc (I := I) g P))‖ ^ 2 ≤
        10 * ‖iteratedCovGrad (I := I) g 0 2 (i + 1) P‖ ^ 2 := by
    intro i _hi
    have hperm :
        ‖iteratedCovGrad (I := I) g 0 3 i
          (domDomCongrSection (I := I) g (finRotate 3).symm
            (koszulCovecCc (I := I) g P))‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g 0 3 i
            (koszulCovecCc (I := I) g P)‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun x =>
          riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
            (I := I) (M := M) g (finRotate 3).symm
            (koszulCovecCc (I := I) g P) i x)
    rw [hperm]
    exact koszul_l2_succ (I := I) (M := M) g P i
  have hsum := Finset.sum_le_sum hterm
  unfold covariantJetNormSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at hsum ⊢
  nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g 0 2 0 P‖,
    sq_nonneg ‖iteratedCovGrad (I := I) g 0 2 1 P‖,
    sq_nonneg ‖iteratedCovGrad (I := I) g 0 2 2 P‖]

omit [NeZero (Module.finrank ℝ E)] in
private theorem lieCorrectionZeroKappa_self_difference_covariantJetNormSq_one_le
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
    (hUtie : ∀ (x : M) (u v : TangentSpace I x),
      gU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    covariantJetNormSq (I := I) (M := M) g 1
        (lieCorrectionZeroKappa (I := I) (M := M) g gT g -
          lieCorrectionZeroKappa (I := I) (M := M) g gU g) ≤
      10 * covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
  rw [lieCorrectionZeroKappa_self_sub (I := I) (M := M) g gT gU T U hTtie hUtie]
  exact covariantJetNormSq_one_lieCorrectionZeroKappa_self_le (I := I) (M := M) g (T - U)

omit [NeZero (Module.finrank ℝ E)] in
private theorem lieCorrectionZeroKappa_self_covariantJetNormSq_one_le
    (g gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    covariantJetNormSq (I := I) (M := M) g 1
        (lieCorrectionZeroKappa (I := I) (M := M) g gm g) ≤
      10 * covariantJetNormSq (I := I) (M := M) g 2 P := by
  rw [kappa_self (I := I) (M := M) g gm P htie]
  exact covariantJetNormSq_one_lieCorrectionZeroKappa_self_le (I := I) (M := M) g P

private theorem exists_lieCorrectionZeroPbLow_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P : SmoothCcTensor g 0 2) (A : ℝ), 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2
            (lieCorrectionZeroPbLow (I := I) (M := M) g P g g_bg) ≤
          (C * A) ^ 2 := by
  obtain ⟨K, hK, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 1 1 2
  let F : SmoothCcTensor g 1 2 :=
    lieArm1FixCd (I := I) (M := M) g g_bg
  let JF : ℝ := covariantJetNormSq (I := I) (M := M) g 2 F
  let Q : ℝ := K * JF
  let C : ℝ := Real.sqrt Q
  have hJF : 0 ≤ JF := by
    dsimp only [JF]
    exact covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g F
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    exact mul_nonneg hK hJF
  have hCsq : C ^ 2 = Q := by
    simpa only [C] using Real.sq_sqrt hQ
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro P A hA hP
  let W : SmoothCcTensor g 1 1 :=
    cometricRaiseSlot0Field (I := I) (M := M) g 0
      (symmS (I := I) (M := M) g P)
  have hWterm : ∀ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 1 1 j W‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2 := by
    intro j _hj
    have hraise :
        ‖iteratedCovGrad (I := I) g 1 1 j W‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g 0 2 j
            (symmS (I := I) (M := M) g P)‖ ^ 2 := by
      simpa only [W] using congrArg (fun z : ℝ => z ^ 2)
        (norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
          (I := I) (M := M) g 0
          (symmS (I := I) (M := M) g P) j)
    rw [hraise]
    have hs := norm_iteratedCovGrad_symmS_le
      (I := I) (M := M) g P j
    nlinarith [norm_nonneg (iteratedCovGrad (I := I) g 0 2 j
      (symmS (I := I) (M := M) g P)),
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 j P)]
  have hW : covariantJetNormSq (I := I) (M := M) g 2 W ≤ A ^ 2 := by
    unfold covariantJetNormSq
    exact (Finset.sum_le_sum hWterm).trans hP
  have heq : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroPbLow (I := I) (M := M) g P g g_bg) =
        covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 1 1 2 F W) := by
    unfold covariantJetNormSq
    apply Finset.sum_congr rfl
    intro i _hi
    rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => by
        simpa only [F, W] using
          pbLow_riemannianFiberNormSq (I := I) (M := M) g g_bg P i x)
  rw [heq]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 1 1 2 F W) ≤
      K * JF * covariantJetNormSq (I := I) (M := M) g 2 W := by
        simpa only [JF, F] using happ F W
    _ ≤ K * JF * A ^ 2 :=
      mul_le_mul_of_nonneg_left hW (mul_nonneg hK hJF)
    _ = (C * A) ^ 2 := by
      simp only [mul_pow, hCsq]
      dsimp only [Q]

private noncomputable def lieCorrectionZeroKappaBackgroundDifference
    (g gm g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 3 :=
  lieCorrectionZeroKappa (I := I) (M := M) g gm g_bg -
    lieCorrectionZeroKappa (I := I) (M := M) g gm g

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem lieCorrectionZeroKappaBackgroundDifference_sub
    (g gT gU g_bg : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
    (hUtie : ∀ (x : M) (u v : TangentSpace I x),
      gU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    lieCorrectionZeroKappaBackgroundDifference (I := I) (M := M) g gT g_bg -
        lieCorrectionZeroKappaBackgroundDifference (I := I) (M := M) g gU g_bg =
      lieCorrectionZeroPbLow (I := I) (M := M) g (T - U) g g_bg := by
  unfold lieCorrectionZeroKappaBackgroundDifference
  rw [kappa_bg (I := I) (M := M) g gT g_bg T hTtie,
    kappa_bg (I := I) (M := M) g gU g_bg U hUtie,
    pbLow_sub (I := I) (M := M) g T U g g_bg]
  module

private noncomputable def lieCorrectionZeroMixedConnectionBackgroundHalf
    (g gm g_bg : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g 2 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 2
    (reindexedPureTrace (I := I) (M := M) g gm 2 σ)
    (ccOperatorFieldComp (I := I) (M := M) g 2 6 4
      (reindexedPureTrace (I := I) (M := M) g gm 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 6
        (slotExtendIter (I := I) (M := M) g 0 3 3
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g_bg -
            metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g))
        (ccOperatorFieldComp (I := I) (M := M) g 2 5 3
          (reindexedPureTrace (I := I) (M := M) g gm 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
          (slotExtendIter (I := I) (M := M) g 0 3 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g)))))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem slotExtendIter_sub
    (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (A B : SmoothCcTensor g r s) :
    slotExtendIter (I := I) (M := M) g r s w (A - B) =
      slotExtendIter (I := I) (M := M) g r s w A -
        slotExtendIter (I := I) (M := M) g r s w B := by
  induction w with
  | zero => simp only [slotExtendIter]
  | succ w ih =>
      change slotExtend (I := I) (M := M) g (r + w) (s + w)
          (slotExtendIter (I := I) (M := M) g r s w (A - B)) = _
      rw [ih, slotExtend_sub]
      rfl

omit [NeZero (Module.finrank ℝ E)] in
private theorem lieCorrectionZeroMixedConnectionHalfRF_backgroundDifference
    (g gm g_bg : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) :
    lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gm g_bg σ -
        lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gm g σ =
      lieCorrectionZeroMixedConnectionBackgroundHalf (I := I) (M := M) g gm g_bg σ := by
  unfold lieCorrectionZeroMixedConnectionHalfExpansion lieCorrectionZeroMixedConnectionBackgroundHalf
  rw [← ccOperatorFieldComp_sub_right, ← ccOperatorFieldComp_sub_right,
    ← operatorFieldComposition_sub_left, ← slotExtendIter_sub]

private theorem exists_lieCorrectionZeroKappaBackgroundDifference_covariantJetNormSq_two_bounds
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      (∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ 1 →
        covariantJetNormSq (I := I) (M := M) g 2
            (lieCorrectionZeroKappaBackgroundDifference (I := I) (M := M) g gT g_bg) ≤ B ^ 2) ∧
      (∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) →
        (∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) →
        covariantJetNormSq (I := I) (M := M) g 2
            (lieCorrectionZeroKappaBackgroundDifference (I := I) (M := M) g gT g_bg -
              lieCorrectionZeroKappaBackgroundDifference (I := I) (M := M) g gU g_bg) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2) := by
  obtain ⟨Kp, hKp, hpb⟩ :=
    exists_lieCorrectionZeroPbLow_covariantJetNormSq_two_bound (I := I) (M := M) hDim g g_bg
  obtain ⟨Ch, hCh, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  let F : SmoothCcTensor g 0 3 :=
    lieCorrectionZeroKappa (I := I) (M := M) g g g_bg
  let F0 : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 F)
  let P0 : ℝ := Kp * Ch
  let B : ℝ := 2 * (F0 + P0)
  let C : ℝ := Kp * Ch
  have hF0 : 0 ≤ F0 := Real.sqrt_nonneg _
  have hF0sq : F0 ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 F := by
    simpa only [F0] using Real.sq_sqrt
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g F)
  have hP0 : 0 ≤ P0 := mul_nonneg hKp hCh
  have hB : 0 ≤ B :=
    mul_nonneg (by norm_num) (add_nonneg hF0 hP0)
  have hC : 0 ≤ C := mul_nonneg hKp hCh
  refine ⟨B, C, hB, hC, ?_, ?_⟩
  · intro T gT hTtie hTHs
    let PbT : SmoothCcTensor g 0 3 :=
      lieCorrectionZeroPbLow (I := I) (M := M) g T g g_bg
    have hT2 : covariantJetNormSq (I := I) (M := M) g 2 T ≤ Ch ^ 2 := by
      calc
        covariantJetNormSq (I := I) (M := M) g 2 T ≤
            (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
              (2 : ℝ) T‖) ^ 2 := by
          simpa only [covariantJetNormSq, Nat.reduceAdd] using hhs T
        _ ≤ (Ch * 1) ^ 2 :=
          pow_le_pow_left₀
            (mul_nonneg hCh (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hTHs hCh) 2
        _ = Ch ^ 2 := by rw [mul_one]
    have hPbT : covariantJetNormSq (I := I) (M := M) g 2 PbT ≤ P0 ^ 2 := by
      simpa only [PbT, P0] using hpb T Ch hCh hT2
    have hkT : lieCorrectionZeroKappaBackgroundDifference (I := I) (M := M) g gT g_bg = F + PbT := by
      unfold lieCorrectionZeroKappaBackgroundDifference
      rw [kappa_bg (I := I) (M := M) g gT g_bg T hTtie]
      dsimp only [F, PbT]
      module
    rw [hkT]
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (F + PbT) ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 F +
            covariantJetNormSq (I := I) (M := M) g 2 PbT) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 2 F PbT
      _ ≤ 2 * (F0 ^ 2 + P0 ^ 2) := by
        rw [hF0sq]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hPbT) (by norm_num)
      _ ≤ B ^ 2 := by
        dsimp only [B]
        nlinarith [mul_nonneg hF0 hP0]
  · intro T U gT gU hTtie hUtie
    let N : ℝ :=
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
    have hN : 0 ≤ N := norm_nonneg _
    have hTU2 : covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤
        (Ch * N) ^ 2 := by
      simpa only [covariantJetNormSq, Nat.reduceAdd, N] using hhs (T - U)
    rw [lieCorrectionZeroKappaBackgroundDifference_sub (I := I) (M := M) g gT gU g_bg T U hTtie hUtie]
    have hp := hpb (T - U) (Ch * N) (mul_nonneg hCh hN) hTU2
    simpa only [C, N, mul_assoc] using hp

private theorem exists_lieCorrectionZeroKappa_self_covariantJetNormSq_bounds
    (g : SmoothRiemannianMetric I M) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      (∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ 1 →
        covariantJetNormSq (I := I) (M := M) g 1
            (lieCorrectionZeroKappa (I := I) (M := M) g gT g) ≤ B ^ 2) ∧
      (∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) →
        (∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) →
        covariantJetNormSq (I := I) (M := M) g 1
            (lieCorrectionZeroKappa (I := I) (M := M) g gT g -
              lieCorrectionZeroKappa (I := I) (M := M) g gU g) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2) := by
  obtain ⟨Ch, hCh, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  let B : ℝ := 4 * Ch
  let C : ℝ := 4 * Ch
  have hB : 0 ≤ B := mul_nonneg (by norm_num) hCh
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hCh
  refine ⟨B, C, hB, hC, ?_, ?_⟩
  · intro T gT hTtie hTHs
    have hT2 : covariantJetNormSq (I := I) (M := M) g 2 T ≤ Ch ^ 2 := by
      calc
        covariantJetNormSq (I := I) (M := M) g 2 T ≤
            (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
              (2 : ℝ) T‖) ^ 2 := by
          simpa only [covariantJetNormSq, Nat.reduceAdd] using hhs T
        _ ≤ (Ch * 1) ^ 2 :=
          pow_le_pow_left₀
            (mul_nonneg hCh (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hTHs hCh) 2
        _ = Ch ^ 2 := by rw [mul_one]
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (lieCorrectionZeroKappa (I := I) (M := M) g gT g) ≤
        10 * covariantJetNormSq (I := I) (M := M) g 2 T :=
          lieCorrectionZeroKappa_self_covariantJetNormSq_one_le (I := I) (M := M) g gT T hTtie
      _ ≤ 10 * Ch ^ 2 := mul_le_mul_of_nonneg_left hT2 (by norm_num)
      _ ≤ B ^ 2 := by
        dsimp only [B]
        nlinarith [sq_nonneg Ch]
  · intro T U gT gU hTtie hUtie
    let N : ℝ :=
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
    have hTU2 : covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤
        (Ch * N) ^ 2 := by
      simpa only [covariantJetNormSq, Nat.reduceAdd, N] using hhs (T - U)
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (lieCorrectionZeroKappa (I := I) (M := M) g gT g -
            lieCorrectionZeroKappa (I := I) (M := M) g gU g) ≤
        10 * covariantJetNormSq (I := I) (M := M) g 2 (T - U) :=
          lieCorrectionZeroKappa_self_difference_covariantJetNormSq_one_le (I := I) (M := M) g gT gU T U hTtie hUtie
      _ ≤ 10 * (Ch * N) ^ 2 :=
        mul_le_mul_of_nonneg_left hTU2 (by norm_num)
      _ ≤ (C * N) ^ 2 := by
        dsimp only [C]
        nlinarith [sq_nonneg (Ch * N)]

private theorem exists_lieCorrectionZeroMixedConnectionBackgroundHalf_pairing_first_order_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (σ : Equiv.Perm (Fin 4))
        (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) →
        (∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 1
            (lieCorrectionZeroMixedConnectionBackgroundHalf (I := I) (M := M) g gT g_bg σ -
              lieCorrectionZeroMixedConnectionBackgroundHalf (I := I) (M := M) g gU g_bg σ) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ2p, Ct2, hρ2p, hCt2, hp2⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ2b, Bt2, hρ2b, hBt2, hb2⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρ3p, Ct3, hρ3p, hCt3, hp3⟩ :=
    RicciDeTurckLowOrder.trace3_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ3b, Bt3, hρ3b, hBt3, hb3⟩ :=
    RicciDeTurckLowOrder.trace_three_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρ4p, Ct4, hρ4p, hCt4, hp4⟩ :=
    RicciDeTurckLowOrder.trace4_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ4b, Bt4, hρ4b, hBt4, hb4⟩ :=
    RicciDeTurckLowOrder.trace_four_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Bk, Ck, hBk, hCk, hkOne, hkPair⟩ :=
    exists_lieCorrectionZeroKappaBackgroundDifference_covariantJetNormSq_two_bounds (I := I) (M := M) hDim g g_bg
  obtain ⟨B0, C0, hB0, hC0, h0One, h0Pair⟩ :=
    exists_lieCorrectionZeroKappa_self_covariantJetNormSq_bounds (I := I) (M := M) g
  obtain ⟨O2, hO2, hone2⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_one_bound (I := I) (M := M) hDim g 2 4 2
  obtain ⟨P2, hP2, hpair2⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_one_bound (I := I) (M := M) hDim g 2 4 2
  obtain ⟨O4, hO4, hone4⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_one_bound (I := I) (M := M) hDim g 2 6 4
  obtain ⟨P4, hP4, hpair4⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_one_bound (I := I) (M := M) hDim g 2 6 4
  obtain ⟨Ok, hOk, honek⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_one_bound (I := I) (M := M) hDim g 2 3 6
  obtain ⟨Pk, hPk, hpairk⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_one_bound (I := I) (M := M) hDim g 2 3 6
  obtain ⟨O3, hO3, hone3⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_one_bound (I := I) (M := M) hDim g 2 5 3
  obtain ⟨P3, hP3, hpair3⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_one_bound (I := I) (M := M) hDim g 2 5 3
  let sf2 : ℝ := Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2)
  let sf3 : ℝ := Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3)
  let A5 : ℝ := sf2 * B0
  let D5 : ℝ := sf2 * C0
  let A4 : ℝ := O3 * Bt3 * A5
  let D4 : ℝ := P3 * (Bt3 * D5 + Ct3 * A5)
  let Ak : ℝ := sf3 * Bk
  let Dk : ℝ := sf3 * Ck
  let A3 : ℝ := Ok * Ak * A4
  let D3 : ℝ := Pk * (Ak * D4 + Dk * A4)
  let A2 : ℝ := O4 * Bt4 * A3
  let D2 : ℝ := P4 * (Bt4 * D3 + Ct4 * A3)
  let A1 : ℝ := O2 * Bt2 * A2
  let D1 : ℝ := P2 * (Bt2 * D2 + Ct2 * A2)
  let ρ : ℝ := min 1
    (min ρ2p (min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b)))))
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact lt_min (by norm_num)
      (lt_min hρ2p (lt_min hρ2b
        (lt_min hρ3p (lt_min hρ3b (lt_min hρ4p hρ4b)))))
  have hsf2 : 0 ≤ sf2 := Real.sqrt_nonneg _
  have hsf3 : 0 ≤ sf3 := Real.sqrt_nonneg _
  have hA5 : 0 ≤ A5 := mul_nonneg hsf2 hB0
  have hD5 : 0 ≤ D5 := mul_nonneg hsf2 hC0
  have hA4 : 0 ≤ A4 := mul_nonneg (mul_nonneg hO3 hBt3) hA5
  have hD4 : 0 ≤ D4 := pairing_product_coefficient_nonneg hP3 hBt3 hD5 hCt3 hA5
  have hAk : 0 ≤ Ak := mul_nonneg hsf3 hBk
  have hDk : 0 ≤ Dk := mul_nonneg hsf3 hCk
  have hA3 : 0 ≤ A3 := mul_nonneg (mul_nonneg hOk hAk) hA4
  have hD3 : 0 ≤ D3 := pairing_product_coefficient_nonneg hPk hAk hD4 hDk hA4
  have hA2 : 0 ≤ A2 := mul_nonneg (mul_nonneg hO4 hBt4) hA3
  have hD2 : 0 ≤ D2 := pairing_product_coefficient_nonneg hP4 hBt4 hD3 hCt4 hA3
  have hA1 : 0 ≤ A1 := mul_nonneg (mul_nonneg hO2 hBt2) hA2
  have hD1 : 0 ≤ D1 := pairing_product_coefficient_nonneg hP2 hBt2 hD2 hCt2 hA2
  refine ⟨ρ, D1, hρ, hD1, ?_⟩
  intro σ T U gT gU hTtie hUtie hTHs hUHs
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hρ1 : ρ ≤ 1 := by
    dsimp only [ρ]
    exact min_le_left _ _
  have hρ2p' : ρ ≤ ρ2p := by
    dsimp only [ρ]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hρ2b' : ρ ≤ ρ2b := by
    dsimp only [ρ]
    calc
      _ ≤ min ρ2p (min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b)))) :=
        min_le_right _ _
      _ ≤ min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b))) := min_le_right _ _
      _ ≤ ρ2b := min_le_left _ _
  have hρ3p' : ρ ≤ ρ3p := by
    dsimp only [ρ]
    calc
      _ ≤ min ρ2p (min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b)))) :=
        min_le_right _ _
      _ ≤ min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b))) := min_le_right _ _
      _ ≤ min ρ3p (min ρ3b (min ρ4p ρ4b)) := min_le_right _ _
      _ ≤ ρ3p := min_le_left _ _
  have hρ3b' : ρ ≤ ρ3b := by
    dsimp only [ρ]
    calc
      _ ≤ min ρ2p (min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b)))) :=
        min_le_right _ _
      _ ≤ min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b))) := min_le_right _ _
      _ ≤ min ρ3p (min ρ3b (min ρ4p ρ4b)) := min_le_right _ _
      _ ≤ min ρ3b (min ρ4p ρ4b) := min_le_right _ _
      _ ≤ ρ3b := min_le_left _ _
  have hρ4p' : ρ ≤ ρ4p := by
    dsimp only [ρ]
    calc
      _ ≤ min ρ2p (min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b)))) :=
        min_le_right _ _
      _ ≤ min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b))) := min_le_right _ _
      _ ≤ min ρ3p (min ρ3b (min ρ4p ρ4b)) := min_le_right _ _
      _ ≤ min ρ3b (min ρ4p ρ4b) := min_le_right _ _
      _ ≤ min ρ4p ρ4b := min_le_right _ _
      _ ≤ ρ4p := min_le_left _ _
  have hρ4b' : ρ ≤ ρ4b := by
    dsimp only [ρ]
    calc
      _ ≤ min ρ2p (min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b)))) :=
        min_le_right _ _
      _ ≤ min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b))) := min_le_right _ _
      _ ≤ min ρ3p (min ρ3b (min ρ4p ρ4b)) := min_le_right _ _
      _ ≤ min ρ3b (min ρ4p ρ4b) := min_le_right _ _
      _ ≤ min ρ4p ρ4b := min_le_right _ _
      _ ≤ ρ4b := min_le_right _ _
  have hTHs1 : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ 1 := hTHs.trans hρ1
  have hUHs1 : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ 1 := hUHs.trans hρ1
  have hTHs2p : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρ2p := hTHs.trans hρ2p'
  have hUHs2p : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρ2p := hUHs.trans hρ2p'
  have hTHs2b : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρ2b := hTHs.trans hρ2b'
  have hUHs2b : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρ2b := hUHs.trans hρ2b'
  have hTHs3p : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρ3p := hTHs.trans hρ3p'
  have hUHs3p : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρ3p := hUHs.trans hρ3p'
  have hTHs3b : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρ3b := hTHs.trans hρ3b'
  have hUHs3b : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρ3b := hUHs.trans hρ3b'
  have hTHs4p : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρ4p := hTHs.trans hρ4p'
  have hUHs4p : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρ4p := hUHs.trans hρ4p'
  have hTHs4b : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρ4b := hTHs.trans hρ4b'
  have hUHs4b : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρ4b := hUHs.trans hρ4b'
  let Tr2T : SmoothCcTensor g 4 2 :=
    reindexedPureTrace (I := I) (M := M) g gT 2 σ
  let Tr2U : SmoothCcTensor g 4 2 :=
    reindexedPureTrace (I := I) (M := M) g gU 2 σ
  let Tr3T : SmoothCcTensor g 5 3 :=
    reindexedPureTrace (I := I) (M := M) g gT 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour
  let Tr3U : SmoothCcTensor g 5 3 :=
    reindexedPureTrace (I := I) (M := M) g gU 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour
  let Tr4T : SmoothCcTensor g 6 4 :=
    reindexedPureTrace (I := I) (M := M) g gT 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne
  let Tr4U : SmoothCcTensor g 6 4 :=
    reindexedPureTrace (I := I) (M := M) g gU 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne
  let K0T : SmoothCcTensor g 0 3 :=
    lieCorrectionZeroKappa (I := I) (M := M) g gT g
  let K0U : SmoothCcTensor g 0 3 :=
    lieCorrectionZeroKappa (I := I) (M := M) g gU g
  let KbT : SmoothCcTensor g 0 3 :=
    lieCorrectionZeroKappaBackgroundDifference (I := I) (M := M) g gT g_bg
  let KbU : SmoothCcTensor g 0 3 :=
    lieCorrectionZeroKappaBackgroundDifference (I := I) (M := M) g gU g_bg
  let S5T : SmoothCcTensor g 2 5 :=
    slotExtendIter (I := I) (M := M) g 0 3 2 K0T
  let S5U : SmoothCcTensor g 2 5 :=
    slotExtendIter (I := I) (M := M) g 0 3 2 K0U
  let E3T : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 KbT
  let E3U : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 KbU
  let S4T : SmoothCcTensor g 2 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 5 3 Tr3T S5T
  let S4U : SmoothCcTensor g 2 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 5 3 Tr3U S5U
  let S3T : SmoothCcTensor g 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 3 6 E3T S4T
  let S3U : SmoothCcTensor g 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 3 6 E3U S4U
  let S2T : SmoothCcTensor g 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 4 Tr4T S3T
  let S2U : SmoothCcTensor g 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 4 Tr4U S3U
  let S1T : SmoothCcTensor g 2 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 4 2 Tr2T S2T
  let S1U : SmoothCcTensor g 2 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 4 2 Tr2U S2U
  have hTr2T : covariantJetNormSq (I := I) (M := M) g 2 Tr2T ≤ Bt2 ^ 2 := by
    rw [show Tr2T = reindexedPureTrace (I := I) (M := M) g gT 2 σ by rfl,
      covariantJetNormSq_reindexedPureTrace]
    exact hb2 T gT hTtie hTHs2b
  have hTr2U : covariantJetNormSq (I := I) (M := M) g 2 Tr2U ≤ Bt2 ^ 2 := by
    rw [show Tr2U = reindexedPureTrace (I := I) (M := M) g gU 2 σ by rfl,
      covariantJetNormSq_reindexedPureTrace]
    exact hb2 U gU hUtie hUHs2b
  have hTr2D : covariantJetNormSq (I := I) (M := M) g 2 (Tr2T - Tr2U) ≤
      (Ct2 * N) ^ 2 := by
    rw [show Tr2T - Tr2U =
        reindexedPureTrace (I := I) (M := M) g gT 2 σ -
          reindexedPureTrace (I := I) (M := M) g gU 2 σ by rfl,
      reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
    simpa only [N] using hp2 T U gT gU hTtie hUtie hTHs2p hUHs2p
  have hTr3T : covariantJetNormSq (I := I) (M := M) g 2 Tr3T ≤ Bt3 ^ 2 := by
    rw [show Tr3T = reindexedPureTrace (I := I) (M := M) g gT 3
        lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour by rfl, covariantJetNormSq_reindexedPureTrace]
    exact hb3 T gT hTtie hTHs3b
  have hTr3U : covariantJetNormSq (I := I) (M := M) g 2 Tr3U ≤ Bt3 ^ 2 := by
    rw [show Tr3U = reindexedPureTrace (I := I) (M := M) g gU 3
        lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour by rfl, covariantJetNormSq_reindexedPureTrace]
    exact hb3 U gU hUtie hUHs3b
  have hTr3D : covariantJetNormSq (I := I) (M := M) g 2 (Tr3T - Tr3U) ≤
      (Ct3 * N) ^ 2 := by
    rw [show Tr3T - Tr3U =
        reindexedPureTrace (I := I) (M := M) g gT 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour -
          reindexedPureTrace (I := I) (M := M) g gU 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour by rfl,
      reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
    simpa only [N] using hp3 T U gT gU hTtie hUtie hTHs3p hUHs3p
  have hTr4T : covariantJetNormSq (I := I) (M := M) g 2 Tr4T ≤ Bt4 ^ 2 := by
    rw [show Tr4T = reindexedPureTrace (I := I) (M := M) g gT 4
        lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne by rfl, covariantJetNormSq_reindexedPureTrace]
    exact hb4 T gT hTtie hTHs4b
  have hTr4U : covariantJetNormSq (I := I) (M := M) g 2 Tr4U ≤ Bt4 ^ 2 := by
    rw [show Tr4U = reindexedPureTrace (I := I) (M := M) g gU 4
        lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne by rfl, covariantJetNormSq_reindexedPureTrace]
    exact hb4 U gU hUtie hUHs4b
  have hTr4D : covariantJetNormSq (I := I) (M := M) g 2 (Tr4T - Tr4U) ≤
      (Ct4 * N) ^ 2 := by
    rw [show Tr4T - Tr4U =
        reindexedPureTrace (I := I) (M := M) g gT 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne -
          reindexedPureTrace (I := I) (M := M) g gU 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne by rfl,
      reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
    simpa only [N] using hp4 T U gT gU hTtie hUtie hTHs4p hUHs4p
  have hK0T : covariantJetNormSq (I := I) (M := M) g 1 K0T ≤ B0 ^ 2 := by
    simpa only [K0T] using h0One T gT hTtie hTHs1
  have hK0D : covariantJetNormSq (I := I) (M := M) g 1 (K0T - K0U) ≤
      (C0 * N) ^ 2 := by
    simpa only [K0T, K0U, N] using h0Pair T U gT gU hTtie hUtie
  have hKbT : covariantJetNormSq (I := I) (M := M) g 2 KbT ≤ Bk ^ 2 := by
    simpa only [KbT] using hkOne T gT hTtie hTHs1
  have hKbU : covariantJetNormSq (I := I) (M := M) g 2 KbU ≤ Bk ^ 2 := by
    simpa only [KbU] using hkOne U gU hUtie hUHs1
  have hKbD : covariantJetNormSq (I := I) (M := M) g 2 (KbT - KbU) ≤
      (Ck * N) ^ 2 := by
    simpa only [KbT, KbU, N] using hkPair T U gT gU hTtie hUtie
  have hS5T : covariantJetNormSq (I := I) (M := M) g 1 S5T ≤ A5 ^ 2 := by
    simpa only [S5T, A5, sf2] using
      slotIter_h1b (I := I) (M := M) g 0 3 2 K0T B0 hK0T
  have hS5D : covariantJetNormSq (I := I) (M := M) g 1 (S5T - S5U) ≤
      (D5 * N) ^ 2 := by
    rw [show S5T - S5U =
        slotExtendIter (I := I) (M := M) g 0 3 2 (K0T - K0U) by
      dsimp only [S5T, S5U]
      rw [slotExtendIter_sub]]
    have hs := slotIter_h1b (I := I) (M := M) g 0 3 2
      (K0T - K0U) (C0 * N) hK0D
    simpa only [D5, sf2, mul_assoc] using hs
  have hE3T : covariantJetNormSq (I := I) (M := M) g 2 E3T ≤ Ak ^ 2 := by
    simpa only [E3T, Ak, sf3] using
      slotIter_h2b (I := I) (M := M) g 0 3 3 KbT Bk hKbT
  have hE3U : covariantJetNormSq (I := I) (M := M) g 2 E3U ≤ Ak ^ 2 := by
    simpa only [E3U, Ak, sf3] using
      slotIter_h2b (I := I) (M := M) g 0 3 3 KbU Bk hKbU
  have hE3D : covariantJetNormSq (I := I) (M := M) g 2 (E3T - E3U) ≤
      (Dk * N) ^ 2 := by
    rw [show E3T - E3U =
        slotExtendIter (I := I) (M := M) g 0 3 3 (KbT - KbU) by
      dsimp only [E3T, E3U]
      rw [slotExtendIter_sub]]
    have hs := slotIter_h2b (I := I) (M := M) g 0 3 3
      (KbT - KbU) (Ck * N) hKbD
    simpa only [Dk, sf3, mul_assoc] using hs
  have hS4T : covariantJetNormSq (I := I) (M := M) g 1 S4T ≤ A4 ^ 2 := by
    simpa only [S4T, A4] using
      hone3 Tr3T S5T Bt3 A5 hBt3 hA5 hTr3T hS5T
  have hS4D : covariantJetNormSq (I := I) (M := M) g 1 (S4T - S4U) ≤
      (D4 * N) ^ 2 := by
    have hp := hpair3 Tr3T Tr3U S5T S5U Bt3 (Ct3 * N) A5 (D5 * N)
      hBt3 (mul_nonneg hCt3 hN) hA5 (mul_nonneg hD5 hN)
      hTr3U hTr3D hS5T hS5D
    have heq : P3 * (Bt3 * (D5 * N) + (Ct3 * N) * A5) = D4 * N := by
      simpa only [D4] using pairing_product_coefficient_mul P3 Bt3 D5 Ct3 A5 N
    rw [← heq]
    simpa only [S4T, S4U] using hp
  have hS3T : covariantJetNormSq (I := I) (M := M) g 1 S3T ≤ A3 ^ 2 := by
    simpa only [S3T, A3] using
      honek E3T S4T Ak A4 hAk hA4 hE3T hS4T
  have hS3D : covariantJetNormSq (I := I) (M := M) g 1 (S3T - S3U) ≤
      (D3 * N) ^ 2 := by
    have hp := hpairk E3T E3U S4T S4U Ak (Dk * N) A4 (D4 * N)
      hAk (mul_nonneg hDk hN) hA4 (mul_nonneg hD4 hN)
      hE3U hE3D hS4T hS4D
    have heq : Pk * (Ak * (D4 * N) + (Dk * N) * A4) = D3 * N := by
      simpa only [D3] using pairing_product_coefficient_mul Pk Ak D4 Dk A4 N
    rw [← heq]
    simpa only [S3T, S3U] using hp
  have hS2T : covariantJetNormSq (I := I) (M := M) g 1 S2T ≤ A2 ^ 2 := by
    simpa only [S2T, A2] using
      hone4 Tr4T S3T Bt4 A3 hBt4 hA3 hTr4T hS3T
  have hS2D : covariantJetNormSq (I := I) (M := M) g 1 (S2T - S2U) ≤
      (D2 * N) ^ 2 := by
    have hp := hpair4 Tr4T Tr4U S3T S3U Bt4 (Ct4 * N) A3 (D3 * N)
      hBt4 (mul_nonneg hCt4 hN) hA3 (mul_nonneg hD3 hN)
      hTr4U hTr4D hS3T hS3D
    have heq : P4 * (Bt4 * (D3 * N) + (Ct4 * N) * A3) = D2 * N := by
      simpa only [D2] using pairing_product_coefficient_mul P4 Bt4 D3 Ct4 A3 N
    rw [← heq]
    simpa only [S2T, S2U] using hp
  have hS1T : covariantJetNormSq (I := I) (M := M) g 1 S1T ≤ A1 ^ 2 := by
    simpa only [S1T, A1] using
      hone2 Tr2T S2T Bt2 A2 hBt2 hA2 hTr2T hS2T
  have hS1D : covariantJetNormSq (I := I) (M := M) g 1 (S1T - S1U) ≤
      (D1 * N) ^ 2 := by
    have hp := hpair2 Tr2T Tr2U S2T S2U Bt2 (Ct2 * N) A2 (D2 * N)
      hBt2 (mul_nonneg hCt2 hN) hA2 (mul_nonneg hD2 hN)
      hTr2U hTr2D hS2T hS2D
    have heq : P2 * (Bt2 * (D2 * N) + (Ct2 * N) * A2) = D1 * N := by
      simpa only [D1] using pairing_product_coefficient_mul P2 Bt2 D2 Ct2 A2 N
    rw [← heq]
    simpa only [S1T, S1U] using hp
  have hhalfT : lieCorrectionZeroMixedConnectionBackgroundHalf (I := I) (M := M) g gT g_bg σ = S1T := by
    rfl
  have hhalfU : lieCorrectionZeroMixedConnectionBackgroundHalf (I := I) (M := M) g gU g_bg σ = S1U := by
    rfl
  rw [hhalfT, hhalfU]
  simpa only [N] using hS1D

omit [NeZero (Module.finrank ℝ E)] in
private theorem lieCorrectionZeroMixedConnection_backgroundDifference_eq
    (g gm g_bg : SmoothRiemannianMetric I M) :
    lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g_bg -
        lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g =
      (2 : ℝ) •
        (lieCorrectionZeroMixedConnectionBackgroundHalf (I := I) (M := M) g gm g_bg lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
          lieCorrectionZeroMixedConnectionBackgroundHalf (I := I) (M := M) g gm g_bg
            (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)) := by
  rw [lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g gm g_bg,
    lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g gm g]
  have h0 := lieCorrectionZeroMixedConnectionHalfRF_backgroundDifference (I := I) (M := M) g gm g_bg lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  have h1 := lieCorrectionZeroMixedConnectionHalfRF_backgroundDifference (I := I) (M := M) g gm g_bg
    (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
  simp only [lieCorrectionZeroMixedConnectionExpansion]
  rw [show
      (2 : ℝ) •
          (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gm g_bg lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
            lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gm g_bg
              (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)) -
        (2 : ℝ) •
          (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gm g lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
            lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gm g
              (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)) =
        (2 : ℝ) •
          ((lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gm g_bg lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne -
              lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gm g lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) +
            (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gm g_bg
                (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) -
              lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gm g
                (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))) by module,
    h0, h1]

theorem exists_lieCorrectionZeroMixedConnection_backgroundDifference_pairing_firstOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) →
        (∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 1
            ((lieCorrectionZeroMixedConnection (I := I) (M := M) g gT g_bg -
                lieCorrectionZeroMixedConnection (I := I) (M := M) g gT g) -
              (lieCorrectionZeroMixedConnection (I := I) (M := M) g gU g_bg -
                lieCorrectionZeroMixedConnection (I := I) (M := M) g gU g)) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, Ch, hρ, hCh, hhalf⟩ :=
    exists_lieCorrectionZeroMixedConnectionBackgroundHalf_pairing_first_order_bound (I := I) (M := M) hDim g g_bg
  let C : ℝ := 4 * Ch
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hCh
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hTHs hUHs
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let D0 : SmoothCcTensor g 2 2 :=
    lieCorrectionZeroMixedConnectionBackgroundHalf (I := I) (M := M) g gT g_bg lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne -
      lieCorrectionZeroMixedConnectionBackgroundHalf (I := I) (M := M) g gU g_bg lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  let D1 : SmoothCcTensor g 2 2 :=
    lieCorrectionZeroMixedConnectionBackgroundHalf (I := I) (M := M) g gT g_bg
        (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) -
      lieCorrectionZeroMixedConnectionBackgroundHalf (I := I) (M := M) g gU g_bg
        (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
  have hD0 : covariantJetNormSq (I := I) (M := M) g 1 D0 ≤ (Ch * N) ^ 2 := by
    simpa only [D0, N] using
      hhalf lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne T U gT gU hTtie hUtie hTHs hUHs
  have hD1 : covariantJetNormSq (I := I) (M := M) g 1 D1 ≤ (Ch * N) ^ 2 := by
    simpa only [D1, N] using
      hhalf (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) T U gT gU
        hTtie hUtie hTHs hUHs
  have heq :
      (lieCorrectionZeroMixedConnection (I := I) (M := M) g gT g_bg -
          lieCorrectionZeroMixedConnection (I := I) (M := M) g gT g) -
        (lieCorrectionZeroMixedConnection (I := I) (M := M) g gU g_bg -
          lieCorrectionZeroMixedConnection (I := I) (M := M) g gU g) =
      (2 : ℝ) • (D0 + D1) := by
    rw [lieCorrectionZeroMixedConnection_backgroundDifference_eq (I := I) (M := M) g gT g_bg,
      lieCorrectionZeroMixedConnection_backgroundDifference_eq (I := I) (M := M) g gU g_bg]
    dsimp only [D0, D1]
    module
  have hsum : covariantJetNormSq (I := I) (M := M) g 1 (D0 + D1) ≤
      4 * (Ch * N) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 1 (D0 + D1) ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 1 D0 +
            covariantJetNormSq (I := I) (M := M) g 1 D1) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 1 D0 D1
      _ ≤ 2 * ((Ch * N) ^ 2 + (Ch * N) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hD0 hD1) (by norm_num)
      _ = 4 * (Ch * N) ^ 2 := by ring
  rw [heq, covariantJetNormSq_smul]
  norm_num
  calc
    4 * covariantJetNormSq (I := I) (M := M) g 1 (D0 + D1) ≤
        4 * (4 * (Ch * N) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (C * N) ^ 2 := by
      dsimp only [C]
      ring

private theorem deTurckLieCoefficient_backgroundDifference_decomposition
    (g gT gU gB : SmoothRiemannianMetric I M) :
    ((deTurckLieCoeffField (I := I) (M := M) g gT gB +
          lieCorrectionZeroField (I := I) (M := M) g gT gB) -
        (deTurckLieCoeffField (I := I) (M := M) g gT g +
          lieCorrectionZeroField (I := I) (M := M) g gT g)) -
      ((deTurckLieCoeffField (I := I) (M := M) g gU gB +
          lieCorrectionZeroField (I := I) (M := M) g gU gB) -
        (deTurckLieCoeffField (I := I) (M := M) g gU g +
          lieCorrectionZeroField (I := I) (M := M) g gU g)) =
      (((deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gT gB -
            deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gT g) -
          (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gU gB -
            deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gU g)) +
        (((deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gT gB -
              deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gT g) +
            (lieCorrectionZeroInsertion (I := I) (M := M) g gT gB -
              lieCorrectionZeroInsertion (I := I) (M := M) g gT g)) -
          ((deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gU gB -
              deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gU g) +
            (lieCorrectionZeroInsertion (I := I) (M := M) g gU gB -
              lieCorrectionZeroInsertion (I := I) (M := M) g gU g)))) +
      ((lieCorrectionZeroMixedConnection (I := I) (M := M) g gT gB -
          lieCorrectionZeroMixedConnection (I := I) (M := M) g gT g) -
        (lieCorrectionZeroMixedConnection (I := I) (M := M) g gU gB -
          lieCorrectionZeroMixedConnection (I := I) (M := M) g gU g)) := by
  rw [← deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField
      (I := I) (M := M) g gT gB,
    ← deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField
      (I := I) (M := M) g gT g,
    ← deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField
      (I := I) (M := M) g gU gB,
    ← deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField
      (I := I) (M := M) g gU g,
    lieCorrectionZero_decomp (I := I) (M := M) g gT gB,
    lieCorrectionZero_decomp (I := I) (M := M) g gT g,
    lieCorrectionZero_decomp (I := I) (M := M) g gU gB,
    lieCorrectionZero_decomp (I := I) (M := M) g gU g]
  module


theorem exists_deTurckLieCoefficient_backgroundDifference_pairing_firstOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ ρ : ℝ, ∃ B0 : ℝ → ℝ → ℝ, ∃ B1 : ℝ → ℝ,
      0 < ρ ∧
      (∀ R A : ℝ, 0 ≤ B0 R A) ∧
      (∀ A : ℝ, 0 ≤ B1 A) ∧
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
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      let N := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      covariantJetNormSq (I := I) (M := M) g 1
          (((deTurckLieCoeffField (I := I) (M := M) g gT gB +
                lieCorrectionZeroField (I := I) (M := M) g gT gB) -
              (deTurckLieCoeffField (I := I) (M := M) g gT g +
                lieCorrectionZeroField (I := I) (M := M) g gT g)) -
            ((deTurckLieCoeffField (I := I) (M := M) g gU gB +
                lieCorrectionZeroField (I := I) (M := M) g gU gB) -
              (deTurckLieCoeffField (I := I) (M := M) g gU g +
                lieCorrectionZeroField (I := I) (M := M) g gU g))) ≤
        (B0 R A * D2 + B1 A * N) ^ 2 := by
  obtain ⟨ρa, Ba0, Ba1, hρa, hBa0, hBa1, hDLa⟩ :=
    exists_deTurckLieConnectionDifferenceDerivativeCoefficient_backgroundDifference_pairing_firstOrder_bound (I := I) (M := M) hDim g gB hδ₀0 hδ₀
  obtain ⟨ρb, Cb, hρb, hCb, hDLb⟩ :=
    exists_deTurckLieInsertionCorrection_pairing_firstOrder_bound (I := I) (M := M) hDim g gB
  obtain ⟨ρm, Cm, hρm, hCm, hAMix⟩ :=
    exists_lieCorrectionZeroMixedConnection_backgroundDifference_pairing_firstOrder_bound
      (I := I) (M := M) hDim g gB
  let ρ : ℝ := min ρa (min ρb ρm)
  let B0 : ℝ → ℝ → ℝ := fun R A => 2 * Ba0 R A
  let B1 : ℝ → ℝ := fun A => 2 * (Ba1 A + Cb + Cm)
  have hρ : 0 < ρ := lt_min hρa (lt_min hρb hρm)
  refine ⟨ρ, B0, B1, hρ, ?_, ?_, ?_⟩
  · intro R A
    exact mul_nonneg (by norm_num) (hBa0 R A)
  · intro A
    exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg (hBa1 A) hCb) hCm)
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    hTHs hUHs R A D2 hR hA hD2 hU2 hT3 hTU2
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let S : ℝ := Ba0 R A * D2 + Ba1 A * N
  let X : SmoothCcTensor g 2 2 :=
    (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gT gB -
        deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gT g) -
      (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gU gB -
        deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gU g)
  let Y : SmoothCcTensor g 2 2 :=
    ((deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gT gB -
          deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gT g) +
        (lieCorrectionZeroInsertion (I := I) (M := M) g gT gB -
          lieCorrectionZeroInsertion (I := I) (M := M) g gT g)) -
      ((deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gU gB -
          deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gU g) +
        (lieCorrectionZeroInsertion (I := I) (M := M) g gU gB -
          lieCorrectionZeroInsertion (I := I) (M := M) g gU g))
  let Z : SmoothCcTensor g 2 2 :=
    (lieCorrectionZeroMixedConnection (I := I) (M := M) g gT gB -
        lieCorrectionZeroMixedConnection (I := I) (M := M) g gT g) -
      (lieCorrectionZeroMixedConnection (I := I) (M := M) g gU gB -
        lieCorrectionZeroMixedConnection (I := I) (M := M) g gU g)
  have hN : 0 ≤ N := norm_nonneg _
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact add_nonneg (mul_nonneg (hBa0 R A) hD2)
      (mul_nonneg (hBa1 A) hN)
  have hTHsa : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρa := hTHs.trans (min_le_left _ _)
  have hUHsa : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρa := hUHs.trans (min_le_left _ _)
  have hTHsb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρb :=
    hTHs.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hUHsb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρb :=
    hUHs.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hTHsm : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρm :=
    hTHs.trans (le_trans (min_le_right _ _) (min_le_right _ _))
  have hUHsm : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρm :=
    hUHs.trans (le_trans (min_le_right _ _) (min_le_right _ _))
  have hX : covariantJetNormSq (I := I) (M := M) g 1 X ≤ S ^ 2 := by
    simpa only [X, S, N] using
      hDLa gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU hTHsa hUHsa
        R A D2 hR hA hD2 hU2 hT3 hTU2
  have hY : covariantJetNormSq (I := I) (M := M) g 1 Y ≤ (Cb * N) ^ 2 := by
    simpa only [Y, N] using
      hDLb T U gT gU hTtie hUtie hTHsb hUHsb
  have hZ : covariantJetNormSq (I := I) (M := M) g 1 Z ≤ (Cm * N) ^ 2 := by
    simpa only [Z, N] using
      hAMix T U gT gU hTtie hUtie hTHsm hUHsm
  have hsplit :
      ((deTurckLieCoeffField (I := I) (M := M) g gT gB +
            lieCorrectionZeroField (I := I) (M := M) g gT gB) -
          (deTurckLieCoeffField (I := I) (M := M) g gT g +
            lieCorrectionZeroField (I := I) (M := M) g gT g)) -
        ((deTurckLieCoeffField (I := I) (M := M) g gU gB +
            lieCorrectionZeroField (I := I) (M := M) g gU gB) -
          (deTurckLieCoeffField (I := I) (M := M) g gU g +
            lieCorrectionZeroField (I := I) (M := M) g gU g)) =
        (X + Y) + Z := by
    simpa only [X, Y, Z] using
      deTurckLieCoefficient_backgroundDifference_decomposition (I := I) (M := M) g gT gU gB
  have hsum : covariantJetNormSq (I := I) (M := M) g 1 ((X + Y) + Z) ≤
      4 * S ^ 2 + 4 * (Cb * N) ^ 2 + 2 * (Cm * N) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 1 ((X + Y) + Z) ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 1 (X + Y) +
            covariantJetNormSq (I := I) (M := M) g 1 Z) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 1 (X + Y) Z
      _ ≤ 2 * (2 * (covariantJetNormSq (I := I) (M := M) g 1 X +
              covariantJetNormSq (I := I) (M := M) g 1 Y) +
            covariantJetNormSq (I := I) (M := M) g 1 Z) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add
            (covariantJetNormSq_add_le (I := I) (M := M) g 1 X Y) le_rfl) (by norm_num)
      _ ≤ 2 * (2 * (S ^ 2 + (Cb * N) ^ 2) + (Cm * N) ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add
            (mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)) hZ)
          (by norm_num)
      _ = 4 * S ^ 2 + 4 * (Cb * N) ^ 2 + 2 * (Cm * N) ^ 2 := by ring
  have hCbN : 0 ≤ Cb * N := mul_nonneg hCb hN
  have hCmN : 0 ≤ Cm * N := mul_nonneg hCm hN
  have hsq : 4 * S ^ 2 + 4 * (Cb * N) ^ 2 + 2 * (Cm * N) ^ 2 ≤
      (2 * (S + Cb * N + Cm * N)) ^ 2 := by
    nlinarith [mul_nonneg hS hCbN, mul_nonneg hS hCmN,
      mul_nonneg hCbN hCmN, sq_nonneg (Cm * N)]
  have hlin : B0 R A * D2 + B1 A * N =
      2 * (S + Cb * N + Cm * N) := by
    dsimp only [B0, B1, S]
    ring
  rw [hsplit]
  calc
    covariantJetNormSq (I := I) (M := M) g 1 ((X + Y) + Z) ≤
        4 * S ^ 2 + 4 * (Cb * N) ^ 2 + 2 * (Cm * N) ^ 2 := hsum
    _ ≤ (2 * (S + Cb * N + Cm * N)) ^ 2 := hsq
    _ = (B0 R A * D2 + B1 A * N) ^ 2 := by rw [hlin]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
