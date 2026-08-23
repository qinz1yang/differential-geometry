import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.InverseCoefficientSecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.MixedTensorApplicationSecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Morrey
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SecondOrderCoefficientLipschitzBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.UnifBochnerGap

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Elliptic
  (integrable_riemannianFiberNormSq_toSection riemannianFiberNormSq
   tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq)
open DifferentialGeometry.Analysis.Sobolev
  (inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc iteratedCovGrad iteratedCovGrad_zero
   normSq_le_integral_of_pointwise_fiberNormSq_le_rs
   norm_le_of_pointwise_fiberNormSq_bound_rs riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
   tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs)
open DifferentialGeometry.Analysis.Spectral
  (ccOperatorFieldComp ccTensorToHs metricComparisonEndomorphismField inverseMetricDifferenceSlotCoefficient iteratedCovGrad_add
   iteratedCovGrad_neg)
open DifferentialGeometry.Analysis.Spectral
  (h2CovsumC h2CovsumC_nonneg IsCurvAction0 covsum_hs_two)
open DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower
  (metricComparisonEndomorphismField_diff_split iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero
   sharpFlatEndoCc_eq_slotInsert_fullRaised)
open DifferentialGeometry.Geometry.Connection (slotInsertEndoCc slotInsertEndoCc_add)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
private theorem permICG (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (T : SmoothCcTensor g 0 s) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 s k
        (domDomCongrSection (I := I) g σ T)‖ =
      ‖iteratedCovGrad (I := I) g 0 s k T‖ := by
  classical
  have hbridge : ∀ W : SmoothCcTensor g 0 s,
      ‖iteratedCovGrad (I := I) g 0 s k W‖ ^ 2 =
        ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) x
          ((iteratedCovGrad (I := I) g 0 s k W).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro W
    rw [SmoothCcTensor.norm_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g 0 s k W)]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
      (I := I) (M := M) g (s + k)
        (iteratedCovGrad (I := I) g 0 s k W)
  have hsq :
      ‖iteratedCovGrad (I := I) g 0 s k
          (domDomCongrSection (I := I) g σ T)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g 0 s k T‖ ^ 2 := by
    rw [hbridge (domDomCongrSection (I := I) g σ T), hbridge T]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun x =>
        riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
          (I := I) (M := M) g σ T k x))
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

omit [NeZero (Module.finrank ℝ E)] in
private theorem symmICG (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 2 k
        (symmS (I := I) (M := M) g T)‖ ≤
      ‖iteratedCovGrad (I := I) g 0 2 k T‖ := by
  classical
  have hiter :
      iteratedCovGrad (I := I) g 0 2 k
          (symmS (I := I) (M := M) g T) =
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k T +
          (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k
            (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T) :=
    iteratedCovGrad_symmS_eq (I := I) (M := M) g T k
  rw [hiter]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul,
    permICG (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1) T k]
  have habs : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by
    rw [Real.norm_eq_abs]; norm_num
  rw [habs]
  linarith [norm_nonneg (iteratedCovGrad (I := I) g 0 2 k T)]

private theorem insOneICG
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g 1 Λ)‖ ≤
      3 * ‖iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ := by
  classical
  set F : M → ℝ := fun x => 3 *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
      ((iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x) with hF
  have hFint : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [hF]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 1 (1 + i)
        (iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ))).const_mul _
  have hpt : ∀ x,
      riemannianFiberNormSq (I := I) (M := M) g 2 (2 + i) x
          ((iteratedCovGrad (I := I) g 2 2 i
            (slotInsertEndoCc (I := I) (M := M) g 1 Λ)).toSection x) ≤
        F x := by
    intro x
    have h := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
      (I := I) (M := M) g 1 Λ i x
    rw [hDim] at h
    norm_num at h
    simpa only [hF, Nat.reduceAdd] using h
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g 2 (2 + i)
      (iteratedCovGrad (I := I) g 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g 1 Λ)) F hFint hpt
  have hint :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
          ((iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g 1 (1 + i)]
  rw [hF] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  refine le_of_sq_le_sq ?_
    (mul_nonneg (by norm_num) (norm_nonneg _))
  calc
    ‖iteratedCovGrad (I := I) g 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g 1 Λ)‖ ^ 2
        ≤ 3 * ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := hsq
    _ ≤ (3 * ‖iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖) ^ 2 := by
      nlinarith [sq_nonneg
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖]

private theorem perturbICG
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g 1
          (symmRaiseEndo (I := I) (M := M) g T))‖ ≤
      3 * ‖iteratedCovGrad (I := I) g 0 2 i T‖ := by
  have hslot := insOneICG (I := I) (M := M) hDim g i
    (symmRaiseEndo (I := I) (M := M) g T)
  have hbase :
      ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0
            (symmRaiseEndo (I := I) (M := M) g T))‖ ≤
        ‖iteratedCovGrad (I := I) g 0 2 i T‖ := by
    rw [insert_symmRaise_eq (I := I) (M := M) g T]
    calc
      _ = ‖iteratedCovGrad (I := I) g 0 2 i
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (symmS (I := I) (M := M) g T))‖ := by
            simpa only [Nat.zero_add, Nat.reduceAdd] using
              norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
                (I := I) (M := M) g 0
                (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 2) 1)
                  (symmS (I := I) (M := M) g T)) i
      _ = ‖iteratedCovGrad (I := I) g 0 2 i
          (symmS (I := I) (M := M) g T)‖ :=
        permICG (I := I) (M := M) g
          (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g T) i
      _ ≤ _ := symmICG (I := I) (M := M) g T i
  exact hslot.trans (mul_le_mul_of_nonneg_left hbase (by norm_num))

private theorem idSlotPt
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 2 x
        ((slotInsertEndoCc (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g g)).toSection x) ≤ 27 := by
  have h := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
    (I := I) (M := M) g 1 (metricComparisonEndomorphismField (I := I) (M := M) g g) 0 x
  rw [hDim] at h
  simp only [iteratedCovGrad_zero, Nat.add_zero, Nat.reduceAdd, pow_one] at h
  push_cast at h
  refine h.trans ?_
  have hid : riemannianFiberNormSq (I := I) (M := M) g 1 1 x
      ((slotInsertEndoCc (I := I) (M := M) g 0
        (metricComparisonEndomorphismField (I := I) (M := M) g g)).toSection x) ≤ 9 := by
    have hb := riemannianFiberNormSq_idEndo_le (I := I) (M := M) g x
    rw [hDim] at hb
    rw [← sharpFlatEndoCc_eq_slotInsert_fullRaised (I := I) (M := M) g g]
    norm_num at hb
    exact hb
  linarith

private theorem idSlotSucc
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (m : ℕ) :
    ‖iteratedCovGrad (I := I) g 2 2 (m + 1)
        (slotInsertEndoCc (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g g))‖ = 0 := by
  have h := insOneICG (I := I) (M := M) hDim g (m + 1)
    (metricComparisonEndomorphismField (I := I) (M := M) g g)
  rw [iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero
    (I := I) (M := M) g m, norm_zero, mul_zero] at h
  exact le_antisymm h (norm_nonneg _)

private theorem idSlotJet
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 2 2 j
        (slotInsertEndoCc (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g g))‖ ^ 2) ≤
      27 * ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal := by
  have h0 : ‖iteratedCovGrad (I := I) g 2 2 0
      (slotInsertEndoCc (I := I) (M := M) g 1
        (metricComparisonEndomorphismField (I := I) (M := M) g g))‖ ^ 2 ≤
      27 * ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal := by
    rw [iteratedCovGrad_zero]
    exact norm_le_of_pointwise_fiberNormSq_bound_rs (I := I) (M := M) g 2 2
      (slotInsertEndoCc (I := I) (M := M) g 1
        (metricComparisonEndomorphismField (I := I) (M := M) g g)) 27
      (idSlotPt (I := I) (M := M) hDim g)
  have h1 : ‖iteratedCovGrad (I := I) g 2 2 1
      (slotInsertEndoCc (I := I) (M := M) g 1
        (metricComparisonEndomorphismField (I := I) (M := M) g g))‖ = 0 :=
    idSlotSucc (I := I) (M := M) hDim g 0
  have h2 : ‖iteratedCovGrad (I := I) g 2 2 2
      (slotInsertEndoCc (I := I) (M := M) g 1
        (metricComparisonEndomorphismField (I := I) (M := M) g g))‖ = 0 :=
    idSlotSucc (I := I) (M := M) hDim g 1
  have hexp : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 2 2 j
        (slotInsertEndoCc (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g g))‖ ^ 2) =
      ‖iteratedCovGrad (I := I) g 2 2 0
        (slotInsertEndoCc (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g g))‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g 2 2 1
        (slotInsertEndoCc (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g g))‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g 2 2 2
        (slotInsertEndoCc (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g g))‖ ^ 2 := by
    norm_num [Finset.sum_range_succ]
  rw [hexp, h1, h2]
  simpa using h0

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem fullSlotSplit (g gm : SmoothRiemannianMetric I M) :
    slotInsertEndoCc (I := I) (M := M) g 1
        (metricComparisonEndomorphismField (I := I) (M := M) g gm) =
      inverseMetricDifferenceSlotCoefficient (I := I) g gm +
        slotInsertEndoCc (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g g) := by
  rw [metricComparisonEndomorphismField_diff_split (I := I) (M := M) g gm,
    slotInsertEndoCc_add,
    inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc (I := I) g gm]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iteratedCovGradNormSq_add_le (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A B : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g r s j (A + B)‖ ^ 2) ≤
      2 * ((∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) +
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
  calc
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g r s j (A + B)‖ ^ 2) ≤
        ∑ j ∈ Finset.range 3,
          2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [iteratedCovGrad_add]
      have htri := norm_add_le
        (iteratedCovGrad (I := I) g r s j A)
        (iteratedCovGrad (I := I) g r s j B)
      calc
        ‖iteratedCovGrad (I := I) g r s j A +
            iteratedCovGrad (I := I) g r s j B‖ ^ 2 ≤
            (‖iteratedCovGrad (I := I) g r s j A‖ +
              ‖iteratedCovGrad (I := I) g r s j B‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
        _ ≤ 2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
          nlinarith [sq_nonneg
            (‖iteratedCovGrad (I := I) g r s j A‖ -
              ‖iteratedCovGrad (I := I) g r s j B‖)]
    _ = 2 * ((∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) +
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]


theorem invCoeff_h2_lip_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T U : SmoothCcTensor g 0 2)
          (gT gU : SmoothRiemannianMetric I M),
          (∀ (y : M) (v w : TangentSpace I y),
            gT.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
          (∀ (y : M) (v w : TangentSpace I y),
            gU.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 2 2 x
                ((inverseMetricDifferenceSlotCoefficient (I := I) g gT -
                  inverseMetricDifferenceSlotCoefficient (I := I) g gU).toSection x) ≤
              (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
                (T - U)‖) ^ 2) ∧
            (∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 2 2 j
                (inverseMetricDifferenceSlotCoefficient (I := I) g gT -
                  inverseMetricDifferenceSlotCoefficient (I := I) g gU)‖ ^ 2) ≤
              (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
                (T - U)‖) ^ 2 := by
  classical
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    exists_inverseMetricDifferenceSlotCoefficient_secondOrder_bound_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Cmul, hCmul, hmul⟩ :=
    operatorFieldComposition_h2_h2_to_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 2 2 2
  obtain ⟨Cpt, hCpt, hpoint⟩ :=
    morreyRS_uniform (I := I) (M := M) hDim gBase hΛ 2 2
  let Ch : ℝ := h2CovsumC Kcurv.rankTwo
  let vol : ℝ := volCompareC (E := E) Λ *
    ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  let Cp : ℝ := 3 * Ch
  let Z : ℝ := 2 * ((Cinv * ρ) ^ 2 + 27 * vol)
  let A : ℝ := Real.sqrt Z
  let C0 : ℝ := Cmul ^ 2 * Cp * A ^ 2
  let C : ℝ := (Cpt + 1) * C0
  have hCh : 0 ≤ Ch := by
    dsimp only [Ch]; exact h2CovsumC_nonneg Kcurv.rankTwo
  have hvol : 0 ≤ vol := by
    dsimp only [vol]
    exact mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
  have hCp : 0 ≤ Cp := by dsimp only [Cp]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = Z := by simpa only [A] using Real.sq_sqrt hZ
  have hC0 : 0 ≤ C0 := by dsimp only [C0]; positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (add_nonneg hCpt (by norm_num)) hC0
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro g hEq hjet T U gT gU hTtie hUtie hT hU
  have hact : IsCurvAction0 (I := I) (M := M) g 2 Kcurv.rankTwo :=
    (hKcurv.bounds g hEq hjet).1
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  have hvolg : ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal ≤
      vol := by
    simpa only [vol] using
      (volumeReal_cross (I := I) (M := M) gBase g hEq).1
  let NT : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let NU : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  have hNT : 0 ≤ NT := norm_nonneg _
  have hNU : 0 ≤ NU := norm_nonneg _
  have hN : 0 ≤ N := norm_nonneg _
  have hid : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 2 2 j
        (slotInsertEndoCc (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g g))‖ ^ 2) ≤ 27 * vol := by
    refine (idSlotJet (I := I) (M := M) hDim g).trans ?_
    exact mul_le_mul_of_nonneg_left hvolg (by norm_num)
  have hfull : ∀ gm : SmoothRiemannianMetric I M,
      ∀ W : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ ≤ ρ →
      (∀ (y : M) (v w : TangentSpace I y),
        gm.inner y v w =
          g.inner y v w + ccTensorBilinSymm (I := I) g W y v w) →
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 2 j
          (slotInsertEndoCc (I := I) (M := M) g 1
            (metricComparisonEndomorphismField (I := I) (M := M) g gm))‖ ^ 2) ≤ A ^ 2 := by
    intro gm W hW hWtie
    rw [fullSlotSplit (I := I) (M := M) g gm]
    have hdiff := (hinv g hEq hjet W gm hW hWtie).2
    calc
      _ ≤ 2 * ((∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (inverseMetricDifferenceSlotCoefficient (I := I) g gm)‖ ^ 2) +
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 2 2 j
              (slotInsertEndoCc (I := I) (M := M) g 1
                (metricComparisonEndomorphismField (I := I) (M := M) g g))‖ ^ 2) :=
        iteratedCovGradNormSq_add_le (I := I) (M := M) g _ _
      _ ≤ 2 * ((Cinv * ρ) ^ 2 + 27 * vol) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ hid) (by norm_num)
        refine hdiff.trans ?_
        exact pow_le_pow_left₀
          (mul_nonneg hCinv (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hW hCinv) 2
      _ = A ^ 2 := by rw [hAsq]
  have hfullT := hfull gT T hT hTtie
  have hfullU := hfull gU U hU hUtie
  have hpert : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 2 2 j
        (slotInsertEndoCc (I := I) (M := M) g 1
          (symmRaiseEndo (I := I) (M := M) g (T - U)))‖ ^ 2) ≤
      (Cp * N) ^ 2 := by
    have hsum : ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j (T - U)‖ ≤ Ch * N := by
      simpa only [Ch, N] using
        (covsum_hs_two (I := I) (M := M) g 2 hact (T - U))
    have hsq : (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j (T - U)‖ ^ 2) ≤ (Ch * N) ^ 2 :=
      (Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)).trans
        (pow_le_pow_left₀
          (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hsum 2)
    calc
      (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (slotInsertEndoCc (I := I) (M := M) g 1
              (symmRaiseEndo (I := I) (M := M) g (T - U)))‖ ^ 2) ≤
          ∑ j ∈ Finset.range 3,
            (3 * ‖iteratedCovGrad (I := I) g 0 2 j (T - U)‖) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _)
          (perturbICG (I := I) (M := M) hDim g (T - U) j) 2
      _ = 9 * (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j (T - U)‖ ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ 9 * (Ch * N) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = (Cp * N) ^ 2 := by dsimp only [Cp]; ring
  have hMid : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 2 2 j
        (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
          (slotInsertEndoCc (I := I) (M := M) g 1
            (symmRaiseEndo (I := I) (M := M) g (T - U)))
          (slotInsertEndoCc (I := I) (M := M) g 1
            (metricComparisonEndomorphismField (I := I) (M := M) g gT)))‖ ^ 2) ≤
      (Cmul * (Cp * N) * A) ^ 2 :=
    hmul g hEq hjet1 hjet2 _ _ (Cp * N) A
      (mul_nonneg hCp hN) hA hpert hfullT
  have hOut : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 2 2 j
        (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
          (slotInsertEndoCc (I := I) (M := M) g 1
            (metricComparisonEndomorphismField (I := I) (M := M) g gU))
          (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
            (slotInsertEndoCc (I := I) (M := M) g 1
              (symmRaiseEndo (I := I) (M := M) g (T - U)))
            (slotInsertEndoCc (I := I) (M := M) g 1
              (metricComparisonEndomorphismField (I := I) (M := M) g gT))))‖ ^ 2) ≤
      (C0 * N) ^ 2 := by
    have h := hmul g hEq hjet1 hjet2 _ _ A (Cmul * (Cp * N) * A) hA
      (mul_nonneg (mul_nonneg hCmul (mul_nonneg hCp hN)) hA) hfullU hMid
    refine h.trans (le_of_eq ?_)
    dsimp only [C0]
    ring
  have hD : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 2 2 j
        (inverseMetricDifferenceSlotCoefficient (I := I) g gT -
          inverseMetricDifferenceSlotCoefficient (I := I) g gU)‖ ^ 2) ≤ (C0 * N) ^ 2 := by
    rw [invSlot_sub_factor (I := I) (M := M) g gT gU T U hTtie hUtie]
    simpa only [iteratedCovGrad_neg, norm_neg] using hOut
  have hC0C : C0 ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hCpt hC0]
  have hCptC : Cpt * C0 ≤ C := by
    dsimp only [C]
    nlinarith
  refine ⟨?_, ?_⟩
  · intro x
    have hpt := hpoint g hEq hjet1 hjet2
      (inverseMetricDifferenceSlotCoefficient (I := I) g gT -
        inverseMetricDifferenceSlotCoefficient (I := I) g gU) x
    calc
      riemannianFiberNormSq (I := I) (M := M) g 2 2 x
          ((inverseMetricDifferenceSlotCoefficient (I := I) g gT -
            inverseMetricDifferenceSlotCoefficient (I := I) g gU).toSection x) ≤
          Cpt ^ 2 * (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 2 2 j
              (inverseMetricDifferenceSlotCoefficient (I := I) g gT -
                inverseMetricDifferenceSlotCoefficient (I := I) g gU)‖ ^ 2) := hpt
      _ ≤ Cpt ^ 2 * (C0 * N) ^ 2 :=
        mul_le_mul_of_nonneg_left hD (sq_nonneg Cpt)
      _ = (Cpt * C0 * N) ^ 2 := by ring
      _ ≤ (C * N) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCpt hC0) hN)
          (mul_le_mul_of_nonneg_right hCptC hN) 2
  · refine hD.trans ?_
    exact pow_le_pow_left₀ (mul_nonneg hC0 hN)
      (mul_le_mul_of_nonneg_right hC0C hN) 2

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
