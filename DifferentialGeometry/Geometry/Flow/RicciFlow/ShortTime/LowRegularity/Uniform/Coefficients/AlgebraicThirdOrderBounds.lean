import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Coefficients.InverseThirdOrderBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Lowered

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

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
  let F : M → ℝ := fun x => 3 *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
      ((iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
  have hFint : Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
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
    simpa only [F, Nat.reduceAdd] using h
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
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  refine le_of_sq_le_sq ?_
    (mul_nonneg (by norm_num) (norm_nonneg _))
  calc
    ‖iteratedCovGrad (I := I) g 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g 1 Λ)‖ ^ 2 ≤
        3 * ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := hsq
    _ ≤ (3 * ‖iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖) ^ 2 := by
      nlinarith [sq_nonneg
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖]

omit [SigmaCompactSpace M] in
private theorem idSlotPt
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 2 x
        ((slotInsertEndoCc (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g g)).toSection x) ≤ 27 := by
  have h := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
    (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g g) 0 x
  rw [hDim] at h
  simp only [iteratedCovGrad_zero, Nat.add_zero, Nat.reduceAdd, pow_one] at h
  push_cast at h
  refine h.trans ?_
  have hid : riemannianFiberNormSq (I := I) (M := M) g 1 1 x
      ((slotInsertEndoCc (I := I) (M := M) g 0
        (metricComparisonEndomorphismField (I := I) (M := M) g g)).toSection x) ≤ 9 := by
    have hb := riemannianFiberNormSq_idEndo_le (I := I) (M := M) g x
    rw [hDim] at hb
    rw [← sharpFlatEndoCc_eq_slotInsert_fullRaised
      (I := I) (M := M) g g]
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
    (∑ j ∈ Finset.range 4,
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
  have h1 := idSlotSucc (I := I) (M := M) hDim g 0
  have h2 := idSlotSucc (I := I) (M := M) hDim g 1
  have h3 := idSlotSucc (I := I) (M := M) hDim g 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [h1, h2, h3]
  norm_num
  simpa only [iteratedCovGrad_zero] using h0

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

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iteratedCovGradNormSq_add_le (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A B : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g r s j (A + B)‖ ^ 2) ≤
      2 * ((∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) +
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
  calc
    _ ≤ ∑ j ∈ Finset.range 4,
          2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [iteratedCovGrad_add]
      have htri := norm_add_le
        (iteratedCovGrad (I := I) g r s j A)
        (iteratedCovGrad (I := I) g r s j B)
      calc
        _ ≤ (‖iteratedCovGrad (I := I) g r s j A‖ +
              ‖iteratedCovGrad (I := I) g r s j B‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
        _ ≤ 2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
          nlinarith [sq_nonneg
            (‖iteratedCovGrad (I := I) g r s j A‖ -
              ‖iteratedCovGrad (I := I) g r s j B‖)]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

private theorem affineSq (a b n : ℝ) (hb : 0 ≤ b) (hn : 0 ≤ n) :
    2 * ((a * n) ^ 2 + b) ≤ 2 * (a ^ 2 + b) * (1 + n) ^ 2 := by
  have hn_sq : n ^ 2 ≤ (1 + n) ^ 2 := by nlinarith
  have hone_sq : (1 : ℝ) ≤ (1 + n) ^ 2 := by nlinarith
  have ha := mul_le_mul_of_nonneg_left hn_sq (sq_nonneg a)
  have hb' := mul_le_mul_of_nonneg_left hone_sq hb
  nlinarith

theorem fullRaised_h3_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2) (gm : SmoothRiemannianMetric I M),
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
          (∀ (y : M) (v w : TangentSpace I y),
            gm.inner y v w = g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 2 2 x
                ((slotInsertEndoCc (I := I) (M := M) g 1
                  (metricComparisonEndomorphismField (I := I) (M := M) g gm)).toSection x) ≤
              (C * (1 +
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖)) ^ 2) ∧
            (∑ j ∈ Finset.range 4,
              ‖iteratedCovGrad (I := I) g 2 2 j
                (slotInsertEndoCc (I := I) (M := M) g 1
                  (metricComparisonEndomorphismField (I := I) (M := M) g gm))‖ ^ 2) ≤
              (C * (1 +
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖)) ^ 2 := by
  classical
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    inv_coeff_h3_uniform (I := I) (M := M) hDim gBase hΛ
  let vol : ℝ := volCompareC (E := E) Λ *
    ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  let K : ℝ := 2 * (Cinv ^ 2 + 27 + 27 * vol)
  have hvol : 0 ≤ vol := by
    dsimp only [vol, volCompareC]
    positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine ⟨ρ, Real.sqrt K, hρ, Real.sqrt_nonneg _, ?_⟩
  intro g hEq hjet T gm hT htie
  obtain ⟨hinvPt, hinvJet⟩ := hinv g hEq hjet T gm hT htie
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  have hN : 0 ≤ N := norm_nonneg _
  have hvolg :
      ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal ≤ vol := by
    simpa only [vol] using
      (volumeReal_cross (I := I) (M := M) gBase g hEq).1
  have hidJet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 2 2 j
        (slotInsertEndoCc (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g g))‖ ^ 2) ≤ 27 * vol := by
    refine (idSlotJet (I := I) (M := M) hDim g).trans ?_
    exact mul_le_mul_of_nonneg_left hvolg (by norm_num)
  have hcoefPt : 2 * (Cinv ^ 2 + 27) ≤ K := by
    dsimp only [K]
    nlinarith
  have hcoefJet : 2 * (Cinv ^ 2 + 27 * vol) ≤ K := by
    dsimp only [K]
    nlinarith
  constructor
  · intro x
    rw [fullSlotSplit (I := I) (M := M) g gm,
      SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
    calc
      _ ≤ 2 * (riemannianFiberNormSq (I := I) (M := M) g 2 2 x
            ((inverseMetricDifferenceSlotCoefficient (I := I) g gm).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
            ((slotInsertEndoCc (I := I) (M := M) g 1
              (metricComparisonEndomorphismField (I := I) (M := M) g g)).toSection x)) :=
        by
          simpa only [mul_add] using
            (riemannianFiberNormSq_add_le (I := I) (M := M) g 2 2 x
              ((inverseMetricDifferenceSlotCoefficient (I := I) g gm).toSection x)
              ((slotInsertEndoCc (I := I) (M := M) g 1
                (metricComparisonEndomorphismField (I := I) (M := M) g g)).toSection x))
      _ ≤ 2 * ((Cinv * N) ^ 2 + 27) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
        · simpa only [N] using hinvPt x
        · exact idSlotPt (I := I) (M := M) hDim g x
      _ ≤ 2 * (Cinv ^ 2 + 27) * (1 + N) ^ 2 :=
        affineSq Cinv 27 N (by norm_num) hN
      _ ≤ K * (1 + N) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoefPt (sq_nonneg _)
      _ = (Real.sqrt K * (1 + N)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hK]
  · rw [fullSlotSplit (I := I) (M := M) g gm]
    calc
      _ ≤ 2 * ((∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (inverseMetricDifferenceSlotCoefficient (I := I) g gm)‖ ^ 2) +
          ∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 2 2 j
              (slotInsertEndoCc (I := I) (M := M) g 1
                (metricComparisonEndomorphismField (I := I) (M := M) g g))‖ ^ 2) :=
        iteratedCovGradNormSq_add_le (I := I) (M := M) g _ _
      _ ≤ 2 * ((Cinv * N) ^ 2 + 27 * vol) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ hidJet) (by norm_num)
        simpa only [N] using hinvJet
      _ ≤ 2 * (Cinv ^ 2 + 27 * vol) * (1 + N) ^ 2 :=
        affineSq Cinv (27 * vol) N (mul_nonneg (by norm_num) hvol) hN
      _ ≤ K * (1 + N) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoefJet (sq_nonneg _)
      _ = (Real.sqrt K * (1 + N)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hK]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
