import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.JetProduct
import DifferentialGeometry.Analysis.Estimates.ProductBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.SymmetricRaiseEndomorphism
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.FirstOrderCoefficientLipschitzBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.MoserTameBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.TopOrderSeparatedCurvatureBounds

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis (sq_add_sq_le_sq_add_of_nonneg)
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq
  covariantJetNormSq_add_le covariantJetNormSq_mono covariantJetNormSq_neg
  covariantJetNormSq_nonneg covariantJetNormSq_slotExtend_le
  exists_covariantJetNormSq_three_operatorFieldComposition_tame_bound
  exists_covariantJetNormSq_two_operatorFieldComposition_le)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Elliptic (integrable_riemannianFiberNormSq_toSection
  riemannianFiberNormSq)
open DifferentialGeometry.Analysis.Sobolev (metricComparisonDifferenceEndomorphismField iteratedCovGrad
  inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc normSq_le_integral_of_pointwise_fiberNormSq_le_rs
  riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongr_both_eq riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
  tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral (ccOperatorFieldComp operatorFieldComposition_sub_right
  metricComparisonEndomorphismField inverseMetricDifferenceSlotCoefficient norm_iteratedCovGrad_domDomCongrSection pureTrace pureTrace_split
  riemannianFiberNormSq_iteratedCovGrad_slotExtend_le
  riemannianFiberNormSq_ccTensor02Symm_zero_le_fibreSmall slotExtend
  ccTensor02Symm_eq_self)
open DifferentialGeometry.Geometry.Connection (endoSlotZeroCcTensor slotInsertEndoCc)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

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
    F hF (fun x => riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
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

private theorem covariantJetNormSq_slotInsertEndoCc_le
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
      Finset.sum_le_sum fun i _ => iteratedCovGrad_slotInsertEndoCc_norm_sq_le (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

theorem covariantJetNormSq_slotInsert_symmRaiseEndo_le
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (D : SmoothCcTensor g 0 2)
    (hD : ccTensor02Symm (I := I) (M := M) g D = D) :
    covariantJetNormSq (I := I) (M := M) g m
        (slotInsertEndoCc (I := I) (M := M) g 1
          (symmRaiseEndo (I := I) (M := M) g D)) ≤
      (Module.finrank ℝ E : ℝ) *
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
              (ccTensor02Symm (I := I) (M := M) g D))) =
        covariantJetNormSq (I := I) (M := M) g m
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (ccTensor02Symm (I := I) (M := M) g D)) := by
          unfold covariantJetNormSq
          apply Finset.sum_congr rfl
          intro q _
          rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
            (I := I) (M := M) g 0
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1)
              (ccTensor02Symm (I := I) (M := M) g D)) q]
      _ = covariantJetNormSq (I := I) (M := M) g m
          (ccTensor02Symm (I := I) (M := M) g D) := by
        unfold covariantJetNormSq
        apply Finset.sum_congr rfl
        intro q _
        rw [norm_iteratedCovGrad_domDomCongrSection
          (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g D) q]
      _ = covariantJetNormSq (I := I) (M := M) g m D := by rw [hD]
  have hslot := covariantJetNormSq_slotInsertEndoCc_le (I := I) (M := M) g 1 m
    (symmRaiseEndo (I := I) (M := M) g D)
  rw [h0] at hslot
  simpa only [pow_one] using hslot

private theorem exists_slotInsertEndoCc_metricComparisonEndomorphismField_covariantJetNormSq_bound
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
      covariantJetNormSq (I := I) (M := M) g 3
          (slotInsertEndoCc (I := I) (M := M) g 1
            (metricComparisonEndomorphismField (I := I) (M := M) g gm)) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
  obtain ⟨Aw, Sw, hwin⟩ :=
    HasMoserTameBounds.metricComparisonEndomorphismSlot (I := I) (M := M) g 1 hδ₀0 hδ₀
  let K : ℝ := |Aw 3|
  refine ⟨K, abs_nonneg _, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
  have hsymm : ccTensor02Symm (I := I) (M := M) g P = P :=
    ccTensor02Symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (P.toSection x) ≤
        ((Module.finrank ℝ E : ℝ) * δ₀) ^ 2 := by
    intro x
    rw [← hsymm]
    exact riemannianFiberNormSq_ccTensor02Symm_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  have hpert : IsControlledMetricPerturbation (I := I) (M := M) g gm P P δ₀ :=
    ⟨⟨δ, hδ0, hδ_le, hδ⟩, htie, hsup, fun _ => le_rfl⟩
  have hj := (hwin P gm P hpert).2.2 3
  have hfac : 0 ≤ 1 + covariantJetNormSq (I := I) (M := M) g 3 P := by
    have := covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g P
    linarith
  exact hj.trans (mul_le_mul_of_nonneg_right (le_abs_self (Aw 3))
    hfac)

theorem exists_inverseMetricDifferenceSlotCoefficient_covariantJetNormSq_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 3
          (inverseMetricDifferenceSlotCoefficient (I := I) g gT -
            inverseMetricDifferenceSlotCoefficient (I := I) g gU) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨Bh, hBh, hbdd⟩ :=
    RicciDeTurckLowOrder.full_slot_sobolev_two_bound
      (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kh, hKh, hh3⟩ :=
    exists_slotInsertEndoCc_metricComparisonEndomorphismField_covariantJetNormSq_bound (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨C2, hC2, happ2⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 2 2
  obtain ⟨C3, hC3, happ3⟩ := exists_covariantJetNormSq_three_operatorFieldComposition_tame_bound (I := I) (M := M) hDim g 2 2 2
  let fr : ℝ := Module.finrank ℝ E
  let Z3 : ℝ → ℝ := fun R => C3 ^ 2 * fr * (Bh R) ^ 4
  let Z2 : ℝ → ℝ := fun R => C3 * Kh * fr * (Bh R) ^ 2 * (C2 + C3)
  let Z : ℝ → ℝ := fun R => Z3 R + Z2 R
  let B : ℝ → ℝ := fun R => Real.sqrt (Z R)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hZ3 : ∀ R : ℝ, 0 ≤ Z3 R := by
    intro R
    dsimp only [Z3]
    positivity
  have hZ2 : ∀ R : ℝ, 0 ≤ Z2 R := by
    intro R
    dsimp only [Z2]
    positivity
  have hZ : ∀ R : ℝ, 0 ≤ Z R := by
    intro R
    exact add_nonneg (hZ3 R) (hZ2 R)
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  let LT : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gT)
  let LU : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gU)
  let P : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (symmRaiseEndo (I := I) (M := M) g (T - U))
  let X : SmoothCcTensor g 2 2 := ccOperatorFieldComp (I := I) (M := M) g 2 2 2 P LT
  let Y : SmoothCcTensor g 2 2 := ccOperatorFieldComp (I := I) (M := M) g 2 2 2 LU X
  let H3 : ℝ := Kh * (1 + A ^ 2)
  have hsymm : ccTensor02Symm (I := I) (M := M) g (T - U) = T - U := by
    rw [ccTensor02Symm_sub,
      ccTensor02Symm_eq_self (I := I) (M := M) g T hT,
      ccTensor02Symm_eq_self (I := I) (M := M) g U hU]
  have hLT2 : covariantJetNormSq (I := I) (M := M) g 2 LT ≤ (Bh R) ^ 2 := by
    simpa only [LT] using hbdd gT T hT hTtie hδT_le hδT0 hδT R hR hT2
  have hLU2 : covariantJetNormSq (I := I) (M := M) g 2 LU ≤ (Bh R) ^ 2 := by
    simpa only [LU] using hbdd gU U hU hUtie hδU_le hδU0 hδU R hR hU2
  have hLT3 : covariantJetNormSq (I := I) (M := M) g 3 LT ≤ H3 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 3 LT ≤
          Kh * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) := by
        simpa only [LT] using hh3 gT T hT hTtie hδT_le hδT0 hδT
      _ ≤ H3 := mul_le_mul_of_nonneg_left (by linarith) hKh
  have hLU3 : covariantJetNormSq (I := I) (M := M) g 3 LU ≤ H3 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 3 LU ≤
          Kh * (1 + covariantJetNormSq (I := I) (M := M) g 3 U) := by
        simpa only [LU] using hh3 gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ H3 := mul_le_mul_of_nonneg_left (by linarith) hKh
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ fr * D2 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 P ≤
          fr * covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
        simpa only [P, fr] using
          covariantJetNormSq_slotInsert_symmRaiseEndo_le (I := I) (M := M) g 2 (T - U) hsymm
      _ ≤ fr * D2 ^ 2 := mul_le_mul_of_nonneg_left hTU2 hfr
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ fr * D3 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 3 P ≤
          fr * covariantJetNormSq (I := I) (M := M) g 3 (T - U) := by
        simpa only [P, fr] using
          covariantJetNormSq_slotInsert_symmRaiseEndo_le (I := I) (M := M) g 3 (T - U) hsymm
      _ ≤ fr * D3 ^ 2 := mul_le_mul_of_nonneg_left hTU3 hfr
  have hH3 : 0 ≤ H3 := mul_nonneg hKh (by positivity)
  have hX2 : covariantJetNormSq (I := I) (M := M) g 2 X ≤
      C2 * (fr * D2 ^ 2) * (Bh R) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 X ≤
          C2 * covariantJetNormSq (I := I) (M := M) g 2 P *
            covariantJetNormSq (I := I) (M := M) g 2 LT := by
        simpa only [X] using happ2 P LT
      _ ≤ C2 * (fr * D2 ^ 2) * covariantJetNormSq (I := I) (M := M) g 2 LT := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP2 hC2)
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g LT)
      _ ≤ C2 * (fr * D2 ^ 2) * (Bh R) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hLT2
          (mul_nonneg hC2 (mul_nonneg hfr (sq_nonneg D2)))
  have hX3 : covariantJetNormSq (I := I) (M := M) g 3 X ≤
      C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 + (fr * D2 ^ 2) * H3) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 3 X ≤
          C3 * (covariantJetNormSq (I := I) (M := M) g 3 P *
              covariantJetNormSq (I := I) (M := M) g 2 LT +
            covariantJetNormSq (I := I) (M := M) g 2 P *
              covariantJetNormSq (I := I) (M := M) g 3 LT) := by
        simpa only [X] using happ3 P LT
      _ ≤ C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 + (fr * D2 ^ 2) * H3) := by
        apply mul_le_mul_of_nonneg_left _ hC3
        exact add_le_add
          (mul_le_mul hP3 hLT2 (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g LT)
            (mul_nonneg hfr (sq_nonneg D3)))
          (mul_le_mul hP2 hLT3 (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g LT)
            (mul_nonneg hfr (sq_nonneg D2)))
  have hY3 : covariantJetNormSq (I := I) (M := M) g 3 Y ≤
      C3 * (H3 * (C2 * (fr * D2 ^ 2) * (Bh R) ^ 2) +
        (Bh R) ^ 2 *
          (C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 + (fr * D2 ^ 2) * H3))) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 3 Y ≤
          C3 * (covariantJetNormSq (I := I) (M := M) g 3 LU *
              covariantJetNormSq (I := I) (M := M) g 2 X +
            covariantJetNormSq (I := I) (M := M) g 2 LU *
              covariantJetNormSq (I := I) (M := M) g 3 X) := by
        simpa only [Y] using happ3 LU X
      _ ≤ C3 * (H3 * (C2 * (fr * D2 ^ 2) * (Bh R) ^ 2) +
          (Bh R) ^ 2 *
            (C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 + (fr * D2 ^ 2) * H3))) := by
        apply mul_le_mul_of_nonneg_left _ hC3
        exact add_le_add
          (mul_le_mul hLU3 hX2 (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g X) hH3)
          (mul_le_mul hLU2 hX3 (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g X)
            (sq_nonneg (Bh R)))
  have hYfold : covariantJetNormSq (I := I) (M := M) g 3 Y ≤
      Z R * (D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2) := by
    have heq :
        C3 * (H3 * (C2 * (fr * D2 ^ 2) * (Bh R) ^ 2) +
          (Bh R) ^ 2 *
            (C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 + (fr * D2 ^ 2) * H3))) =
        Z3 R * D3 ^ 2 + Z2 R * ((1 + A ^ 2) * D2 ^ 2) := by
      simp only [H3, Z3, Z2]
      ring
    rw [heq] at hY3
    refine hY3.trans ?_
    calc
      Z3 R * D3 ^ 2 + Z2 R * ((1 + A ^ 2) * D2 ^ 2) ≤
          Z3 R * (D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2) +
            Z2 R * (D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg D2)))
            (hZ3 R))
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg D3))
            (hZ2 R))
      _ = Z R * (D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2) := by
        simp only [Z]
        ring
  have hlin : D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2 ≤
      (D3 + D2 + A * D2) ^ 2 := by
    calc
      D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2 =
          (D3 ^ 2 + D2 ^ 2) + (A * D2) ^ 2 := by ring
      _ ≤ (D3 + D2) ^ 2 + (A * D2) ^ 2 := by
        exact add_le_add (sq_add_sq_le_sq_add_of_nonneg hD3 hD2) le_rfl
      _ ≤ (D3 + D2 + A * D2) ^ 2 :=
        sq_add_sq_le_sq_add_of_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)
  have hBsq : (B R) ^ 2 = Z R := by
    simpa only [B] using Real.sq_sqrt (hZ R)
  rw [invSlot_sub_factor (I := I) (M := M) g gT gU T U hTtie hUtie,
    covariantJetNormSq_neg (I := I) (M := M) g 3]
  have hYmain : covariantJetNormSq (I := I) (M := M) g 3 Y ≤
      Z R * (D3 + D2 + A * D2) ^ 2 :=
    hYfold.trans (mul_le_mul_of_nonneg_left hlin (hZ R))
  calc
    covariantJetNormSq (I := I) (M := M) g 3
        (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
          (slotInsertEndoCc (I := I) (M := M) g 1
            (metricComparisonEndomorphismField (I := I) (M := M) g gU))
          (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
            (slotInsertEndoCc (I := I) (M := M) g 1
              (symmRaiseEndo (I := I) (M := M) g (T - U)))
            (slotInsertEndoCc (I := I) (M := M) g 1
              (metricComparisonEndomorphismField (I := I) (M := M) g gT)))) =
      covariantJetNormSq (I := I) (M := M) g 3 Y := rfl
    _ ≤ Z R * (D3 + D2 + A * D2) ^ 2 := hYmain
    _ = (B R * (D3 + D2 + A * D2)) ^ 2 := by
      rw [mul_pow, hBsq]

private theorem iteratedCovGrad_slotInsertEndoCc_succ_norm_sq_le
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g (s + 2) (s + 2) i
        (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 := by
  let F : M → ℝ := fun x =>
    (Module.finrank ℝ E : ℝ) *
      riemannianFiberNormSq (I := I) (M := M) g
        (s + 1) ((s + 1) + i) x
        ((iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g (s + 1) ((s + 1) + i)
      (iteratedCovGrad (I := I) g (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g s Λ))).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g
          (s + 2) ((s + 2) + i) x
          ((iteratedCovGrad (I := I) g (s + 2) (s + 2) i
            (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ)).toSection x) ≤
        F x := by
    intro x
    have heq :
        riemannianFiberNormSq (I := I) (M := M) g
            (s + 2) ((s + 2) + i) x
            ((iteratedCovGrad (I := I) g (s + 2) (s + 2) i
              (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g
            (s + 2) ((s + 2) + i) x
            ((iteratedCovGrad (I := I) g (s + 2) (s + 2) i
              (slotExtend (I := I) (M := M) g (s + 1) (s + 1)
                (slotInsertEndoCc (I := I) (M := M) g s Λ))).toSection x) := by
      rw [DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower.slotInsertEndoCc_succ_eq_reindex_slotExtend
        (I := I) (M := M) g s Λ]
      simpa only [Nat.add_assoc] using
        riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongr_both_eq
          (I := I) (M := M) g (s + 2) (s + 2)
          (Equiv.swap (0 : Fin (s + 2)) 1)
          (Equiv.swap (0 : Fin (s + 2)) 1)
          (slotExtend (I := I) (M := M) g (s + 1) (s + 1)
            (slotInsertEndoCc (I := I) (M := M) g s Λ)) i x
    rw [heq]
    simpa only [F, Nat.add_assoc] using
      riemannianFiberNormSq_iteratedCovGrad_slotExtend_le
        (I := I) (M := M) g (s + 1) (s + 1)
        (slotInsertEndoCc (I := I) (M := M) g s Λ) i x
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (s + 2) ((s + 2) + i)
    (iteratedCovGrad (I := I) g (s + 2) (s + 2) i
      (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ)) F hF hpt
  have hint :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g
          (s + 1) ((s + 1) + i) x
          ((iteratedCovGrad (I := I) g (s + 1) (s + 1) i
            (slotInsertEndoCc (I := I) (M := M) g s Λ)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g (s + 1) ((s + 1) + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

theorem covariantJetNormSq_slotInsertEndoCc_succ_le
    (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    covariantJetNormSq (I := I) (M := M) g m
        (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g m
          (slotInsertEndoCc (I := I) (M := M) g s Λ) := by
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (s + 2) (s + 2) i
          (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range (m + 1), (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => iteratedCovGrad_slotInsertEndoCc_succ_norm_sq_le (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) *
        ∑ i ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
            (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

namespace RicciDeTurckLowOrder

theorem exists_pureTrace_one_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 3
          (pureTrace (I := I) (M := M) g gT 1 -
            pureTrace (I := I) (M := M) g gU 1) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨Bi, hBi, hinv⟩ :=
    exists_inverseMetricDifferenceSlotCoefficient_covariantJetNormSq_tame_difference_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨C, hC, happ⟩ := exists_covariantJetNormSq_three_operatorFieldComposition_tame_bound (I := I) (M := M) hDim g 3 3 1
  let F₁ : SmoothCcTensor g 3 1 := cometricDoubleTraceField (I := I) g 1
  let J2 : ℝ := covariantJetNormSq (I := I) (M := M) g 2 F₁
  let J3 : ℝ := covariantJetNormSq (I := I) (M := M) g 3 F₁
  let fr : ℝ := Module.finrank ℝ E
  let Z : ℝ := C * fr * (J3 + J2)
  let B : ℝ → ℝ := fun R => Real.sqrt Z * Bi R
  have hJ2 : 0 ≤ J2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g F₁
  have hJ3 : 0 ≤ J3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g F₁
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hZ : 0 ≤ Z := mul_nonneg (mul_nonneg hC hfr) (add_nonneg hJ3 hJ2)
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (Real.sqrt_nonneg _) (hBi R hR)
  · intro gT gU T U hT hU hTtie hUtie
      δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
      R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
    let Q : ℝ := D3 + D2 + A * D2
    let Λ := metricComparisonDifferenceEndomorphismField (I := I) g gT -
      metricComparisonDifferenceEndomorphismField (I := I) g gU
    let D₁ : SmoothCcTensor g 2 2 :=
      slotInsertEndoCc (I := I) (M := M) g 1 Λ
    let D₂ : SmoothCcTensor g 3 3 :=
      slotInsertEndoCc (I := I) (M := M) g 2 Λ
    have hQ : 0 ≤ Q :=
      add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)
    have hD₁eq : D₁ =
        inverseMetricDifferenceSlotCoefficient (I := I) g gT -
          inverseMetricDifferenceSlotCoefficient (I := I) g gU := by
      dsimp only [D₁, Λ]
      rw [slotInsertEndoCc_sub]
      change endoSlotZeroCcTensor (I := I) (M := M) g 1
          (metricComparisonDifferenceEndomorphismField (I := I) g gT) -
          endoSlotZeroCcTensor (I := I) (M := M) g 1
            (metricComparisonDifferenceEndomorphismField (I := I) g gU) =
        inverseMetricDifferenceSlotCoefficient (I := I) g gT - inverseMetricDifferenceSlotCoefficient (I := I) g gU
      rw [← inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc (I := I) g gT,
        ← inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc (I := I) g gU]
    have hD₁3 : covariantJetNormSq (I := I) (M := M) g 3 D₁ ≤
        (Bi R * Q) ^ 2 := by
      rw [hD₁eq]
      simpa only [Q] using
        hinv gT gU T U hT hU hTtie hUtie
          hδT_le hδT0 hδT hδU_le hδU0 hδU
          R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
    have hD₁2 : covariantJetNormSq (I := I) (M := M) g 2 D₁ ≤
        (Bi R * Q) ^ 2 :=
      (covariantJetNormSq_mono (I := I) (M := M) g (by omega : 2 ≤ 3) D₁).trans hD₁3
    have hD₂2 : covariantJetNormSq (I := I) (M := M) g 2 D₂ ≤
        fr * (Bi R * Q) ^ 2 := by
      calc
        covariantJetNormSq (I := I) (M := M) g 2 D₂ ≤
            fr * covariantJetNormSq (I := I) (M := M) g 2 D₁ := by
          simpa only [D₂, D₁, fr] using
            covariantJetNormSq_slotInsertEndoCc_succ_le (I := I) (M := M) g 1 2 Λ
        _ ≤ fr * (Bi R * Q) ^ 2 := mul_le_mul_of_nonneg_left hD₁2 hfr
    have hD₂3 : covariantJetNormSq (I := I) (M := M) g 3 D₂ ≤
        fr * (Bi R * Q) ^ 2 := by
      calc
        covariantJetNormSq (I := I) (M := M) g 3 D₂ ≤
            fr * covariantJetNormSq (I := I) (M := M) g 3 D₁ := by
          simpa only [D₂, D₁, fr] using
            covariantJetNormSq_slotInsertEndoCc_succ_le (I := I) (M := M) g 1 3 Λ
        _ ≤ fr * (Bi R * Q) ^ 2 := mul_le_mul_of_nonneg_left hD₁3 hfr
    have htrace :
        pureTrace (I := I) (M := M) g gT 1 -
            pureTrace (I := I) (M := M) g gU 1 =
          ccOperatorFieldComp (I := I) (M := M) g 3 3 1 F₁ D₂ := by
      rw [pureTrace_split (I := I) (M := M) g gT 1,
        pureTrace_split (I := I) (M := M) g gU 1]
      calc
        (ccOperatorFieldComp (I := I) (M := M) g 3 3 1 F₁
              (slotInsertEndoCc (I := I) (M := M) g 2
                (metricComparisonDifferenceEndomorphismField (I := I) g gT)) + F₁) -
            (ccOperatorFieldComp (I := I) (M := M) g 3 3 1 F₁
              (slotInsertEndoCc (I := I) (M := M) g 2
                (metricComparisonDifferenceEndomorphismField (I := I) g gU)) + F₁) =
          ccOperatorFieldComp (I := I) (M := M) g 3 3 1 F₁
              (slotInsertEndoCc (I := I) (M := M) g 2
                (metricComparisonDifferenceEndomorphismField (I := I) g gT)) -
            ccOperatorFieldComp (I := I) (M := M) g 3 3 1 F₁
              (slotInsertEndoCc (I := I) (M := M) g 2
                (metricComparisonDifferenceEndomorphismField (I := I) g gU)) := by abel
        _ = ccOperatorFieldComp (I := I) (M := M) g 3 3 1 F₁ D₂ := by
          rw [← operatorFieldComposition_sub_right]
          congr 1
          dsimp only [D₂, Λ]
          rw [slotInsertEndoCc_sub]
    rw [htrace]
    have hmain : covariantJetNormSq (I := I) (M := M) g 3
        (ccOperatorFieldComp (I := I) (M := M) g 3 3 1 F₁ D₂) ≤
          Z * (Bi R * Q) ^ 2 := by
      calc
        covariantJetNormSq (I := I) (M := M) g 3
            (ccOperatorFieldComp (I := I) (M := M) g 3 3 1 F₁ D₂) ≤
          C * (J3 * covariantJetNormSq (I := I) (M := M) g 2 D₂ +
            J2 * covariantJetNormSq (I := I) (M := M) g 3 D₂) := by
              simpa only [J2, J3] using happ F₁ D₂
        _ ≤ C * (J3 * (fr * (Bi R * Q) ^ 2) +
            J2 * (fr * (Bi R * Q) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hC
          exact add_le_add
            (mul_le_mul_of_nonneg_left hD₂2 hJ3)
            (mul_le_mul_of_nonneg_left hD₂3 hJ2)
        _ = Z * (Bi R * Q) ^ 2 := by
          simp only [Z]
          ring
    calc
      covariantJetNormSq (I := I) (M := M) g 3
          (ccOperatorFieldComp (I := I) (M := M) g 3 3 1 F₁ D₂) ≤
        Z * (Bi R * Q) ^ 2 := hmain
      _ = (B R * Q) ^ 2 := by
        dsimp only [B]
        calc
          Z * (Bi R * Q) ^ 2 =
              (Real.sqrt Z) ^ 2 * (Bi R * Q) ^ 2 := by
            rw [Real.sq_sqrt hZ]
          _ = (Real.sqrt Z * Bi R * Q) ^ 2 := by ring
      _ = (B R * (D3 + D2 + A * D2)) ^ 2 := by
        simp only [Q]

end RicciDeTurckLowOrder

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
