import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.LowOrderCoefficientBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorFieldJetProduct
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJetNaturality

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
  covariantJetNormSq_add_le covariantJetNormSq_nonneg covariantJetNormSq_smul
  covariantJetNormSq_rsDomDomCongrSection covariantJetNormSq_slotExtend_le
  covariantJetNormSq_sum_six_le exists_covariantJetNormSq_two_operatorFieldComposition_le)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Sobolev (metricConnectionDifferenceLoweredCoefficient)
open DifferentialGeometry.Analysis.Spectral
  (ccOperatorFieldComp operatorFieldComposition_sub_left operatorFieldComposition_sub_right ccTensorToHs ccTensorToHs_smul
    metricComparisonEndomorphismField permCoeff slotExtend slotExtend_sub slotExtendIter
    symmS_eq_self_of_ccTensorBilin_symm)
open DifferentialGeometry.Geometry.Connection
  (slotInsertEndoCc slotInsertEndoCc_add)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

private lemma weighted_three_term_le_product_sum
    (l0 l1 D3 D2 A N : ℝ)
    (hl0 : 0 ≤ l0) (hl1 : 0 ≤ l1) (hD3 : 0 ≤ D3)
    (hD2 : 0 ≤ D2) (hA : 0 ≤ A) (hN : 0 ≤ N) :
    l0 * D3 + l1 * D2 + l1 * A * D2 ≤
      (l0 + l1) * (D3 + D2 + A * D2 + N) := by
  nlinarith only [mul_nonneg hl0 hD2,
    mul_nonneg hl0 (mul_nonneg hA hD2), mul_nonneg hl0 hN,
    mul_nonneg hl1 hD3, mul_nonneg hl1 hN]

private lemma mul_le_mul_one_add
    (l A D : ℝ) (hl : 0 ≤ l) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    l * D ≤ l * (1 + A) * D := by
  calc
    l * D = (l * 1) * D := by ring
    _ ≤ (l * (1 + A)) * D :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hA) hl) hD

private lemma add_le_four_term_sum
    (D3 D2 A N : ℝ) (hD3 : 0 ≤ D3) (hD2 : 0 ≤ D2) (hA : 0 ≤ A) :
    D2 + N ≤ D3 + D2 + A * D2 + N := by
  nlinarith only [hD3, mul_nonneg hA hD2]

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

theorem exists_lieCorrectionZeroVectorBundleDerivativeCoefficient_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρt, Ct, hρt, hCt, htrace⟩ :=
    RicciDeTurckLowOrder.trace_one_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρc, Cc, hρc, hCc, hconn⟩ :=
    RicciDeTurckLowOrder.low_connection_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Bm, hBm, hmcd⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)
  obtain ⟨Kr, hKr, hriem⟩ :=
    exists_reindexedCometricDoubleTrace_covariantJetNormSq_two_low_bound (I := I) (M := M) g
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)
  obtain ⟨C0, hC0, happ0⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 1
  obtain ⟨C1, hC1, happ1⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 1 1
  obtain ⟨C2, hC2, happ2⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 1 4
  obtain ⟨C3, hC3, happ3⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 4 2
  let ρ : ℝ := min ρt ρc
  let fr : ℝ := Module.finrank ℝ E
  let Z0 : ℝ := C0 * Ct ^ 2 * Cc ^ 2
  let Z1 : ℝ → ℝ := fun R => C1 * R ^ 2 * Z0
  let Z2 : ℝ → ℝ := fun R => C2 * (fr * Bm R ^ 2) * Z1 R
  let Zr : ℝ → ℝ := fun R => Kr * (1 + R ^ 2)
  let L : ℝ → ℝ := fun R => 4 * C3 * Zr R * Z2 R
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hρ : 0 < ρ := lt_min hρt hρc
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hZ0 : 0 ≤ Z0 :=
    mul_nonneg (mul_nonneg hC0 (sq_nonneg Ct)) (sq_nonneg Cc)
  have hZ1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z1 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC1 (sq_nonneg R)) hZ0
  have hZ2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z2 R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg hC2 (mul_nonneg hfr (sq_nonneg (Bm R))))
      (hZ1 R hR)
  have hZr : ∀ R : ℝ, 0 ≤ R → 0 ≤ Zr R := by
    intro R hR
    exact mul_nonneg hKr (add_nonneg (by norm_num) (sq_nonneg R))
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hC3) (hZr R hR))
      (hZ2 R hR)
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P W hP htie δ hδ_le hδ0 hδP
    R A hR hA hP2 hP3 hW2 hPn
  let S : ℝ := (1 + A) ^ 2
  have hS : 0 ≤ S := sq_nonneg _
  have hPnt : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) P‖ ≤ ρt := hPn.trans (min_le_left _ _)
  have hPnc : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) P‖ ≤ ρc := hPn.trans (min_le_right _ _)
  have htr : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedPureTrace (I := I) (M := M) g gm 1 (Equiv.refl _)) ≤ Ct ^ 2 := by
    rw [covariantJetNormSq_reindexedPureTrace]
    exact htrace P gm htie hPnt
  have hc : covariantJetNormSq (I := I) (M := M) g 2
      (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm) ≤ Cc ^ 2 :=
    hconn P gm htie hPnc
  have hz0 : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 1
        (reindexedPureTrace (I := I) (M := M) g gm 1 (Equiv.refl _))
        (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)) ≤ Z0 := by
    refine (happ0 _ _).trans ?_
    simpa only [Z0] using
      mul_le_mul (mul_le_mul_of_nonneg_left htr hC0) hc
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hC0 (sq_nonneg Ct))
  have hw : covariantJetNormSq (I := I) (M := M) g 2
      (cometricRaiseSlot0Field (I := I) (M := M) g 0 W) ≤ R ^ 2 := by
    rw [covariantJetNormSq_cometricRaiseSlot0Field (I := I) (M := M) g 0 2 W]
    exact hW2
  have hz1 : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 1 1
        (cometricRaiseSlot0Field (I := I) (M := M) g 0 W)
        (ccOperatorFieldComp (I := I) (M := M) g 3 3 1
          (reindexedPureTrace (I := I) (M := M) g gm 1 (Equiv.refl _))
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm))) ≤ Z1 R := by
    refine (happ1 _ _).trans ?_
    simpa only [Z1] using
      mul_le_mul (mul_le_mul_of_nonneg_left hw hC1) hz0
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hC1 (sq_nonneg R))
  have hm0 : covariantJetNormSq (I := I) (M := M) g 2
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g) ≤
        Bm R ^ 2 * S := by
    calc
      _ ≤ (Bm R * (1 + A)) ^ 2 :=
        hmcd gm P hP htie hδ_le hδ0 hδP
          R A hR hA hP2 hP3
      _ = Bm R ^ 2 * S := by simp only [S]; ring
  have hvm : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gm) ≤
        fr * Bm R ^ 2 * S := by
    refine (covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g gm).trans ?_
    calc
      (Module.finrank ℝ E : ℝ) *
          covariantJetNormSq (I := I) (M := M) g 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g) ≤
        fr * (Bm R ^ 2 * S) :=
          mul_le_mul_of_nonneg_left hm0 hfr
      _ = fr * Bm R ^ 2 * S := by ring
  have hz2 : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 1 4
        (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gm)
        (ccOperatorFieldComp (I := I) (M := M) g 3 1 1
          (cometricRaiseSlot0Field (I := I) (M := M) g 0 W)
          (ccOperatorFieldComp (I := I) (M := M) g 3 3 1
            (reindexedPureTrace (I := I) (M := M) g gm 1 (Equiv.refl _))
            (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)))) ≤
        Z2 R * S := by
    refine (happ2 _ _).trans ?_
    have hmul := mul_le_mul
      (mul_le_mul_of_nonneg_left hvm hC2) hz1
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hC2
        (mul_nonneg (mul_nonneg hfr (sq_nonneg (Bm R))) hS))
    refine hmul.trans_eq ?_
    simp only [Z2]
    ring
  have hr : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedCometricDoubleTrace (I := I) (M := M) g gm) ≤ Zr R := by
    refine (hriem gm P hP htie hδ_le hδ0 hδP).trans ?_
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hP2) hKr
  have hcore : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g gm W) ≤
        C3 * Zr R * (Z2 R * S) := by
    rw [lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient]
    refine (happ3 _ _).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hr hC3) hz2
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hC3 (hZr R hR))
  rw [lieCorrectionZeroVectorBundleDerivativeCoefficient, covariantJetNormSq_smul]
  norm_num
  refine (mul_le_mul_of_nonneg_left hcore (by norm_num)).trans ?_
  calc
    4 * (C3 * Zr R * (Z2 R * S)) = L R * S := by
      simp only [L]
      ring
    _ = (B R * (1 + A)) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      simpa only [S, mul_pow] using
        congrArg (fun x : ℝ => x * (1 + A) ^ 2) hBR.symm
    _ ≤ (B R * (1 + A)) ^ 2 := le_rfl

theorem covariantJetNormSq_slotExtendIter_three_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtendIter (I := I) (M := M) g r s 3 F) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        covariantJetNormSq (I := I) (M := M) g 2 F := by
  let fr : ℝ := Module.finrank ℝ E
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  simp only [slotExtendIter, Nat.add_zero]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g (r + 2) (s + 2)
          (slotExtend (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s F))) ≤
      fr * covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s F)) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g (r + 2) (s + 2) _
    _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g r s F)) :=
      mul_le_mul_of_nonneg_left
        (covariantJetNormSq_slotExtend_le (I := I) (M := M) g (r + 1) (s + 1) _) hfr
    _ ≤ fr * (fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 F)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g r s F) hfr) hfr
    _ = fr ^ 3 * covariantJetNormSq (I := I) (M := M) g 2 F := by ring

theorem exists_tensorThreeTwoProductCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 2
          (tensorThreeTwoProductCoefficient (I := I) (M := M) g W) ≤
        C * covariantJetNormSq (I := I) (M := M) g 2 W := by
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 5 5
  let J : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g tensorThreeTwoBlockPermutation)
  let fr : ℝ := Module.finrank ℝ E
  let C : ℝ := Ca * J * fr ^ 3
  have hJ : 0 ≤ J := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hCa hJ) (pow_nonneg hfr 3)
  refine ⟨C, hC, ?_⟩
  intro W
  rw [tensorThreeTwoProductCoefficient]
  refine (happ _ _).trans ?_
  have hs := covariantJetNormSq_slotExtendIter_three_le (I := I) (M := M) g 0 2 W
  have hmul := mul_le_mul_of_nonneg_left hs (mul_nonneg hCa hJ)
  refine hmul.trans_eq ?_
  simp only [J, fr, C]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem slotExtendIter_sub
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

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem tensorThreeTwoProductCoefficient_sub
    (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) :
    tensorThreeTwoProductCoefficient (I := I) (M := M) g (A - B) =
      tensorThreeTwoProductCoefficient (I := I) (M := M) g A -
        tensorThreeTwoProductCoefficient (I := I) (M := M) g B := by
  rw [tensorThreeTwoProductCoefficient, tensorThreeTwoProductCoefficient, tensorThreeTwoProductCoefficient, ← operatorFieldComposition_sub_right,
    ← slotExtendIter_sub]

theorem exists_lieCorrectionZeroMixedConnectionDerivativeCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm g W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρ2, Ct2, hρ2, hCt2, htrace2⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρ3, Ct3, hρ3, hCt3, htrace3⟩ :=
    RicciDeTurckLowOrder.trace_three_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρ4, Ct4, hρ4, hCt4, htrace4⟩ :=
    RicciDeTurckLowOrder.trace_four_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Bm, hBm, hmcd⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)
  obtain ⟨Cp, hCp, hprod⟩ := exists_tensorThreeTwoProductCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨C0, hC0, happ0⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 5
  obtain ⟨C1, hC1, happ1⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 5 3
  obtain ⟨C2, hC2, happ2⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 6
  obtain ⟨C3, hC3, happ3⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 6 4
  obtain ⟨C4, hC4, happ4⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 4 2
  let ρ : ℝ := min ρ2 (min ρ3 ρ4)
  let fr : ℝ := Module.finrank ℝ E
  let Jm : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g)
  let Zp : ℝ → ℝ := fun R => Cp * R ^ 2
  let Z0 : ℝ → ℝ := fun R => C0 * Zp R * Jm
  let Z1 : ℝ → ℝ := fun R => C1 * Ct3 ^ 2 * Z0 R
  let Zm : ℝ → ℝ := fun R => fr ^ 3 * Bm R ^ 2
  let Z2 : ℝ → ℝ := fun R => C2 * Zm R * Z1 R
  let Z3 : ℝ → ℝ := fun R => C3 * Ct4 ^ 2 * Z2 R
  let Q : ℝ → ℝ := fun R => C4 * Ct2 ^ 2 * Z3 R
  let L : ℝ → ℝ := fun R => 16 * Q R
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hρ : 0 < ρ := lt_min hρ2 (lt_min hρ3 hρ4)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hJm : 0 ≤ Jm := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hZp : ∀ R : ℝ, 0 ≤ R → 0 ≤ Zp R := by
    intro R hR
    exact mul_nonneg hCp (sq_nonneg R)
  have hZ0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z0 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC0 (hZp R hR)) hJm
  have hZ1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z1 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC1 (sq_nonneg Ct3)) (hZ0 R hR)
  have hZm : ∀ R : ℝ, 0 ≤ R → 0 ≤ Zm R := by
    intro R hR
    exact mul_nonneg (pow_nonneg hfr 3) (sq_nonneg (Bm R))
  have hZ2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z2 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC2 (hZm R hR)) (hZ1 R hR)
  have hZ3 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z3 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC3 (sq_nonneg Ct4)) (hZ2 R hR)
  have hQ : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC4 (sq_nonneg Ct2)) (hZ3 R hR)
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num) (hQ R hR)
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P W hP htie δ hδ_le hδ0 hδP
    R A hR hA hP2 hP3 hW2 hPn
  let S : ℝ := (1 + A) ^ 2
  have hS : 0 ≤ S := sq_nonneg _
  have hPn2 : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) P‖ ≤ ρ2 := hPn.trans (min_le_left _ _)
  have hPn3 : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) P‖ ≤ ρ3 :=
    hPn.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hPn4 : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) P‖ ≤ ρ4 :=
    hPn.trans ((min_le_right _ _).trans (min_le_right _ _))
  have ht2 : ∀ σ : Equiv.Perm (Fin 4),
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g gm 2 σ) ≤ Ct2 ^ 2 := by
    intro σ
    rw [covariantJetNormSq_reindexedPureTrace]
    exact htrace2 P gm htie hPn2
  have ht3 : ∀ σ : Equiv.Perm (Fin 5),
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g gm 3 σ) ≤ Ct3 ^ 2 := by
    intro σ
    rw [covariantJetNormSq_reindexedPureTrace]
    exact htrace3 P gm htie hPn3
  have ht4 : ∀ σ : Equiv.Perm (Fin 6),
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g gm 4 σ) ≤ Ct4 ^ 2 := by
    intro σ
    rw [covariantJetNormSq_reindexedPureTrace]
    exact htrace4 P gm htie hPn4
  have hp : covariantJetNormSq (I := I) (M := M) g 2
      (tensorThreeTwoProductCoefficient (I := I) (M := M) g W) ≤ Zp R := by
    refine (hprod W).trans ?_
    exact mul_le_mul_of_nonneg_left hW2 hCp
  have hm0 : covariantJetNormSq (I := I) (M := M) g 2
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g) ≤
        Bm R ^ 2 * S := by
    calc
      _ ≤ (Bm R * (1 + A)) ^ 2 :=
        hmcd gm P hP htie hδ_le hδ0 hδP
          R A hR hA hP2 hP3
      _ = Bm R ^ 2 * S := by simp only [S]; ring
  have hms : covariantJetNormSq (I := I) (M := M) g 2
      (slotExtendIter (I := I) (M := M) g 0 3 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g)) ≤
        Zm R * S := by
    refine (covariantJetNormSq_slotExtendIter_three_le (I := I) (M := M) g 0 3 _).trans ?_
    have hmul := mul_le_mul_of_nonneg_left hm0 (pow_nonneg hfr 3)
    refine hmul.trans_eq ?_
    simp only [Zm, fr]
    ring
  have hhalf : ∀ σlast : Equiv.Perm (Fin 4),
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm g W σlast) ≤
        Q R * S := by
    intro σlast
    let X0 : SmoothCcTensor g 3 5 :=
      ccOperatorFieldComp (I := I) (M := M) g 3 3 5
        (tensorThreeTwoProductCoefficient (I := I) (M := M) g W)
        (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g)
    let X1 : SmoothCcTensor g 3 3 :=
      ccOperatorFieldComp (I := I) (M := M) g 3 5 3
        (reindexedPureTrace (I := I) (M := M) g gm 3
          DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) X0
    let X2 : SmoothCcTensor g 3 6 :=
      ccOperatorFieldComp (I := I) (M := M) g 3 3 6
        (slotExtendIter (I := I) (M := M) g 0 3 3
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g)) X1
    let X3 : SmoothCcTensor g 3 4 :=
      ccOperatorFieldComp (I := I) (M := M) g 3 6 4
        (reindexedPureTrace (I := I) (M := M) g gm 4
          DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) X2
    let X4 : SmoothCcTensor g 3 2 :=
      ccOperatorFieldComp (I := I) (M := M) g 3 4 2
        (reindexedPureTrace (I := I) (M := M) g gm 2 σlast) X3
    have hx0 : covariantJetNormSq (I := I) (M := M) g 2 X0 ≤ Z0 R := by
      dsimp only [X0]
      refine (happ0 _ _).trans ?_
      simpa only [Z0, Jm] using
        mul_le_mul (mul_le_mul_of_nonneg_left hp hC0) le_rfl
          hJm (mul_nonneg hC0 (hZp R hR))
    have hx1 : covariantJetNormSq (I := I) (M := M) g 2 X1 ≤ Z1 R := by
      dsimp only [X1]
      refine (happ1 _ _).trans ?_
      simpa only [Z1] using
        mul_le_mul (mul_le_mul_of_nonneg_left
          (ht3 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) hC1) hx0
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g X0)
          (mul_nonneg hC1 (sq_nonneg Ct3))
    have hx2 : covariantJetNormSq (I := I) (M := M) g 2 X2 ≤ Z2 R * S := by
      dsimp only [X2]
      refine (happ2 _ _).trans ?_
      have hmul := mul_le_mul
        (mul_le_mul_of_nonneg_left hms hC2) hx1
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g X1)
        (mul_nonneg hC2 (mul_nonneg (hZm R hR) hS))
      refine hmul.trans_eq ?_
      simp only [Z2]
      ring
    have hx3 : covariantJetNormSq (I := I) (M := M) g 2 X3 ≤ Z3 R * S := by
      dsimp only [X3]
      refine (happ3 _ _).trans ?_
      have hmul := mul_le_mul
        (mul_le_mul_of_nonneg_left
          (ht4 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) hC3) hx2
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g X2)
        (mul_nonneg hC3 (sq_nonneg Ct4))
      refine hmul.trans_eq ?_
      simp only [Z3]
      ring
    have hx4 : covariantJetNormSq (I := I) (M := M) g 2 X4 ≤ Q R * S := by
      dsimp only [X4]
      refine (happ4 _ _).trans ?_
      have hmul := mul_le_mul
        (mul_le_mul_of_nonneg_left (ht2 σlast) hC4) hx3
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g X3)
        (mul_nonneg hC4 (sq_nonneg Ct2))
      refine hmul.trans_eq ?_
      simp only [Q]
      ring
    simpa only [lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient, X0, X1, X2, X3, X4] using hx4
  let Y0 := lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm g W
    DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  let Y1 := lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm g W
    (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
  have hy0 : covariantJetNormSq (I := I) (M := M) g 2 Y0 ≤ Q R * S :=
    hhalf DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  have hy1 : covariantJetNormSq (I := I) (M := M) g 2 Y1 ≤ Q R * S :=
    hhalf (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
  have hadd := covariantJetNormSq_add_le (I := I) (M := M) g 2 Y0 Y1
  have hsum : covariantJetNormSq (I := I) (M := M) g 2 (Y0 + Y1) ≤
      4 * (Q R * S) := by linarith
  rw [lieCorrectionZeroMixedConnectionDerivativeCoefficient, covariantJetNormSq_smul]
  norm_num
  change 4 * covariantJetNormSq (I := I) (M := M) g 2 (Y0 + Y1) ≤ _
  refine (mul_le_mul_of_nonneg_left hsum (by norm_num)).trans ?_
  calc
    4 * (4 * (Q R * S)) = L R * S := by simp only [L]; ring
    _ = (B R * (1 + A)) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      simpa only [S, mul_pow] using
        congrArg (fun x : ℝ => x * (1 + A) ^ 2) hBR.symm
    _ ≤ (B R * (1 + A)) ^ 2 := le_rfl

theorem exists_rotatedConnectionDifferenceLowOrderOperator_covariantJetNormSq_two_bound
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
            (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
              (permCoeff (I := I) (M := M) g (finRotate 3))
              (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)) ≤
          B ^ 2 := by
  obtain ⟨ρ, Cc, hρ, hCc, hconn⟩ :=
    RicciDeTurckLowOrder.low_connection_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨C0, hC0, happ0⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 3
  let J : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g (finRotate 3))
  let L : ℝ := C0 * J * Cc ^ 2
  let B : ℝ := Real.sqrt L
  have hJ : 0 ≤ J := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hL : 0 ≤ L :=
    mul_nonneg (mul_nonneg hC0 hJ) (sq_nonneg Cc)
  refine ⟨ρ, B, hρ, Real.sqrt_nonneg _, ?_⟩
  intro P gm htie hPn
  have hc : covariantJetNormSq (I := I) (M := M) g 2
      (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm) ≤ Cc ^ 2 :=
    hconn P gm htie hPn
  refine (happ0 _ _).trans ?_
  rw [show B ^ 2 = L by simpa only [B] using Real.sq_sqrt hL]
  simpa only [L, J] using
    mul_le_mul (le_refl (C0 * J)) hc
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hC0 hJ)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem metricComparisonSlotInsertion_eq
    (g gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) gm g) =
      slotInsertEndoCc (I := I) (M := M) g 2
          (metricComparisonEndomorphismField (I := I) (M := M) g g) +
        slotInsertEndoCc (I := I) (M := M) g 2
          (symmRaiseEndo (I := I) (M := M) g P) := by
  have hzero : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v = g.inner x u v +
        ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  have hrev := RicciDeTurckLowOrder.fullRev_sub (I := I) (M := M)
    g gm g P (0 : SmoothCcTensor g 0 2) htie hzero
  rw [sub_zero] at hrev
  have hfull :
      metricComparisonEndomorphismField (I := I) (M := M) gm g =
        metricComparisonEndomorphismField (I := I) (M := M) g g +
          symmRaiseEndo (I := I) (M := M) g P := by
    calc
      _ = symmRaiseEndo (I := I) (M := M) g P +
          metricComparisonEndomorphismField (I := I) (M := M) g g :=
        sub_eq_iff_eq_add.mp hrev
      _ = _ := add_comm _ _
  rw [hfull, slotInsertEndoCc_add]

theorem exists_metricComparisonSlotInsertion_covariantJetNormSq_two_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
          (slotInsertEndoCc (I := I) (M := M) g 2
            (metricComparisonEndomorphismField (I := I) (M := M) gm g)) ≤ B R ^ 2 := by
  let F₀ : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) g g)
  let J₀ : ℝ := covariantJetNormSq (I := I) (M := M) g 2 F₀
  let fr : ℝ := Module.finrank ℝ E
  let L : ℝ → ℝ := fun R => 2 * (J₀ + fr ^ 2 * R ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hJ₀ : 0 ≤ J₀ := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g F₀
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hL : ∀ R : ℝ, 0 ≤ L R := by
    intro R
    exact mul_nonneg (by norm_num)
      (add_nonneg hJ₀ (mul_nonneg (pow_nonneg hfr 2) (sq_nonneg R)))
  refine ⟨B, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P hP htie R hR hP2
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g P hP
  have hpert :
      covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 2
            (symmRaiseEndo (I := I) (M := M) g P)) ≤
        fr ^ 2 * R ^ 2 := by
    refine (covariantJetNormSq_slotInsertEndoCc_symmRaiseEndo_le (I := I) (M := M) g 2 2 P hsymm).trans ?_
    exact mul_le_mul_of_nonneg_left hP2 (pow_nonneg hfr 2)
  rw [metricComparisonSlotInsertion_eq (I := I) (M := M) g gm P htie]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 F₀
    (slotInsertEndoCc (I := I) (M := M) g 2
      (symmRaiseEndo (I := I) (M := M) g P))).trans ?_
  rw [show B R ^ 2 = L R by
    simpa only [B] using Real.sq_sqrt (hL R)]
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hpert) (by norm_num)

theorem exists_operatorFieldComposition_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r)
        (X Y : ℝ), 0 ≤ X → 0 ≤ Y →
        covariantJetNormSq (I := I) (M := M) g 2 Φ ≤ X ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ Y ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
        (C * X * Y) ^ 2 := by
  obtain ⟨K, hK, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g p r c
  let C : ℝ := Real.sqrt K
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCsq : C ^ 2 = K := by
    simpa only [C] using Real.sq_sqrt hK
  refine ⟨C, hC, ?_⟩
  intro Φ W X Y hX hY hΦ hW
  refine (happ Φ W).trans ?_
  calc
    K * covariantJetNormSq (I := I) (M := M) g 2 Φ *
        covariantJetNormSq (I := I) (M := M) g 2 W ≤
      K * X ^ 2 * Y ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hΦ hK) hW
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g W)
          (mul_nonneg hK (sq_nonneg X))
    _ = (C * X * Y) ^ 2 := by rw [← hCsq]; ring

theorem exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ΦT ΦU : SmoothCcTensor g r c)
        (WT WU : SmoothCcTensor g p r)
        (FD FB WB WD : ℝ),
        0 ≤ FD → 0 ≤ FB → 0 ≤ WB → 0 ≤ WD →
        covariantJetNormSq (I := I) (M := M) g 2 (ΦT - ΦU) ≤ FD ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 ΦU ≤ FB ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 WT ≤ WB ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (WT - WU) ≤ WD ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g p r c ΦT WT -
            ccOperatorFieldComp (I := I) (M := M) g p r c ΦU WU) ≤
        (C * (FD * WB + FB * WD)) ^ 2 := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g p r c
  let C : ℝ := 2 * C₀
  refine ⟨C, mul_nonneg (by norm_num) hC₀, ?_⟩
  intro ΦT ΦU WT WU FD FB WB WD hFD hFB hWB hWD
    hΦdiff hΦU hWT hWdiff
  let X : SmoothCcTensor g p c :=
    ccOperatorFieldComp (I := I) (M := M) g p r c (ΦT - ΦU) WT
  let Y : SmoothCcTensor g p c :=
    ccOperatorFieldComp (I := I) (M := M) g p r c ΦU (WT - WU)
  let x : ℝ := C₀ * FD * WB
  let y : ℝ := C₀ * FB * WD
  have hx0 : 0 ≤ x := mul_nonneg (mul_nonneg hC₀ hFD) hWB
  have hy0 : 0 ≤ y := mul_nonneg (mul_nonneg hC₀ hFB) hWD
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ x ^ 2 := by
    simpa only [X, x] using happ (ΦT - ΦU) WT FD WB hFD hWB hΦdiff hWT
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ y ^ 2 := by
    simpa only [Y, y] using happ ΦU (WT - WU) FB WD hFB hWD hΦU hWdiff
  have hsplit :
      ccOperatorFieldComp (I := I) (M := M) g p r c ΦT WT -
          ccOperatorFieldComp (I := I) (M := M) g p r c ΦU WU = X + Y := by
    simp only [X, Y, operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  rw [hsplit]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
        covariantJetNormSq (I := I) (M := M) g 2 Y) ≤
      2 * (x ^ 2 + y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ (2 * (x + y)) ^ 2 := by
      nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg hx0 hy0]
    _ = (C * (FD * WB + FB * WD)) ^ 2 := by
      simp only [C, x, y]
      ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem connectionDifferenceMetricLoweringCoefficient_eq
    (g gm : SmoothRiemannianMetric I M) :
    connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm =
      ccOperatorFieldComp (I := I) (M := M) g 3 3 3
        (slotInsertEndoCc (I := I) (M := M) g 2
          (metricComparisonEndomorphismField (I := I) (M := M) gm g))
        (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (permCoeff (I := I) (M := M) g (finRotate 3))
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)) := by
  rfl

theorem exists_connectionDifferenceMetricLoweringCoefficient_product_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M) (X Y : ℝ),
        0 ≤ X → 0 ≤ Y →
        covariantJetNormSq (I := I) (M := M) g 2
            (slotInsertEndoCc (I := I) (M := M) g 2
              (metricComparisonEndomorphismField (I := I) (M := M) gm g)) ≤ X ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
              (permCoeff (I := I) (M := M) g (finRotate 3))
              (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)) ≤ Y ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm) ≤ (C * X * Y) ^ 2 := by
  obtain ⟨C, hC, happ⟩ := exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 3
  refine ⟨C, hC, ?_⟩
  intro gm X Y hX hY hf hi
  rw [connectionDifferenceMetricLoweringCoefficient_eq (I := I) (M := M) g gm]
  exact happ _ _ X Y hX hY hf hi

theorem exists_connectionDifferenceMetricLoweringCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm) ≤ B R ^ 2 := by
  obtain ⟨ρ, Bi, hρ, hBi, hinner⟩ :=
    exists_rotatedConnectionDifferenceLowOrderOperator_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Bf, hBf, hfull⟩ := exists_metricComparisonSlotInsertion_covariantJetNormSq_two_bound (I := I) (M := M) g
  obtain ⟨Ca, hCa, hmul⟩ := exists_connectionDifferenceMetricLoweringCoefficient_product_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => Ca * Bf R * Bi
  refine ⟨ρ, B, hρ, fun R hR =>
    mul_nonneg (mul_nonneg hCa (hBf R hR)) hBi, ?_⟩
  intro gm P hP htie R hR hP2 hPn
  have hi := hinner P gm htie hPn
  have hf : covariantJetNormSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) gm g)) ≤ Bf R ^ 2 :=
    hfull gm P hP htie R hR hP2
  exact hmul gm (Bf R) Bi (hBf R hR) hBi hf hi

theorem exists_connectionDifferenceMetricLoweringCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
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
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R D2 N : ℝ), 0 ≤ R → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gT -
            connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gU) ≤
        (B R * (D2 + N)) ^ 2 := by
  obtain ⟨ρcp, Cc, hρcp, hCc, hcp⟩ :=
    RicciDeTurckLowOrder.connLow_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρcb, Bc, hρcb, hBc, hcb⟩ :=
    RicciDeTurckLowOrder.low_connection_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Cr, hCr, hrev⟩ :=
    RicciDeTurckLowOrder.reverse_slot_sobolev_two_bound (I := I) (M := M) g
  obtain ⟨P, hP, happ⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 3
  let ρ : ℝ := min ρcp ρcb
  let fr : ℝ := Module.finrank ℝ E
  let a : ℝ := fr * Bc
  let b : ℝ → ℝ := fun R => Cr * (1 + R) * Cc
  let B : ℝ → ℝ := fun R => P * (a + b R)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have ha : 0 ≤ a := mul_nonneg hfr hBc
  have hb : ∀ R : ℝ, 0 ≤ R → 0 ≤ b R := fun R hR =>
    mul_nonneg (mul_nonneg hCr (add_nonneg (by norm_num) hR)) hCc
  refine ⟨ρ, B, lt_min hρcp hρcb,
    fun R hR => mul_nonneg hP (add_nonneg ha (hb R hR)), ?_⟩
  intro gT gU T U hT hU hTtie hUtie hTn hUn
    R D2 N hR hD2 hN hT2 hU2 hTU2 hTUn
  have hTnc : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρcp :=
    hTn.trans (min_le_left _ _)
  have hUnc : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρcp :=
    hUn.trans (min_le_left _ _)
  have hTnb : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρcb :=
    hTn.trans (min_le_right _ _)
  let FT : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) gT g)
  let FU : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) gU g)
  let WT : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (permCoeff (I := I) (M := M) g (finRotate 3))
      (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT)
  let WU : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (permCoeff (I := I) (M := M) g (finRotate 3))
      (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gU)
  have hFD : covariantJetNormSq (I := I) (M := M) g 2 (FT - FU) ≤
      (fr * D2) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (FT - FU) ≤
          fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
        simpa only [FT, FU, fr] using
          RicciDeTurckLowOrder.revSlot_pair_h2 (I := I) (M := M)
            g gT gU T U hT hU hTtie hUtie
      _ ≤ fr ^ 2 * D2 ^ 2 :=
        mul_le_mul_of_nonneg_left hTU2 (sq_nonneg fr)
      _ = (fr * D2) ^ 2 := by ring
  have hFB : covariantJetNormSq (I := I) (M := M) g 2 FU ≤
      (Cr * (1 + R)) ^ 2 := by
    simpa only [FU] using hrev gU U hU hUtie R hR hU2
  have hWT : covariantJetNormSq (I := I) (M := M) g 2 WT ≤ Bc ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
        (permCoeff (I := I) (M := M) g (finRotate 3))
        (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT)) ≤ Bc ^ 2
    rw [operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g,
      covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact hcb T gT hTtie hTnb
  have hWD : covariantJetNormSq (I := I) (M := M) g 2 (WT - WU) ≤
      (Cc * N) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (permCoeff (I := I) (M := M) g (finRotate 3))
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT) -
        ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (permCoeff (I := I) (M := M) g (finRotate 3))
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gU)) ≤
        (Cc * N) ^ 2
    rw [← operatorFieldComposition_sub_right]
    have hp := operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g (finRotate 3)
      (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT -
        RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gU)
    rw [hp, covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    have hc := hcp T U gT gU hTtie hUtie hTnc hUnc
    exact hc.trans (pow_le_pow_left₀
      (mul_nonneg hCc (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hTUn hCc) 2)
  have hraw := happ FT FU WT WU
    (fr * D2) (Cr * (1 + R)) Bc (Cc * N)
    (mul_nonneg hfr hD2)
    (mul_nonneg hCr (add_nonneg (by norm_num) hR)) hBc
    (mul_nonneg hCc hN) hFD hFB hWT hWD
  let L : ℝ := P * (a * D2 + b R * N)
  have hL0 : 0 ≤ L :=
    mul_nonneg hP (add_nonneg (mul_nonneg ha hD2)
      (mul_nonneg (hb R hR) hN))
  have hraw' : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gT -
        connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gU) ≤ L ^ 2 := by
    have hraw0 : covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gT -
          connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gU) ≤
        (P * (fr * D2 * Bc + Cr * (1 + R) * (Cc * N))) ^ 2 := by
      simpa only [connectionDifferenceMetricLoweringCoefficient, FT, FU, WT, WU] using hraw
    refine hraw0.trans_eq ?_
    simp only [L, a, b]
    ring
  have hlead : L ≤ B R * (D2 + N) := by
    simp only [L, B]
    calc
      P * (a * D2 + b R * N) ≤
          P * ((a + b R) * (D2 + N)) :=
        mul_le_mul_of_nonneg_left
          (by nlinarith [mul_nonneg ha hN, mul_nonneg (hb R hR) hD2]) hP
      _ = P * (a + b R) * (D2 + N) := by rw [mul_assoc]
  exact hraw'.trans (pow_le_pow_left₀ hL0 hlead 2)

private theorem quadratic_arm_pairing_scale_sq (p l o b d a q : ℝ) :
    (p * ((l * a * q) * o + (b * a) * (d * q))) ^ 2 =
      (p * (l * o + b * d) * a * q) ^ 2 := by
  ring

theorem exists_connectionDifferenceQuadraticArmDerivativeCoefficients_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
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
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      let D := D3 + D2 + A * D2 + N
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT -
            connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU) ≤
          (B R * (1 + A) * D) ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT -
            connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU) ≤
          (B R * (1 + A) * D) ^ 2 := by
  obtain ⟨ρop, Bod, hρop, hBod, hop⟩ :=
    exists_connectionDifferenceMetricLoweringCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρob, Bo, hρob, hBo, hob⟩ :=
    exists_connectionDifferenceMetricLoweringCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨L0, L1, hL0, hL1, hlp⟩ :=
    lieArm2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨Bl, hBl, hlb⟩ :=
    deTurck_lie_arm_two_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨P, hP, happ⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 4
  let ρ : ℝ := min ρop ρob
  let Ld : ℝ → ℝ := fun R => L0 R + L1 R
  let B : ℝ → ℝ := fun R =>
    P * (Ld R * Bo R + Bl R * Bod R)
  have hLd : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ld R := fun R hR =>
    add_nonneg (hL0 R hR) (hL1 R hR)
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := fun R hR =>
    mul_nonneg hP
      (add_nonneg (mul_nonneg (hLd R hR) (hBo R hR))
        (mul_nonneg (hBl R hR) (hBod R hR)))
  refine ⟨ρ, B, lt_min hρop hρob, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  dsimp only
  let D : ℝ := D3 + D2 + A * D2 + N
  have hD : 0 ≤ D :=
    add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have honeA : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hTnop : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρop :=
    hTn.trans (min_le_left _ _)
  have hUnop : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρop :=
    hUn.trans (min_le_left _ _)
  have hTnob : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρob :=
    hTn.trans (min_le_right _ _)
  let LT : SmoothCcTensor g 3 4 := deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT
  let LU : SmoothCcTensor g 3 4 := deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU
  let OT : SmoothCcTensor g 3 3 := connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gT
  let OU : SmoothCcTensor g 3 3 := connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gU
  have hlraw := hlp gT gU T U hT hU hTtie hUtie
    hδ_le hδ0 hδT hδ_le hδ0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  let X : ℝ := L0 R * D3 + L1 R * D2 + L1 R * A * D2
  have hX : 0 ≤ X :=
    add_nonneg (add_nonneg (mul_nonneg (hL0 R hR) hD3)
      (mul_nonneg (hL1 R hR) hD2))
      (mul_nonneg (mul_nonneg (hL1 R hR) hA) hD2)
  have hXD : X ≤ Ld R * D := by
    simp only [X, Ld, D]
    exact weighted_three_term_le_product_sum (L0 R) (L1 R) D3 D2 A N
      (hL0 R hR) (hL1 R hR) hD3 hD2 hA hN
  have hXDA : X ≤ Ld R * (1 + A) * D := by
    refine hXD.trans ?_
    exact mul_le_mul_one_add (Ld R) A D (hLd R hR) hA hD
  have hLD : covariantJetNormSq (I := I) (M := M) g 2 (LT - LU) ≤
      (Ld R * (1 + A) * D) ^ 2 := by
    have h0 : covariantJetNormSq (I := I) (M := M) g 2 (LT - LU) ≤ X ^ 2 := by
      simpa only [LT, LU, X] using hlraw
    exact h0.trans (pow_le_pow_left₀ hX hXDA 2)
  have hlU : covariantJetNormSq (I := I) (M := M) g 2 LU ≤
      (Bl R * (1 + A)) ^ 2 := by
    have h0 : covariantJetNormSq (I := I) (M := M) g 2 LU ≤
        (Bl R * A) ^ 2 := by
      simpa only [LU] using hlb gU U hU hUtie hδ_le hδ0 hδU hδZ
        R A hR hA hU2 hU3
    exact h0.trans (pow_le_pow_left₀ (mul_nonneg (hBl R hR) hA)
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (hBl R hR)) 2)
  have hoT : covariantJetNormSq (I := I) (M := M) g 2 OT ≤ (Bo R) ^ 2 := by
    simpa only [OT] using hob gT T hT hTtie R hR hT2 hTnob
  have hop0 := hop gT gU T U hT hU hTtie hUtie hTnop hUnop
    R D2 N hR hD2 hN hT2 hU2 hTU2 hTUn
  have hsmall : D2 + N ≤ D := by
    simp only [D]
    exact add_le_four_term_sum D3 D2 A N hD3 hD2 hA
  have hoD : covariantJetNormSq (I := I) (M := M) g 2 (OT - OU) ≤
      (Bod R * D) ^ 2 := by
    have h0 : covariantJetNormSq (I := I) (M := M) g 2 (OT - OU) ≤
        (Bod R * (D2 + N)) ^ 2 := by
      simpa only [OT, OU] using hop0
    exact h0.trans (pow_le_pow_left₀
      (mul_nonneg (hBod R hR) (add_nonneg hD2 hN))
      (mul_le_mul_of_nonneg_left hsmall (hBod R hR)) 2)
  have hqraw := happ LT LU OT OU
    (Ld R * (1 + A) * D) (Bl R * (1 + A))
    (Bo R) (Bod R * D)
    (mul_nonneg (mul_nonneg (hLd R hR) honeA) hD)
    (mul_nonneg (hBl R hR) honeA) (hBo R hR)
    (mul_nonneg (hBod R hR) hD) hLD hlU hoT hoD
  have hq : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT -
        connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU) ≤
      (B R * (1 + A) * D) ^ 2 := by
    have h0 : covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT -
          connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU) ≤
        (P * ((Ld R * (1 + A) * D) * Bo R +
          (Bl R * (1 + A)) * (Bod R * D))) ^ 2 := by
      simpa only [connectionDifferenceQuadraticPairedDerivativeCoefficient, LT, LU, OT, OU] using hqraw
    refine h0.trans_eq ?_
    simpa only [B] using
      quadratic_arm_pairing_scale_sq P (Ld R) (Bo R) (Bl R) (Bod R) (1 + A) D
  let ST : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1)) OT
  let SU : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1)) OU
  have hsT : covariantJetNormSq (I := I) (M := M) g 2 ST ≤ (Bo R) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
        (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1)) OT) ≤
      (Bo R) ^ 2
    rw [operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g,
      covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact hoT
  have hsD : covariantJetNormSq (I := I) (M := M) g 2 (ST - SU) ≤
      (Bod R * D) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1)) OT -
        ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1)) OU) ≤
      (Bod R * D) ^ 2
    rw [← operatorFieldComposition_sub_right]
    have hp := operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1) (OT - OU)
    rw [hp, covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact hoD
  have haraw := happ LT LU ST SU
    (Ld R * (1 + A) * D) (Bl R * (1 + A))
    (Bo R) (Bod R * D)
    (mul_nonneg (mul_nonneg (hLd R hR) honeA) hD)
    (mul_nonneg (hBl R hR) honeA) (hBo R hR)
    (mul_nonneg (hBod R hR) hD) hLD hlU hsT hsD
  have ha : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT -
        connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU) ≤
      (B R * (1 + A) * D) ^ 2 := by
    have h0 : covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT -
          connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU) ≤
        (P * ((Ld R * (1 + A) * D) * Bo R +
          (Bl R * (1 + A)) * (Bod R * D))) ^ 2 := by
      simpa only [connectionDifferenceQuadraticComposedDerivativeCoefficient, LT, LU, ST, SU, OT, OU] using haraw
    refine h0.trans_eq ?_
    simpa only [B] using
      quadratic_arm_pairing_scale_sq P (Ld R) (Bo R) (Bl R) (Bod R) (1 + A) D
  exact ⟨hq, ha⟩

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem covariantJetNormSq_sum_six_sq_le
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A B C D E' F : SmoothCcTensor g r s) (X : ℝ)
    (hA : covariantJetNormSq (I := I) (M := M) g 2 A ≤ X ^ 2)
    (hB : covariantJetNormSq (I := I) (M := M) g 2 B ≤ X ^ 2)
    (hC : covariantJetNormSq (I := I) (M := M) g 2 C ≤ X ^ 2)
    (hD : covariantJetNormSq (I := I) (M := M) g 2 D ≤ X ^ 2)
    (hE : covariantJetNormSq (I := I) (M := M) g 2 E' ≤ X ^ 2)
    (hF : covariantJetNormSq (I := I) (M := M) g 2 F ≤ X ^ 2) :
    covariantJetNormSq (I := I) (M := M) g 2 (A + B + C + D + E' + F) ≤
      (32 * X) ^ 2 := by
  have hAB : covariantJetNormSq (I := I) (M := M) g 2 (A + B) ≤
      (2 * X) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 A B).trans ?_
    nlinarith [sq_nonneg X]
  have hABC : covariantJetNormSq (I := I) (M := M) g 2 (A + B + C) ≤
      (4 * X) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 (A + B) C).trans ?_
    nlinarith [sq_nonneg X]
  have hABCD : covariantJetNormSq (I := I) (M := M) g 2 (A + B + C + D) ≤
      (8 * X) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 (A + B + C) D).trans ?_
    nlinarith [sq_nonneg X]
  have hABCDE : covariantJetNormSq (I := I) (M := M) g 2
      (A + B + C + D + E') ≤ (16 * X) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 (A + B + C + D) E').trans ?_
    nlinarith [sq_nonneg X]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2
    (A + B + C + D + E') F).trans ?_
  nlinarith [sq_nonneg X]

theorem exists_connectionDifferenceQuadraticCurvatureDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
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
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gT -
            connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gU) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρ, Bq, hρ, hBq, hqba⟩ :=
    exists_connectionDifferenceQuadraticArmDerivativeCoefficients_pairing_secondOrder_bound (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => 32 * Bq R
  refine ⟨ρ, B, hρ,
    fun R hR => mul_nonneg (by norm_num) (hBq R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let S : ℝ := Bq R * (1 + A) * (D3 + D2 + A * D2 + N)
  have hpair := hqba gT gU T U hT hU hTtie hUtie
    hδ_le hδ0 hδT hδU hδZ hTn hUn
    R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hq : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT -
        connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU) ≤ S ^ 2 := by
    simpa only [S] using hpair.1
  have ha : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT -
        connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU) ≤ S ^ 2 := by
    simpa only [S] using hpair.2
  let Q0 : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT) -
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU)
  let Q1 : SmoothCcTensor g 3 4 :=
    connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT - connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU
  let A0 : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermA)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT) -
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermA)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU)
  let A1 : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2))
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT) -
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2))
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU)
  let A2 : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermB)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT) -
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermB)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU)
  let A3 : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermC)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT) -
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermC)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU)
  have hperm (σ : Equiv.Perm (Fin 4)) :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
              (permCoeff (I := I) (M := M) g σ)
              (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT) -
            ccOperatorFieldComp (I := I) (M := M) g 3 4 4
              (permCoeff (I := I) (M := M) g σ)
              (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU)) ≤ S ^ 2 := by
    rw [← operatorFieldComposition_sub_right]
    have hp := operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g σ
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU)
    rw [hp, covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact ha
  have hQ0 : covariantJetNormSq (I := I) (M := M) g 2 Q0 ≤ S ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
          (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT) -
        ccOperatorFieldComp (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
          (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU)) ≤ S ^ 2
    rw [← operatorFieldComposition_sub_right]
    have hp := operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1)
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT - connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU)
    rw [hp, covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact hq
  have hQ1 : covariantJetNormSq (I := I) (M := M) g 2 Q1 ≤ S ^ 2 := by
    simpa only [Q1] using hq
  have hA0 : covariantJetNormSq (I := I) (M := M) g 2 A0 ≤ S ^ 2 := by
    simpa only [A0] using hperm lrPermA
  have hA1 : covariantJetNormSq (I := I) (M := M) g 2 A1 ≤ S ^ 2 := by
    simpa only [A1] using hperm (Equiv.swap (0 : Fin 4) 2)
  have hA2 : covariantJetNormSq (I := I) (M := M) g 2 A2 ≤ S ^ 2 := by
    simpa only [A2] using hperm lrPermB
  have hA3 : covariantJetNormSq (I := I) (M := M) g 2 A3 ≤ S ^ 2 := by
    simpa only [A3] using hperm lrPermC
  have hsplit :
      connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gT - connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gU =
        Q0 + Q1 + A0 + A1 + A2 + A3 := by
    simp only [connectionDifferenceQuadraticCurvatureDerivativeCoefficient, Q0, Q1, A0, A1, A2, A3]
    module
  rw [hsplit]
  have hsum := covariantJetNormSq_sum_six_sq_le (I := I) (M := M) g
    Q0 Q1 A0 A1 A2 A3 S hQ0 hQ1 hA0 hA1 hA2 hA3
  refine hsum.trans_eq ?_
  simp only [B, S]
  ring

theorem exists_deTurckLieCovariantDerivativeArmTwoCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
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
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨Bc, hBc, hconn⟩ := exists_connectionDifferenceContravariantInsertionField_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ := exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 4
  let J : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapBlocks)
  let Cp : ℝ := Real.sqrt J
  let B : ℝ → ℝ := fun R => Ca * Cp * Bc R
  have hJ : 0 ≤ J := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hCp : 0 ≤ Cp := Real.sqrt_nonneg _
  have hCp2 : Cp ^ 2 = J := by
    simpa only [Cp] using Real.sq_sqrt hJ
  have hperm : covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapBlocks) ≤ Cp ^ 2 := by
    change J ≤ Cp ^ 2
    exact hCp2.symm.le
  refine ⟨B, fun R hR =>
    mul_nonneg (mul_nonneg hCa hCp) (hBc R hR), ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3
  have hc := hconn gm P hP htie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3
  have hraw := happ
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapBlocks)
    (connectionDifferenceContravariantInsertionField (I := I) g gm)
    Cp (Bc R * (1 + A)) hCp
    (mul_nonneg (hBc R hR) (add_nonneg (by norm_num) hA))
    hperm hc
  rw [deTurckLieCovariantDerivativeArmTwoCoefficient_eq_permuted_connectionDifferenceContravariantInsertionField (I := I) (M := M) g gm]
  refine hraw.trans_eq ?_
  simp only [B]
  ring

theorem exists_connectionDifferenceQuadraticArmDerivativeCoefficients_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ Bq Ba : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ Bq R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ Ba R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
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
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gm) ≤
          (Bq R * (1 + A)) ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gm) ≤
          (Ba R * (1 + A)) ^ 2 := by
  obtain ⟨ρ, Bo, hρ, hBo, homega⟩ :=
    exists_connectionDifferenceMetricLoweringCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Bl, hBl, harm⟩ := exists_deTurckLieCovariantDerivativeArmTwoCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Cb, hCb, hb⟩ := exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 4
  obtain ⟨Cs, hCs, hs⟩ := exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 3
  let Jp : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
  let Cp : ℝ := Real.sqrt Jp
  let Bs : ℝ → ℝ := fun R => Cs * Cp * Bo R
  let Bq : ℝ → ℝ := fun R => Cb * Bl R * Bo R
  let Ba : ℝ → ℝ := fun R => Cb * Bl R * Bs R
  have hJp : 0 ≤ Jp := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hCp : 0 ≤ Cp := Real.sqrt_nonneg _
  have hCp2 : Cp ^ 2 = Jp := by
    simpa only [Cp] using Real.sq_sqrt hJp
  have hp : covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g
        (Equiv.swap (0 : Fin 3) 1)) ≤ Cp ^ 2 := by
    change Jp ≤ Cp ^ 2
    exact hCp2.symm.le
  have hBs : ∀ R : ℝ, 0 ≤ R → 0 ≤ Bs R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCs hCp) (hBo R hR)
  refine ⟨ρ, Bq, Ba, hρ,
    fun R hR => mul_nonneg (mul_nonneg hCb (hBl R hR)) (hBo R hR),
    fun R hR => mul_nonneg (mul_nonneg hCb (hBl R hR)) (hBs R hR), ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3 hPn
  have ho := homega gm P hP htie R hR hP2 hPn
  have hl := harm gm P hP htie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3
  have honeA : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hqraw := hb
    (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm)
    (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm)
    (Bl R * (1 + A)) (Bo R)
    (mul_nonneg (hBl R hR) honeA) (hBo R hR) hl ho
  have hq : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gm) ≤
      (Bq R * (1 + A)) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
        (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm)
        (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm)) ≤ _
    refine hqraw.trans_eq ?_
    simp only [Bq]
    ring
  have hsraw := hs
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
    (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm)
    Cp (Bo R) hCp (hBo R hR) hp ho
  have hswap : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
        (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
        (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm)) ≤ Bs R ^ 2 := by
    refine hsraw.trans_eq ?_
    simp only [Bs]
  have haraw := hb
    (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm)
    (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
      (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm))
    (Bl R * (1 + A)) (Bs R)
    (mul_nonneg (hBl R hR) honeA) (hBs R hR) hl hswap
  have ha : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gm) ≤
      (Ba R * (1 + A)) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
        (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm)
        (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
          (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm))) ≤ _
    refine haraw.trans_eq ?_
    simp only [Ba]
    ring
  exact ⟨hq, ha⟩

private noncomputable def quadraticCurvaturePermutationJetCap
    (g : SmoothRiemannianMetric I M) : ℝ :=
  covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1)) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g lrPermA) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2)) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g lrPermB) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g lrPermC)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem quadraticCurvaturePermutationJetCap_nonneg (g : SmoothRiemannianMetric I M) :
    0 ≤ quadraticCurvaturePermutationJetCap (I := I) (M := M) g := by
  unfold quadraticCurvaturePermutationJetCap
  have h0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
  have h1 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g lrPermA)
  have h2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2))
  have h3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g lrPermB)
  have h4 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g lrPermC)
  linarith

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_permutationCoefficient_le_quadraticCurvaturePermutationJetCap
    (g : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
    (hpm : pm = Equiv.swap (0 : Fin 4) 1 ∨ pm = lrPermA ∨
      pm = Equiv.swap (0 : Fin 4) 2 ∨ pm = lrPermB ∨ pm = lrPermC) :
    covariantJetNormSq (I := I) (M := M) g 2
        (permCoeff (I := I) (M := M) g pm) ≤
      quadraticCurvaturePermutationJetCap (I := I) (M := M) g := by
  have h0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
  have h1 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g lrPermA)
  have h2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2))
  have h3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g lrPermB)
  have h4 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g lrPermC)
  unfold quadraticCurvaturePermutationJetCap
  rcases hpm with rfl | rfl | rfl | rfl | rfl <;> linarith

theorem exists_connectionDifferenceQuadraticCurvatureDerivativeCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
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
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρ, Bq, Ba, hρ, hBq, hBa, hqba⟩ :=
    exists_connectionDifferenceQuadraticArmDerivativeCoefficients_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ := exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 4
  let Jp : ℝ := quadraticCurvaturePermutationJetCap (I := I) (M := M) g
  let Cp : ℝ := Real.sqrt Jp
  let D : ℝ → ℝ := fun R => Bq R + Ba R
  let E₀ : ℝ := 1 + Ca * Cp
  let L : ℝ → ℝ := fun R => 94 * (E₀ * D R) ^ 2
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hJp : 0 ≤ Jp := quadraticCurvaturePermutationJetCap_nonneg (I := I) (M := M) g
  have hCp : 0 ≤ Cp := Real.sqrt_nonneg _
  have hCp2 : Cp ^ 2 = Jp := by
    simpa only [Cp] using Real.sq_sqrt hJp
  have hD : ∀ R : ℝ, 0 ≤ R → 0 ≤ D R := by
    intro R hR
    exact add_nonneg (hBq R hR) (hBa R hR)
  have hE₀ : 0 ≤ E₀ :=
    add_nonneg (by norm_num) (mul_nonneg hCa hCp)
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num) (sq_nonneg _)
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3 hPn
  obtain ⟨hqb, hqa⟩ := hqba gm P hP htie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hPn
  have honeA : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hamp : 0 ≤ D R * (1 + A) := mul_nonneg (hD R hR) honeA
  have hqbD : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gm) ≤
      (D R * (1 + A)) ^ 2 := by
    refine hqb.trans (pow_le_pow_left₀
      (mul_nonneg (hBq R hR) honeA) ?_ 2)
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (hBa R hR)) honeA
  have hqaD : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gm) ≤
      (D R * (1 + A)) ^ 2 := by
    refine hqa.trans (pow_le_pow_left₀
      (mul_nonneg (hBa R hR) honeA) ?_ 2)
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (hBq R hR)) honeA
  have hperm (pm : Equiv.Perm (Fin 4))
      (hpm : pm = Equiv.swap (0 : Fin 4) 1 ∨ pm = lrPermA ∨
        pm = Equiv.swap (0 : Fin 4) 2 ∨ pm = lrPermB ∨ pm = lrPermC) :
      covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) ≤ Cp ^ 2 := by
    refine (covariantJetNormSq_permutationCoefficient_le_quadraticCurvaturePermutationJetCap (I := I) (M := M) g pm hpm).trans_eq ?_
    exact hCp2.symm
  let Q : ℝ := (E₀ * D R * (1 + A)) ^ 2
  have hsmall : Ca * Cp ≤ E₀ := by
    simp only [E₀]
    linarith
  have hone : (1 : ℝ) ≤ E₀ := by
    simp only [E₀]
    exact le_add_of_nonneg_right (mul_nonneg hCa hCp)
  have hqbQ : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gm) ≤ Q := by
    refine hqbD.trans ?_
    simp only [Q]
    refine pow_le_pow_left₀ hamp ?_ 2
    calc
      D R * (1 + A) = 1 * D R * (1 + A) := by ring
      _ ≤ E₀ * D R * (1 + A) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hone (hD R hR)) honeA
  have hact (pm : Equiv.Perm (Fin 4))
      (hpm : pm = Equiv.swap (0 : Fin 4) 1 ∨ pm = lrPermA ∨
        pm = Equiv.swap (0 : Fin 4) 2 ∨ pm = lrPermB ∨ pm = lrPermC)
      (W : SmoothCcTensor g 3 4)
      (hW : covariantJetNormSq (I := I) (M := M) g 2 W ≤
        (D R * (1 + A)) ^ 2) :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
            (permCoeff (I := I) (M := M) g pm) W) ≤ Q := by
    have hraw := happ
      (permCoeff (I := I) (M := M) g pm) W
      Cp (D R * (1 + A)) hCp hamp (hperm pm hpm) hW
    refine hraw.trans ?_
    simp only [Q]
    refine pow_le_pow_left₀ (mul_nonneg (mul_nonneg hCa hCp) hamp) ?_ 2
    calc
      Ca * Cp * (D R * (1 + A)) = Ca * Cp * D R * (1 + A) := by ring
      _ ≤ E₀ * D R * (1 + A) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsmall (hD R hR)) honeA
  have hx0 := hact (Equiv.swap (0 : Fin 4) 1) (Or.inl rfl) _ hqbD
  have hx1 := hqbQ
  have hx2 := hact lrPermA (Or.inr (Or.inl rfl)) _ hqaD
  have hx3 := hact (Equiv.swap (0 : Fin 4) 2)
    (Or.inr (Or.inr (Or.inl rfl))) _ hqaD
  have hx4 := hact lrPermB
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _ hqaD
  have hx5 := hact lrPermC
    (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) _ hqaD
  rw [connectionDifferenceQuadraticCurvatureDerivativeCoefficient]
  refine (covariantJetNormSq_sum_six_le (I := I) (M := M) g 2 _ _ _ _ _ _
    hx0 hx1 hx2 hx3 hx4 hx5).trans ?_
  calc
    94 * Q = L R * (1 + A) ^ 2 := by simp only [Q, L]; ring
    _ = B R ^ 2 * (1 + A) ^ 2 := by
      rw [show B R ^ 2 = L R by
        simpa only [B] using Real.sq_sqrt (hL R hR)]
    _ = (B R * (1 + A)) ^ 2 := by ring
    _ ≤ (B R * (1 + A)) ^ 2 := le_rfl

theorem covariantJetNormSq_slotExtendIter_two_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtendIter (I := I) (M := M) g r s 2 F) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2 F := by
  let fr : ℝ := Module.finrank ℝ E
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  simp only [slotExtendIter, Nat.add_zero]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s F)) ≤
      fr * covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g r s F) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g (r + 1) (s + 1) _
    _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 F) :=
      mul_le_mul_of_nonneg_left
        (covariantJetNormSq_slotExtend_le (I := I) (M := M) g r s F) hfr
    _ = fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 F := by ring

theorem exists_lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
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
          (lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gm W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρ, Bo, hρ, hBo, hop⟩ :=
    exists_connectionDifferenceQuadraticCurvatureDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ct, hCt, hprod⟩ := exists_tensorThreeTwoProductCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ := exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 5 6
  let fr : ℝ := Module.finrank ℝ E
  let Cr : ℝ := Real.sqrt Ct
  let B : ℝ → ℝ := fun R => Ca * fr * Bo R * Cr * R
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hCr : 0 ≤ Cr := Real.sqrt_nonneg _
  have hCr2 : Cr ^ 2 = Ct := by
    simpa only [Cr] using Real.sq_sqrt hCt
  refine ⟨ρ, B, hρ, fun R hR =>
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCa hfr) (hBo R hR)) hCr) hR,
    ?_⟩
  intro gm P W hP htie δ hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPn
  have hop' := hop gm P hP htie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hPn
  have honeA : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hslot : covariantJetNormSq (I := I) (M := M) g 2
      (slotExtendIter (I := I) (M := M) g 3 4 2
        (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm)) ≤
      (fr * Bo R * (1 + A)) ^ 2 := by
    refine (covariantJetNormSq_slotExtendIter_two_le (I := I) (M := M) g 3 4 _).trans ?_
    calc
      fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm) ≤
        fr ^ 2 * (Bo R * (1 + A)) ^ 2 :=
          mul_le_mul_of_nonneg_left hop' (pow_nonneg hfr 2)
      _ = (fr * Bo R * (1 + A)) ^ 2 := by ring
  have hp : covariantJetNormSq (I := I) (M := M) g 2
      (tensorThreeTwoProductCoefficient (I := I) (M := M) g W) ≤ (Cr * R) ^ 2 := by
    refine (hprod W).trans ?_
    calc
      Ct * covariantJetNormSq (I := I) (M := M) g 2 W ≤ Ct * R ^ 2 :=
        mul_le_mul_of_nonneg_left hW2 hCt
      _ = (Cr * R) ^ 2 := by rw [mul_pow, hCr2]
  rw [lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient]
  have hraw := happ
    (slotExtendIter (I := I) (M := M) g 3 4 2
      (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm))
    (tensorThreeTwoProductCoefficient (I := I) (M := M) g W)
    (fr * Bo R * (1 + A)) (Cr * R)
    (mul_nonneg (mul_nonneg hfr (hBo R hR)) honeA)
    (mul_nonneg hCr hR) hslot hp
  refine hraw.trans_eq ?_
  simp only [B]
  ring

theorem exists_lieCorrectionQuadraticFirstDerivativeCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
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
          (lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρm, Bm, hρm, hBm, hmid⟩ :=
    exists_lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρp, Bp, hρp, hBp, hpair⟩ :=
    RicciDeTurckLowOrder.pair_trace_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ := exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 6 2
  let ρ : ℝ := min ρm ρp
  let B : ℝ → ℝ := fun R => Ca * Bp * Bm R
  have hρ : 0 < ρ := lt_min hρm hρp
  refine ⟨ρ, B, hρ, fun R hR =>
    mul_nonneg (mul_nonneg hCa hBp) (hBm R hR), ?_⟩
  intro gm P W hP htie δ hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPn
  have hPnM : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρm :=
    hPn.trans (min_le_left _ _)
  have hPnP : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρp :=
    hPn.trans (min_le_right _ _)
  have hm := hmid gm P W hP htie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPnM
  have hp : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm) ≤ Bp ^ 2 :=
    hpair P gm htie hPnP
  have hs : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 6 6
        (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
        (lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gm W)) ≤
      (Bm R * (1 + A)) ^ 2 := by
    rw [operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation,
      covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact hm
  rw [lieCorrectionQuadraticFirstDerivativeCoefficient]
  have hraw := happ
    (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
    (ccOperatorFieldComp (I := I) (M := M) g 3 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
      (lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gm W))
    Bp (Bm R * (1 + A)) hBp
    (mul_nonneg (hBm R hR) (add_nonneg (by norm_num) hA)) hp hs
  refine hraw.trans_eq ?_
  simp only [B]
  ring

private theorem intermediate_coefficient_pairing_scale_sq (p f c d b r a q : ℝ) :
    (p * ((f * d * a * q) * (c * r) +
      (f * b * a) * (c * q))) ^ 2 =
      (p * f * c * (d * r + b) * a * q) ^ 2 := by
  ring

theorem exists_lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
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
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gT T -
            lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gU U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρd, Bd, hρd, hBd, hopd⟩ :=
    exists_connectionDifferenceQuadraticCurvatureDerivativeCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρb, Bb, hρb, hBb, hopb⟩ :=
    exists_connectionDifferenceQuadraticCurvatureDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ct, hCt, hprod⟩ := exists_tensorThreeTwoProductCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨P, hP, happ⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 5 6
  let ρ : ℝ := min ρd ρb
  let fr : ℝ := Module.finrank ℝ E
  let Cr : ℝ := Real.sqrt Ct
  let B : ℝ → ℝ := fun R =>
    P * fr * Cr * (Bd R * R + Bb R)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hCr : 0 ≤ Cr := Real.sqrt_nonneg _
  have hCr2 : Cr ^ 2 = Ct := by
    simpa only [Cr] using Real.sq_sqrt hCt
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := fun R hR =>
    mul_nonneg (mul_nonneg (mul_nonneg hP hfr) hCr)
      (add_nonneg (mul_nonneg (hBd R hR) hR) (hBb R hR))
  refine ⟨ρ, B, lt_min hρd hρb, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let D : ℝ := D3 + D2 + A * D2 + N
  have hD : 0 ≤ D :=
    add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have honeA : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hTnd : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρd :=
    hTn.trans (min_le_left _ _)
  have hUnd : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρd :=
    hUn.trans (min_le_left _ _)
  have hUnb : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρb :=
    hUn.trans (min_le_right _ _)
  let OT : SmoothCcTensor g 3 4 := connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gT
  let OU : SmoothCcTensor g 3 4 := connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gU
  let ST : SmoothCcTensor g 5 6 :=
    slotExtendIter (I := I) (M := M) g 3 4 2 OT
  let SU : SmoothCcTensor g 5 6 :=
    slotExtendIter (I := I) (M := M) g 3 4 2 OU
  let PT : SmoothCcTensor g 3 5 := tensorThreeTwoProductCoefficient (I := I) (M := M) g T
  let PU : SmoothCcTensor g 3 5 := tensorThreeTwoProductCoefficient (I := I) (M := M) g U
  have hoD : covariantJetNormSq (I := I) (M := M) g 2 (OT - OU) ≤
      (Bd R * (1 + A) * D) ^ 2 := by
    simpa only [OT, OU, D] using
      hopd gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU hδZ
        hTnd hUnd R A D2 D3 N hR hA hD2 hD3 hN
        hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hoB : covariantJetNormSq (I := I) (M := M) g 2 OU ≤
      (Bb R * (1 + A)) ^ 2 := by
    simpa only [OU] using
      hopb gU U hU hUtie hδ_le hδ0 hδU hδZ
        R A hR hA hU2 hU3 hUnb
  have hsD : covariantJetNormSq (I := I) (M := M) g 2 (ST - SU) ≤
      (fr * Bd R * (1 + A) * D) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (slotExtendIter (I := I) (M := M) g 3 4 2 OT -
        slotExtendIter (I := I) (M := M) g 3 4 2 OU) ≤ _
    rw [← slotExtendIter_sub]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtendIter (I := I) (M := M) g 3 4 2 (OT - OU)) ≤
        fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 (OT - OU) := by
          simpa only [fr] using covariantJetNormSq_slotExtendIter_two_le (I := I) (M := M) g 3 4 (OT - OU)
      _ ≤ fr ^ 2 * (Bd R * (1 + A) * D) ^ 2 :=
        mul_le_mul_of_nonneg_left hoD (sq_nonneg fr)
      _ = (fr * Bd R * (1 + A) * D) ^ 2 := by ring
  have hsB : covariantJetNormSq (I := I) (M := M) g 2 SU ≤
      (fr * Bb R * (1 + A)) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (slotExtendIter (I := I) (M := M) g 3 4 2 OU) ≤ _
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtendIter (I := I) (M := M) g 3 4 2 OU) ≤
        fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 OU := by
          simpa only [fr] using covariantJetNormSq_slotExtendIter_two_le (I := I) (M := M) g 3 4 OU
      _ ≤ fr ^ 2 * (Bb R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_left hoB (sq_nonneg fr)
      _ = (fr * Bb R * (1 + A)) ^ 2 := by ring
  have hpT : covariantJetNormSq (I := I) (M := M) g 2 PT ≤ (Cr * R) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (tensorThreeTwoProductCoefficient (I := I) (M := M) g T) ≤ _
    refine (hprod T).trans ?_
    calc
      Ct * covariantJetNormSq (I := I) (M := M) g 2 T ≤ Ct * R ^ 2 :=
        mul_le_mul_of_nonneg_left hT2 hCt
      _ = (Cr * R) ^ 2 := by rw [mul_pow, hCr2]
  have hsmall : D2 ≤ D := by
    simp only [D]
    nlinarith [mul_nonneg hA hD2]
  have hpD : covariantJetNormSq (I := I) (M := M) g 2 (PT - PU) ≤
      (Cr * D) ^ 2 := by
    have h0 : covariantJetNormSq (I := I) (M := M) g 2 (PT - PU) ≤
        (Cr * D2) ^ 2 := by
      change covariantJetNormSq (I := I) (M := M) g 2
        (tensorThreeTwoProductCoefficient (I := I) (M := M) g T -
          tensorThreeTwoProductCoefficient (I := I) (M := M) g U) ≤ _
      rw [← tensorThreeTwoProductCoefficient_sub]
      refine (hprod (T - U)).trans ?_
      calc
        Ct * covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ Ct * D2 ^ 2 :=
          mul_le_mul_of_nonneg_left hTU2 hCt
        _ = (Cr * D2) ^ 2 := by rw [mul_pow, hCr2]
    exact h0.trans (pow_le_pow_left₀ (mul_nonneg hCr hD2)
      (mul_le_mul_of_nonneg_left hsmall hCr) 2)
  have hraw := happ ST SU PT PU
    (fr * Bd R * (1 + A) * D) (fr * Bb R * (1 + A))
    (Cr * R) (Cr * D)
    (mul_nonneg (mul_nonneg (mul_nonneg hfr (hBd R hR)) honeA) hD)
    (mul_nonneg (mul_nonneg hfr (hBb R hR)) honeA)
    (mul_nonneg hCr hR) (mul_nonneg hCr hD)
    hsD hsB hpT hpD
  have h0 : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gT T -
        lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gU U) ≤
      (P * ((fr * Bd R * (1 + A) * D) * (Cr * R) +
        (fr * Bb R * (1 + A)) * (Cr * D))) ^ 2 := by
    simpa only [lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient, ST, SU, PT, PU, OT, OU] using hraw
  refine h0.trans_eq ?_
  simpa only [B] using
    intermediate_coefficient_pairing_scale_sq P fr Cr (Bd R) (Bb R) R (1 + A) D

private theorem first_derivative_coefficient_pairing_scale_sq (p c m b d a q : ℝ) :
    (p * ((c * q) * (m * a) + b * (d * a * q))) ^ 2 =
      (p * (c * m + b * d) * a * q) ^ 2 := by
  ring

theorem exists_lieCorrectionQuadraticFirstDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
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
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gT T -
            lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gU U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρmd, Bmd, hρmd, hBmd, hmidd⟩ :=
    exists_lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρmb, Bmb, hρmb, hBmb, hmidb⟩ :=
    exists_lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρpp, Cp, hρpp, hCp, hpairp⟩ :=
    RicciDeTurckLowOrder.pairTrace_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρpb, Bp, hρpb, hBp, hbddp⟩ :=
    RicciDeTurckLowOrder.pair_trace_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨P, hP, happ⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 6 2
  let ρ : ℝ := min (min ρmd ρmb) (min ρpp ρpb)
  let B : ℝ → ℝ := fun R =>
    P * (Cp * Bmb R + Bp * Bmd R)
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := fun R hR =>
    mul_nonneg hP
      (add_nonneg (mul_nonneg hCp (hBmb R hR))
        (mul_nonneg hBp (hBmd R hR)))
  have hρ : 0 < ρ := lt_min (lt_min hρmd hρmb) (lt_min hρpp hρpb)
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let D : ℝ := D3 + D2 + A * D2 + N
  have hD : 0 ≤ D :=
    add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have honeA : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hND : N ≤ D := by
    simp only [D]
    nlinarith [mul_nonneg hA hD2]
  have hTnmd : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρmd :=
    hTn.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hUnmd : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρmd :=
    hUn.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hTnmb : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρmb :=
    hTn.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hTnpp : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρpp :=
    hTn.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hUnpp : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρpp :=
    hUn.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hUnpb : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρpb :=
    hUn.trans ((min_le_right _ _).trans (min_le_right _ _))
  let MT : SmoothCcTensor g 3 6 := lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gT T
  let MU : SmoothCcTensor g 3 6 := lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gU U
  let ST : SmoothCcTensor g 3 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation) MT
  let SU : SmoothCcTensor g 3 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation) MU
  let PT : SmoothCcTensor g 6 2 := cometricDoublePairTraceCoefficient (I := I) (M := M) g gT
  let PU : SmoothCcTensor g 6 2 := cometricDoublePairTraceCoefficient (I := I) (M := M) g gU
  have hmD : covariantJetNormSq (I := I) (M := M) g 2 (MT - MU) ≤
      (Bmd R * (1 + A) * D) ^ 2 := by
    simpa only [MT, MU, D] using
      hmidd gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU hδZ
        hTnmd hUnmd R A D2 D3 N hR hA hD2 hD3 hN
        hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hmT : covariantJetNormSq (I := I) (M := M) g 2 MT ≤
      (Bmb R * (1 + A)) ^ 2 := by
    simpa only [MT] using
      hmidb gT T T hT hTtie hδ_le hδ0 hδT hδZ
        R A hR hA hT2 hT3 hT2 hTnmb
  have hsD : covariantJetNormSq (I := I) (M := M) g 2 (ST - SU) ≤
      (Bmd R * (1 + A) * D) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 6 6
          (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation) MT -
        ccOperatorFieldComp (I := I) (M := M) g 3 6 6
          (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation) MU) ≤ _
    rw [← operatorFieldComposition_sub_right]
    have hp := operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation (MT - MU)
    rw [hp, covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact hmD
  have hsT : covariantJetNormSq (I := I) (M := M) g 2 ST ≤
      (Bmb R * (1 + A)) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 6 6
        (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation) MT) ≤ _
    rw [operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g,
      covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact hmT
  have hp0 := hpairp T U gT gU hTtie hUtie hTnpp hUnpp
  have hpD : covariantJetNormSq (I := I) (M := M) g 2 (PT - PU) ≤
      (Cp * D) ^ 2 := by
    have h0 : covariantJetNormSq (I := I) (M := M) g 2 (PT - PU) ≤
        (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
      simpa only [PT, PU] using hp0
    have hnormD : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ D :=
      hTUn.trans hND
    exact h0.trans (pow_le_pow_left₀
      (mul_nonneg hCp (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hnormD hCp) 2)
  have hpU : covariantJetNormSq (I := I) (M := M) g 2 PU ≤ Bp ^ 2 := by
    simpa only [PU] using hbddp U gU hUtie hUnpb
  have hraw := happ PT PU ST SU
    (Cp * D) Bp (Bmb R * (1 + A)) (Bmd R * (1 + A) * D)
    (mul_nonneg hCp hD) hBp (mul_nonneg (hBmb R hR) honeA)
    (mul_nonneg (mul_nonneg (hBmd R hR) honeA) hD)
    hpD hpU hsT hsD
  have h0 : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gT T -
        lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gU U) ≤
      (P * ((Cp * D) * (Bmb R * (1 + A)) +
        Bp * (Bmd R * (1 + A) * D))) ^ 2 := by
    simpa only [lieCorrectionQuadraticFirstDerivativeCoefficient, PT, PU, ST, SU, MT, MU] using hraw
  refine h0.trans_eq ?_
  simpa only [B] using
    first_derivative_coefficient_pairing_scale_sq P Cp (Bmb R) Bp (Bmd R) (1 + A) D

theorem exists_lowOrderFirstDerivativeCoefficientPath_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρr, Br, hρr, hBr, hric⟩ :=
    exists_ricciConnectionDifferenceDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρv, Bv, hρv, hBv, hvb⟩ :=
    exists_lieCorrectionZeroVectorBundleDerivativeCoefficient_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρa, Ba, hρa, hBa, hamix⟩ :=
    exists_lieCorrectionZeroMixedConnectionDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let ρ : ℝ := min ρr (min ρv ρa)
  let L : ℝ → ℝ := fun R =>
    2 * (2 * (4 * Br R ^ 2 + Bv R ^ 2) + Ba R ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hρ : 0 < ρ := lt_min hρr (lt_min hρv hρa)
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg
        (mul_nonneg (by norm_num)
          (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg (Br R)))
            (sq_nonneg (Bv R))))
        (sq_nonneg (Ba R)))
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgm
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by nlinarith [hs.1, hs.2]
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
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
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTn)
  have hPnr : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρr :=
    hPn.trans (min_le_left _ _)
  have hPnv : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρv :=
    hPn.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hPna : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρa :=
    hPn.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr := hric gm P T hPsymm hT hPtie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hT2 hPnr
  have hv := hvb gm P T hPsymm hPtie hδ_le hδ0 hδP
    R A hR hA hP2 hP3 hT2 hPnv
  have ha := hamix gm P T hPsymm hPtie hδ_le hδ0 hδP
    R A hR hA hP2 hP3 hT2 hPna
  have hrs : covariantJetNormSq (I := I) (M := M) g 2
      ((-2 * s : ℝ) • ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm T) ≤
      4 * (Br R * (1 + A)) ^ 2 := by
    rw [covariantJetNormSq_smul]
    calc
      (-2 * s) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm T) =
        4 * s ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm T) := by ring
      _ ≤ 4 * 1 * covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm T) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs2 (by norm_num))
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      _ ≤ 4 * 1 * (Br R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = 4 * (Br R * (1 + A)) ^ 2 := by ring
  have hvs : covariantJetNormSq (I := I) (M := M) g 2
      (s • lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm T) ≤
      (Bv R * (1 + A)) ^ 2 := by
    rw [covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _) hs2).trans hv
  have has : covariantJetNormSq (I := I) (M := M) g 2
      (s • lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm g T) ≤
      (Ba R * (1 + A)) ^ 2 := by
    rw [covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _) hs2).trans ha
  rw [lowOrderFirstDerivativeCoefficientPath]
  have hrv := covariantJetNormSq_add_le (I := I) (M := M) g 2
    ((-2 * s : ℝ) • ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm T)
    (s • lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm T)
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2
          ((-2 * s : ℝ) • ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm T +
            s • lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm T) +
        covariantJetNormSq (I := I) (M := M) g 2
          (s • lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm g T)) ≤
      2 * (2 * (covariantJetNormSq (I := I) (M := M) g 2
            ((-2 * s : ℝ) • ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm T) +
          covariantJetNormSq (I := I) (M := M) g 2
            (s • lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm T)) +
        covariantJetNormSq (I := I) (M := M) g 2
          (s • lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm g T)) :=
        mul_le_mul_of_nonneg_left (add_le_add hrv le_rfl) (by norm_num)
    _ ≤ 2 * (2 * (4 * (Br R * (1 + A)) ^ 2 +
          (Bv R * (1 + A)) ^ 2) +
        (Ba R * (1 + A)) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left (add_le_add hrs hvs) (by norm_num))
          has) (by norm_num)
    _ = L R * (1 + A) ^ 2 := by simp only [L]; ring
    _ = (B R * (1 + A)) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      simpa only [mul_pow] using
        congrArg (fun x : ℝ => x * (1 + A) ^ 2) hBR.symm

theorem exists_affineLowOrderFirstDerivativeCoefficientPath_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρl, Bl, hρl, hBl, hlow⟩ :=
    exists_lowOrderFirstDerivativeCoefficientPath_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρq, Bq, hρq, hBq, hquad⟩ :=
    exists_lieCorrectionQuadraticFirstDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let ρ : ℝ := min ρl ρq
  let L : ℝ → ℝ := fun R => 2 * (Bl R ^ 2 + Bq R ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hρ : 0 < ρ := lt_min hρl hρq
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg (Bl R)) (sq_nonneg (Bq R)))
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn s hs
  have hl := hlow T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
    (hTn.trans (min_le_left _ _)) hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgm
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by nlinarith [hs.1, hs.2]
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
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
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρq := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTn.trans (min_le_right _ _))
  have hq := hquad gm P T hPsymm hPtie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hT2 hPn
  have hqs : covariantJetNormSq (I := I) (M := M) g 2
      (s • lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm T) ≤
      (Bq R * (1 + A)) ^ 2 := by
    rw [covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _) hs2).trans hq
  rw [affineLowOrderFirstDerivativeCoefficientPath]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2
          (lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s) +
        covariantJetNormSq (I := I) (M := M) g 2
          (s • lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm T)) ≤
      2 * ((Bl R * (1 + A)) ^ 2 + (Bq R * (1 + A)) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hl hqs) (by norm_num)
    _ = L R * (1 + A) ^ 2 := by simp only [L]; ring
    _ = (B R * (1 + A)) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      simpa only [mul_pow] using
        congrArg (fun x : ℝ => x * (1 + A) ^ 2) hBR.symm

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
