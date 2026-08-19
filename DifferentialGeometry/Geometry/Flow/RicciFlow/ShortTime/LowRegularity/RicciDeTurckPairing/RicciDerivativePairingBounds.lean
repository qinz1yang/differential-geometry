import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.RicciQuadraticDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.MetricDifference

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
  covariantJetNormSq_sub_le)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply operatorFieldApplication_sub_left ccOperatorFieldComp operatorFieldComposition_sub_left operatorFieldComposition_sub_right
    operatorFieldComposition_zero_eq_operatorFieldApply ccOperatorFieldComp metricComparisonEndomorphismField operatorFieldApply)
open DifferentialGeometry.Geometry.Connection (slotInsertEndoCc)

private lemma two_mul_sum_sq_le_square_two_mul_sum
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * (x ^ 2 + y ^ 2) ≤ (2 * (x + y)) ^ 2 := by
  nlinarith only [sq_nonneg x, sq_nonneg y, mul_nonneg hx hy]

private lemma one_add_square_le_square_one_add (x : ℝ) (hx : 0 ≤ x) :
    1 + x ^ 2 ≤ (1 + x) ^ 2 := by
  nlinarith only [hx]

private lemma two_mul_sum_le_four_sq
    (x y z : ℝ) (hx : x ≤ z ^ 2) (hy : y ≤ z ^ 2) :
    2 * (x + y) ≤ 4 * z ^ 2 := by
  linarith only [hx, hy]

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

theorem exists_ricciConnectionDifferenceDerivativeMetricWeight_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
        (R D2 : ℝ), 0 ≤ R → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gT T -
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gU U) ≤
        (B R * D2) ^ 2 := by
  obtain ⟨Be, hBe, hslotB⟩ :=
    RicciDeTurckLowOrder.full_slot_sobolev_two_bound (I := I) (M := M) g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bed, hBed, hslotD⟩ :=
    exists_slotInsertEndoCc_metricComparisonEndomorphismField_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨C, hC, happ⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 0 2 2
  let B : ℝ → ℝ := fun R => 2 * C * (Bed R * R + Be R)
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact mul_nonneg (mul_nonneg (by norm_num) hC)
      (add_nonneg (mul_nonneg (hBed R hR) hR) (hBe R hR))
  refine ⟨B, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU
    R D2 hR hD2 hT2 hU2 hTU2
  let ET : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gT)
  let EU : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gU)
  let X : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 (ET - EU) T
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 EU (T - U)
  let x : ℝ := C * (Bed R * D2) * R
  let y : ℝ := C * Be R * D2
  have hx0 : 0 ≤ x :=
    mul_nonneg (mul_nonneg hC (mul_nonneg (hBed R hR) hD2)) hR
  have hy0 : 0 ≤ y :=
    mul_nonneg (mul_nonneg hC (hBe R hR)) hD2
  have hEU :
      covariantJetNormSq (I := I) (M := M) g 2 EU ≤ (Be R) ^ 2 := by
    simpa only [EU] using
      hslotB gU U hU hUtie hδ_le hδ0 hδU R hR hU2
  have hEdiff :
      covariantJetNormSq (I := I) (M := M) g 2 (ET - EU) ≤
        (Bed R * D2) ^ 2 := by
    simpa only [ET, EU] using
      hslotD gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R D2 hR hD2 hT2 hU2 hTU2
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ x ^ 2 := by
    simpa only [X, x, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ (ET - EU) T (Bed R * D2) R
        (mul_nonneg (hBed R hR) hD2) hR hEdiff hT2
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ y ^ 2 := by
    simpa only [Y, y, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ EU (T - U) (Be R) D2
        (hBe R hR) hD2 hEU hTU2
  have happSub (Φ : SmoothCcTensor g 2 2)
      (V W : SmoothCcTensor g 0 2) :
      operatorFieldApply (I := I) (M := M) g 2 2 Φ (V - W) =
        operatorFieldApply (I := I) (M := M) g 2 2 Φ V -
          operatorFieldApply (I := I) (M := M) g 2 2 Φ W := by
    calc
      operatorFieldApply (I := I) (M := M) g 2 2 Φ (V - W) =
          ccOperatorFieldComp (I := I) (M := M) g 0 2 2 Φ (V - W) :=
        (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g 2 2 Φ (V - W)).symm
      _ = ccOperatorFieldComp (I := I) (M := M) g 0 2 2 Φ V -
          ccOperatorFieldComp (I := I) (M := M) g 0 2 2 Φ W :=
        operatorFieldComposition_sub_right (I := I) (M := M) g 0 2 2 Φ V W
      _ = operatorFieldApply (I := I) (M := M) g 2 2 Φ V -
          operatorFieldApply (I := I) (M := M) g 2 2 Φ W :=
        congrArg₂ (fun A B : SmoothCcTensor g 0 2 => A - B)
          (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g 2 2 Φ V)
          (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g 2 2 Φ W)
  have hsplit :
      RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gT T -
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gU U =
        X + Y := by
    simp only [RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight, X, Y, ET, EU]
    rw [operatorFieldApplication_sub_left, happSub]
    module
  rw [hsplit]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
        covariantJetNormSq (I := I) (M := M) g 2 Y) ≤
      2 * (x ^ 2 + y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ (2 * (x + y)) ^ 2 :=
      two_mul_sum_sq_le_square_two_mul_sum x y hx0 hy0
    _ = (B R * D2) ^ 2 := by
      simp only [B, x, y]
      ring

theorem exists_ricciConnectionDifferenceDerivativeTransposedCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
        (R D2 : ℝ), 0 ≤ R → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gT T -
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gU U) ≤
        (B R * D2) ^ 2 := by
  obtain ⟨Bw, hBw, hweight⟩ :=
    exists_ricciConnectionDifferenceDerivativeMetricWeight_pairing_secondOrder_bound
      (I := I) (M := M) hDim g
  obtain ⟨Cm, hCm, hmono⟩ :=
    curv_pair_h2 (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => 2 * Cm * Bw R
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact mul_nonneg (mul_nonneg (by norm_num) hCm) (hBw R hR)
  refine ⟨B, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU
    R D2 hR hD2 hT2 hU2 hTU2
  let WT : SmoothCcTensor g 0 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gT T
  let WU : SmoothCcTensor g 0 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gU U
  let z : ℝ := Cm * (Bw R * D2)
  have hz0 : 0 ≤ z :=
    mul_nonneg hCm (mul_nonneg (hBw R hR) hD2)
  have hWdiff :
      covariantJetNormSq (I := I) (M := M) g 2 (WT - WU) ≤
        (Bw R * D2) ^ 2 := by
    simpa only [WT, WU] using
      hweight gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU
        R D2 hR hD2 hT2 hU2 hTU2
  have hMono (σ : Equiv.Perm (Fin 4)) :
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g gT T σ -
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g gU U σ) ≤
        z ^ 2 := by
    simpa only [RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial, WT, WU, z] using
      hmono WT WU σ (Bw R * D2)
        (mul_nonneg (hBw R hR) hD2) hWdiff
  let XA : SmoothCcTensor g 4 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M)
        g gT T RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation -
      RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M)
        g gU U RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation
  let XB : SmoothCcTensor g 4 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M)
        g gT T RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap -
      RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M)
        g gU U RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap
  have hXA : covariantJetNormSq (I := I) (M := M) g 2 XA ≤ z ^ 2 := by
    simpa only [XA] using hMono RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation
  have hXB : covariantJetNormSq (I := I) (M := M) g 2 XB ≤ z ^ 2 := by
    simpa only [XB] using hMono RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap
  have hsplit :
      RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gT T -
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gU U =
        XA - XB := by
    simp only [RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient, XA, XB]
    module
  rw [hsplit]
  refine (covariantJetNormSq_sub_le (I := I) (M := M) g 2 XA XB).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2 XA +
        covariantJetNormSq (I := I) (M := M) g 2 XB) ≤
      4 * z ^ 2 := two_mul_sum_le_four_sq _ _ _ hXA hXB
    _ = (B R * D2) ^ 2 := by
      simp only [B, z]
      ring

theorem exists_ricciConnectionDerivativeTransposedCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gT T -
            RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gU U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨Bt, hBt, htransD⟩ :=
    exists_ricciConnectionDifferenceDerivativeTransposedCoefficient_pairing_secondOrder_bound
      (I := I) (M := M) hDim g
  obtain ⟨Kd, hKd, hdagB⟩ :=
    exists_ricciConnectionDerivativeCoefficient_covariantJetNormSq_two_radiusFree_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bd, hBd, hdagD⟩ :=
    exists_ricciConnectionDerivativeCoefficient_covariantJetNormSq_tame_difference_bound
      (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 2
  let C0 : SmoothCcTensor g 4 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g g
      (0 : SmoothCcTensor g 0 2)
  let J0 : ℝ := covariantJetNormSq (I := I) (M := M) g 2 C0
  let S0 : ℝ := Real.sqrt J0
  let Sd : ℝ := Real.sqrt Kd
  let Tu : ℝ → ℝ := fun R => 2 * (Bt R * R + S0)
  let B : ℝ → ℝ := fun R =>
    2 * Ca * (Bt R * Sd + Tu R * Bd R)
  have hJ0 : 0 ≤ J0 :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g C0
  have hS0 : 0 ≤ S0 := Real.sqrt_nonneg _
  have hS0sq : S0 ^ 2 = J0 := by
    simpa only [S0] using Real.sq_sqrt hJ0
  have hSd : 0 ≤ Sd := Real.sqrt_nonneg _
  have hSdsq : Sd ^ 2 = Kd := by
    simpa only [Sd] using Real.sq_sqrt hKd
  have hTu : ∀ R : ℝ, 0 ≤ R → 0 ≤ Tu R := by
    intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (hBt R hR) hR) hS0)
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact mul_nonneg (mul_nonneg (by norm_num) hCa)
      (add_nonneg (mul_nonneg (hBt R hR) hSd)
        (mul_nonneg (hTu R hR) (hBd R hR)))
  refine ⟨B, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  let CT : SmoothCcTensor g 4 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gT T
  let CU : SmoothCcTensor g 4 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gU U
  let DT : SmoothCcTensor g 3 4 :=
    RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT
  let DU : SmoothCcTensor g 3 4 :=
    RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU
  let Q : ℝ := D3 + D2 + A * D2
  have hQ : 0 ≤ Q :=
    add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)
  have h1A : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hCTU :
      covariantJetNormSq (I := I) (M := M) g 2 (CT - CU) ≤
        (Bt R * D2) ^ 2 := by
    simpa only [CT, CU] using
      htransD gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU
        R D2 hR hD2 hT2 hU2 hTU2
  have hzeroSymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  have hzeroTie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  have h02 :
      covariantJetNormSq (I := I) (M := M) g 2
          (0 : SmoothCcTensor g 0 2) ≤ (0 : ℝ) ^ 2 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • T by simp, covariantJetNormSq_smul]
    norm_num
  have hU0 :
      covariantJetNormSq (I := I) (M := M) g 2
          (U - (0 : SmoothCcTensor g 0 2)) ≤ R ^ 2 := by
    simpa only [sub_zero] using hU2
  have h02R :
      covariantJetNormSq (I := I) (M := M) g 2
          (0 : SmoothCcTensor g 0 2) ≤ R ^ 2 := by
    exact h02.trans (by norm_num; exact sq_nonneg R)
  have hCU0 :
      covariantJetNormSq (I := I) (M := M) g 2 (CU - C0) ≤
        (Bt R * R) ^ 2 := by
    simpa only [CU, C0] using
      htransD gU g U (0 : SmoothCcTensor g 0 2)
        hU hzeroSymm hUtie hzeroTie hδ_le hδ0 hδU hδZ
        R R hR hR hU2 h02R hU0
  have hCU :
      covariantJetNormSq (I := I) (M := M) g 2 CU ≤ (Tu R) ^ 2 := by
    rw [show CU = (CU - C0) + C0 by module]
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 (CU - C0) C0).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2 (CU - C0) +
          covariantJetNormSq (I := I) (M := M) g 2 C0) ≤
        2 * ((Bt R * R) ^ 2 + S0 ^ 2) := by
          rw [hS0sq]
          exact mul_le_mul_of_nonneg_left (add_le_add hCU0 le_rfl)
            (by norm_num)
      _ ≤ (2 * (Bt R * R + S0)) ^ 2 := by
        nlinarith [mul_nonneg (hBt R hR) hR,
          sq_nonneg (Bt R * R), sq_nonneg S0]
      _ = (Tu R) ^ 2 := by rfl
  have hDT0 :
      covariantJetNormSq (I := I) (M := M) g 2 DT ≤
        Kd * (1 + A ^ 2) := by
    refine (hdagB gT T hT hTtie hδ_le hδ0 hδT).trans ?_
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hT3) hKd
  have hDT :
      covariantJetNormSq (I := I) (M := M) g 2 DT ≤
        (Sd * (1 + A)) ^ 2 := by
    refine hDT0.trans ?_
    rw [mul_pow, hSdsq]
    exact mul_le_mul_of_nonneg_left
      (one_add_square_le_square_one_add A hA) hKd
  have hDD :
      covariantJetNormSq (I := I) (M := M) g 2 (DT - DU) ≤
        (Bd R * Q) ^ 2 := by
    simpa only [DT, DU, Q] using
      hdagD gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 D3 hR hA hD2 hD3
        hT2 hU2 hT3 hU3 hTU2 hTU3
  let X : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 (CT - CU) DT
  let Y : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 CU (DT - DU)
  let x : ℝ := Ca * (Bt R * D2) * (Sd * (1 + A))
  let y : ℝ := Ca * Tu R * (Bd R * Q)
  have hx0 : 0 ≤ x :=
    mul_nonneg (mul_nonneg hCa (mul_nonneg (hBt R hR) hD2))
      (mul_nonneg hSd h1A)
  have hy0 : 0 ≤ y :=
    mul_nonneg (mul_nonneg hCa (hTu R hR))
      (mul_nonneg (hBd R hR) hQ)
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ x ^ 2 := by
    simpa only [X, x] using
      happ (CT - CU) DT (Bt R * D2) (Sd * (1 + A))
        (mul_nonneg (hBt R hR) hD2) (mul_nonneg hSd h1A) hCTU hDT
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ y ^ 2 := by
    simpa only [Y, y] using
      happ CU (DT - DU) (Tu R) (Bd R * Q)
        (hTu R hR) (mul_nonneg (hBd R hR) hQ) hCU hDD
  have hsplit :
      RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gT T -
          RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gU U =
        X + Y := by
    simp only [RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient, CT, CU, DT, DU, X, Y]
    rw [operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  have hD2Q : D2 ≤ Q := by
    dsimp only [Q]
    exact (le_add_of_nonneg_left hD3).trans
      (le_add_of_nonneg_right (mul_nonneg hA hD2))
  have hxle :
      x ≤ Ca * (Bt R * Sd) * (1 + A) * Q := by
    calc
      x = Ca * (Bt R * Sd) * (1 + A) * D2 := by
        simp only [x]
        ring
      _ ≤ Ca * (Bt R * Sd) * (1 + A) * Q :=
        mul_le_mul_of_nonneg_left hD2Q
          (mul_nonneg
            (mul_nonneg hCa (mul_nonneg (hBt R hR) hSd)) h1A)
  have hyle :
      y ≤ Ca * (Tu R * Bd R) * (1 + A) * Q := by
    let c : ℝ := Ca * (Tu R * Bd R)
    have hc : 0 ≤ c :=
      mul_nonneg hCa (mul_nonneg (hTu R hR) (hBd R hR))
    calc
      y = (c * 1) * Q := by simp only [y, c]; ring
      _ ≤ (c * (1 + A)) * Q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hA) hc) hQ
      _ = Ca * (Tu R * Bd R) * (1 + A) * Q := by
        simp only [c]
  have hlin :
      2 * (x + y) ≤ B R * (1 + A) * Q := by
    calc
      2 * (x + y) ≤
          2 * (Ca * (Bt R * Sd) * (1 + A) * Q +
            Ca * (Tu R * Bd R) * (1 + A) * Q) :=
        mul_le_mul_of_nonneg_left (add_le_add hxle hyle) (by norm_num)
      _ = B R * (1 + A) * Q := by
        simp only [B]
        ring
  rw [hsplit]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
        covariantJetNormSq (I := I) (M := M) g 2 Y) ≤
      2 * (x ^ 2 + y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ (2 * (x + y)) ^ 2 :=
      two_mul_sum_sq_le_square_two_mul_sum x y hx0 hy0
    _ ≤ (B R * (1 + A) * Q) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by norm_num) (add_nonneg hx0 hy0)) hlin 2

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
