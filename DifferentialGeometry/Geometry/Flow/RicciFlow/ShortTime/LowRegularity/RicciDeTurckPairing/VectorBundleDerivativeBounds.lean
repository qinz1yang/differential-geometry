import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.LowOrderDerivativeBounds

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
  covariantJetNormSq_reindexCoeffGen covariantJetNormSq_smul)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Sobolev (metricConnectionDifferenceLoweredCoefficient)
open DifferentialGeometry.Analysis.Spectral (ccOperatorFieldComp ccTensorToHs pureTrace)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

private lemma le_square_one_add (x : ℝ) :
    x ≤ (1 + x) ^ 2 := by
  nlinarith only [sq_nonneg x]

private lemma second_le_four_term_sum
    (D3 D2 A N : ℝ) (hD3 : 0 ≤ D3) (hD2 : 0 ≤ D2)
    (hA : 0 ≤ A) (hN : 0 ≤ N) :
    D2 ≤ D3 + D2 + A * D2 + N := by
  nlinarith only [hD3, hN, mul_nonneg hA hD2]

private lemma first_le_four_term_sum
    (D3 D2 A N : ℝ) (hD2 : 0 ≤ D2) (hA : 0 ≤ A) (hN : 0 ≤ N) :
    D3 ≤ D3 + D2 + A * D2 + N := by
  nlinarith only [hD2, hN, mul_nonneg hA hD2]

private lemma middle_le_four_term_sum
    (D3 D2 A N : ℝ) (hD3 : 0 ≤ D3) (hN : 0 ≤ N) :
    D2 + A * D2 ≤ D3 + D2 + A * D2 + N := by
  linarith only [hD3, hN]

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

private theorem exists_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_pairing_second_order_bounds
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ SM DM : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ SM R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ DM R) ∧
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
        (R A D2 D3 D : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D →
        D3 ≤ D → D2 + A * D2 ≤ D →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT) ≤
          (SM R * (1 + A)) ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤
          (SM R * (1 + A)) ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT -
            lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤
          (DM R * D) ^ 2 := by
  obtain ⟨B0m, B1m, hB0m, hB1m, hmcdp⟩ :=
    RicciDeTurckLowOrder.mcd_pair_h2 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm, hBm, hmcdb⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let fr : ℝ := Module.finrank ℝ E
  let SM : ℝ → ℝ := fun R => (1 + fr) * Bm R
  let DM : ℝ → ℝ := fun R => (1 + fr) * (B0m R + B1m R)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hSM : ∀ R : ℝ, 0 ≤ R → 0 ≤ SM R := fun R hR =>
    mul_nonneg (add_nonneg (by norm_num) hfr) (hBm R hR)
  have hDM : ∀ R : ℝ, 0 ≤ R → 0 ≤ DM R := fun R hR =>
    mul_nonneg (add_nonneg (by norm_num) hfr)
      (add_nonneg (hB0m R hR) (hB1m R hR))
  refine ⟨SM, DM, hSM, hDM, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU
    R A D2 D3 D hR hA hD2 hD3 hD hD3le hrestle
    hT2 hU2 hT3 hU3 hTU2 hTU3
  let M0 : ℝ := B0m R * D3 + B1m R * D2 + B1m R * A * D2
  have hM0 : 0 ≤ M0 := by
    dsimp only [M0]
    exact add_nonneg
      (add_nonneg (mul_nonneg (hB0m R hR) hD3)
        (mul_nonneg (hB1m R hR) hD2))
      (mul_nonneg (mul_nonneg (hB1m R hR) hA) hD2)
  have hM0le : M0 ≤ (B0m R + B1m R) * D := by
    calc
      M0 = B0m R * D3 + B1m R * (D2 + A * D2) := by
        simp only [M0]
        ring
      _ ≤ B0m R * D + B1m R * D :=
        add_le_add
          (mul_le_mul_of_nonneg_left hD3le (hB0m R hR))
          (mul_le_mul_of_nonneg_left hrestle (hB1m R hR))
      _ = (B0m R + B1m R) * D := by ring
  have hfr_le : fr ≤ (1 + fr) ^ 2 := le_square_one_add fr
  have hVmT : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT) ≤
      (SM R * (1 + A)) ^ 2 := by
    have hm := hmcdb gT T hT hTtie hδ_le hδ0 hδT
      R A hR hA hT2 hT3
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT) ≤
          fr * covariantJetNormSq (I := I) (M := M) g 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gT g) := by
        simpa only [fr] using covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g gT
      _ ≤ fr * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_left hm hfr
      _ ≤ (1 + fr) ^ 2 * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_right hfr_le (sq_nonneg _)
      _ = (SM R * (1 + A)) ^ 2 := by
        simp only [SM]
        ring
  have hVmU : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤
      (SM R * (1 + A)) ^ 2 := by
    have hm := hmcdb gU U hU hUtie hδ_le hδ0 hδU
      R A hR hA hU2 hU3
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤
          fr * covariantJetNormSq (I := I) (M := M) g 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU g) := by
        simpa only [fr] using covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g gU
      _ ≤ fr * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_left hm hfr
      _ ≤ (1 + fr) ^ 2 * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_right hfr_le (sq_nonneg _)
      _ = (SM R * (1 + A)) ^ 2 := by
        simp only [SM]
        ring
  have hVmD : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT -
        lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤ (DM R * D) ^ 2 := by
    have hm := hmcdp gT gU T U hT hU hTtie hUtie
      hδ_le hδ0 hδT hδ_le hδ0 hδU
      R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT -
            lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤
          fr * covariantJetNormSq (I := I) (M := M) g 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gT g -
              metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU g) := by
        simpa only [fr] using covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_sub_le (I := I) (M := M) g gT gU
      _ ≤ fr * M0 ^ 2 := by
        simpa only [M0] using mul_le_mul_of_nonneg_left hm hfr
      _ ≤ fr * ((B0m R + B1m R) * D) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hM0 hM0le 2) hfr
      _ ≤ (1 + fr) ^ 2 * ((B0m R + B1m R) * D) ^ 2 :=
        mul_le_mul_of_nonneg_right hfr_le (sq_nonneg _)
      _ = (DM R * D) ^ 2 := by
        simp only [DM]
        ring
  exact ⟨hVmT, hVmU, hVmD⟩

theorem exists_lieCorrectionZeroVectorBundleDerivativeCoefficient_pairing_secondOrder_bound
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
          (lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gT T -
            lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gU U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρt1p, Ct1, hρt1p, hCt1, ht1p⟩ :=
    RicciDeTurckLowOrder.trace1_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρt1b, Bt1, hρt1b, hBt1, ht1b⟩ :=
    RicciDeTurckLowOrder.trace_one_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρcp, Cc, hρcp, hCc, hcp⟩ :=
    RicciDeTurckLowOrder.connLow_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρcb, Bc, hρcb, hBc, hcb⟩ :=
    RicciDeTurckLowOrder.low_connection_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρt2p, Ct2, hρt2p, hCt2, ht2p⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρt2b, Bt2, hρt2b, hBt2, ht2b⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨SM, DM, hSM, hDM, hvm⟩ :=
    exists_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_pairing_second_order_bounds (I := I) (M := M) hDim g
  obtain ⟨C0, hC0, happ0⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 1
  obtain ⟨P0, hP0, hpair0⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 1
  obtain ⟨C1, hC1, happ1⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 1 1
  obtain ⟨P1, hP1, hpair1⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 1 1
  obtain ⟨C2, hC2, happ2⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 1 4
  obtain ⟨P2, hP2, hpair2⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 1 4
  obtain ⟨C3, hC3, happ3⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 2
  obtain ⟨P3, hP3, hpair3⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 2
  let ρ : ℝ :=
    min (min ρt1p ρt1b) (min (min ρcp ρcb) (min ρt2p ρt2b))
  let S0 : ℝ := C0 * Bt1 * Bc
  let D0 : ℝ := P0 * (Ct1 * Bc + Bt1 * Cc)
  let S1 : ℝ → ℝ := fun R => C1 * R * S0
  let D1 : ℝ → ℝ := fun R => P1 * (S0 + R * D0)
  let S2 : ℝ → ℝ := fun R => C2 * SM R * S1 R
  let D2c : ℝ → ℝ := fun R => P2 * (DM R * S1 R + SM R * D1 R)
  let D3c : ℝ → ℝ := fun R => P3 * (Ct2 * S2 R + Bt2 * D2c R)
  let B : ℝ → ℝ := fun R => 2 * D3c R
  have hρ : 0 < ρ :=
    lt_min (lt_min hρt1p hρt1b)
      (lt_min (lt_min hρcp hρcb) (lt_min hρt2p hρt2b))
  have hS0 : 0 ≤ S0 := mul_nonneg (mul_nonneg hC0 hBt1) hBc
  have hD0 : 0 ≤ D0 :=
    mul_nonneg hP0
      (add_nonneg (mul_nonneg hCt1 hBc) (mul_nonneg hBt1 hCc))
  have hS1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S1 R := fun R hR =>
    mul_nonneg (mul_nonneg hC1 hR) hS0
  have hD1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ D1 R := fun R hR =>
    mul_nonneg hP1 (add_nonneg hS0 (mul_nonneg hR hD0))
  have hS2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S2 R := fun R hR =>
    mul_nonneg (mul_nonneg hC2 (hSM R hR)) (hS1 R hR)
  have hD2c : ∀ R : ℝ, 0 ≤ R → 0 ≤ D2c R := fun R hR =>
    mul_nonneg hP2
      (add_nonneg (mul_nonneg (hDM R hR) (hS1 R hR))
        (mul_nonneg (hSM R hR) (hD1 R hR)))
  have hD3c : ∀ R : ℝ, 0 ≤ R → 0 ≤ D3c R := fun R hR =>
    mul_nonneg hP3
      (add_nonneg (mul_nonneg hCt2 (hS2 R hR))
        (mul_nonneg hBt2 (hD2c R hR)))
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := fun R hR =>
    mul_nonneg (by norm_num) (hD3c R hR)
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let D : ℝ := D3 + D2 + A * D2 + N
  have hD : 0 ≤ D :=
    add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have h1A : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hNle : N ≤ D := by
    dsimp only [D]
    exact le_add_of_nonneg_left
      (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2))
  have hD2le : D2 ≤ D := by
    dsimp only [D]
    exact second_le_four_term_sum D3 D2 A N hD3 hD2 hA hN
  have hρt1p_le : ρ ≤ ρt1p :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hρt1b_le : ρ ≤ ρt1b :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hρcp_le : ρ ≤ ρcp :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρcb_le : ρ ≤ ρcb :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hρt2p_le : ρ ≤ ρt2p :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρt2b_le : ρ ≤ ρt2b :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hTt1p := hTn.trans hρt1p_le
  have hUt1p := hUn.trans hρt1p_le
  have hTt1b := hTn.trans hρt1b_le
  have hUt1b := hUn.trans hρt1b_le
  have hTcp := hTn.trans hρcp_le
  have hUcp := hUn.trans hρcp_le
  have hTcb := hTn.trans hρcb_le
  have hUcb := hUn.trans hρcb_le
  have hTt2p := hTn.trans hρt2p_le
  have hUt2p := hUn.trans hρt2p_le
  have hUt2b := hUn.trans hρt2b_le
  let TrT : SmoothCcTensor g 3 1 :=
    reindexedPureTrace (I := I) (M := M) g gT 1 (Equiv.refl _)
  let TrU : SmoothCcTensor g 3 1 :=
    reindexedPureTrace (I := I) (M := M) g gU 1 (Equiv.refl _)
  let CnT : SmoothCcTensor g 3 3 :=
    RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT
  let CnU : SmoothCcTensor g 3 3 :=
    RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gU
  let Rt : SmoothCcTensor g 1 1 :=
    cometricRaiseSlot0Field (I := I) (M := M) g 0 T
  let Ru : SmoothCcTensor g 1 1 :=
    cometricRaiseSlot0Field (I := I) (M := M) g 0 U
  let VmT : SmoothCcTensor g 1 4 := lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT
  let VmU : SmoothCcTensor g 1 4 := lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU
  let LvT : SmoothCcTensor g 4 2 := reindexedCometricDoubleTrace (I := I) (M := M) g gT
  let LvU : SmoothCcTensor g 4 2 := reindexedCometricDoubleTrace (I := I) (M := M) g gU
  let Z0T : SmoothCcTensor g 3 1 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 1 TrT CnT
  let Z0U : SmoothCcTensor g 3 1 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 1 TrU CnU
  let Z1T : SmoothCcTensor g 3 1 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 1 1 Rt Z0T
  let Z1U : SmoothCcTensor g 3 1 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 1 1 Ru Z0U
  let Z2T : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 1 4 VmT Z1T
  let Z2U : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 1 4 VmU Z1U
  let Z3T : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 LvT Z2T
  let Z3U : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 LvU Z2U
  have hTrT : covariantJetNormSq (I := I) (M := M) g 2 TrT ≤ Bt1 ^ 2 := by
    dsimp only [TrT]
    rw [covariantJetNormSq_reindexedPureTrace]
    exact ht1b T gT hTtie hTt1b
  have hTrU : covariantJetNormSq (I := I) (M := M) g 2 TrU ≤ Bt1 ^ 2 := by
    dsimp only [TrU]
    rw [covariantJetNormSq_reindexedPureTrace]
    exact ht1b U gU hUtie hUt1b
  have hTrD : covariantJetNormSq (I := I) (M := M) g 2 (TrT - TrU) ≤
      (Ct1 * D) ^ 2 := by
    have hraw := ht1p T U gT gU hTtie hUtie hTt1p hUt1p
    have hmul : Ct1 * ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) (T - U)‖ ≤ Ct1 * D :=
      (mul_le_mul_of_nonneg_left hTUn hCt1).trans
        (mul_le_mul_of_nonneg_left hNle hCt1)
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (TrT - TrU) =
          covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 1 -
              pureTrace (I := I) (M := M) g gU 1) := by
        dsimp only [TrT, TrU]
        rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
      _ ≤ (Ct1 * ‖ccTensorToHs (I := I) (M := M) g 2
          (2 : ℝ) (T - U)‖) ^ 2 := hraw
      _ ≤ (Ct1 * D) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hCt1 (norm_nonneg _)) hmul 2
  have hCnT : covariantJetNormSq (I := I) (M := M) g 2 CnT ≤ Bc ^ 2 := by
    simpa only [CnT] using hcb T gT hTtie hTcb
  have hCnU : covariantJetNormSq (I := I) (M := M) g 2 CnU ≤ Bc ^ 2 := by
    simpa only [CnU] using hcb U gU hUtie hUcb
  have hCnD : covariantJetNormSq (I := I) (M := M) g 2 (CnT - CnU) ≤
      (Cc * D) ^ 2 := by
    have hraw := hcp T U gT gU hTtie hUtie hTcp hUcp
    have hmul : Cc * ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) (T - U)‖ ≤ Cc * D :=
      (mul_le_mul_of_nonneg_left hTUn hCc).trans
        (mul_le_mul_of_nonneg_left hNle hCc)
    exact hraw.trans
      (pow_le_pow_left₀ (mul_nonneg hCc (norm_nonneg _)) hmul 2)
  have hRt : covariantJetNormSq (I := I) (M := M) g 2 Rt ≤ R ^ 2 := by
    simpa only [Rt, covariantJetNormSq_cometricRaiseSlot0Field] using hT2
  have hRu : covariantJetNormSq (I := I) (M := M) g 2 Ru ≤ R ^ 2 := by
    simpa only [Ru, covariantJetNormSq_cometricRaiseSlot0Field] using hU2
  have hRd : covariantJetNormSq (I := I) (M := M) g 2 (Rt - Ru) ≤ D ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Rt - Ru) =
          covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
        dsimp only [Rt, Ru]
        rw [← cometricRaiseSlot0Field_zero_sub, covariantJetNormSq_cometricRaiseSlot0Field]
      _ ≤ D2 ^ 2 := hTU2
      _ ≤ D ^ 2 := pow_le_pow_left₀ hD2 hD2le 2
  have hD3le : D3 ≤ D := by
    dsimp only [D]
    exact first_le_four_term_sum D3 D2 A N hD2 hA hN
  have hrestle : D2 + A * D2 ≤ D := by
    dsimp only [D]
    exact middle_le_four_term_sum D3 D2 A N hD3 hN
  obtain ⟨hVmT, hVmU, hVmD⟩ :=
    hvm gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU
      R A D2 D3 D hR hA hD2 hD3 hD hD3le hrestle
      hT2 hU2 hT3 hU3 hTU2 hTU3
  have hLvU : covariantJetNormSq (I := I) (M := M) g 2 LvU ≤ Bt2 ^ 2 := by
    dsimp only [LvU]
    rw [reindexedCometricDoubleTrace_eq_pureTrace]
    exact ht2b U gU hUtie hUt2b
  have hLvD : covariantJetNormSq (I := I) (M := M) g 2 (LvT - LvU) ≤
      (Ct2 * D) ^ 2 := by
    have hraw := ht2p T U gT gU hTtie hUtie hTt2p hUt2p
    have hmul : Ct2 * ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) (T - U)‖ ≤ Ct2 * D :=
      (mul_le_mul_of_nonneg_left hTUn hCt2).trans
        (mul_le_mul_of_nonneg_left hNle hCt2)
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (LvT - LvU) =
          covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2) := by
        dsimp only [LvT, LvU]
        rw [reindexedCometricDoubleTrace_eq_pureTrace, reindexedCometricDoubleTrace_eq_pureTrace]
      _ ≤ (Ct2 * ‖ccTensorToHs (I := I) (M := M) g 2
          (2 : ℝ) (T - U)‖) ^ 2 := hraw
      _ ≤ (Ct2 * D) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hCt2 (norm_nonneg _)) hmul 2
  have hZ0T : covariantJetNormSq (I := I) (M := M) g 2 Z0T ≤ S0 ^ 2 := by
    simpa only [Z0T, S0] using
      happ0 TrT CnT Bt1 Bc hBt1 hBc hTrT hCnT
  have hZ0D : covariantJetNormSq (I := I) (M := M) g 2 (Z0T - Z0U) ≤
      (D0 * D) ^ 2 := by
    have hraw := hpair0 TrT TrU CnT CnU
      (Ct1 * D) Bt1 Bc (Cc * D)
      (mul_nonneg hCt1 hD) hBt1 hBc (mul_nonneg hCc hD)
      hTrD hTrU hCnT hCnD
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z0T - Z0U) ≤
          (P0 * ((Ct1 * D) * Bc + Bt1 * (Cc * D))) ^ 2 := by
        simpa only [Z0T, Z0U] using hraw
      _ = (D0 * D) ^ 2 := by
        apply congrArg (fun x : ℝ => x ^ 2)
        simp only [D0]
        ring
  have hZ1T : covariantJetNormSq (I := I) (M := M) g 2 Z1T ≤ (S1 R) ^ 2 := by
    simpa only [Z1T, S1] using
      happ1 Rt Z0T R S0 hR hS0 hRt hZ0T
  have hZ1D : covariantJetNormSq (I := I) (M := M) g 2 (Z1T - Z1U) ≤
      (D1 R * D) ^ 2 := by
    have hraw := hpair1 Rt Ru Z0T Z0U D R S0 (D0 * D)
      hD hR hS0 (mul_nonneg hD0 hD) hRd hRu hZ0T hZ0D
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z1T - Z1U) ≤
          (P1 * (D * S0 + R * (D0 * D))) ^ 2 := by
        simpa only [Z1T, Z1U] using hraw
      _ = (D1 R * D) ^ 2 := by
        apply congrArg (fun x : ℝ => x ^ 2)
        simp only [D1]
        ring
  have hZ2T : covariantJetNormSq (I := I) (M := M) g 2 Z2T ≤
      (S2 R * (1 + A)) ^ 2 := by
    have hraw := happ2 VmT Z1T (SM R * (1 + A)) (S1 R)
      (mul_nonneg (hSM R hR) h1A) (hS1 R hR) hVmT hZ1T
    calc
      covariantJetNormSq (I := I) (M := M) g 2 Z2T ≤
          (C2 * (SM R * (1 + A)) * S1 R) ^ 2 := by
        simpa only [Z2T] using hraw
      _ = (S2 R * (1 + A)) ^ 2 := by
        apply congrArg (fun x : ℝ => x ^ 2)
        simp only [S2]
        ring
  have hZ2D : covariantJetNormSq (I := I) (M := M) g 2 (Z2T - Z2U) ≤
      (D2c R * (1 + A) * D) ^ 2 := by
    let u : ℝ := P2 *
      ((DM R * D) * S1 R + (SM R * (1 + A)) * (D1 R * D))
    let v : ℝ := D2c R * (1 + A) * D
    have hu : 0 ≤ u := by
      dsimp only [u]
      exact mul_nonneg hP2
        (add_nonneg (mul_nonneg (mul_nonneg (hDM R hR) hD) (hS1 R hR))
          (mul_nonneg (mul_nonneg (hSM R hR) h1A)
            (mul_nonneg (hD1 R hR) hD)))
    have huv : u ≤ v := by
      have hfirst : DM R * S1 R * D ≤ DM R * S1 R * (1 + A) * D := by
        have hbase : DM R * S1 R ≤ DM R * S1 R * (1 + A) := by
          calc
            DM R * S1 R = DM R * S1 R * 1 := by ring
            _ ≤ DM R * S1 R * (1 + A) :=
              mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_right hA)
                (mul_nonneg (hDM R hR) (hS1 R hR))
        exact mul_le_mul_of_nonneg_right hbase hD
      calc
        u = P2 * (DM R * S1 R * D + SM R * D1 R * (1 + A) * D) := by
          simp only [u]
          ring
        _ ≤ P2 * (DM R * S1 R * (1 + A) * D +
            SM R * D1 R * (1 + A) * D) :=
          mul_le_mul_of_nonneg_left (add_le_add hfirst le_rfl) hP2
        _ = v := by simp only [v, D2c]; ring
    have hraw := hpair2 VmT VmU Z1T Z1U
      (DM R * D) (SM R * (1 + A)) (S1 R) (D1 R * D)
      (mul_nonneg (hDM R hR) hD) (mul_nonneg (hSM R hR) h1A)
      (hS1 R hR) (mul_nonneg (hD1 R hR) hD)
      hVmD hVmU hZ1T hZ1D
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z2T - Z2U) ≤ u ^ 2 := by
        simpa only [Z2T, Z2U, u] using hraw
      _ ≤ v ^ 2 := pow_le_pow_left₀ hu huv 2
      _ = (D2c R * (1 + A) * D) ^ 2 := rfl
  have hZ3D : covariantJetNormSq (I := I) (M := M) g 2 (Z3T - Z3U) ≤
      (D3c R * (1 + A) * D) ^ 2 := by
    have hraw := hpair3 LvT LvU Z2T Z2U
      (Ct2 * D) Bt2 (S2 R * (1 + A)) (D2c R * (1 + A) * D)
      (mul_nonneg hCt2 hD) hBt2 (mul_nonneg (hS2 R hR) h1A)
      (mul_nonneg (mul_nonneg (hD2c R hR) h1A) hD)
      hLvD hLvU hZ2T hZ2D
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z3T - Z3U) ≤
          (P3 * ((Ct2 * D) * (S2 R * (1 + A)) +
            Bt2 * (D2c R * (1 + A) * D))) ^ 2 := by
        simpa only [Z3T, Z3U] using hraw
      _ = (D3c R * (1 + A) * D) ^ 2 := by
        apply congrArg (fun x : ℝ => x ^ 2)
        simp only [D3c]
        ring
  have hcoreT : lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g gT T = Z3T := by rfl
  have hcoreU : lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g gU U = Z3U := by rfl
  have hvb :
      lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gT T -
          lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gU U =
        (2 : ℝ) • (Z3T - Z3U) := by
    simp only [lieCorrectionZeroVectorBundleDerivativeCoefficient, hcoreT, hcoreU]
    module
  rw [hvb, covariantJetNormSq_smul]
  norm_num
  calc
    4 * covariantJetNormSq (I := I) (M := M) g 2 (Z3T - Z3U) ≤
        4 * (D3c R * (1 + A) * D) ^ 2 :=
      mul_le_mul_of_nonneg_left hZ3D (by norm_num)
    _ = (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← mul_pow]
      apply congrArg (fun x : ℝ => x ^ 2)
      simp only [B, D]
      ring

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
