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
  covariantJetNormSq_add_le covariantJetNormSq_nonneg
  covariantJetNormSq_reindexCoeffGen covariantJetNormSq_smul)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Sobolev (metricConnectionDifferenceLoweredCoefficient)
open DifferentialGeometry.Analysis.Spectral
  (ccOperatorFieldComp operatorFieldComposition_sub_left ccTensorToHs pureTrace slotExtendIter)
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

private lemma mul_sq_mul_sq (a b : ℝ) : a ^ 2 * b ^ 2 = (a * b) ^ 2 := by
  rw [mul_pow]

private lemma reassociate_four_factor_sq_left (a b c d : ℝ) :
    (a * (b * d) * c) ^ 2 = (a * b * c * d) ^ 2 := by
  ring

private lemma reassociate_four_factor_sq_left' (a b c d : ℝ) :
    (a * b * (c * d)) ^ 2 = (a * b * c * d) ^ 2 := by
  ring

private lemma factor_common_product (p a b c d : ℝ) :
    p * (a * c * d + b * c * d) = p * (a + b) * c * d := by
  ring

private lemma mixed_pairing_scale_sq (p a b c d e f : ℝ) :
    (p * ((a * d) * (b * c) + e * (f * c * d))) ^ 2 =
      (p * (a * b + e * f) * c * d) ^ 2 := by
  ring

theorem exists_lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (σ : Equiv.Perm (Fin 4))
        (gT gU : SmoothRiemannianMetric I M)
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
          (lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gT g T σ -
            lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gU g U σ) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρ2p, Ct2, hρ2p, hCt2, ht2p⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ2b, Bt2, hρ2b, hBt2, ht2b⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρ3p, Ct3, hρ3p, hCt3, ht3p⟩ :=
    RicciDeTurckLowOrder.trace3_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ3b, Bt3, hρ3b, hBt3, ht3b⟩ :=
    RicciDeTurckLowOrder.trace_three_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρ4p, Ct4, hρ4p, hCt4, ht4p⟩ :=
    RicciDeTurckLowOrder.trace4_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ4b, Bt4, hρ4b, hBt4, ht4b⟩ :=
    RicciDeTurckLowOrder.trace_four_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨B0m, B1m, hB0m, hB1m, hmcdp⟩ :=
    RicciDeTurckLowOrder.mcd_pair_h2 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm, hBm, hmcdb⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Cp, hCp, hprod⟩ := exists_tensorThreeTwoProductCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨C0, hC0, happ0⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 5
  obtain ⟨C1, hC1, happ1⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 5 3
  obtain ⟨P1, hP1, hpair1⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 5 3
  obtain ⟨C2, hC2, happ2⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 6
  obtain ⟨P2, hP2, hpair2⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 6
  obtain ⟨C3, hC3, happ3⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 6 4
  obtain ⟨P3, hP3, hpair3⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 6 4
  obtain ⟨C4, hC4, happ4⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 2
  obtain ⟨P4, hP4, hpair4⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 2
  let fr : ℝ := Module.finrank ℝ E
  let Jm : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g)
  let FP : ℝ := 1 + Cp
  let FM : ℝ := 1 + fr ^ 3
  let M1 : ℝ := 1 + Jm
  let ρ : ℝ := min (min ρ2p ρ2b) (min (min ρ3p ρ3b) (min ρ4p ρ4b))
  let S0 : ℝ → ℝ := fun R => C0 * (FP * R) * M1
  let D0 : ℝ := C0 * FP * M1
  let S1 : ℝ → ℝ := fun R => C1 * Bt3 * S0 R
  let D1 : ℝ → ℝ := fun R => P1 * (Ct3 * S0 R + Bt3 * D0)
  let SM : ℝ → ℝ := fun R => FM * Bm R
  let DM : ℝ → ℝ := fun R => FM * (B0m R + B1m R)
  let S2 : ℝ → ℝ := fun R => C2 * SM R * S1 R
  let D2c : ℝ → ℝ := fun R => P2 * (DM R * S1 R + SM R * D1 R)
  let S3 : ℝ → ℝ := fun R => C3 * Bt4 * S2 R
  let D3c : ℝ → ℝ := fun R => P3 * (Ct4 * S2 R + Bt4 * D2c R)
  let D4c : ℝ → ℝ := fun R => P4 * (Ct2 * S3 R + Bt2 * D3c R)
  let B : ℝ → ℝ := D4c
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hJm : 0 ≤ Jm := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hFP : 0 ≤ FP := add_nonneg (by norm_num) hCp
  have hFM : 0 ≤ FM := add_nonneg (by norm_num) (pow_nonneg hfr 3)
  have hM1 : 0 ≤ M1 := add_nonneg (by norm_num) hJm
  have hρ : 0 < ρ :=
    lt_min (lt_min hρ2p hρ2b)
      (lt_min (lt_min hρ3p hρ3b) (lt_min hρ4p hρ4b))
  have hS0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S0 R := fun R hR =>
    mul_nonneg (mul_nonneg hC0 (mul_nonneg hFP hR)) hM1
  have hD0 : 0 ≤ D0 := mul_nonneg (mul_nonneg hC0 hFP) hM1
  have hS1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S1 R := fun R hR =>
    mul_nonneg (mul_nonneg hC1 hBt3) (hS0 R hR)
  have hD1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ D1 R := fun R hR =>
    mul_nonneg hP1
      (add_nonneg (mul_nonneg hCt3 (hS0 R hR)) (mul_nonneg hBt3 hD0))
  have hSM : ∀ R : ℝ, 0 ≤ R → 0 ≤ SM R := fun R hR =>
    mul_nonneg hFM (hBm R hR)
  have hDM : ∀ R : ℝ, 0 ≤ R → 0 ≤ DM R := fun R hR =>
    mul_nonneg hFM (add_nonneg (hB0m R hR) (hB1m R hR))
  have hS2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S2 R := fun R hR =>
    mul_nonneg (mul_nonneg hC2 (hSM R hR)) (hS1 R hR)
  have hD2c : ∀ R : ℝ, 0 ≤ R → 0 ≤ D2c R := fun R hR =>
    mul_nonneg hP2
      (add_nonneg (mul_nonneg (hDM R hR) (hS1 R hR))
        (mul_nonneg (hSM R hR) (hD1 R hR)))
  have hS3 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S3 R := fun R hR =>
    mul_nonneg (mul_nonneg hC3 hBt4) (hS2 R hR)
  have hD3c : ∀ R : ℝ, 0 ≤ R → 0 ≤ D3c R := fun R hR =>
    mul_nonneg hP3
      (add_nonneg (mul_nonneg hCt4 (hS2 R hR))
        (mul_nonneg hBt4 (hD2c R hR)))
  have hD4c : ∀ R : ℝ, 0 ≤ R → 0 ≤ D4c R := fun R hR =>
    mul_nonneg hP4
      (add_nonneg (mul_nonneg hCt2 (hS3 R hR))
        (mul_nonneg hBt2 (hD3c R hR)))
  refine ⟨ρ, B, hρ, fun R hR => hD4c R hR, ?_⟩
  intro σ gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
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
  have hρ2p_le : ρ ≤ ρ2p := (min_le_left _ _).trans (min_le_left _ _)
  have hρ2b_le : ρ ≤ ρ2b := (min_le_left _ _).trans (min_le_right _ _)
  have hρ3p_le : ρ ≤ ρ3p :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρ3b_le : ρ ≤ ρ3b :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hρ4p_le : ρ ≤ ρ4p :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ4b_le : ρ ≤ ρ4b :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let PrT : SmoothCcTensor g 3 5 := tensorThreeTwoProductCoefficient (I := I) (M := M) g T
  let PrU : SmoothCcTensor g 3 5 := tensorThreeTwoProductCoefficient (I := I) (M := M) g U
  let Mo : SmoothCcTensor g 3 3 := metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g
  let T2T : SmoothCcTensor g 4 2 := reindexedPureTrace (I := I) (M := M) g gT 2 σ
  let T2U : SmoothCcTensor g 4 2 := reindexedPureTrace (I := I) (M := M) g gU 2 σ
  let T3T : SmoothCcTensor g 5 3 := reindexedPureTrace (I := I) (M := M) g gT 3
    DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour
  let T3U : SmoothCcTensor g 5 3 := reindexedPureTrace (I := I) (M := M) g gU 3
    DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour
  let T4T : SmoothCcTensor g 6 4 := reindexedPureTrace (I := I) (M := M) g gT 4
    DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne
  let T4U : SmoothCcTensor g 6 4 := reindexedPureTrace (I := I) (M := M) g gU 4
    DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne
  let McT : SmoothCcTensor g 0 3 :=
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gT g
  let McU : SmoothCcTensor g 0 3 :=
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU g
  let ExT : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 McT
  let ExU : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 McU
  let Z0T : SmoothCcTensor g 3 5 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 5 PrT Mo
  let Z0U : SmoothCcTensor g 3 5 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 5 PrU Mo
  let Z1T : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 5 3 T3T Z0T
  let Z1U : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 5 3 T3U Z0U
  let Z2T : SmoothCcTensor g 3 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 6 ExT Z1T
  let Z2U : SmoothCcTensor g 3 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 6 ExU Z1U
  let Z3T : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 6 4 T4T Z2T
  let Z3U : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 6 4 T4U Z2U
  let Z4T : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 T2T Z3T
  let Z4U : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 T2U Z3U
  have hCp_le : Cp ≤ FP ^ 2 := by
    dsimp only [FP]
    exact le_square_one_add Cp
  have hJm_le : Jm ≤ M1 ^ 2 := by
    dsimp only [M1]
    exact le_square_one_add Jm
  have hPrT : covariantJetNormSq (I := I) (M := M) g 2 PrT ≤ (FP * R) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 PrT ≤
          Cp * covariantJetNormSq (I := I) (M := M) g 2 T := by
        simpa only [PrT] using hprod T
      _ ≤ Cp * R ^ 2 := mul_le_mul_of_nonneg_left hT2 hCp
      _ ≤ FP ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_right hCp_le (sq_nonneg R)
      _ = (FP * R) ^ 2 := mul_sq_mul_sq FP R
  have hPrU : covariantJetNormSq (I := I) (M := M) g 2 PrU ≤ (FP * R) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 PrU ≤
          Cp * covariantJetNormSq (I := I) (M := M) g 2 U := by
        simpa only [PrU] using hprod U
      _ ≤ Cp * R ^ 2 := mul_le_mul_of_nonneg_left hU2 hCp
      _ ≤ FP ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_right hCp_le (sq_nonneg R)
      _ = (FP * R) ^ 2 := mul_sq_mul_sq FP R
  have hPrD : covariantJetNormSq (I := I) (M := M) g 2 (PrT - PrU) ≤
      (FP * D) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (PrT - PrU) =
          covariantJetNormSq (I := I) (M := M) g 2
            (tensorThreeTwoProductCoefficient (I := I) (M := M) g (T - U)) := by
        dsimp only [PrT, PrU]
        rw [tensorThreeTwoProductCoefficient_sub]
      _ ≤ Cp * covariantJetNormSq (I := I) (M := M) g 2 (T - U) := hprod (T - U)
      _ ≤ Cp * D2 ^ 2 := mul_le_mul_of_nonneg_left hTU2 hCp
      _ ≤ FP ^ 2 * D ^ 2 :=
        (mul_le_mul_of_nonneg_right hCp_le (sq_nonneg D2)).trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hD2 hD2le 2) (sq_nonneg FP))
      _ = (FP * D) ^ 2 := mul_sq_mul_sq FP D
  have hMo : covariantJetNormSq (I := I) (M := M) g 2 Mo ≤ M1 ^ 2 := by
    simpa only [Mo, Jm] using hJm_le
  have hT2U : covariantJetNormSq (I := I) (M := M) g 2 T2U ≤ Bt2 ^ 2 := by
    dsimp only [T2U]
    rw [covariantJetNormSq_reindexedPureTrace]
    exact ht2b U gU hUtie (hUn.trans hρ2b_le)
  have hT2D : covariantJetNormSq (I := I) (M := M) g 2 (T2T - T2U) ≤
      (Ct2 * D) ^ 2 := by
    have hraw := ht2p T U gT gU hTtie hUtie
      (hTn.trans hρ2p_le) (hUn.trans hρ2p_le)
    have hmul : Ct2 * ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) (T - U)‖ ≤ Ct2 * D :=
      (mul_le_mul_of_nonneg_left hTUn hCt2).trans
        (mul_le_mul_of_nonneg_left hNle hCt2)
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (T2T - T2U) =
          covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2) := by
        dsimp only [T2T, T2U]
        rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
      _ ≤ (Ct2 * ‖ccTensorToHs (I := I) (M := M) g 2
          (2 : ℝ) (T - U)‖) ^ 2 := hraw
      _ ≤ (Ct2 * D) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hCt2 (norm_nonneg _)) hmul 2
  have hT3T : covariantJetNormSq (I := I) (M := M) g 2 T3T ≤ Bt3 ^ 2 := by
    dsimp only [T3T]
    rw [covariantJetNormSq_reindexedPureTrace]
    exact ht3b T gT hTtie (hTn.trans hρ3b_le)
  have hT3U : covariantJetNormSq (I := I) (M := M) g 2 T3U ≤ Bt3 ^ 2 := by
    dsimp only [T3U]
    rw [covariantJetNormSq_reindexedPureTrace]
    exact ht3b U gU hUtie (hUn.trans hρ3b_le)
  have hT3D : covariantJetNormSq (I := I) (M := M) g 2 (T3T - T3U) ≤
      (Ct3 * D) ^ 2 := by
    have hraw := ht3p T U gT gU hTtie hUtie
      (hTn.trans hρ3p_le) (hUn.trans hρ3p_le)
    have hmul : Ct3 * ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) (T - U)‖ ≤ Ct3 * D :=
      (mul_le_mul_of_nonneg_left hTUn hCt3).trans
        (mul_le_mul_of_nonneg_left hNle hCt3)
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (T3T - T3U) =
          covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 3 -
              pureTrace (I := I) (M := M) g gU 3) := by
        dsimp only [T3T, T3U]
        rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
      _ ≤ (Ct3 * ‖ccTensorToHs (I := I) (M := M) g 2
          (2 : ℝ) (T - U)‖) ^ 2 := hraw
      _ ≤ (Ct3 * D) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hCt3 (norm_nonneg _)) hmul 2
  have hT4U : covariantJetNormSq (I := I) (M := M) g 2 T4U ≤ Bt4 ^ 2 := by
    dsimp only [T4U]
    rw [covariantJetNormSq_reindexedPureTrace]
    exact ht4b U gU hUtie (hUn.trans hρ4b_le)
  have hT4D : covariantJetNormSq (I := I) (M := M) g 2 (T4T - T4U) ≤
      (Ct4 * D) ^ 2 := by
    have hraw := ht4p T U gT gU hTtie hUtie
      (hTn.trans hρ4p_le) (hUn.trans hρ4p_le)
    have hmul : Ct4 * ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) (T - U)‖ ≤ Ct4 * D :=
      (mul_le_mul_of_nonneg_left hTUn hCt4).trans
        (mul_le_mul_of_nonneg_left hNle hCt4)
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (T4T - T4U) =
          covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 4 -
              pureTrace (I := I) (M := M) g gU 4) := by
        dsimp only [T4T, T4U]
        rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
      _ ≤ (Ct4 * ‖ccTensorToHs (I := I) (M := M) g 2
          (2 : ℝ) (T - U)‖) ^ 2 := hraw
      _ ≤ (Ct4 * D) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hCt4 (norm_nonneg _)) hmul 2
  have hMcT : covariantJetNormSq (I := I) (M := M) g 2 McT ≤
      (Bm R * (1 + A)) ^ 2 := by
    simpa only [McT] using
      hmcdb gT T hT hTtie hδ_le hδ0 hδT R A hR hA hT2 hT3
  have hMcU : covariantJetNormSq (I := I) (M := M) g 2 McU ≤
      (Bm R * (1 + A)) ^ 2 := by
    simpa only [McU] using
      hmcdb gU U hU hUtie hδ_le hδ0 hδU R A hR hA hU2 hU3
  let M0 : ℝ := B0m R * D3 + B1m R * D2 + B1m R * A * D2
  have hM0 : 0 ≤ M0 := by
    dsimp only [M0]
    exact add_nonneg
      (add_nonneg (mul_nonneg (hB0m R hR) hD3)
        (mul_nonneg (hB1m R hR) hD2))
      (mul_nonneg (mul_nonneg (hB1m R hR) hA) hD2)
  have hM0le : M0 ≤ (B0m R + B1m R) * D := by
    have hD3le : D3 ≤ D := by
      dsimp only [D]
      exact first_le_four_term_sum D3 D2 A N hD2 hA hN
    have hrestle : D2 + A * D2 ≤ D := by
      dsimp only [D]
      exact middle_le_four_term_sum D3 D2 A N hD3 hN
    calc
      M0 = B0m R * D3 + B1m R * (D2 + A * D2) := by
        simp only [M0]
        ring
      _ ≤ B0m R * D + B1m R * D :=
        add_le_add
          (mul_le_mul_of_nonneg_left hD3le (hB0m R hR))
          (mul_le_mul_of_nonneg_left hrestle (hB1m R hR))
      _ = (B0m R + B1m R) * D := by ring
  have hMcD : covariantJetNormSq (I := I) (M := M) g 2 (McT - McU) ≤ M0 ^ 2 := by
    simpa only [McT, McU, M0] using
      hmcdp gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hfr3_le : fr ^ 3 ≤ FM ^ 2 := by
    dsimp only [FM]
    exact le_square_one_add (fr ^ 3)
  have hExT : covariantJetNormSq (I := I) (M := M) g 2 ExT ≤
      (SM R * (1 + A)) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 ExT ≤
          fr ^ 3 * covariantJetNormSq (I := I) (M := M) g 2 McT := by
        simpa only [ExT, fr] using covariantJetNormSq_slotExtendIter_three_le (I := I) (M := M) g 0 3 McT
      _ ≤ fr ^ 3 * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_left hMcT (pow_nonneg hfr 3)
      _ ≤ FM ^ 2 * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_right hfr3_le (sq_nonneg _)
      _ = (SM R * (1 + A)) ^ 2 := by
        simp only [SM]
        simpa only [mul_assoc] using mul_sq_mul_sq FM (Bm R * (1 + A))
  have hExU : covariantJetNormSq (I := I) (M := M) g 2 ExU ≤
      (SM R * (1 + A)) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 ExU ≤
          fr ^ 3 * covariantJetNormSq (I := I) (M := M) g 2 McU := by
        simpa only [ExU, fr] using covariantJetNormSq_slotExtendIter_three_le (I := I) (M := M) g 0 3 McU
      _ ≤ fr ^ 3 * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_left hMcU (pow_nonneg hfr 3)
      _ ≤ FM ^ 2 * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_right hfr3_le (sq_nonneg _)
      _ = (SM R * (1 + A)) ^ 2 := by
        simp only [SM]
        simpa only [mul_assoc] using mul_sq_mul_sq FM (Bm R * (1 + A))
  have hExD : covariantJetNormSq (I := I) (M := M) g 2 (ExT - ExU) ≤
      (DM R * D) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (ExT - ExU) =
          covariantJetNormSq (I := I) (M := M) g 2
            (slotExtendIter (I := I) (M := M) g 0 3 3 (McT - McU)) := by
        dsimp only [ExT, ExU]
        rw [slotExtendIter_sub]
      _ ≤ fr ^ 3 * covariantJetNormSq (I := I) (M := M) g 2 (McT - McU) := by
        simpa only [fr] using covariantJetNormSq_slotExtendIter_three_le (I := I) (M := M) g 0 3 (McT - McU)
      _ ≤ fr ^ 3 * M0 ^ 2 :=
        mul_le_mul_of_nonneg_left hMcD (pow_nonneg hfr 3)
      _ ≤ fr ^ 3 * ((B0m R + B1m R) * D) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM0 hM0le 2)
          (pow_nonneg hfr 3)
      _ ≤ FM ^ 2 * ((B0m R + B1m R) * D) ^ 2 :=
        mul_le_mul_of_nonneg_right hfr3_le (sq_nonneg _)
      _ = (DM R * D) ^ 2 := by
        simp only [DM]
        simpa only [mul_assoc] using mul_sq_mul_sq FM ((B0m R + B1m R) * D)
  have hZ0T : covariantJetNormSq (I := I) (M := M) g 2 Z0T ≤ (S0 R) ^ 2 := by
    simpa only [Z0T, S0] using
      happ0 PrT Mo (FP * R) M1 (mul_nonneg hFP hR) hM1 hPrT hMo
  have hZ0D : covariantJetNormSq (I := I) (M := M) g 2 (Z0T - Z0U) ≤
      (D0 * D) ^ 2 := by
    have heq : Z0T - Z0U =
        ccOperatorFieldComp (I := I) (M := M) g 3 3 5 (PrT - PrU) Mo := by
      simp only [Z0T, Z0U, operatorFieldComposition_sub_left]
    rw [heq]
    have hraw := happ0 (PrT - PrU) Mo (FP * D) M1
      (mul_nonneg hFP hD) hM1 hPrD hMo
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 3 3 5 (PrT - PrU) Mo) ≤
        (C0 * (FP * D) * M1) ^ 2 := hraw
      _ = (D0 * D) ^ 2 := by
        simp only [D0]
        exact reassociate_four_factor_sq_left C0 FP M1 D
  have hZ1T : covariantJetNormSq (I := I) (M := M) g 2 Z1T ≤ (S1 R) ^ 2 := by
    simpa only [Z1T, S1] using
      happ1 T3T Z0T Bt3 (S0 R) hBt3 (hS0 R hR) hT3T hZ0T
  have hZ1D : covariantJetNormSq (I := I) (M := M) g 2 (Z1T - Z1U) ≤
      (D1 R * D) ^ 2 := by
    have hraw := hpair1 T3T T3U Z0T Z0U
      (Ct3 * D) Bt3 (S0 R) (D0 * D)
      (mul_nonneg hCt3 hD) hBt3 (hS0 R hR) (mul_nonneg hD0 hD)
      hT3D hT3U hZ0T hZ0D
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z1T - Z1U) ≤
          (P1 * ((Ct3 * D) * S0 R + Bt3 * (D0 * D))) ^ 2 := by
        simpa only [Z1T, Z1U] using hraw
      _ = (D1 R * D) ^ 2 := by
        simp only [D1]
        simpa only [one_mul, mul_one] using
          mixed_pairing_scale_sq P1 Ct3 (S0 R) 1 D Bt3 D0
  have hZ2T : covariantJetNormSq (I := I) (M := M) g 2 Z2T ≤
      (S2 R * (1 + A)) ^ 2 := by
    have hraw := happ2 ExT Z1T (SM R * (1 + A)) (S1 R)
      (mul_nonneg (hSM R hR) h1A) (hS1 R hR) hExT hZ1T
    calc
      covariantJetNormSq (I := I) (M := M) g 2 Z2T ≤
          (C2 * (SM R * (1 + A)) * S1 R) ^ 2 := by
        simpa only [Z2T] using hraw
      _ = (S2 R * (1 + A)) ^ 2 := by
        simp only [S2]
        exact reassociate_four_factor_sq_left C2 (SM R) (S1 R) (1 + A)
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
      have hbase : DM R * S1 R ≤ DM R * S1 R * (1 + A) := by
        calc
          DM R * S1 R = DM R * S1 R * 1 := by ring
          _ ≤ DM R * S1 R * (1 + A) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hA)
              (mul_nonneg (hDM R hR) (hS1 R hR))
      have hfirst : DM R * S1 R * D ≤ DM R * S1 R * (1 + A) * D :=
        mul_le_mul_of_nonneg_right hbase hD
      calc
        u = P2 * (DM R * S1 R * D + SM R * D1 R * (1 + A) * D) := by
          simp only [u]
          ring
        _ ≤ P2 * (DM R * S1 R * (1 + A) * D +
            SM R * D1 R * (1 + A) * D) :=
          mul_le_mul_of_nonneg_left (add_le_add hfirst le_rfl) hP2
        _ = v := by
          simp only [v, D2c]
          exact factor_common_product P2 (DM R * S1 R) (SM R * D1 R) (1 + A) D
    have hraw := hpair2 ExT ExU Z1T Z1U
      (DM R * D) (SM R * (1 + A)) (S1 R) (D1 R * D)
      (mul_nonneg (hDM R hR) hD) (mul_nonneg (hSM R hR) h1A)
      (hS1 R hR) (mul_nonneg (hD1 R hR) hD)
      hExD hExU hZ1T hZ1D
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z2T - Z2U) ≤ u ^ 2 := by
        simpa only [Z2T, Z2U, u] using hraw
      _ ≤ v ^ 2 := pow_le_pow_left₀ hu huv 2
      _ = (D2c R * (1 + A) * D) ^ 2 := rfl
  have hZ3T : covariantJetNormSq (I := I) (M := M) g 2 Z3T ≤
      (S3 R * (1 + A)) ^ 2 := by
    have hT4T : covariantJetNormSq (I := I) (M := M) g 2 T4T ≤ Bt4 ^ 2 := by
      dsimp only [T4T]
      rw [covariantJetNormSq_reindexedPureTrace]
      exact ht4b T gT hTtie (hTn.trans hρ4b_le)
    have hraw := happ3 T4T Z2T Bt4 (S2 R * (1 + A))
      hBt4 (mul_nonneg (hS2 R hR) h1A) hT4T hZ2T
    calc
      covariantJetNormSq (I := I) (M := M) g 2 Z3T ≤
          (C3 * Bt4 * (S2 R * (1 + A))) ^ 2 := by
        simpa only [Z3T] using hraw
      _ = (S3 R * (1 + A)) ^ 2 := by
        simp only [S3]
        exact reassociate_four_factor_sq_left' C3 Bt4 (S2 R) (1 + A)
  have hZ3D : covariantJetNormSq (I := I) (M := M) g 2 (Z3T - Z3U) ≤
      (D3c R * (1 + A) * D) ^ 2 := by
    have hraw := hpair3 T4T T4U Z2T Z2U
      (Ct4 * D) Bt4 (S2 R * (1 + A)) (D2c R * (1 + A) * D)
      (mul_nonneg hCt4 hD) hBt4 (mul_nonneg (hS2 R hR) h1A)
      (mul_nonneg (mul_nonneg (hD2c R hR) h1A) hD)
      hT4D hT4U hZ2T hZ2D
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z3T - Z3U) ≤
          (P3 * ((Ct4 * D) * (S2 R * (1 + A)) +
            Bt4 * (D2c R * (1 + A) * D))) ^ 2 := by
        simpa only [Z3T, Z3U] using hraw
      _ = (D3c R * (1 + A) * D) ^ 2 := by
        simp only [D3c]
        exact mixed_pairing_scale_sq P3 Ct4 (S2 R) (1 + A) D Bt4 (D2c R)
  have hZ4D : covariantJetNormSq (I := I) (M := M) g 2 (Z4T - Z4U) ≤
      (D4c R * (1 + A) * D) ^ 2 := by
    have hraw := hpair4 T2T T2U Z3T Z3U
      (Ct2 * D) Bt2 (S3 R * (1 + A)) (D3c R * (1 + A) * D)
      (mul_nonneg hCt2 hD) hBt2 (mul_nonneg (hS3 R hR) h1A)
      (mul_nonneg (mul_nonneg (hD3c R hR) h1A) hD)
      hT2D hT2U hZ3T hZ3D
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z4T - Z4U) ≤
          (P4 * ((Ct2 * D) * (S3 R * (1 + A)) +
            Bt2 * (D3c R * (1 + A) * D))) ^ 2 := by
        simpa only [Z4T, Z4U] using hraw
      _ = (D4c R * (1 + A) * D) ^ 2 := by
        simp only [D4c]
        exact mixed_pairing_scale_sq P4 Ct2 (S3 R) (1 + A) D Bt2 (D3c R)
  have hhalfT : lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gT g T σ = Z4T := by rfl
  have hhalfU : lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gU g U σ = Z4U := by rfl
  simpa only [hhalfT, hhalfU, B, D] using hZ4D

theorem exists_lieCorrectionZeroMixedConnectionDerivativeCoefficient_pairing_secondOrder_bound
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
          (lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gT g T -
            lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gU g U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρ, Bh, hρ, hBh, hhalf⟩ :=
    exists_lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => 4 * Bh R
  refine ⟨ρ, B, hρ, fun R hR => mul_nonneg (by norm_num) (hBh R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let σ1 : Equiv.Perm (Fin 4) :=
    DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  let σ2 : Equiv.Perm (Fin 4) :=
    lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  let X : SmoothCcTensor g 3 2 :=
    lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gT g T σ1 -
      lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gU g U σ1
  let Y : SmoothCcTensor g 3 2 :=
    lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gT g T σ2 -
      lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gU g U σ2
  let S : ℝ := Bh R * (1 + A) * (D3 + D2 + A * D2 + N)
  have hS : 0 ≤ S :=
    mul_nonneg (mul_nonneg (hBh R hR) (add_nonneg (by norm_num) hA))
      (add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN)
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ S ^ 2 := by
    simpa only [X, S, σ1] using
      hhalf σ1 gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδU hδZ hTn hUn
        R A D2 D3 N hR hA hD2 hD3 hN
        hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ S ^ 2 := by
    simpa only [Y, S, σ2] using
      hhalf σ2 gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδU hδZ hTn hUn
        R A D2 D3 N hR hA hD2 hD3 hN
        hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hsum : covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤ (2 * S) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
          covariantJetNormSq (I := I) (M := M) g 2 Y) ≤
        2 * (S ^ 2 + S ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
      _ = (2 * S) ^ 2 := by ring
  have hsplit :
      lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gT g T -
          lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gU g U =
        (2 : ℝ) • (X + Y) := by
    simp only [lieCorrectionZeroMixedConnectionDerivativeCoefficient, X, Y, σ1, σ2]
    module
  rw [hsplit, covariantJetNormSq_smul]
  norm_num
  calc
    4 * covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤
        4 * (2 * S) ^ 2 := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
      simp only [B, S]
      ring

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
