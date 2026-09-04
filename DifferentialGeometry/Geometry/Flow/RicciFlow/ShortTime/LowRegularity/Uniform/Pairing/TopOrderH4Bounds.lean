import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Pairing.FirstOrderPathBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.Lifting.LowerScaleCoefficientBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.BackgroundDifferenceSecondDerivativePairingBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.CenteredPathPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Interpolation
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Inclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Coefficients.LowOrderJetBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle intervalIntegral
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
  (ccTensorToHs_norm_three_sq_le_norm_two_mul_norm_four covariantJetNormSq
    covariantJetNormSq_add_le)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Sobolev (iteratedCovGrad)
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply operatorFieldApplication_add_left operatorFieldComposition_zero_eq_operatorFieldApply operator_field_composition_h2_h2_to_h2_bound ccTensorToHs
   ccTensorToHs_coeff ccTensorToHs_smul deTurckMetricPrincipalDefectTotal hs2_low2 hsJet_le lieCorrectionZeroRiemann
   norm_ccHs_eq_smoothHs oneMinusConnLapSmooth metricPrincipalDefectCurvCoeff smoothCcToTensorHs
   smoothCcToTensorHs_even_norm_eq_toL2_iter)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem riem_action_h2_split
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ D F : ℝ, 0 < ρ ∧ 0 ≤ D ∧ 0 ≤ F ∧
      ∀ (P : SmoothCcTensor g 0 2) (gP : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gP.inner x u v = g.inner x u v +
            ccTensorBilinSymm (I := I) g P x u v) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
        ∀ (W : SmoothCcTensor g 0 2) (R A : ℝ),
          0 ≤ R → 0 ≤ A →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ R →
          covariantJetNormSq (I := I) (M := M) g 2 W ≤ A ^ 2 →
          covariantJetNormSq (I := I) (M := M) g 2
              (operatorFieldApply (I := I) (M := M) g 2 2
                (lieCorrectionZeroRiemann (I := I) (M := M) g gP) W) ≤
            (D * R * A + F * A) ^ 2 := by
  obtain ⟨ρ, Cp, hρ, hCp, hpair⟩ :=
    exists_lieCorrectionZeroRiemann_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g 0 2 2
  let J : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (lieCorrectionZeroRiemann (I := I) (M := M) g g)
  let Q : ℝ := Real.sqrt J
  let D : ℝ := 2 * Ca * Cp
  let F : ℝ := 2 * Ca * Q
  have hJ : 0 ≤ J :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  refine ⟨ρ, D, F, hρ,
    mul_nonneg (mul_nonneg (by norm_num) hCa) hCp,
    mul_nonneg (mul_nonneg (by norm_num) hCa) hQ, ?_⟩
  intro P gP hPtie hPρ W R A hR hA hPR hW
  let Z : SmoothCcTensor g 2 2 :=
    lieCorrectionZeroRiemann (I := I) (M := M) g gP -
      lieCorrectionZeroRiemann (I := I) (M := M) g g
  let Y₁ : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 Z W
  let Y₀ : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2
      (lieCorrectionZeroRiemann (I := I) (M := M) g g) W
  have hzeroTie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v = g.inner x u v +
        ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) from (zero_smul ℝ _).symm,
      ccTensorBilinSymm_smul]
    ring
  have hzeroHs : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) from (zero_smul ℝ _).symm,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact hρ.le
  have hZ : covariantJetNormSq (I := I) (M := M) g 2 Z ≤ (Cp * R) ^ 2 := by
    have hraw := hpair P (0 : SmoothCcTensor g 0 2) gP g
      hPtie hzeroTie hPρ hzeroHs
    have hnorm : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - (0 : SmoothCcTensor g 0 2))‖ ≤ R := by
      simpa only [sub_zero] using hPR
    exact hraw.trans
      (pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hnorm hCp) 2)
  have hY₁ : covariantJetNormSq (I := I) (M := M) g 2 Y₁ ≤
      (Ca * (Cp * R) * A) ^ 2 := by
    simpa only [Y₁, Z, covariantJetNormSq, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ Z W (Cp * R) A (mul_nonneg hCp hR) hA hZ hW
  have hbase : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroRiemann (I := I) (M := M) g g) ≤ Q ^ 2 := by
    simpa only [J, Q] using (Real.sq_sqrt hJ).symm.le
  have hY₀ : covariantJetNormSq (I := I) (M := M) g 2 Y₀ ≤
      (Ca * Q * A) ^ 2 := by
    simpa only [Y₀, covariantJetNormSq, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ (lieCorrectionZeroRiemann (I := I) (M := M) g g) W Q A hQ hA hbase hW
  have hsplit :
      operatorFieldApply (I := I) (M := M) g 2 2
          (lieCorrectionZeroRiemann (I := I) (M := M) g gP) W = Y₁ + Y₀ := by
    dsimp only [Y₁, Y₀, Z]
    rw [← operatorFieldApplication_add_left]
    congr 1
    module
  rw [hsplit]
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (Y₁ + Y₀) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 Y₁ +
          covariantJetNormSq (I := I) (M := M) g 2 Y₀) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 Y₁ Y₀
    _ ≤ 2 * ((Ca * (Cp * R) * A) ^ 2 + (Ca * Q * A) ^ 2) := by
      gcongr
    _ ≤ (D * R * A + F * A) ^ 2 := by
      dsimp only [D, F]
      nlinarith [sq_nonneg (Ca * (Cp * R) * A),
        sq_nonneg (Ca * Q * A),
        mul_nonneg (mul_nonneg (mul_nonneg hCa hCp) hR) hA,
        mul_nonneg (mul_nonneg hCa hQ) hA]

private theorem hs_two_norm_le_of_low_jet
    (g : SmoothRiemannianMetric I M) (Y : SmoothCcTensor g 0 2)
    {A : ℝ} (hA : 0 ≤ A)
    (hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ A ^ 2) :
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
      3 * hsTwoJetC (Module.finrank ℝ E) * A := by
  let C : ℝ := hsTwoJetC (Module.finrank ℝ E)
  have hC : 0 ≤ C := hsTwoJetC_nonneg _
  have hterm : ∀ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤ A := by
    intro j hj
    have hsingle :
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2 ≤
          ∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 i Y‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun i => ‖iteratedCovGrad (I := I) g 0 2 i Y‖ ^ 2)
        (fun i _ => sq_nonneg _) hj
    nlinarith [hsingle.trans hY,
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 j Y)]
  have hsum :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤ 3 * A := by
    calc
      _ ≤ ∑ _j ∈ Finset.range 3, A :=
        Finset.sum_le_sum fun j hj => hterm j hj
      _ = 3 * A := by norm_num
  calc
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        C * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j Y‖ := by
      simpa only [C] using hs_two_le_jet (I := I) (M := M) g 2 Y
    _ ≤ C * (3 * A) := mul_le_mul_of_nonneg_left hsum hC
    _ = 3 * hsTwoJetC (Module.finrank ℝ E) * A := by
      simp only [C]
      ring

theorem rhs_self_bg_corr_action_h2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    (Rcap : ℝ) (hRcap : 0 ≤ Rcap) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ →
        ∀ (hδ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ)
          (hδZ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g
              (0 : SmoothCcTensor g 0 2)) δ)
          {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ Rcap →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (operatorFieldApply (I := I) (M := M) g 2 2
              (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
                  g gB T hδ hδZ s -
                RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
                  g g T hδ hδZ s) T)‖ ≤
          D * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
            (1 + ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) := by
  obtain ⟨C2, hC2, hjet2⟩ := hs2_low2 (I := I) (M := M) g 2
  obtain ⟨C3, hC3, hjet3⟩ := hsJet_le (I := I) (M := M) g 2 3
  obtain ⟨B0, B1, hB0, hB1, hcorr⟩ :=
    exists_lowOrderPathIntegrand_backgroundDifference_covariantJetNormSq_two_tame_bound (I := I) (M := M) hDim g gB
      (hδ₀ := (by norm_num : (1 : ℝ) / 3 < 1))
  obtain ⟨Ca, hCa, happ⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g 0 2 2
  let R0 : ℝ := C2 * Rcap
  let D : ℝ := 3 * hsTwoJetC (Module.finrank ℝ E) * Ca * C2 *
    (B0 R0 + B1 R0 * C3)
  have hR0 : 0 ≤ R0 := mul_nonneg hC2 hRcap
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (hsTwoJetC_nonneg _)) hCa) hC2)
      (add_nonneg (hB0 R0 hR0) (mul_nonneg (hB1 R0 hR0) hC3))
  refine ⟨D, hD, ?_⟩
  intro T δ hδ_le hδ_nonneg hδ hδZ s hs hTcap
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let A : ℝ := B0 R0 + B1 R0 * (C3 * y)
  let Q : ℝ := Ca * A * (C2 * x)
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2
      (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
          g gB T hδ hδZ s -
        RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
          g g T hδ hδZ s) T
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hA : 0 ≤ A := add_nonneg (hB0 R0 hR0)
    (mul_nonneg (hB1 R0 hR0) (mul_nonneg hC3 hy))
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg hCa hA) (mul_nonneg hC2 hx)
  have hT2 : covariantJetNormSq (I := I) (M := M) g 2 T ≤ R0 ^ 2 := by
    exact (hjet2 T).trans (pow_le_pow_left₀ (mul_nonneg hC2 hx)
      (mul_le_mul_of_nonneg_left (by simpa only [x] using hTcap) hC2) 2)
  have hT3sum :
      ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤ (C3 * y) ^ 2 := by
    exact (Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => norm_nonneg (iteratedCovGrad (I := I) g 0 2 j T))).trans
        (pow_le_pow_left₀
          (Finset.sum_nonneg fun j _ =>
            norm_nonneg (iteratedCovGrad (I := I) g 0 2 j T))
          (by
            have h := hjet3 T
            have hthree : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
            rw [hthree] at h
            simpa only [y] using h) 2)
  have hcoeff :
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
              g gB T hδ hδZ s -
            RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
              g g T hδ hδZ s) ≤ A ^ 2 := by
    simpa only [covariantJetNormSq, Nat.reduceAdd, A, mul_assoc] using
      hcorr T hδ_le hδ_nonneg hδ hδZ R0 (C3 * y)
        hR0 (mul_nonneg hC3 hy) hT2 hT3sum s hs
  have hTlow : covariantJetNormSq (I := I) (M := M) g 2 T ≤ (C2 * x) ^ 2 :=
    hjet2 T
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ Q ^ 2 := by
    simpa only [Y, Q, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ
        (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
            g gB T hδ hδZ s -
          RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
            g g T hδ hδZ s)
        T A (C2 * x) hA (mul_nonneg hC2 hx) hcoeff hTlow
  have hsp := hs_two_norm_le_of_low_jet (I := I) (M := M) g Y hQ hY
  change ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
    D * x * (1 + y)
  calc
    _ ≤ 3 * hsTwoJetC (Module.finrank ℝ E) * Q := hsp
    _ = 3 * hsTwoJetC (Module.finrank ℝ E) * Ca * C2 *
        (B0 R0 * x + B1 R0 * C3 * x * y) := by
      dsimp only [Q, A]
      ring
    _ ≤ D * x * (1 + y) := by
      dsimp only [D]
      let K : ℝ := 3 * hsTwoJetC (Module.finrank ℝ E) * Ca * C2
      have hK : 0 ≤ K := by
        dsimp only [K]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) (hsTwoJetC_nonneg _)) hCa) hC2
      have hcore : B0 R0 * x + B1 R0 * C3 * x * y ≤
          (B0 R0 + B1 R0 * C3) * x * (1 + y) := by
        nlinarith [mul_nonneg (hB0 R0 hR0) (mul_nonneg hx hy),
          mul_nonneg (mul_nonneg (hB1 R0 hR0) hC3) hx]
      calc
        3 * hsTwoJetC (Module.finrank ℝ E) * Ca * C2 *
              (B0 R0 * x + B1 R0 * C3 * x * y) =
            K * (B0 R0 * x + B1 R0 * C3 * x * y) := by rfl
        _ ≤ K * ((B0 R0 + B1 R0 * C3) * x * (1 + y)) :=
          mul_le_mul_of_nonneg_left hcore hK
        _ = 3 * hsTwoJetC (Module.finrank ℝ E) * Ca * C2 *
              (B0 R0 + B1 R0 * C3) * x * (1 + y) := by
          dsimp only [K]
          ring

theorem ricciDeTurck_low_order_path_action_h2_bound
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ}, 0 ≤ δ → δ ≤ 1 / 3 →
        ∀ (hδ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ)
          (hδZ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g
              (0 : SmoothCcTensor g 0 2)) δ)
          {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (operatorFieldApply (I := I) (M := M) g 2 2
              (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
                  g gB T hδ hδZ s +
                metricPrincipalDefectCurvCoeff (I := I) g g) T)‖ ≤
          D * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
            (1 + ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2) := by
  obtain ⟨C2, hC2, hjet2⟩ := hs2_low2 (I := I) (M := M) g 2
  obtain ⟨C3, hC3, hjet3⟩ := hsJet_le (I := I) (M := M) g 2 3
  obtain ⟨K0, K2, hK0, hK2, hself⟩ :=
    selfLowJetQBackground (I := I) (M := M) hDim g gB
  obtain ⟨Ca, hCa, happ⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g 0 2 2
  let Ks : ℝ := (K0 2 + K2 2 * C3 ^ 2) * (1 + C3 ^ 2)
  let Qs : ℝ := Real.sqrt Ks
  let Jc : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (metricPrincipalDefectCurvCoeff (I := I) g g)
  let Qc : ℝ := Real.sqrt Jc
  let Q : ℝ := Real.sqrt (2 * (Qs ^ 2 + Qc ^ 2))
  let D : ℝ := 3 * hsTwoJetC (Module.finrank ℝ E) * Ca * Q * C2
  have hKs : 0 ≤ Ks := by
    dsimp only [Ks]
    exact mul_nonneg
      (add_nonneg (hK0 2) (mul_nonneg (hK2 2) (sq_nonneg C3)))
      (add_nonneg (by norm_num) (sq_nonneg C3))
  have hQs : 0 ≤ Qs := Real.sqrt_nonneg _
  have hQs_sq : Qs ^ 2 = Ks := by
    simpa only [Qs] using Real.sq_sqrt hKs
  have hJc : 0 ≤ Jc :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQc : 0 ≤ Qc := Real.sqrt_nonneg _
  have hQc_sq : Qc ^ 2 = Jc := by
    simpa only [Qc] using Real.sq_sqrt hJc
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hQ_sq : Q ^ 2 = 2 * (Qs ^ 2 + Qc ^ 2) := by
    simpa only [Q] using Real.sq_sqrt
      (mul_nonneg (by norm_num) (add_nonneg (sq_nonneg Qs) (sq_nonneg Qc)))
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (hsTwoJetC_nonneg _)) hCa) hQ) hC2
  refine ⟨D, hD, ?_⟩
  intro T _hT δ hδ0 hδ_le hδ hδZ s hs
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let S : SmoothCcTensor g 2 2 :=
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
      g gB T hδ hδZ s
  let C : SmoothCcTensor g 2 2 := metricPrincipalDefectCurvCoeff (I := I) g g
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 (S + C) T
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hsum3 :
      ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤ (C3 * y) ^ 2 := by
    have hsq :
        ∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤
          (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg
        (fun j _ => norm_nonneg (iteratedCovGrad (I := I) g 0 2 j T))
    calc
      _ ≤ (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 := hsq
      _ ≤ (C3 * y) ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ =>
          norm_nonneg (iteratedCovGrad (I := I) g 0 2 j T))
        (by
          have h := hjet3 T
          have hthree : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
          rw [hthree] at h
          simpa only [y] using h) 2
  have hshift :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 ≤
            (C3 * y) ^ 2 := by
    refine (show
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 ≤
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, Nat.reduceAdd]
      nlinarith [sq_nonneg
        ‖iteratedCovGrad (I := I) g 0 2 0 T‖]).trans hsum3
  have hS : covariantJetNormSq (I := I) (M := M) g 2 S ≤
      (Qs * (1 + y ^ 2)) ^ 2 := by
    refine (hself T _hT hδ0 hδ_le hδ hδZ 2 s hs).trans ?_
    let U : ℝ := ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2
    let V : ℝ := ∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2
    have hU : U ≤ (C3 * y) ^ 2 := by simpa only [U] using hshift
    have hV : V ≤ (C3 * y) ^ 2 := by simpa only [V] using hsum3
    have hU0 : 0 ≤ U := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hV0 : 0 ≤ V := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hfirst : K0 2 + K2 2 * U ≤
        (K0 2 + K2 2 * C3 ^ 2) * (1 + y ^ 2) := by
      calc
        K0 2 + K2 2 * U ≤ K0 2 + K2 2 * (C3 * y) ^ 2 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hU (hK2 2))
        _ ≤ (K0 2 + K2 2 * C3 ^ 2) * (1 + y ^ 2) := by
          nlinarith [hK0 2, hK2 2, sq_nonneg C3, sq_nonneg y]
    have hsecond : 1 + V ≤ (1 + C3 ^ 2) * (1 + y ^ 2) := by
      calc
        1 + V ≤ 1 + (C3 * y) ^ 2 := add_le_add le_rfl hV
        _ ≤ (1 + C3 ^ 2) * (1 + y ^ 2) := by
          nlinarith [sq_nonneg C3, sq_nonneg y]
    rw [show (Qs * (1 + y ^ 2)) ^ 2 =
      Ks * (1 + y ^ 2) ^ 2 by rw [mul_pow, hQs_sq]]
    change (K0 2 + K2 2 * U) * (1 + V) ≤
      Ks * (1 + y ^ 2) ^ 2
    calc
      _ ≤ ((K0 2 + K2 2 * C3 ^ 2) * (1 + y ^ 2)) *
          ((1 + C3 ^ 2) * (1 + y ^ 2)) :=
        mul_le_mul hfirst hsecond (add_nonneg (by norm_num) hV0)
          (mul_nonneg
            (add_nonneg (hK0 2) (mul_nonneg (hK2 2) (sq_nonneg C3)))
            (add_nonneg (by norm_num) (sq_nonneg y)))
      _ = Ks * (1 + y ^ 2) ^ 2 := by
        dsimp only [Ks]
        ring
  have hC : covariantJetNormSq (I := I) (M := M) g 2 C ≤
      (Qc * (1 + y ^ 2)) ^ 2 := by
    dsimp only [C]
    change Jc ≤ (Qc * (1 + y ^ 2)) ^ 2
    rw [← hQc_sq]
    exact pow_le_pow_left₀ hQc
      (le_mul_of_one_le_right hQc (by nlinarith [sq_nonneg y])) 2
  have hSC : covariantJetNormSq (I := I) (M := M) g 2 (S + C) ≤
      (Q * (1 + y ^ 2)) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 S C).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2 S +
          covariantJetNormSq (I := I) (M := M) g 2 C) ≤
          2 * ((Qs * (1 + y ^ 2)) ^ 2 +
            (Qc * (1 + y ^ 2)) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hS hC) (by norm_num)
      _ = (Q * (1 + y ^ 2)) ^ 2 := by
        calc
          2 * ((Qs * (1 + y ^ 2)) ^ 2 +
              (Qc * (1 + y ^ 2)) ^ 2) =
              2 * (Qs ^ 2 + Qc ^ 2) * (1 + y ^ 2) ^ 2 := by ring
          _ = Q ^ 2 * (1 + y ^ 2) ^ 2 := by rw [hQ_sq]
          _ = (Q * (1 + y ^ 2)) ^ 2 := by ring
  have hT2 : covariantJetNormSq (I := I) (M := M) g 2 T ≤ (C2 * x) ^ 2 := by
    simpa only [x] using hjet2 T
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤
      (Ca * (Q * (1 + y ^ 2)) * (C2 * x)) ^ 2 := by
    simpa only [Y, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ (S + C) T (Q * (1 + y ^ 2)) (C2 * x)
        (mul_nonneg hQ (add_nonneg (by norm_num) (sq_nonneg y)))
        (mul_nonneg hC2 hx) hSC hT2
  have hsp := hs_two_norm_le_of_low_jet (I := I) (M := M) g Y
    (mul_nonneg
      (mul_nonneg hCa
        (mul_nonneg hQ (add_nonneg (by norm_num) (sq_nonneg y))))
      (mul_nonneg hC2 hx)) hY
  change ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
    D * x * (1 + y ^ 2)
  calc
    _ ≤ 3 * hsTwoJetC (Module.finrank ℝ E) *
        (Ca * (Q * (1 + y ^ 2)) * (C2 * x)) := hsp
    _ = D * x * (1 + y ^ 2) := by
      dsimp only [D]
      ring

private lemma two_mul_le_eps {eta x y : ℝ} (heta : 0 < eta) :
    2 * x * y ≤ eta * x ^ 2 + eta⁻¹ * y ^ 2 := by
  have hinv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
  have hs := mul_nonneg hinv (sq_nonneg (eta * x - y))
  have hexpand :
      eta⁻¹ * (eta * x - y) ^ 2 =
        eta * x ^ 2 - 2 * x * y + eta⁻¹ * y ^ 2 := by
    field_simp [ne_of_gt heta]
    ring
  rw [hexpand] at hs
  linarith

theorem fourth_order_energy_pairing_bound_of_h2_polynomial_bound
    (g : SmoothRiemannianMetric I M)
    (T Y : SmoothCcTensor g 0 2)
    {eta D R : ℝ}
    (heta : 0 < eta) (hR1 : R ≤ 1)
    (hT2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R)
    (hY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        D * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
          (1 + ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2)) :
    2 * |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 T)).toFun
        (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
      eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
        (eta / 2)⁻¹ * D ^ 2 *
          (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let e : ℝ := eta / 2
  let LT : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 T
  let L2T : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 LT
  let LY : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 Y
  have hx : 0 ≤ x := norm_nonneg _
  have he : 0 < e := by
    dsimp only [e]
    positivity
  have hxR : x ≤ R := by simpa only [x] using hT2
  have hx1 : x ≤ 1 := hxR.trans hR1
  have hxy : x ≤ y := by
    let S3 := ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T
    have hinc := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num) S3
    have heq :
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ 3 by norm_num) S3 =
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T := by
      ext i
      simp only [S3, tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]
    simpa only [x, y, S3, heq] using hinc
  have hL2T : ‖L2T‖ = z := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 2 T
    change ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ =
      ‖SmoothCcTensor.toL2 L2T‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [z, norm_ccHs_eq_smoothHs] using heven.symm
  have hLY : ‖LY‖ =
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 1 Y
    change ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) Y‖ =
      ‖SmoothCcTensor.toL2 LY‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [norm_ccHs_eq_smoothHs] using heven.symm
  have hpair :
      |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        ‖L2T‖ * ‖LY‖ := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) L2T LY]
    exact abs_real_inner_le_norm L2T LY
  have hY' :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        D * x + D * x * y ^ 2 := by
    simpa only [x, y] using hY.trans_eq (by ring)
  have hfirst : 2 * z * (D * x) ≤
      e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
    have hsq := pow_le_pow_left₀ hx hxy 2
    have hprod : (D * x) ^ 2 ≤ D ^ 2 * y ^ 2 := by
      have hfac := mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hsq)
      nlinarith
    calc
      2 * z * (D * x) ≤ e * z ^ 2 + e⁻¹ * (D * x) ^ 2 :=
        two_mul_le_eps he
      _ ≤ e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
        simpa only [mul_assoc] using add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr he.le))
  have hsecond : 2 * z * (D * x * y ^ 2) ≤
      e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 4 := by
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hprod : (D * x * y ^ 2) ^ 2 ≤ D ^ 2 * y ^ 4 := by
      have hfac := mul_nonneg (mul_nonneg (sq_nonneg D) (sq_nonneg (y ^ 2)))
        (sub_nonneg.mpr hx2)
      nlinarith [sq_nonneg y]
    calc
      2 * z * (D * x * y ^ 2) ≤
          e * z ^ 2 + e⁻¹ * (D * x * y ^ 2) ^ 2 :=
        two_mul_le_eps he
      _ ≤ e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 4 := by
        simpa only [mul_assoc] using add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr he.le))
  change
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤ _
  calc
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        2 * (z * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖) := by
      rw [← hL2T, ← hLY]
      exact mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ ≤ 2 * z * (D * x + D * x * y ^ 2) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hY'
          (mul_nonneg (by norm_num) (norm_nonneg _))
    _ = 2 * z * (D * x) + 2 * z * (D * x * y ^ 2) := by ring
    _ ≤ (e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2) +
          (e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 4) :=
      add_le_add hfirst hsecond
    _ = eta * z ^ 2 + (eta / 2)⁻¹ * D ^ 2 * (y ^ 2 + y ^ 4) := by
      dsimp only [e]
      ring

theorem fourth_order_energy_pairing_bound_of_h2_action_bound
    (g : SmoothRiemannianMetric I M)
    (T Y : SmoothCcTensor g 0 2)
    {eta C D R : ℝ}
    (heta : 0 < eta) (hC : 0 ≤ C)
    (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (hT2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R)
    (hY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        D * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
            (1 + ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) +
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ *
            (1 + ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖)) :
    2 * |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 T)).toFun
        (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
      eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
        ((eta / 2)⁻¹ * (D ^ 2 + (D + C) ^ 2)) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
        2 * C * R ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 := by
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let e : ℝ := eta / 2
  let LT : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 T
  let L2T : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 LT
  let LY : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 Y
  have hx : 0 ≤ x := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have he : 0 < e := by
    dsimp only [e]
    positivity
  have hxR : x ≤ R := by simpa only [x] using hT2
  have hx1 : x ≤ 1 := hxR.trans hR1
  have hxy : x ≤ y := by
    let S3 := ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T
    have hinc := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num) S3
    have heq :
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ 3 by norm_num) S3 =
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T := by
      ext i
      simp only [S3, tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]
    simpa only [x, y, S3, heq] using hinc
  have hinterp : y ^ 2 ≤ x * z := by
    dsimp only [x, y, z]
    exact ccTensorToHs_norm_three_sq_le_norm_two_mul_norm_four
      (I := I) (M := M) g 2 T
  have hL2T : ‖L2T‖ = z := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 2 T
    change ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ =
      ‖SmoothCcTensor.toL2 L2T‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [z, norm_ccHs_eq_smoothHs] using heven.symm
  have hLY : ‖LY‖ =
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 1 Y
    change ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) Y‖ =
      ‖SmoothCcTensor.toL2 LY‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [norm_ccHs_eq_smoothHs] using heven.symm
  have hpair :
      |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        ‖L2T‖ * ‖LY‖ := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) L2T LY]
    exact abs_real_inner_le_norm L2T LY
  have hY' :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        D * x + (D + C) * x * y + C * x * y ^ 2 := by
    simpa only [x, y] using hY.trans_eq (by ring)
  have hfirst : 2 * z * (D * x) ≤
      e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
    have hsq := pow_le_pow_left₀ hx hxy 2
    have hprod : (D * x) ^ 2 ≤ D ^ 2 * y ^ 2 := by
      have hfac := mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hsq)
      nlinarith
    calc
      2 * z * (D * x) ≤ e * z ^ 2 + e⁻¹ * (D * x) ^ 2 :=
        two_mul_le_eps he
      _ ≤ e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
        simpa only [mul_assoc] using add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr he.le))
  have hsecond : 2 * z * ((D + C) * x * y) ≤
      e * z ^ 2 + e⁻¹ * (D + C) ^ 2 * y ^ 2 := by
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hcore : ((D + C) * x * y) ^ 2 ≤
        (D + C) ^ 2 * y ^ 2 := by
      have hfac := mul_nonneg
        (mul_nonneg (sq_nonneg (D + C)) (sq_nonneg y))
        (sub_nonneg.mpr hx2)
      nlinarith
    calc
      2 * z * ((D + C) * x * y) ≤
          e * z ^ 2 + e⁻¹ * ((D + C) * x * y) ^ 2 :=
        two_mul_le_eps he
      _ ≤ e * z ^ 2 + e⁻¹ * (D + C) ^ 2 * y ^ 2 := by
        simpa only [mul_assoc] using add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hcore (inv_nonneg.mpr he.le))
  have hthird : 2 * z * (C * x * y ^ 2) ≤
      2 * C * R ^ 2 * z ^ 2 := by
    have hxy2 : x * y ^ 2 ≤ R ^ 2 * z := by
      calc
        x * y ^ 2 ≤ x * (x * z) :=
          mul_le_mul_of_nonneg_left hinterp hx
        _ ≤ R ^ 2 * z := by
          have hx2 : x ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hx hxR 2
          nlinarith
    nlinarith [mul_nonneg hC hz, mul_nonneg hR hR]
  change
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤ _
  calc
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        2 * (z * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖) := by
      rw [← hL2T, ← hLY]
      exact mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ ≤ 2 * z * (D * x + (D + C) * x * y + C * x * y ^ 2) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hY' (mul_nonneg (by norm_num) hz)
    _ = 2 * z * (D * x) + 2 * z * ((D + C) * x * y) +
          2 * z * (C * x * y ^ 2) := by ring
    _ ≤ (e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2) +
          (e * z ^ 2 + e⁻¹ * (D + C) ^ 2 * y ^ 2) +
          2 * C * R ^ 2 * z ^ 2 := by
      exact add_le_add (add_le_add hfirst hsecond) hthird
    _ = eta * z ^ 2 +
          (eta / 2)⁻¹ * (D ^ 2 + (D + C) ^ 2) * y ^ 2 +
          2 * C * R ^ 2 * z ^ 2 := by
      dsimp only [e]
      ring

theorem fourth_order_energy_pairing_bound_of_affine_h2_action_bound
    (g : SmoothRiemannianMetric I M)
    (T Y : SmoothCcTensor g 0 2)
    {eta C D R : ℝ}
    (heta : 0 < eta) (hC : 0 ≤ C)
    (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (hT2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R)
    (hY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        D * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
            (1 + ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) +
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ *
            (1 + ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖)) :
    2 * |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 T)).toFun
        (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
      eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
        ((eta / 2)⁻¹ * (D ^ 2 + 2 * (D ^ 2 + C ^ 2))) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
        2 * C * R *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 := by
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let e : ℝ := eta / 2
  let LT : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 T
  let L2T : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 LT
  let LY : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 Y
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have he : 0 < e := by
    dsimp only [e]
    positivity
  have hxR : x ≤ R := by simpa only [x] using hT2
  have hx1 : x ≤ 1 := hxR.trans hR1
  have hxy : x ≤ y := by
    let S3 := ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T
    have hinc := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num) S3
    have heq :
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ 3 by norm_num) S3 =
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T := by
      ext i
      simp only [S3, tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]
    simpa only [x, y, S3, heq] using hinc
  have hinterp : y ^ 2 ≤ x * z := by
    dsimp only [x, y, z]
    exact ccTensorToHs_norm_three_sq_le_norm_two_mul_norm_four
      (I := I) (M := M) g 2 T
  have hL2T : ‖L2T‖ = z := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 2 T
    change ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ =
      ‖SmoothCcTensor.toL2 L2T‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [z, norm_ccHs_eq_smoothHs] using heven.symm
  have hLY : ‖LY‖ =
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 1 Y
    change ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) Y‖ =
      ‖SmoothCcTensor.toL2 LY‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [norm_ccHs_eq_smoothHs] using heven.symm
  have hpair :
      |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        ‖L2T‖ * ‖LY‖ := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) L2T LY]
    exact abs_real_inner_le_norm L2T LY
  have hY' :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        D * x + (D * x + C) * y + C * y ^ 2 := by
    simpa only [x, y] using hY.trans_eq (by ring)
  have hfirst : 2 * z * (D * x) ≤
      e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
    have hsq := pow_le_pow_left₀ hx hxy 2
    have hprod : (D * x) ^ 2 ≤ D ^ 2 * y ^ 2 := by
      have hfac := mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hsq)
      nlinarith
    calc
      2 * z * (D * x) ≤ e * z ^ 2 + e⁻¹ * (D * x) ^ 2 :=
        two_mul_le_eps he
      _ ≤ e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
        simpa only [mul_assoc] using add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr he.le))
  have hsecond : 2 * z * ((D * x + C) * y) ≤
      e * z ^ 2 + e⁻¹ * (2 * (D ^ 2 + C ^ 2)) * y ^ 2 := by
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hcoef : (D * x + C) ^ 2 ≤ 2 * (D ^ 2 + C ^ 2) := by
      nlinarith [sq_nonneg (D * x - C),
        mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hx2)]
    have hcore : ((D * x + C) * y) ^ 2 ≤
        2 * (D ^ 2 + C ^ 2) * y ^ 2 := by
      calc
        ((D * x + C) * y) ^ 2 = (D * x + C) ^ 2 * y ^ 2 := by ring
        _ ≤ 2 * (D ^ 2 + C ^ 2) * y ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg y)
    calc
      2 * z * ((D * x + C) * y) ≤
          e * z ^ 2 + e⁻¹ * ((D * x + C) * y) ^ 2 :=
        two_mul_le_eps he
      _ ≤ e * z ^ 2 + e⁻¹ * (2 * (D ^ 2 + C ^ 2)) * y ^ 2 := by
        simpa only [mul_assoc] using add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hcore (inv_nonneg.mpr he.le))
  have hthird : 2 * z * (C * y ^ 2) ≤
      2 * C * R * z ^ 2 := by
    have hy2 : y ^ 2 ≤ R * z := hinterp.trans (by
      exact mul_le_mul_of_nonneg_right hxR hz)
    nlinarith [mul_nonneg hC hz, mul_nonneg hR hz]
  change
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤ _
  calc
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        2 * (z * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖) := by
      rw [← hL2T, ← hLY]
      exact mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ ≤ 2 * z * (D * x + (D * x + C) * y + C * y ^ 2) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hY' (mul_nonneg (by norm_num) hz)
    _ = 2 * z * (D * x) + 2 * z * ((D * x + C) * y) +
          2 * z * (C * y ^ 2) := by ring
    _ ≤ (e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2) +
          (e * z ^ 2 + e⁻¹ * (2 * (D ^ 2 + C ^ 2)) * y ^ 2) +
          2 * C * R * z ^ 2 := by
      exact add_le_add (add_le_add hfirst hsecond) hthird
    _ = eta * z ^ 2 +
          (eta / 2)⁻¹ * (D ^ 2 + 2 * (D ^ 2 + C ^ 2)) * y ^ 2 +
          2 * C * R * z ^ 2 := by
      dsimp only [e]
      ring

theorem fourth_order_energy_pairing_bound_of_linear_quadratic_h2_action_bound
    (g : SmoothRiemannianMetric I M)
    (T Y : SmoothCcTensor g 0 2)
    {eta C D E R : ℝ}
    (heta : 0 < eta) (hC : 0 ≤ C)
    (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (hT2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R)
    (hY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        D * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
            (1 + ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) +
          E * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ +
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2) :
    2 * |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 T)).toFun
        (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
      eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
        ((eta / 3)⁻¹ * (2 * D ^ 2 + E ^ 2)) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
        2 * C * R *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 := by
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let e : ℝ := eta / 3
  let LT : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 T
  let L2T : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 LT
  let LY : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 Y
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have he : 0 < e := by
    dsimp only [e]
    positivity
  have hxR : x ≤ R := by simpa only [x] using hT2
  have hx1 : x ≤ 1 := hxR.trans hR1
  have hxy : x ≤ y := by
    let S3 := ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T
    have hinc := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num) S3
    have heq :
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ 3 by norm_num) S3 =
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T := by
      ext i
      simp only [S3, tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]
    simpa only [x, y, S3, heq] using hinc
  have hinterp : y ^ 2 ≤ x * z := by
    dsimp only [x, y, z]
    exact ccTensorToHs_norm_three_sq_le_norm_two_mul_norm_four
      (I := I) (M := M) g 2 T
  have hL2T : ‖L2T‖ = z := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 2 T
    change ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ =
      ‖SmoothCcTensor.toL2 L2T‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [z, norm_ccHs_eq_smoothHs] using heven.symm
  have hLY : ‖LY‖ =
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 1 Y
    change ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) Y‖ =
      ‖SmoothCcTensor.toL2 LY‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [norm_ccHs_eq_smoothHs] using heven.symm
  have hpair :
      |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        ‖L2T‖ * ‖LY‖ := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) L2T LY]
    exact abs_real_inner_le_norm L2T LY
  have hY' :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        D * x + D * x * y + E * y + C * y ^ 2 := by
    simpa only [x, y] using hY.trans_eq (by ring)
  have hfirst : 2 * z * (D * x) ≤
      e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
    have hsq := pow_le_pow_left₀ hx hxy 2
    have hprod : (D * x) ^ 2 ≤ D ^ 2 * y ^ 2 := by
      have hfac := mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hsq)
      nlinarith
    calc
      2 * z * (D * x) ≤ e * z ^ 2 + e⁻¹ * (D * x) ^ 2 :=
        two_mul_le_eps he
      _ ≤ e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
        simpa only [mul_assoc] using add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr he.le))
  have hsecond : 2 * z * (D * x * y) ≤
      e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hprod : (D * x * y) ^ 2 ≤ D ^ 2 * y ^ 2 := by
      have hfac := mul_nonneg (mul_nonneg (sq_nonneg D) (sq_nonneg y))
        (sub_nonneg.mpr hx2)
      nlinarith
    calc
      2 * z * (D * x * y) ≤ e * z ^ 2 + e⁻¹ * (D * x * y) ^ 2 :=
        two_mul_le_eps he
      _ ≤ e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
        simpa only [mul_assoc] using add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr he.le))
  have hthird : 2 * z * (E * y) ≤
      e * z ^ 2 + e⁻¹ * E ^ 2 * y ^ 2 := by
    simpa only [mul_pow, mul_assoc] using
      two_mul_le_eps (x := z) (y := E * y) he
  have hfourth : 2 * z * (C * y ^ 2) ≤
      2 * C * R * z ^ 2 := by
    have hy2 : y ^ 2 ≤ R * z := hinterp.trans
      (mul_le_mul_of_nonneg_right hxR hz)
    nlinarith [mul_nonneg hC hz, mul_nonneg hR hz]
  change
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤ _
  calc
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        2 * (z * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖) := by
      rw [← hL2T, ← hLY]
      exact mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ ≤ 2 * z * (D * x + D * x * y + E * y + C * y ^ 2) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hY' (mul_nonneg (by norm_num) hz)
    _ = 2 * z * (D * x) + 2 * z * (D * x * y) +
          2 * z * (E * y) + 2 * z * (C * y ^ 2) := by ring
    _ ≤ (e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2) +
          (e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2) +
          (e * z ^ 2 + e⁻¹ * E ^ 2 * y ^ 2) +
          2 * C * R * z ^ 2 := by
      exact add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth
    _ = eta * z ^ 2 + (eta / 3)⁻¹ * (2 * D ^ 2 + E ^ 2) * y ^ 2 +
          2 * C * R * z ^ 2 := by
      dsimp only [e]
      ring

theorem ricciDeTurck_remainder_pairing_h4_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta2 R2 : ℝ,
        0 < delta2 ∧ delta2 ≤ 1 / 3 ∧ 0 < R2 ∧ R2 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∃ G : ℝ, 0 ≤ G ∧
            ∀ (T : SmoothCcTensor g 0 2)
              (_hTsymm : ∀ (x : M) (u v : TangentSpace I x),
                ccTensorBilin (I := I) g T x u v =
                  ccTensorBilin (I := I) g T x v u)
              {delta : ℝ}, delta ≤ delta2 → 0 ≤ delta →
              ∀ (hdelta : gFibreOpBound (I := I) (M := M) g
                  (ccTensorBilinSymm (I := I) g T) delta)
                (hdeltaZ : gFibreOpBound (I := I) (M := M) g
                  (ccTensorBilinSymm (I := I) g
                    (0 : SmoothCcTensor g 0 2)) delta)
                {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
              ∀ {R : ℝ}, 0 ≤ R → R ≤ R2 →
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
              let gs := metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s
              let R0 := rhsDecomposition0 (I := I) (M := M) g gBase T
                hdelta hdeltaZ s
              let K0 := metricPrincipalDefectCurvCoeff (I := I) g g
              let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
              let HT := iteratedCovGrad (I := I) g 0 2 2 T
              let HLT := iteratedCovGrad (I := I) g 0 2 2 LT
              let Q : SmoothCcTensor g 0 2 → SmoothCcTensor g 2 2 := fun U =>
                ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
                  ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
              let Z := operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T
              let Cross :=
                operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T +
                  operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT
              let PairComm :=
                oneMinusConnLapSmooth (I := I) g 0 2 Z -
                  operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T -
                  operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT + Z
              let C : SmoothCcTensor g 4 2 :=
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gs -
                  deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
              let J :=
                oneMinusConnLapSmooth (I := I) g 0 2
                    (operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T) +
                  PairComm +
                  (oneMinusConnLapSmooth (I := I) g 0 2
                      (operatorFieldApply (I := I) (M := M) g 4 2 C HT) -
                    operatorFieldApply (I := I) (M := M) g 4 2 C HLT) - Z
              let V := oneMinusConnLapSmooth (I := I) g 0 2 LT
              2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                    (J + Cross).toFun| ≤
                eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                  G * (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
                    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
  intro eta heta
  obtain ⟨delta2, R2, hdelta2, hdelta2third, hR2, hR2one, hcenter⟩ :=
    edge_center_pairing_abs_of_carrier_bound (I := I) (M := M)
      hDim gBase hΛ heta
  refine ⟨delta2, R2, hdelta2, hdelta2third, hR2, hR2one, ?_⟩
  intro g hEq hjet
  obtain ⟨Gd, hGd, hcenterG⟩ := hcenter g hEq hjet
  obtain ⟨D, hD, hcarrier⟩ :=
    ricciDeTurck_low_order_path_action_h2_bound (I := I) (M := M) hDim g gBase
  let Gc : ℝ := (eta / 8)⁻¹ * D ^ 2
  let G : ℝ := Gc + Gd
  have hGc : 0 ≤ Gc := by
    dsimp only [Gc]
    exact mul_nonneg (inv_nonneg.mpr (by positivity)) (sq_nonneg D)
  have hG : 0 ≤ G := add_nonneg hGc hGd
  refine ⟨G, hG, ?_⟩
  intro T hTsymm delta hdelta_le hdelta0 hdelta hdeltaZ s hs
    R hR hRle hT2
  let A : SmoothCcTensor g 2 2 :=
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
        g gBase T hdelta hdeltaZ s +
      metricPrincipalDefectCurvCoeff (I := I) g g
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 A T
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  have hdelta_third : delta ≤ 1 / 3 := hdelta_le.trans hdelta2third
  have hY := hcarrier T hTsymm hdelta0 hdelta_third
    hdelta hdeltaZ hs
  have hRone : R ≤ 1 := hRle.trans hR2one
  have hpair := fourth_order_energy_pairing_bound_of_h2_polynomial_bound
    (I := I) (M := M) g T Y (eta := eta / 4)
    (by positivity) hRone hT2 (by
      simpa only [A, Y] using hY)
  have hpair' :
      2 * |tensorL2Inner (I := I) (M := M) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2 T)).toFun
          (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
        (eta / 4) *
            ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
          Gc * (y ^ 2 + y ^ 4) := by
    have heq : eta / 4 / 2 = eta / 8 := by ring
    simpa only [Gc, y, heq] using hpair
  have hassembled := hcenterG T hTsymm hdelta_le hdelta0
    hdelta hdeltaZ hs hR hRle hT2 (Lc := Gc * (y ^ 2 + y ^ 4)) (by
      simpa only [Y, A, y] using hpair')
  dsimp only at hassembled ⊢
  have hy4 : 0 ≤ y ^ 4 := by positivity
  calc
    _ ≤ eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
        Gc * (y ^ 2 + y ^ 4) + Gd * y ^ 2 := by
      simpa only [y] using hassembled
    _ ≤ eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
        G * (y ^ 2 + y ^ 4) := by
      dsimp only [G]
      nlinarith [mul_nonneg hGd hy4]

theorem ricciDeTurck_remainder_path_pairing_h4_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta2 R2 : ℝ,
        0 < delta2 ∧ delta2 ≤ 1 / 3 ∧ 0 < R2 ∧ R2 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∃ G : ℝ, 0 ≤ G ∧
            ∀ (T : SmoothCcTensor g 0 2)
              (_hTsymm : ∀ (x : M) (u v : TangentSpace I x),
                ccTensorBilin (I := I) g T x u v =
                  ccTensorBilin (I := I) g T x v u)
              {delta : ℝ}, delta ≤ delta2 → 0 ≤ delta →
              ∀ (hdelta_lt : delta < 1)
                (hdelta : gFibreOpBound (I := I) (M := M) g
                  (ccTensorBilinSymm (I := I) g T) delta)
                (hdeltaZ : gFibreOpBound (I := I) (M := M) g
                  (ccTensorBilinSymm (I := I) g
                    (0 : SmoothCcTensor g 0 2)) delta)
                {R : ℝ}, 0 ≤ R → R ≤ R2 →
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
              let P0 := ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g gBase T 0
                hdelta_lt hdelta hdelta_lt hdeltaZ
              let P2 := rhsTopPathIntegral (I := I) (M := M) g T 0
                hdelta_lt hdelta hdelta_lt hdeltaZ
              let K0 := metricPrincipalDefectCurvCoeff (I := I) g g
              let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
              let HT := iteratedCovGrad (I := I) g 0 2 2 T
              let HLT := iteratedCovGrad (I := I) g 0 2 2 LT
              let B02 :=
                oneMinusConnLapSmooth (I := I) g 0 2
                    (operatorFieldApply (I := I) (M := M) g 2 2 P0 T) +
                  (oneMinusConnLapSmooth (I := I) g 0 2
                      (operatorFieldApply (I := I) (M := M) g 4 2 P2 HT) -
                    operatorFieldApply (I := I) (M := M) g 4 2 P2 HLT)
              let V := oneMinusConnLapSmooth (I := I) g 0 2 LT
              2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                    (B02 + operatorFieldApply (I := I) (M := M) g 2 2 K0 LT).toFun| ≤
                eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                  G * (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
                    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
  intro eta heta
  obtain ⟨delta2, R2, hdelta2, hdelta2third, hR2, hR2one, hpoint⟩ :=
    ricciDeTurck_remainder_pairing_h4_uniform_bound (I := I) (M := M) hDim gBase hΛ heta
  refine ⟨delta2, R2, hdelta2, hdelta2third, hR2, hR2one, ?_⟩
  intro g hEq hjet
  obtain ⟨G, hG, hpointG⟩ := hpoint g hEq hjet
  refine ⟨G, hG, ?_⟩
  intro T hTsymm delta hdelta_le hdelta0 hdelta_lt hdelta hdeltaZ R hR hRle hT2
  let P0 := ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g gBase T 0
    hdelta_lt hdelta hdelta_lt hdeltaZ
  let P2 := rhsTopPathIntegral (I := I) (M := M) g T 0
    hdelta_lt hdelta hdelta_lt hdeltaZ
  let K0 := metricPrincipalDefectCurvCoeff (I := I) g g
  let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
  let HT := iteratedCovGrad (I := I) g 0 2 2 T
  let HLT := iteratedCovGrad (I := I) g 0 2 2 LT
  let B02 :=
    oneMinusConnLapSmooth (I := I) g 0 2
        (operatorFieldApply (I := I) (M := M) g 2 2 P0 T) +
      (oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 4 2 P2 HT) -
        operatorFieldApply (I := I) (M := M) g 4 2 P2 HLT)
  let V := oneMinusConnLapSmooth (I := I) g 0 2 LT
  let Js := fun s : ℝ =>
    let gs := metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s
    let R0s := rhsDecomposition0 (I := I) (M := M) g gBase T hdelta hdeltaZ s
    let Qs := fun U : SmoothCcTensor g 0 2 =>
      ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
        ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
    let Zs := operatorFieldApply (I := I) (M := M) g 2 2 (Qs T) T
    let PairComms := oneMinusConnLapSmooth (I := I) g 0 2 Zs -
      operatorFieldApply (I := I) (M := M) g 2 2 (Qs LT) T -
      operatorFieldApply (I := I) (M := M) g 2 2 (Qs T) LT + Zs
    let Cs := deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gs -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
    oneMinusConnLapSmooth (I := I) g 0 2
        (operatorFieldApply (I := I) (M := M) g 2 2 (R0s + K0) T) +
      PairComms +
      (oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 4 2 Cs HT) -
        operatorFieldApply (I := I) (M := M) g 4 2 Cs HLT) - Zs
  let Crosss := fun s : ℝ =>
    let Qs := fun U : SmoothCcTensor g 0 2 =>
      ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
        ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
    operatorFieldApply (I := I) (M := M) g 2 2 (Qs LT) T +
      operatorFieldApply (I := I) (M := M) g 2 2 (Qs T) LT
  let f : ℝ → ℝ := fun s => Inner.inner ℝ V (Js s + Crosss s)
  let Cb : ℝ :=
    eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
      G * (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4)
  obtain ⟨hpair, hfInt⟩ :=
    centeredPathPairing_eq_intervalIntegral_and_intervalIntegrable
      (I := I) (M := M) g gBase T V hTsymm hdelta_lt hdelta hdeltaZ
  have hfInt' : IntervalIntegrable f volume 0 1 := by
    simpa only [f, Js, Crosss, V, LT, HT, HLT, K0] using hfInt
  have hpointwise : ∀ s ∈ Set.Icc (0 : ℝ) 1, 2 * |f s| ≤ Cb := by
    intro s hs
    simpa only [f, Cb, Js, Crosss, V, LT, HT, HLT, K0,
      SmoothCcTensor.inner_def] using
      hpointG T hTsymm hdelta_le hdelta0 hdelta hdeltaZ hs hR hRle hT2
  have habs := intervalIntegral.abs_integral_le_integral_abs
    (μ := volume) (f := f) (a := (0 : ℝ)) (b := 1) (by norm_num)
  have hmono : (∫ s in (0 : ℝ)..1, 2 * |f s|) ≤
      ∫ _s in (0 : ℝ)..1, Cb := by
    exact intervalIntegral.integral_mono_on (by norm_num)
      (hfInt'.abs.const_mul 2) _root_.intervalIntegrable_const hpointwise
  change 2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
      (B02 + operatorFieldApply (I := I) (M := M) g 2 2 K0 LT).toFun| ≤ Cb
  calc
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
        (B02 + operatorFieldApply (I := I) (M := M) g 2 2 K0 LT).toFun| =
        2 * |∫ s in (0 : ℝ)..1, f s| := by
      rw [← SmoothCcTensor.inner_def]
      generalize hleft : Inner.inner ℝ V
        (B02 + operatorFieldApply (I := I) (M := M) g 2 2 K0 LT) = lhs
        at hpair ⊢
      generalize hright : (∫ s in (0 : ℝ)..1, f s) = rhs at hpair ⊢
      exact congrArg (fun z : ℝ => 2 * |z|) hpair
    _ ≤ 2 * (∫ s in (0 : ℝ)..1, |f s|) :=
      mul_le_mul_of_nonneg_left habs (by norm_num)
    _ = ∫ s in (0 : ℝ)..1, 2 * |f s| := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ _s in (0 : ℝ)..1, Cb := hmono
    _ = Cb := by
      rw [intervalIntegral.integral_const]
      norm_num

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
