import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.H1Jet
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJetInterpolation
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.LowOrderCoefficientJetBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Morrey
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.MixedTensorApplicationThirdOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.ConvexJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.CenteredTopOrderPairingH5Bounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
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
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Elliptic (riemannianFiberNormSq)
open DifferentialGeometry.Analysis.Sobolev (iteratedCovGrad)
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply ccTensorToHs ccToHs_norm_mono covsum_hs_three
    deTurckMetricPrincipalDefectTotal h3CovsumC h3CovsumC_nonneg hs2_fiber_sq_action
    hs2FibreActionC hs2FibreAct_nonneg hsJet_le hs_le_jet norm_ccHs_eq_smoothHs oneMinusConnLapSmooth
    oneMinusConnLapSmoothIter metricPrincipalDefectCurvCoeff smoothCcToTensorHs
    smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap smoothCcToTensorHs_coeff
    tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
    tensorL2Inner_eq_tsum_l2Coeff_cross_arm tensorResolventL2_isCompactOperator)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem oneMinusConnLapSmooth_pair_h5_h3
    (g : SmoothRiemannianMetric I M)
    (T Y : SmoothCcTensor g 0 2) :
    |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2 T))).toFun
        (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
      ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ *
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) Y‖ := by
  classical
  let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
  let L2T := oneMinusConnLapSmooth (I := I) g 0 2 LT
  let L3T := oneMinusConnLapSmooth (I := I) g 0 2 L2T
  let LY := oneMinusConnLapSmooth (I := I) g 0 2 Y
  have hL2iter : L2T = oneMinusConnLapSmoothIter (I := I) g 0 2 2 T := by
    simp only [L2T, LT, oneMinusConnLapSmoothIter]
  have hL3iter : L3T = oneMinusConnLapSmoothIter (I := I) g 0 2 3 T := by
    simp only [L3T, L2T, LT, oneMinusConnLapSmoothIter]
  have hLYiter : LY = oneMinusConnLapSmoothIter (I := I) g 0 2 1 Y := by
    simp only [LY, oneMinusConnLapSmoothIter]
  have hinner :
      tensorL2Inner (I := I) (M := M) g 0 2 L3T.toFun LY.toFun =
        (inner ℝ
          (smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ) L2T)
          (smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ) LY) : ℝ) := by
    rw [tensorL2Inner_eq_tsum_l2Coeff_cross_arm
      (I := I) (M := M) g L3T LY,
      tensorHs.inner_def]
    refine tsum_congr (fun i => ?_)
    rw [smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff,
      hL2iter, hLYiter, hL3iter,
      tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
        (I := I) (M := M) g
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) T i 2,
      tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
        (I := I) (M := M) g
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) Y i 1,
      tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
        (I := I) (M := M) g
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) T i 3]
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast]
    ring
  have hTnorm :
      ‖smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ) L2T‖ =
        ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ := by
    rw [norm_ccHs_eq_smoothHs]
    have h5 := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
      (I := I) (M := M) g 3 T
    have h3 := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
      (I := I) (M := M) g 1 LT
    have h5' :
        ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) LT‖ := by
      simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one] using h5
    have h3' :
        ‖smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) LT‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ) L2T‖ := by
      simpa only [L2T, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one] using h3
    exact (h5'.trans h3').symm
  have hYnorm :
      ‖smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ) LY‖ =
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) Y‖ := by
    rw [norm_ccHs_eq_smoothHs]
    have h3 := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
      (I := I) (M := M) g 1 Y
    have h3' :
        ‖smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) Y‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ) LY‖ := by
      simpa only [LY, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one] using h3
    exact h3'.symm
  change |tensorL2Inner (I := I) (M := M) g 0 2 L3T.toFun LY.toFun| ≤ _
  rw [hinner, ← hTnorm, ← hYnorm]
  exact abs_real_inner_le_norm _ _

theorem ricciDeTurck_low_order_path_action_h3_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Lambda : ℝ}
    (hLambda : 1 ≤ Lambda) :
    ∀ g : SmoothRiemannianMetric I M,
      MetricUniformEquivalentOn (I := I) Set.univ gBase g Lambda →
      (∀ a : ℕ, a ≤ 3 →
        MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Lambda) →
      ∃ D : ℝ, 0 ≤ D ∧
        ∀ (T : SmoothCcTensor g 0 2)
          (_hTsymm : ∀ (x : M) (u v : TangentSpace I x),
            ccTensorBilin (I := I) g T x u v =
              ccTensorBilin (I := I) g T x v u)
          {delta : ℝ}, delta ≤ 1 / 3 → 0 ≤ delta →
          ∀ (hdelta : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g T) delta)
            (hdeltaZ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g
                (0 : SmoothCcTensor g 0 2)) delta)
            {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
          ∀ {R : ℝ}, R ≤ 1 →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          let A := RicciDeTurckLowOrder.pathIntegrand
              (I := I) (M := M) g gBase T hdelta hdeltaZ s +
            metricPrincipalDefectCurvCoeff (I := I) g gBase g
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
              (operatorFieldApply (I := I) (M := M) g 2 2 A T)‖ ≤
            D *
              (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ +
                ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
                  ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ +
                ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
                  ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ *
                  ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖) := by
  obtain ⟨Ca, hCa, happ⟩ :=
    operatorFieldComposition_h3_sup_uniform_bound (I := I) (M := M) gBase Lambda 0 2 2
  obtain ⟨Cm0, hCm0, hmor0⟩ :=
    morreyRS_uniform (I := I) (M := M) hDim gBase hLambda 0 2
  obtain ⟨Cm2, hCm2, hmor2⟩ :=
    morreyRS_uniform (I := I) (M := M) hDim gBase hLambda 2 2
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hLambda
  let Ct : ℝ := hs2FibreActionC Cm0 Kcurv.rankTwo
  let Cj : ℝ := h3CovsumC Kcurv.rankTwo Kcurv.rankThree
  have hCt : 0 ≤ Ct := by
    dsimp only [Ct]
    exact hs2FibreAct_nonneg hCm0 _
  have hCj : 0 ≤ Cj := by
    dsimp only [Cj]
    exact h3CovsumC_nonneg _ _
  intro g hEq hjet
  obtain ⟨hact2, hact3⟩ := hKcurv.bounds g hEq hjet
  obtain ⟨K0, K2, hK0, hK2, hself⟩ :=
    selfLowJetQBackground (I := I) (M := M) hDim g gBase
  obtain ⟨C3, hC3, hjet3⟩ := hsJet_le (I := I) (M := M) g 2 3
  obtain ⟨C4, hC4, hjet4⟩ := hsJet_le (I := I) (M := M) g 2 4
  obtain ⟨Ch, hCh, hhs⟩ := hs_le_jet (I := I) (M := M) g 2 3
  let A3 : ℝ := (K0 3 + K2 3 * C3 ^ 2) * (1 + C4 ^ 2)
  let A2 : ℝ := (K0 2 + K2 2 * C3 ^ 2) * (1 + C3 ^ 2)
  let Jc3 : ℝ := covariantJetNormSq (I := I) (M := M) g 3
    (metricPrincipalDefectCurvCoeff (I := I) g gBase g)
  let Jc2 : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (metricPrincipalDefectCurvCoeff (I := I) g gBase g)
  let B3 : ℝ := 2 * (A3 + Jc3)
  let B2 : ℝ := 2 * (A2 + Jc2)
  let K3 : ℝ := Ca * Ct ^ 2 * B3
  let K2a : ℝ := Ca * Cm2 ^ 2 * B2 * Cj ^ 2
  let K : ℝ := 2 * (K3 + K2a)
  let D : ℝ := 2 * Ch * Real.sqrt K
  have hA3 : 0 ≤ A3 := by
    dsimp only [A3]
    exact mul_nonneg
      (add_nonneg (hK0 3) (mul_nonneg (hK2 3) (sq_nonneg C3)))
      (add_nonneg (by norm_num) (sq_nonneg C4))
  have hA2 : 0 ≤ A2 := by
    dsimp only [A2]
    exact mul_nonneg
      (add_nonneg (hK0 2) (mul_nonneg (hK2 2) (sq_nonneg C3)))
      (add_nonneg (by norm_num) (sq_nonneg C3))
  have hJc3 : 0 ≤ Jc3 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hJc2 : 0 ≤ Jc2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB3 : 0 ≤ B3 := mul_nonneg (by norm_num) (add_nonneg hA3 hJc3)
  have hB2 : 0 ≤ B2 := mul_nonneg (by norm_num) (add_nonneg hA2 hJc2)
  have hK3 : 0 ≤ K3 := by dsimp only [K3]; positivity
  have hK2a : 0 ≤ K2a := by dsimp only [K2a]; positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by norm_num) (add_nonneg hK3 hK2a)
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (mul_nonneg (by norm_num) hCh) (Real.sqrt_nonneg _)
  refine ⟨D, hD, ?_⟩
  intro T hTsymm delta hdelta_le hdelta0 hdelta hdeltaZ s hs
    R hRone hT2
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let q : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let S : SmoothCcTensor g 2 2 := RicciDeTurckLowOrder.pathIntegrand
    (I := I) (M := M) g gBase T hdelta hdeltaZ s
  let C : SmoothCcTensor g 2 2 := metricPrincipalDefectCurvCoeff (I := I) g gBase g
  let A : SmoothCcTensor g 2 2 := S + C
  let Y : SmoothCcTensor g 0 2 := operatorFieldApply (I := I) (M := M) g 2 2 A T
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hq : 0 ≤ q := norm_nonneg _
  have hxy : x ≤ y := by
    dsimp only [x, y]
    exact ccToHs_norm_mono (I := I) (M := M) g 2 (by norm_num) T
  have hxone : x ≤ 1 := hT2.trans hRone
  have hinterp : y ^ 2 ≤ x * q := by
    dsimp only [x, y, q]
    exact ccTensorToHs_norm_three_sq_le_norm_two_mul_norm_four
      (I := I) (M := M) g 2 T
  have hsum4 :
      ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤ C3 * y := by
    simpa only [y, Nat.reduceAdd] using hjet3 T
  have hsq4 :
      ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤ (C3 * y) ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _
      _ ≤ (C3 * y) ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ => norm_nonneg _) hsum4 2
  have hsum5 :
      ∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤ C4 * q := by
    simpa only [q, Nat.reduceAdd] using hjet4 T
  have hsq5 :
      ∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤ (C4 * q) ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _
      _ ≤ (C4 * q) ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ => norm_nonneg _) hsum5 2
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
      nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g 0 2 0 T‖]).trans hsq4
  have hS3 : covariantJetNormSq (I := I) (M := M) g 3 S ≤
      A3 * (1 + y ^ 2) * (1 + q ^ 2) := by
    have hraw := hself T hTsymm hdelta0 hdelta_le hdelta hdeltaZ 3 s hs
    let U : ℝ := ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2
    let V : ℝ := ∑ j ∈ Finset.range 5,
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2
    have hU : U ≤ (C3 * y) ^ 2 := by simpa only [U] using hshift
    have hV : V ≤ (C4 * q) ^ 2 := by simpa only [V] using hsq5
    have hU0 : 0 ≤ U := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hV0 : 0 ≤ V := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hfirst : K0 3 + K2 3 * U ≤ K0 3 + K2 3 * (C3 * y) ^ 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hU (hK2 3))
    have hsecond : 1 + V ≤ 1 + (C4 * q) ^ 2 := add_le_add le_rfl hV
    have hfactor1 : K0 3 + K2 3 * (C3 * y) ^ 2 ≤
        (K0 3 + K2 3 * C3 ^ 2) * (1 + y ^ 2) := by
      calc
        _ ≤ (K0 3 + K2 3 * (C3 * y) ^ 2) +
            (K2 3 * C3 ^ 2 + K0 3 * y ^ 2) :=
          le_add_of_nonneg_right (add_nonneg
            (mul_nonneg (hK2 3) (sq_nonneg C3))
            (mul_nonneg (hK0 3) (sq_nonneg y)))
        _ = _ := by ring
    have hfactor2 : 1 + (C4 * q) ^ 2 ≤
        (1 + C4 ^ 2) * (1 + q ^ 2) := by
      calc
        _ ≤ (1 + (C4 * q) ^ 2) + (C4 ^ 2 + q ^ 2) :=
          le_add_of_nonneg_right (add_nonneg (sq_nonneg C4) (sq_nonneg q))
        _ = _ := by ring
    calc
      covariantJetNormSq (I := I) (M := M) g 3 S ≤
          (K0 3 + K2 3 * U) * (1 + V) := by
        simpa only [S, U, V, Nat.reduceAdd] using hraw
      _ ≤ (K0 3 + K2 3 * (C3 * y) ^ 2) *
          (1 + (C4 * q) ^ 2) :=
        mul_le_mul hfirst hsecond (add_nonneg (by norm_num) hV0)
          (add_nonneg (hK0 3)
            (mul_nonneg (hK2 3) (sq_nonneg (C3 * y))))
      _ ≤ A3 * (1 + y ^ 2) * (1 + q ^ 2) := by
        calc
          _ ≤ ((K0 3 + K2 3 * C3 ^ 2) * (1 + y ^ 2)) *
              ((1 + C4 ^ 2) * (1 + q ^ 2)) :=
            mul_le_mul hfactor1 hfactor2
              (add_nonneg (by norm_num) (sq_nonneg (C4 * q)))
              (mul_nonneg
                (add_nonneg (hK0 3) (mul_nonneg (hK2 3) (sq_nonneg C3)))
                (add_nonneg (by norm_num) (sq_nonneg y)))
          _ = A3 * (1 + y ^ 2) * (1 + q ^ 2) := by
            dsimp only [A3]
            ring
  have hS2 : covariantJetNormSq (I := I) (M := M) g 2 S ≤
      A2 * (1 + y ^ 2) ^ 2 := by
    have hraw := hself T hTsymm hdelta0 hdelta_le hdelta hdeltaZ 2 s hs
    let U : ℝ := ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2
    let V : ℝ := ∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2
    have hU : U ≤ (C3 * y) ^ 2 := by simpa only [U] using hshift
    have hV : V ≤ (C3 * y) ^ 2 := by simpa only [V] using hsq4
    have hV0 : 0 ≤ V := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hfirst : K0 2 + K2 2 * U ≤ K0 2 + K2 2 * (C3 * y) ^ 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hU (hK2 2))
    have hsecond : 1 + V ≤ 1 + (C3 * y) ^ 2 := add_le_add le_rfl hV
    have hfactor1 : K0 2 + K2 2 * (C3 * y) ^ 2 ≤
        (K0 2 + K2 2 * C3 ^ 2) * (1 + y ^ 2) := by
      calc
        _ ≤ (K0 2 + K2 2 * (C3 * y) ^ 2) +
            (K2 2 * C3 ^ 2 + K0 2 * y ^ 2) :=
          le_add_of_nonneg_right (add_nonneg
            (mul_nonneg (hK2 2) (sq_nonneg C3))
            (mul_nonneg (hK0 2) (sq_nonneg y)))
        _ = _ := by ring
    have hfactor2 : 1 + (C3 * y) ^ 2 ≤
        (1 + C3 ^ 2) * (1 + y ^ 2) := by
      calc
        _ ≤ (1 + (C3 * y) ^ 2) + (C3 ^ 2 + y ^ 2) :=
          le_add_of_nonneg_right (add_nonneg (sq_nonneg C3) (sq_nonneg y))
        _ = _ := by ring
    calc
      covariantJetNormSq (I := I) (M := M) g 2 S ≤
          (K0 2 + K2 2 * U) * (1 + V) := by
        simpa only [S, U, V, Nat.reduceAdd] using hraw
      _ ≤ (K0 2 + K2 2 * (C3 * y) ^ 2) *
          (1 + (C3 * y) ^ 2) :=
        mul_le_mul hfirst hsecond (add_nonneg (by norm_num) hV0)
          (add_nonneg (hK0 2)
            (mul_nonneg (hK2 2) (sq_nonneg (C3 * y))))
      _ ≤ A2 * (1 + y ^ 2) ^ 2 := by
        calc
          _ ≤ ((K0 2 + K2 2 * C3 ^ 2) * (1 + y ^ 2)) *
              ((1 + C3 ^ 2) * (1 + y ^ 2)) :=
            mul_le_mul hfactor1 hfactor2
              (add_nonneg (by norm_num) (sq_nonneg (C3 * y)))
              (mul_nonneg
                (add_nonneg (hK0 2) (mul_nonneg (hK2 2) (sq_nonneg C3)))
                (add_nonneg (by norm_num) (sq_nonneg y)))
          _ = A2 * (1 + y ^ 2) ^ 2 := by
            dsimp only [A2]
            ring
  have hF3one : 1 ≤ (1 + y ^ 2) * (1 + q ^ 2) := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ (1 + y ^ 2) * (1 + q ^ 2) :=
        mul_le_mul (le_add_of_nonneg_right (sq_nonneg y))
          (le_add_of_nonneg_right (sq_nonneg q)) (by norm_num)
          (add_nonneg (by norm_num) (sq_nonneg y))
  have hF2one : 1 ≤ (1 + y ^ 2) ^ 2 := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ (1 + y ^ 2) * (1 + y ^ 2) :=
        mul_le_mul (le_add_of_nonneg_right (sq_nonneg y))
          (le_add_of_nonneg_right (sq_nonneg y)) (by norm_num)
          (add_nonneg (by norm_num) (sq_nonneg y))
      _ = (1 + y ^ 2) ^ 2 := by ring
  have hAjet3 : covariantJetNormSq (I := I) (M := M) g 3 A ≤
      B3 * (1 + y ^ 2) * (1 + q ^ 2) := by
    calc
      _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 3 S + Jc3) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 3 S C
      _ ≤ 2 * (A3 * ((1 + y ^ 2) * (1 + q ^ 2)) +
          Jc3 * ((1 + y ^ 2) * (1 + q ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply add_le_add
        · simpa only [mul_assoc] using hS3
        · calc
            Jc3 = Jc3 * 1 := (mul_one Jc3).symm
            _ ≤ Jc3 * ((1 + y ^ 2) * (1 + q ^ 2)) :=
              mul_le_mul_of_nonneg_left hF3one hJc3
      _ = B3 * (1 + y ^ 2) * (1 + q ^ 2) := by
        dsimp only [B3]
        ring
  have hAjet2 : covariantJetNormSq (I := I) (M := M) g 2 A ≤
      B2 * (1 + y ^ 2) ^ 2 := by
    calc
      _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2 S + Jc2) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 2 S C
      _ ≤ 2 * (A2 * (1 + y ^ 2) ^ 2 + Jc2 * (1 + y ^ 2) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply add_le_add hS2
        calc
          Jc2 = Jc2 * 1 := (mul_one Jc2).symm
          _ ≤ Jc2 * (1 + y ^ 2) ^ 2 :=
            mul_le_mul_of_nonneg_left hF2one hJc2
      _ = B2 * (1 + y ^ 2) ^ 2 := by
        dsimp only [B2]
        ring
  let Ap : ℝ := Cm2 * Real.sqrt B2 * (1 + y ^ 2)
  have hAp : 0 ≤ Ap := by dsimp only [Ap]; positivity
  have hApt : ∀ z : M,
      riemannianFiberNormSq (I := I) (M := M) g 2 2 z (A.toSection z) ≤
        Ap ^ 2 := by
    intro z
    have hm := hmor2 g hEq (hjet 1 (by norm_num)) (hjet 2 (by norm_num)) A z
    calc
      _ ≤ Cm2 ^ 2 * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 2 2 j A‖ ^ 2 := hm
      _ ≤ Cm2 ^ 2 * (B2 * (1 + y ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hAjet2 (sq_nonneg Cm2)
      _ = Ap ^ 2 := by
        dsimp only [Ap]
        rw [show (Cm2 * Real.sqrt B2 * (1 + y ^ 2)) ^ 2 =
            Cm2 ^ 2 * (Real.sqrt B2) ^ 2 * (1 + y ^ 2) ^ 2 by ring,
          Real.sq_sqrt hB2]
        ring
  have hmor0' : ∀ (U : SmoothCcTensor g 0 2) (z : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 2 z (U.toSection z) ≤
        Cm0 ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ ^ 2 := by
    intro U z
    rw [hDim]
    norm_num
    exact hmor0 g hEq (hjet 1 (by norm_num)) (hjet 2 (by norm_num)) U z
  have hTpt : ∀ z : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 z (T.toSection z) ≤
        (Ct * x) ^ 2 := by
    intro z
    calc
      _ ≤ Ct ^ 2 * x ^ 2 := by
        simpa only [Ct, x] using
          hs2_fiber_sq_action (I := I) (M := M) hDim g hact2 hmor0' T z
      _ = (Ct * x) ^ 2 := by ring
  have hTjet :
      ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤ (Cj * y) ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _
      _ ≤ (Cj * y) ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ => norm_nonneg _)
        (by simpa only [Cj, y] using
          covsum_hs_three (I := I) (M := M) g 2 hact2 hact3 T) 2
  let P2 : ℝ := y ^ 2 + (x * q) ^ 2 + (x * y * q) ^ 2
  have hP2 : 0 ≤ P2 := by dsimp only [P2]; positivity
  have hx2y2 : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2
  have hx2one : x ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hx hxone 2
  have hy4 : y ^ 4 ≤ (x * q) ^ 2 := by
    have h := pow_le_pow_left₀ (sq_nonneg y) hinterp 2
    convert h using 1
    all_goals ring
  have hy6 : y ^ 6 ≤ (x * y * q) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hy4 (sq_nonneg y)
    convert h using 1
    all_goals ring
  have hcore3 : x ^ 2 * (1 + y ^ 2) * (1 + q ^ 2) ≤ 2 * P2 := by
    dsimp only [P2]
    nlinarith only [hx2y2,
      mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hx2one),
      sq_nonneg (x * q), sq_nonneg (x * y * q)]
  have hcore2 : y ^ 2 * (1 + y ^ 2) ^ 2 ≤ 2 * P2 := by
    dsimp only [P2]
    nlinarith only [hy4, hy6, sq_nonneg y, sq_nonneg (x * q),
      sq_nonneg (x * y * q)]
  have hYjet : covariantJetNormSq (I := I) (M := M) g 3 Y ≤ K * P2 := by
    have happRaw := happ g hEq A T Ap (Ct * x)
      hAp (mul_nonneg hCt hx) hApt hTpt
    change (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2) ≤ _
    refine happRaw.trans ?_
    calc
      Ca * ((Ct * x) ^ 2 * ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 2 2 j A‖ ^ 2 +
          Ap ^ 2 * ∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤
          K3 * (x ^ 2 * (1 + y ^ 2) * (1 + q ^ 2)) +
            K2a * (y ^ 2 * (1 + y ^ 2) ^ 2) := by
        rw [show K3 * (x ^ 2 * (1 + y ^ 2) * (1 + q ^ 2)) +
            K2a * (y ^ 2 * (1 + y ^ 2) ^ 2) =
          Ca * (Ct ^ 2 * x ^ 2 *
              (B3 * (1 + y ^ 2) * (1 + q ^ 2)) +
            (Cm2 ^ 2 * B2 * (1 + y ^ 2) ^ 2) *
              (Cj ^ 2 * y ^ 2)) by
          dsimp only [K3, K2a]
          ring]
        apply mul_le_mul_of_nonneg_left _ hCa
        apply add_le_add
        · calc
            (Ct * x) ^ 2 * ∑ j ∈ Finset.range 4,
                ‖iteratedCovGrad (I := I) g 2 2 j A‖ ^ 2 ≤
                (Ct * x) ^ 2 *
                  (B3 * (1 + y ^ 2) * (1 + q ^ 2)) :=
              mul_le_mul_of_nonneg_left hAjet3 (sq_nonneg (Ct * x))
            _ = Ct ^ 2 * x ^ 2 *
                (B3 * (1 + y ^ 2) * (1 + q ^ 2)) := by ring
        · calc
            Ap ^ 2 * ∑ j ∈ Finset.range 4,
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤
                Ap ^ 2 * (Cj * y) ^ 2 :=
              mul_le_mul_of_nonneg_left hTjet (sq_nonneg Ap)
            _ = (Cm2 ^ 2 * B2 * (1 + y ^ 2) ^ 2) *
                (Cj ^ 2 * y ^ 2) := by
              dsimp only [Ap]
              rw [show (Cm2 * Real.sqrt B2 * (1 + y ^ 2)) ^ 2 =
                  Cm2 ^ 2 * (Real.sqrt B2) ^ 2 * (1 + y ^ 2) ^ 2 by ring,
                Real.sq_sqrt hB2]
              ring
      _ ≤ K * P2 := by
        have h3 := mul_le_mul_of_nonneg_left hcore3 hK3
        have h2 := mul_le_mul_of_nonneg_left hcore2 hK2a
        dsimp only [K]
        nlinarith only [h3, h2]
  let P : ℝ := y + x * q + x * y * q
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hP2P : P2 ≤ P ^ 2 := by
    dsimp only [P2, P]
    nlinarith only [mul_nonneg hy (mul_nonneg hx hq),
      mul_nonneg hy (mul_nonneg (mul_nonneg hx hy) hq),
      mul_nonneg (mul_nonneg hx hq) (mul_nonneg (mul_nonneg hx hy) hq)]
  have hYjet' : covariantJetNormSq (I := I) (M := M) g 3 Y ≤
      (Real.sqrt K * P) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK]
    exact hYjet.trans (mul_le_mul_of_nonneg_left hP2P hK)
  let JY : ℝ := ∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g 0 2 j Y‖
  have hJY0 : 0 ≤ JY := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hJYsq : JY ^ 2 ≤ 4 * covariantJetNormSq (I := I) (M := M) g 3 Y := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := Finset.range 4)
      (f := fun j => ‖iteratedCovGrad (I := I) g 0 2 j Y‖)
    simpa only [JY, Finset.card_range, Nat.cast_ofNat, covariantJetNormSq,
      Nat.reduceAdd] using h
  have hJY : JY ≤ 2 * (Real.sqrt K * P) := by
    nlinarith only [hJYsq.trans
      (mul_le_mul_of_nonneg_left hYjet' (by norm_num)), hJY0,
      mul_nonneg (Real.sqrt_nonneg K) hP]
  change ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) Y‖ ≤ D * P
  calc
    _ ≤ Ch * JY := by simpa only [JY, Nat.reduceAdd] using hhs Y
    _ ≤ Ch * (2 * (Real.sqrt K * P)) :=
      mul_le_mul_of_nonneg_left hJY hCh
    _ = D * P := by
      dsimp only [D]
      ring

theorem fifth_order_energy_pairing_bound_of_h3_action_bound
    (g : SmoothRiemannianMetric I M)
    (T Y : SmoothCcTensor g 0 2) {eta D : ℝ}
    (heta : 0 < eta)
    (hT2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ 1)
    (hY : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) Y‖ ≤
      D *
        (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ +
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
            ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ +
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ *
            ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖)) :
    2 * |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2 T))).toFun
        (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
      eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
        8 * eta⁻¹ * D ^ 2 *
          (‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 *
              ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2) := by
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let q : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖
  let P : ℝ := y + x * q + x * y * q
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hq : 0 ≤ q := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have hxone : x ≤ 1 := by simpa only [x] using hT2
  have hyq : y ≤ q := by
    dsimp only [y, q]
    exact ccToHs_norm_mono (I := I) (M := M) g 2 (by norm_num) T
  have hPsmall : P ≤ 2 * q + y * q := by
    dsimp only [P]
    have hxq : x * q ≤ q := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hxone hq
    have hxyq : x * y * q ≤ y * q := by
      have hxy : x * y ≤ y := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hxone hy
      exact mul_le_mul_of_nonneg_right hxy hq
    linarith
  have hP2 : P ^ 2 ≤ 8 * (q ^ 2 + y ^ 2 * q ^ 2) := by
    have hP0 : 0 ≤ P := by dsimp only [P]; positivity
    have hs := pow_le_pow_left₀ hP0 hPsmall 2
    nlinarith [hs, sq_nonneg (2 * q - y * q),
      mul_nonneg (sq_nonneg y) (sq_nonneg q)]
  have hpair := oneMinusConnLapSmooth_pair_h5_h3
    (I := I) (M := M) g T Y
  have hraw :
      2 * |tensorL2Inner (I := I) (M := M) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2
              (oneMinusConnLapSmooth (I := I) g 0 2 T))).toFun
          (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
        2 * z * (D * P) := by
    calc
      _ ≤ 2 * (z *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) Y‖) :=
        mul_le_mul_of_nonneg_left (by simpa only [z] using hpair) (by norm_num)
      _ ≤ 2 * (z * (D * P)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by simpa only [P, x, y, q] using hY) hz)
          (by norm_num)
      _ = 2 * z * (D * P) := by ring
  have hinv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
  have hDP2 : (D * P) ^ 2 ≤
      8 * D ^ 2 * (q ^ 2 + y ^ 2 * q ^ 2) := by
    calc
      (D * P) ^ 2 = D ^ 2 * P ^ 2 := by ring
      _ ≤ D ^ 2 * (8 * (q ^ 2 + y ^ 2 * q ^ 2)) :=
        mul_le_mul_of_nonneg_left hP2 (sq_nonneg D)
      _ = 8 * D ^ 2 * (q ^ 2 + y ^ 2 * q ^ 2) := by ring
  have hyoung : 2 * z * (D * P) ≤
      eta * z ^ 2 + eta⁻¹ * (D * P) ^ 2 := by
    have hs := mul_nonneg hinv (sq_nonneg (eta * z - D * P))
    have hexpand : eta⁻¹ * (eta * z - D * P) ^ 2 =
        eta * z ^ 2 - 2 * z * (D * P) + eta⁻¹ * (D * P) ^ 2 := by
      field_simp [ne_of_gt heta]
      ring
    rw [hexpand] at hs
    linarith
  calc
    _ ≤ 2 * z * (D * P) := hraw
    _ ≤ eta * z ^ 2 + eta⁻¹ * (D * P) ^ 2 := hyoung
    _ ≤ eta * z ^ 2 +
        eta⁻¹ * (8 * D ^ 2 * (q ^ 2 + y ^ 2 * q ^ 2)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hDP2 hinv)
    _ = eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
        8 * eta⁻¹ * D ^ 2 *
          (‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 *
              ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2) := by
      dsimp only [z, y, q]
      ring

theorem ricciDeTurck_remainder_pairing_h5_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Lambda : ℝ}
    (hLambda : 1 ≤ Lambda) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta2 R2 : ℝ,
        0 < delta2 ∧ delta2 ≤ 1 / 3 ∧ 0 < R2 ∧ R2 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Lambda →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Lambda) →
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
              let K0 := metricPrincipalDefectCurvCoeff (I := I) g gBase g
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
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gBase gs -
                  deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gBase g
              let J :=
                oneMinusConnLapSmooth (I := I) g 0 2
                    (operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T) +
                  PairComm +
                  (oneMinusConnLapSmooth (I := I) g 0 2
                      (operatorFieldApply (I := I) (M := M) g 4 2 C HT) -
                    operatorFieldApply (I := I) (M := M) g 4 2 C HLT) - Z
              let V := oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2 LT)
              2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                    (J + Cross).toFun| ≤
                eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
                  G *
                    (‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 *
                        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
  intro eta heta
  obtain ⟨delta2, R2, hdelta2, hdelta2third, hR2, hR2one, hcenter⟩ :=
    ricciDeTurck_remainder_pairing_h5_bound_of_low_order_action_pairing_bound (I := I) (M := M)
      hDim gBase hLambda heta
  refine ⟨delta2, R2, hdelta2, hdelta2third, hR2, hR2one, ?_⟩
  intro g hEq hjet
  obtain ⟨Gd, hGd, hcenterG⟩ := hcenter g hEq hjet
  obtain ⟨D, hD, hcarrier⟩ :=
    ricciDeTurck_low_order_path_action_h3_bound (I := I) (M := M) hDim gBase hLambda g hEq hjet
  let e : ℝ := eta / 5
  let Gc : ℝ := 8 * e⁻¹ * D ^ 2
  let G : ℝ := Gc + Gd
  have he : 0 < e := by dsimp only [e]; positivity
  have hGc : 0 ≤ Gc := by
    dsimp only [Gc]
    exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr he.le))
      (sq_nonneg D)
  have hG : 0 ≤ G := add_nonneg hGc hGd
  refine ⟨G, hG, ?_⟩
  intro T hTsymm delta hdelta_le hdelta0 hdelta hdeltaZ s hs
    R hR hRle hT2
  let A : SmoothCcTensor g 2 2 :=
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
        g gBase T hdelta hdeltaZ s +
      metricPrincipalDefectCurvCoeff (I := I) g gBase g
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 A T
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let q : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  have hdelta_third : delta ≤ 1 / 3 := hdelta_le.trans hdelta2third
  have hRone : R ≤ 1 := hRle.trans hR2one
  have hY := hcarrier T hTsymm hdelta_third hdelta0
    hdelta hdeltaZ hs hRone hT2
  have hpair := fifth_order_energy_pairing_bound_of_h3_action_bound
    (I := I) (M := M) g T Y (eta := e) he (hT2.trans hRone) (by
      simpa only [A, Y] using hY)
  have hpair' :
      2 * |tensorL2Inner (I := I) (M := M) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2
              (oneMinusConnLapSmooth (I := I) g 0 2 T))).toFun
          (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
        (eta / 5) *
            ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
          Gc * (q ^ 2 + y ^ 2 * q ^ 2) := by
    simpa only [e, Gc, q] using hpair
  have hassembled := hcenterG T hTsymm hdelta_le hdelta0
    hdelta hdeltaZ hs hR hRle hT2
      (Lc := Gc * (q ^ 2 + y ^ 2 * q ^ 2)) (by
        simpa only [Y, A, q, y] using hpair')
  dsimp only at hassembled ⊢
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg _
  have hyq2 : 0 ≤ y ^ 2 * q ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hy4 : 0 ≤ y ^ 4 := by positivity
  calc
    _ ≤ eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
        Gc * (q ^ 2 + y ^ 2 * q ^ 2) +
          Gd * (q ^ 2 + y ^ 2 * q ^ 2 + y ^ 4) := by
      simpa only [q, y] using hassembled
    _ ≤ eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
        G * (q ^ 2 + y ^ 2 * q ^ 2 + y ^ 4) := by
      dsimp only [G]
      nlinarith [mul_nonneg hGc hy4]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
