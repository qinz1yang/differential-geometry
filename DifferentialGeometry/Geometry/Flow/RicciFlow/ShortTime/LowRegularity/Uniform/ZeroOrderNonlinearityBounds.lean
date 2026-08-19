import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.ClassBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2PointwiseUnif
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.CovariantSumCross
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem smoothCc_norm_le_of_fibreSq (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) {K : ℝ} (hK : 0 ≤ K)
    (hS : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) ≤ K ^ 2) :
    ‖S‖ ≤ K *
      Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hvol : 0 ≤ (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ :=
    ENNReal.toReal_nonneg
  have hsq : ‖S‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [SmoothCcTensor.norm_def S]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r s
      (fun x => S.toSection x)
  have hint : ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ * K ^ 2 := by
    have hle := MeasureTheory.integral_mono_of_nonneg
      (μ := riemannianVolumeMeasure (I := I) (M := M) g)
      (f := fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))
      (g := fun _ : M => K ^ 2)
      (Filter.Eventually.of_forall
        (fun x => riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _))
      (MeasureTheory.integrable_const _)
      (Filter.Eventually.of_forall hS)
    simpa only [MeasureTheory.integral_const, smul_eq_mul] using hle
  have hfinal : ‖S‖ ^ 2 ≤
      (K * Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ)) ^ 2 := by
    rw [hsq, mul_pow, Real.sq_sqrt hvol, mul_comm (K ^ 2)]
    exact hint
  have hsqrt := Real.sqrt_le_sqrt hfinal
  rwa [Real.sqrt_sq (norm_nonneg S),
    Real.sqrt_sq (mul_nonneg hK (Real.sqrt_nonneg _))] at hsqrt

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem volReal_cross_le (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ) :
    (riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ ≤
      Real.sqrt (Λ ^ Module.finrank ℝ E) *
        (riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) gBase) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) gBase
  have hmeas := (volumeMeasure_cross_le (I := I) (M := M) gBase g₀ hEq).1
  have hpt := Measure.le_iff'.mp hmeas Set.univ
  rw [Measure.smul_apply, smul_eq_mul] at hpt
  have hne : ENNReal.ofReal (Real.sqrt (Λ ^ Module.finrank ℝ E)) *
      (riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have htoReal := ENNReal.toReal_mono hne hpt
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at htoReal
  exact htoReal

theorem smoothCcToTensorHs_zero (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (0 : SmoothCcTensor g₀ 0 2) = 0 := by
  have h := smoothCcToTensorHs_sub (I := I) (M := M) g₀ σ
    (0 : SmoothCcTensor g₀ 0 2) (0 : SmoothCcTensor g₀ 0 2)
  rwa [sub_self, sub_self] at h

theorem zero_mem_smoothCore (g₀ : SmoothRiemannianMetric I M) {R : ℝ} (hR : 0 ≤ R) :
    (⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR⟩ :
        lowerState (I := I) (M := M) g₀ 1 R) ∈
      smoothCore (I := I) (M := M) g₀ R := by
  change (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) ∈
    Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2))
  exact ⟨0, smoothCcToTensorHs_zero (I := I) (M := M) g₀ _⟩

omit [CompactSpace M] [BoundarylessManifold I M] in
theorem realizeMetric_zero (g₀ : SmoothRiemannianMetric I M) {δ : ℝ} (hδ : δ < 1)
    (hb : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) :
    tensorSectionRealizeMetric (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) hδ hb = g₀ := by
  refine smoothRiemannianMetric_ext_inner (fun x v w => ?_)
  rw [tensorSectionRealizeMetric_inner, ccTensorBilinSymm_apply,
    ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  ring

omit [CompactSpace M] [I.Boundaryless] in
theorem rawTensorConnLapSmooth_zero (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    rawTensorConnLapSmooth (I := I) g r s (0 : SmoothCcTensor g r s) = 0 := by
  have h := rawTensorConnLapSmooth_sub (I := I) (M := M) g r s
    (0 : SmoothCcTensor g r s) (0 : SmoothCcTensor g r s)
  rwa [sub_self, sub_self] at h

theorem deTurckRem_zero (g₀ g_bg : SmoothRiemannianMetric I M) {δ : ℝ} (hδ : δ < 1)
    (hb : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) :
    deTurckSmoothRemainder (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2) hδ hb =
      deTurckRHSSection (I := I) g_bg g₀ := by
  have hg := realizeMetric_zero (I := I) (M := M) g₀ hδ hb
  have hlap :
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 (0 : SmoothCcTensor g₀ 0 2)).toSection = 0 := by
    rw [rawTensorConnLapSmooth_zero]
    rfl
  refine SmoothCcTensor.ext ?_
  change
    (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)
          hδ hb)).toSection -
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 (0 : SmoothCcTensor g₀ 0 2)).toSection =
    (deTurckRHSSection (I := I) g_bg g₀).toSection
  rw [hlap, sub_zero]
  exact congrArg
    (fun h : SmoothRiemannianMetric I M => (deTurckRHSSection (I := I) g_bg h).toSection) hg

theorem deTurckSmoothN_zero (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {δ : ℝ}
    (hδ : δ < 1)
    (hb : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) :
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a (0 : SmoothCcTensor g₀ 0 2) hδ hb =
      smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
        (deTurckRHSSection (I := I) g_bg g₀) := by
  have hrem : smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
      (deTurckSmoothRemainder (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2) hδ hb) =
      smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
        (deTurckRHSSection (I := I) g_bg g₀) := by
    rw [deTurckRem_zero]
  refine Eq.trans ?_ hrem
  exact tensorHs.ext (funext fun _ => rfl)

theorem deTurckRemainderOnLowerState_zero_eq_deTurckRHS (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ} (hR : 0 < R)
    (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal)) :
    deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
        (deTurckRHSSection (I := I) g_bg g₀) := by
  classical
  have hmem : (⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ :
      lowerState (I := I) (M := M) g₀ 1 R) ∈ smoothCore (I := I) (M := M) g₀ R :=
    zero_mem_smoothCore (I := I) (M := M) g₀ hR.le
  have hrep : smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
      (coreRep (I := I) (M := M) g₀
        (⟨⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩, hmem⟩ :
          smoothCore (I := I) (M := M) g₀ R)) = 0 := by
    rw [coreRep_spec]
  have hsymm : smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
      (symmS (I := I) (M := M) g₀
        (coreRep (I := I) (M := M) g₀
          (⟨⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩, hmem⟩ :
            smoothCore (I := I) (M := M) g₀ R))) =
      smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2) := by
    rw [smoothCcToTensorHs_zero]
    have hle := norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀
      (((1 : ℕ) : ℝ) + 2)
      (coreRep (I := I) (M := M) g₀
        (⟨⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩, hmem⟩ :
          smoothCore (I := I) (M := M) g₀ R))
    rw [hrep, norm_zero] at hle
    exact norm_le_zero_iff.mp hle
  have hb0 : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ := by
    refine hreal (0 : SmoothCcTensor g₀ 0 2) ?_
    rw [smoothCcToTensorHs_zero, norm_zero]
    exact hR.le
  calc deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩
      = deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal
          ⟨⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩, hmem⟩ :=
        (smoothCore_dense (I := I) (M := M) g₀ hR).extend_eq hcore
          ⟨⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩, hmem⟩
    _ = deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
          (symmS (I := I) (M := M) g₀
            (coreRep (I := I) (M := M) g₀
              ⟨⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩, hmem⟩)) hδ
          (hreal _ (coreSymm_h2 (I := I) (M := M) g₀
            ⟨⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩, hmem⟩)) := rfl
    _ = deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
          (0 : SmoothCcTensor g₀ 0 2) hδ hb0 :=
        smoothN_wd (I := I) (M := M) g₀ g_bg 1 _ _ hδ _ hδ hb0 hsymm
    _ = smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
          (deTurckRHSSection (I := I) g_bg g₀) :=
        deTurckSmoothN_zero (I := I) (M := M) g₀ g_bg 1 hδ hb0

private theorem hsOne_sq (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) S‖ ^ 2 =
      ‖S‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ ^ 2 := by
  classical
  have hsum0 :
      Summable (fun m :
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2 =>
        (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m) ^ 0 *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 S) m) ^ 2) := by
    simpa only [pow_zero, one_mul, tensorSobolevWeight_zero, ccTensorToHs_coeff] using
      (ccTensorToHs (I := I) (M := M) g₀ 2 (0 : ℝ) S).weighted_summable
  have hsum1 :
      Summable (fun m :
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2 =>
        (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m) ^ 1 *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 S) m) ^ 2) := by
    have hfull :=
      (ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ) S).weighted_summable
    refine Summable.of_nonneg_of_le ?_ ?_ hfull
    · intro m
      have hlam : (0 : ℝ) ≤
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      positivity
    · intro m
      have hlam : (0 : ℝ) ≤
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      have hle :
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m ≤
            1 +
              DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                (I := I) (M := M) m := by
        linarith
      have hweight :
          tensorSobolevWeight (I := I) (M := M) m (1 : ℝ) =
            1 +
              DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                (I := I) (M := M) m := by
        unfold tensorSobolevWeight
        rw [Real.rpow_one]
      rw [pow_one, hweight, ccTensorToHs_coeff]
      exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  rw [Nat.cast_one]
  rw [← norm_ccHs_eq_smoothHs (I := I) (M := M) g₀ (1 : ℝ) S,
    ccToHs_norm_sq]
  calc
    ∑' m :
        DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) m (1 : ℝ) *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 S) m) ^ 2 =
        ∑' m, (
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ 0 *
              (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 S) m) ^ 2 +
            (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ 1 *
              (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 S) m) ^ 2) := by
          refine tsum_congr (fun m => ?_)
          unfold tensorSobolevWeight
          rw [Real.rpow_one]
          ring
    _ =
        (∑' m,
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ 0 *
            (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 S) m) ^ 2) +
        ∑' m,
          (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m) ^ 1 *
            (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 S) m) ^ 2 :=
      Summable.tsum_add hsum0 hsum1
    _ = ‖S‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ ^ 2 := by
      rw [← rawIter_tsum (I := I) (M := M) g₀ 2 0 S,
        ← covIter_tsum (I := I) (M := M) g₀ 2 0 S,
        rawTensorConnLapIter_zero, SmoothCcTensor.norm_toL2]

def zeroStateRemainderBound (Ksup Λ volBase : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt 2 * (2 * (Ksup * Real.sqrt (Real.sqrt (Λ ^ n) * volBase)))

theorem nZeroC_nonneg {Ksup : ℝ} (hKsup : 0 ≤ Ksup) (Λ volBase : ℝ) (n : ℕ) :
    0 ≤ zeroStateRemainderBound Ksup Λ volBase n := by
  unfold zeroStateRemainderBound
  positivity

theorem staticN_h1_le (gBase g₀ : SmoothRiemannianMetric I M)
    {Λ Ksup : ℝ} (hKsup : 0 ≤ Ksup)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hsup : ∀ j : ℕ, j ≤ 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j
            (deTurckRHSSection (I := I) gBase g₀)).toSection x) ≤ Ksup ^ 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
        (deTurckRHSSection (I := I) gBase g₀)‖ ≤
      zeroStateRemainderBound Ksup Λ
        ((riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)
        (Module.finrank ℝ E) := by
  classical
  have hvol₀nn : 0 ≤ (riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ :=
    ENNReal.toReal_nonneg
  let S := deTurckRHSSection (I := I) gBase g₀
  have hjet_sq := hsOne_sq (I := I) (M := M) g₀ S
  have hcross : 0 ≤ ‖S‖ * ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hjet0 :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) S‖ ≤
        ‖S‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ := by
    apply le_of_sq_le_sq
    · rw [hjet_sq]
      nlinarith
    · positivity
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hjet :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) S‖ ≤
        Real.sqrt 2 * ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by
    calc
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) S‖ ≤
          ‖S‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ := hjet0
      _ = 1 * (‖S‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖) := by ring
      _ ≤ Real.sqrt 2 *
          (‖S‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖) :=
        mul_le_mul_of_nonneg_right hsqrt (add_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = Real.sqrt 2 * ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero]
  have hterm : ∀ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (deTurckRHSSection (I := I) gBase g₀)‖ ≤
        Ksup * Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ) := by
    intro j hj
    have hj1 : j ≤ 1 := by
      have hj2 : j < 2 := Finset.mem_range.mp hj
      omega
    exact smoothCc_norm_le_of_fibreSq (I := I) (M := M) g₀ _ hKsup (hsup j hj1)
  have hsum : ∑ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (deTurckRHSSection (I := I) gBase g₀)‖ ≤
        2 * (Ksup *
          Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ)) := by
    calc ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (deTurckRHSSection (I := I) gBase g₀)‖ ≤
          ∑ _j ∈ Finset.range 2, Ksup *
            Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ) :=
          Finset.sum_le_sum hterm
      _ = 2 * (Ksup *
          Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  have hvolle := volReal_cross_le (I := I) (M := M) gBase g₀ hEq
  have hsqrtvol :
      Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ) ≤
      Real.sqrt (Real.sqrt (Λ ^ Module.finrank ℝ E) *
        (riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ) :=
    Real.sqrt_le_sqrt hvolle
  have hchain : 2 * (Ksup *
        Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ)) ≤
      2 * (Ksup * Real.sqrt (Real.sqrt (Λ ^ Module.finrank ℝ E) *
        (riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)) := by
    have hmul := mul_le_mul_of_nonneg_left hsqrtvol hKsup
    linarith
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
        (deTurckRHSSection (I := I) gBase g₀)‖ ≤
      Real.sqrt 2 * ∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (deTurckRHSSection (I := I) gBase g₀)‖ := hjet
    _ ≤ Real.sqrt 2 * (2 * (Ksup *
        Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ))) :=
        mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg 2)
    _ ≤ Real.sqrt 2 * (2 * (Ksup * Real.sqrt (Real.sqrt (Λ ^ Module.finrank ℝ E) *
        (riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ))) :=
        mul_le_mul_of_nonneg_left hchain (Real.sqrt_nonneg 2)
    _ = zeroStateRemainderBound Ksup Λ
        ((riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)
        (Module.finrank ℝ E) := rfl

theorem zero_state_remainder_uniform_bound (gBase g₀ : SmoothRiemannianMetric I M) {R δ : ℝ} (hR : 0 < R)
    (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ gBase hδ hreal))
    {Λ Ksup : ℝ} (hKsup : 0 ≤ Ksup)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hsup : ∀ j : ℕ, j ≤ 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j
            (deTurckRHSSection (I := I) gBase g₀)).toSection x) ≤ Ksup ^ 2) :
    ‖deTurckRemainderOnLowerState (I := I) (M := M) g₀ gBase hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩‖ ≤
      zeroStateRemainderBound Ksup Λ
        ((riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)
        (Module.finrank ℝ E) := by
  rw [deTurckRemainderOnLowerState_zero_eq_deTurckRHS (I := I) (M := M) g₀ gBase hR hδ hreal hcore]
  exact staticN_h1_le (I := I) (M := M) gBase g₀ hKsup hEq hsup

theorem bounded_deTurck_remainder_zero_uniform_bound (gBase g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B1 ρ P : ℝ} (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ)
    (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ gBase hδ
      (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ) hP.le hreal)))
    {Λ Ksup : ℝ} (hKsup : 0 ≤ Ksup)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hsup : ∀ j : ℕ, j ≤ 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j
            (deTurckRHSSection (I := I) gBase g₀)).toSection x) ≤ Ksup ^ 2) :
    ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ gBase hδ hCtop hB1 hρ hP hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
          (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le⟩‖ ≤
      zeroStateRemainderBound Ksup Λ
        ((riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)
        (Module.finrank ℝ E) :=
  zero_state_remainder_uniform_bound (I := I) (M := M) gBase g₀ (lowRegularityStateRadius_pos hCtop hB1 hρ hP) hδ
    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ) hP.le hreal)
    hcore hKsup hEq hsup

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
