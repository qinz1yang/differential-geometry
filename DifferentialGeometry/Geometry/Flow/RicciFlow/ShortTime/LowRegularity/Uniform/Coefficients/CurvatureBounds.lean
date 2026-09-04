import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricPrincipalDefect.SelfBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricPrincipalDefect.Symmetry
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Pairing.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2PointwiseUnif
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.LaplacianIterateLadder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Sobolev.GagliardoNirenberg
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Application.CovariantTensorBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Application.CovariantDerivativeSlotBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem phiCurv_jet_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (metricPrincipalDefectCurvCoeff (I := I) g g)‖ ^ 2) ≤ C ^ 2 := by
  classical
  obtain ⟨Cg, hCg, hgrad⟩ :=
    gradSlot_grid_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Capp, hCapp, happ⟩ :=
    operatorFieldComposition_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 2 4 2
  let V : ℝ := volCompareC (E := E) Λ *
    ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  let Ks : ℝ := ∑ i ∈ Finset.range 3, phiSelfC (E := E) i
  let Kg : ℝ := ∑ i ∈ Finset.range 2, Cg i
  let As : ℝ := Real.sqrt (Ks * V)
  let Ag : ℝ := Real.sqrt (Kg * V)
  let C : ℝ := (1 / 2 : ℝ) * Capp * As * Ag
  have hV : 0 ≤ V := by
    dsimp only [V, volCompareC]
    positivity
  have hKs : 0 ≤ Ks := by
    dsimp only [Ks]
    exact Finset.sum_nonneg fun i _ ↦ phiSelfC_nonneg (E := E) i
  have hKg : 0 ≤ Kg := by
    dsimp only [Kg]
    exact Finset.sum_nonneg fun i _ ↦ hCg i
  have hAs : 0 ≤ As := Real.sqrt_nonneg _
  have hAg : 0 ≤ Ag := Real.sqrt_nonneg _
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro g hEq hjet
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  have hvol := (volumeReal_cross (I := I) (M := M) gBase g hEq).1
  have hvolV :
      ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal ≤ V := by
    simpa only [V] using hvol
  let Φ : SmoothCcTensor g 4 2 :=
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g -
      cometricDoubleTraceCoefficient (I := I) (M := M) g g
  let G : SmoothCcTensor g 2 4 := gradSwapCurvCoeff (I := I) g
  let Y : SmoothCcTensor g 2 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 4 2 Φ G
  have hΦnorm : ∀ i : ℕ, i < 3 →
      ‖iteratedCovGrad (I := I) g 4 2 i Φ‖ ^ 2 ≤
        phiSelfC (E := E) i * V := by
    intro i hi
    refine (norm_le_of_pointwise_fiberNormSq_bound_rs
      (I := I) (M := M) g 4 (2 + i)
      (iteratedCovGrad (I := I) g 4 2 i Φ)
      (phiSelfC (E := E) i) ?_).trans ?_
    · intro x
      simpa only [Φ] using phiSelf_grid (I := I) (M := M) g i x
    · exact mul_le_mul_of_nonneg_left hvolV (phiSelfC_nonneg (E := E) i)
  have hΦ :
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 i Φ‖ ^ 2) ≤ As ^ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range 3, phiSelfC (E := E) i * V :=
        Finset.sum_le_sum fun i hi ↦ hΦnorm i (Finset.mem_range.mp hi)
      _ = Ks * V := by simp only [Ks, Finset.sum_mul]
      _ = As ^ 2 := by
        dsimp only [As]
        exact (Real.sq_sqrt (mul_nonneg hKs hV)).symm
  have hGnorm : ∀ i : ℕ, i < 2 →
      ‖iteratedCovGrad (I := I) g 2 4 i G‖ ^ 2 ≤ Cg i * V := by
    intro i hi
    refine (norm_le_of_pointwise_fiberNormSq_bound_rs
      (I := I) (M := M) g 2 (4 + i)
      (iteratedCovGrad (I := I) g 2 4 i G) (Cg i) ?_).trans ?_
    · intro x
      simpa only [G, gradSwapCurvCoeff] using hgrad g hEq hjet i hi x
    · exact mul_le_mul_of_nonneg_left hvolV (hCg i)
  have hG :
      (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 2 4 i G‖ ^ 2) ≤ Ag ^ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range 2, Cg i * V :=
        Finset.sum_le_sum fun i hi ↦ hGnorm i (Finset.mem_range.mp hi)
      _ = Kg * V := by simp only [Kg, Finset.sum_mul]
      _ = Ag ^ 2 := by
        dsimp only [Ag]
        exact (Real.sq_sqrt (mul_nonneg hKg hV)).symm
  have hY := happ g hEq hjet1 hjet2 Φ G As Ag hAs hAg hΦ hG
  have hφ : metricPrincipalDefectCurvCoeff (I := I) g g = (1 / 2 : ℝ) • Y := by
    rfl
  have hYnorm :
      ‖(⟨Y⟩ : SmoothCcTensorH1 g 2 2)‖ ≤ Capp * As * Ag := by
    simpa only [Y] using hY
  have hφnorm :
      ‖(⟨metricPrincipalDefectCurvCoeff (I := I) g g⟩ :
          SmoothCcTensorH1 g 2 2)‖ ≤ C := by
    rw [hφ]
    change ‖(1 / 2 : ℝ) • (⟨Y⟩ : SmoothCcTensorH1 g 2 2)‖ ≤ C
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simpa only [C, mul_assoc] using
      (mul_le_mul_of_nonneg_left hYnorm (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hjet_eq :
      (∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 2 2 j
          (metricPrincipalDefectCurvCoeff (I := I) g g)‖ ^ 2) =
        ‖(⟨metricPrincipalDefectCurvCoeff (I := I) g g⟩ :
          SmoothCcTensorH1 g 2 2)‖ ^ 2 := by
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, iteratedCovGrad_succ]
  rw [hjet_eq]
  exact pow_le_pow_left₀ (norm_nonneg _) hφnorm 2

theorem fixed_curv_h1_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ U : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (operatorFieldApply (I := I) (M := M) g 2 2
                (metricPrincipalDefectCurvCoeff (I := I) g g) U)‖ ≤
            C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  obtain ⟨Capp, hCapp, happ⟩ :=
    operatorFieldApplication_h1_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Aφ, hAφ, hφ⟩ :=
    phiCurv_jet_uniform (I := I) (M := M) hDim gBase hΛ
  refine ⟨Capp * Aφ, mul_nonneg hCapp hAφ, ?_⟩
  intro g hEq hjet U
  exact happ g hEq hjet (metricPrincipalDefectCurvCoeff (I := I) g g) U
    Aφ hAφ (hφ g hEq hjet)

theorem curv_pair_abs_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {η : ℝ}, 0 < η →
      ∃ G : ℝ, 0 ≤ G ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∀ T : SmoothCcTensor g 0 2,
            let K0 := metricPrincipalDefectCurvCoeff (I := I) g g
            let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
            2 * |tensorL2Inner (I := I) (M := M) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2 LT).toFun
                (operatorFieldApply (I := I) (M := M) g 2 2 K0 LT).toFun| ≤
              η * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                G * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 := by
  intro η hη
  obtain ⟨C, hC, hact⟩ :=
    fixed_curv_h1_uniform (I := I) (M := M) hDim gBase hΛ
  let G : ℝ := η⁻¹ * C ^ 2
  have hG : 0 ≤ G := by
    dsimp only [G]
    exact mul_nonneg (inv_nonneg.mpr hη.le) (sq_nonneg C)
  refine ⟨G, hG, ?_⟩
  intro g hEq hjet T
  let K0 : SmoothCcTensor g 2 2 := metricPrincipalDefectCurvCoeff (I := I) g g
  let LT : SmoothCcTensor g 0 2 := oneMinusConnLapSmooth (I := I) g 0 2 T
  let Y : SmoothCcTensor g 0 2 := operatorFieldApply (I := I) (M := M) g 2 2 K0 LT
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  have hy : 0 ≤ y := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have hshift1 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) LT‖ = y := by
    dsimp only [LT, y]
    rw [norm_ccHs_eq_smoothHs, norm_ccHs_eq_smoothHs]
    calc
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ)
            (oneMinusConnLapSmooth (I := I) g 0 2 T)‖ :=
        congrArg (fun σ : ℝ => ‖smoothCcToTensorHs (I := I) (M := M) g σ
          (oneMinusConnLapSmooth (I := I) g 0 2 T)‖) (by norm_num)
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g ((1 + 2 : ℕ) : ℝ) T‖ :=
        (smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
          (I := I) (M := M) g 1 T).symm
      _ = _ :=
        congrArg (fun σ : ℝ =>
          ‖smoothCcToTensorHs (I := I) (M := M) g σ T‖) (by norm_num)
  have hshift2 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) LT‖ = z := by
    dsimp only [LT, z]
    rw [norm_ccHs_eq_smoothHs, norm_ccHs_eq_smoothHs]
    calc
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℕ) : ℝ)
            (oneMinusConnLapSmooth (I := I) g 0 2 T)‖ :=
        congrArg (fun σ : ℝ => ‖smoothCcToTensorHs (I := I) (M := M) g σ
          (oneMinusConnLapSmooth (I := I) g 0 2 T)‖) (by norm_num)
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g ((2 + 2 : ℕ) : ℝ) T‖ :=
        (smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
          (I := I) (M := M) g 2 T).symm
      _ = _ :=
        congrArg (fun σ : ℝ =>
          ‖smoothCcToTensorHs (I := I) (M := M) g σ T‖) (by norm_num)
  have hY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y‖ ≤ C * z := by
    calc
      _ ≤ C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) LT‖ := by
        simpa only [Y, K0] using hact g hEq hjet LT
      _ = C * z := by rw [hshift2]
  have hspec (W : SmoothCcTensor g 0 2) :
      ‖smoothToTensorH1Compl (I := I) (M := M) g 0 2
          (⟨W⟩ : SmoothCcTensorH1 g 0 2)‖ =
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) W‖ := by
    rw [smoothToTensorH1Compl_apply, UniformSpace.Completion.norm_coe]
    have hspectral := cc_h1_jet_sq (I := I) (M := M) g W
    have hintrinsic := smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g 0 2 W
    nlinarith [
      norm_nonneg (ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) W),
      norm_nonneg (⟨W⟩ : SmoothCcTensorH1 g 0 2)]
  let u : TensorH1Compl g 0 2 :=
    smoothToTensorH1Compl (I := I) (M := M) g 0 2
      (⟨LT⟩ : SmoothCcTensorH1 g 0 2)
  let v : TensorH1Compl g 0 2 :=
    smoothToTensorH1Compl (I := I) (M := M) g 0 2
      (⟨Y⟩ : SmoothCcTensorH1 g 0 2)
  let Au : TensorL2 0 2 g :=
    ((oneMinusConnLapSmooth (I := I) g 0 2 LT : SmoothCcTensor g 0 2) :
      TensorL2 0 2 g)
  let Av : TensorL2 0 2 g := (Y : TensorL2 0 2 g)
  have hgreen :
      (inner ℝ Au Av : ℝ) = (inner ℝ u v : ℝ) := by
    simpa only [Au, Av, u, v] using
      (oneMinusConnLapSmooth_toL2_inner_eq_h1_general
        (I := I) (M := M) g 2
        (DifferentialGeometry.Analysis.Elliptic.loweringIntertwiner_two
          (I := I) (M := M) g) LT Y)
  have hgreen' :
      tensorL2Inner (I := I) (M := M) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 LT).toFun Y.toFun =
        (inner ℝ u v : ℝ) := by
    calc
      _ = (inner ℝ (SmoothCcTensor.toL2
              (oneMinusConnLapSmooth (I := I) g 0 2 LT))
            (SmoothCcTensor.toL2 Y) : ℝ) := by
        rw [SmoothCcTensor.inner_toL2]
        exact (SmoothCcTensor.inner_def (I := I) (M := M)
          (oneMinusConnLapSmooth (I := I) g 0 2 LT) Y).symm
      _ = _ := by
        simpa only [SmoothCcTensor.toL2_apply] using hgreen
  have hpair :
      |tensorL2Inner (I := I) (M := M) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 LT).toFun Y.toFun| ≤
        y * (C * z) := by
    calc
      _ = |(inner ℝ u v : ℝ)| := by
        rw [hgreen']
      _ ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) LT‖ *
            ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y‖ := by
        dsimp only [u, v]
        rw [hspec LT, hspec Y]
      _ ≤ y * (C * z) := by
        rw [hshift1]
        exact mul_le_mul_of_nonneg_left hY hy
  have hyoung : 2 * z * (C * y) ≤ η * z ^ 2 + η⁻¹ * (C * y) ^ 2 := by
    have hinv : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
    have hs := mul_nonneg hinv (sq_nonneg (η * z - C * y))
    have hexpand :
        η⁻¹ * (η * z - C * y) ^ 2 =
          η * z ^ 2 - 2 * z * (C * y) + η⁻¹ * (C * y) ^ 2 := by
      field_simp [ne_of_gt hη]
      ring
    rw [hexpand] at hs
    linarith
  change
    2 * |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2 LT).toFun Y.toFun| ≤
      η * z ^ 2 + G * y ^ 2
  calc
    _ ≤ 2 * (y * (C * z)) :=
      mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ = 2 * z * (C * y) := by ring
    _ ≤ η * z ^ 2 + η⁻¹ * (C * y) ^ 2 := hyoung
    _ = η * z ^ 2 + G * y ^ 2 := by
      dsimp only [G]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
