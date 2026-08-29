import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroCoeffL2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.GagliardoNirenberg
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.MixedTensorApplicationFirstSecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.CoefficientSecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.FreeSlotFirstOrderBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroCoefficientDecomposition

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma riemRiemannianFiberNormSq_neg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [show (-v) = (-1 : ℝ) • v from by rw [neg_one_smul]]
  rw [DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul]
  norm_num

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma riemRiemannianFiberNormSq_iteratedCovGrad_neg
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i (-Φ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i Φ).toSection x) := by
  rw [iteratedCovGrad_neg]
  change riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
      (-((iteratedCovGrad (I := I) g r s i Φ).toSection x)) = _
  exact riemRiemannianFiberNormSq_neg (I := I) (M := M) g r (s + i) x _

omit [SigmaCompactSpace M] in
private lemma riemPass_riemannianFiberNormSq
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (C : ℕ → ℝ)
    (hgrid : ∀ (i : ℕ), i < 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 1 (3 + i) x
          ((iteratedCovGrad (I := I) g 1 3 i
            (slotFreeOpCc (I := I) (M := M) g 1)).toSection x) ≤ C i)
    (i : ℕ) (hi : i < 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 (4 + i) x
        ((iteratedCovGrad (I := I) g 2 4 i
          (lieCorrectionZeroRiemannLift (I := I) (M := M) g)).toSection x) ≤
      3 * C i := by
  classical
  let X : SmoothCcTensor g 2 4 :=
    reindexCoeffGen (I := I) (M := M) g 2 4
      (slotExtendIter (I := I) (M := M) g 1 3 1
        (slotFreeOpCc (I := I) (M := M) g 1))
      (Equiv.swap (0 : Fin 2) 1)
  let Y : SmoothCcTensor g 2 4 :=
    rsDomDomCongrSection (I := I) (M := M) g 2 4 lieCorrectionZeroVectorBundleTracePermutation X
  have hpass : lieCorrectionZeroRiemannLift (I := I) (M := M) g = -Y := by
    simpa only [X, Y] using lieCorrectionZeroRiemannLift_eq_decomposition (I := I) (M := M) g
  have hperm :
      riemannianFiberNormSq (I := I) (M := M) g 2 (4 + i) x
          ((iteratedCovGrad (I := I) g 2 4 i Y).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 2 (4 + i) x
          ((iteratedCovGrad (I := I) g 2 4 i X).toSection x) := by
    exact DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
      (I := I) (M := M) g 2 4 lieCorrectionZeroVectorBundleTracePermutation X Y
      (fun y d => by
        dsimp only [Y]
        rw [rsDomDomCongrSection_toSection,
          toModel_rsDomDomCongr_apply]) i x
  have hsrc :
      riemannianFiberNormSq (I := I) (M := M) g 2 (4 + i) x
          ((iteratedCovGrad (I := I) g 2 4 i X).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 2 (4 + i) x
          ((iteratedCovGrad (I := I) g 2 4 i
            (slotExtendIter (I := I) (M := M) g 1 3 1
              (slotFreeOpCc (I := I) (M := M) g 1))).toSection x) := by
    dsimp only [X]
    exact DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq
      (I := I) (M := M) g 2 4
      (slotExtendIter (I := I) (M := M) g 1 3 1
        (slotFreeOpCc (I := I) (M := M) g 1))
      (Equiv.swap (0 : Fin 2) 1) i x
  have hext :
      riemannianFiberNormSq (I := I) (M := M) g 2 (4 + i) x
          ((iteratedCovGrad (I := I) g 2 4 i
            (slotExtendIter (I := I) (M := M) g 1 3 1
              (slotFreeOpCc (I := I) (M := M) g 1))).toSection x) ≤
        3 * C i := by
    have h := riemannianFiberNormSq_iteratedCovGrad_slotExtend_le
      (I := I) (M := M) g 1 3
      (slotFreeOpCc (I := I) (M := M) g 1) i x
    rw [hDim] at h
    simpa only [slotExtendIter, Nat.reduceAdd, Nat.cast_ofNat] using
      h.trans (mul_le_mul_of_nonneg_left (hgrid i hi x) (by norm_num))
  calc
    _ = riemannianFiberNormSq (I := I) (M := M) g 2 (4 + i) x
          ((iteratedCovGrad (I := I) g 2 4 i Y).toSection x) := by
        rw [hpass]
        exact riemRiemannianFiberNormSq_iteratedCovGrad_neg (I := I) (M := M) g 2 4 i Y x
    _ = riemannianFiberNormSq (I := I) (M := M) g 2 (4 + i) x
          ((iteratedCovGrad (I := I) g 2 4 i X).toSection x) := hperm
    _ = riemannianFiberNormSq (I := I) (M := M) g 2 (4 + i) x
          ((iteratedCovGrad (I := I) g 2 4 i
            (slotExtendIter (I := I) (M := M) g 1 3 1
              (slotFreeOpCc (I := I) (M := M) g 1))).toSection x) := hsrc
    _ ≤ 3 * C i := hext

theorem lieCorrectionZeroRiemann_h1_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g₀ gBase Λ) →
        ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w +
              ccTensorBilinSymm (I := I) g₀ P y v w) →
          ∀ {δ : ℝ}, δ ≤ δ₀ → 0 ≤ δ →
          gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ P) δ →
          ∀ (R A : ℝ), 0 ≤ R → 0 ≤ A →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
          ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ≤ A →
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  classical
  have hΛ0 : 0 ≤ Λ := le_trans (by norm_num) hΛ
  obtain ⟨Cg, hCg, hsf⟩ :=
    sfOne_grid_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Capp, hCapp, happ⟩ :=
    operatorFieldComposition_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 2 4 2
  obtain ⟨Bt, hBt, htrace⟩ :=
    trace2_h2_uniform (I := I) (M := M) hDim gBase hΛ0 hδ₀
  let V : ℝ := volCompareC (E := E) Λ *
    ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  let Kp : ℝ := ∑ i ∈ Finset.range 2, 3 * Cg i
  let Ap : ℝ := Real.sqrt (Kp * V)
  let B0 : ℝ → ℝ := fun R => Capp * Bt R * Ap
  let B1 : ℝ → ℝ := fun _ => 0
  have hV : 0 ≤ V := by
    dsimp only [V, volCompareC]
    positivity
  have hKp : 0 ≤ Kp := by
    dsimp only [Kp]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (by norm_num) (hCg i)
  have hAp : 0 ≤ Ap := Real.sqrt_nonneg _
  refine ⟨B0, B1, fun R hR => by
    exact mul_nonneg (mul_nonneg hCapp (hBt R hR)) hAp,
    fun _ _ => le_rfl, ?_⟩
  intro g₀ hEq hjet g₁ P htie δ hδ_le hδ_nonneg hbound
    R A hR hA hP2 htop
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  have hvol := (volumeReal_cross (I := I) (M := M) gBase g₀ hEq).1
  have hvolV :
      ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal ≤ V := by
    simpa only [V] using hvol
  let Pass : SmoothCcTensor g₀ 2 4 := lieCorrectionZeroRiemannLift (I := I) (M := M) g₀
  have hPassNorm : ∀ i : ℕ, i < 2 →
      ‖iteratedCovGrad (I := I) g₀ 2 4 i Pass‖ ^ 2 ≤
        (3 * Cg i) * V := by
    intro i hi
    refine (norm_le_of_pointwise_fiberNormSq_bound_rs
      (I := I) (M := M) g₀ 2 (4 + i)
      (iteratedCovGrad (I := I) g₀ 2 4 i Pass) (3 * Cg i) ?_).trans ?_
    · intro x
      simpa only [Pass] using
        riemPass_riemannianFiberNormSq (I := I) (M := M) hDim g₀ Cg
          (hsf g₀ hEq hjet) i hi x
    · exact mul_le_mul_of_nonneg_left hvolV
        (mul_nonneg (by norm_num) (hCg i))
  have hPass :
      (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 2 4 i Pass‖ ^ 2) ≤ Ap ^ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range 2, (3 * Cg i) * V :=
        Finset.sum_le_sum fun i hi => hPassNorm i (Finset.mem_range.mp hi)
      _ = Kp * V := by simp only [Kp, Finset.sum_mul]
      _ = Ap ^ 2 := by
        dsimp only [Ap]
        exact (Real.sq_sqrt (mul_nonneg hKp hV)).symm
  let Live : SmoothCcTensor g₀ 4 2 :=
    reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁
  have hLiveRF :
      Live = reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 (Equiv.refl _) := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    dsimp only [Live]
    change (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁).toSection x) =
      (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 2
          (Equiv.refl _)).toSection x)
    rw [reindexedCometricDoubleTrace_toSection, reindexedPureTrace_toSection]
    rfl
  have hLive :
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i Live‖ ^ 2) ≤ (Bt R) ^ 2 := by
    rw [hLiveRF]
    exact htrace g₀ hEq hjet1 hjet2 g₁ P htie
      hδ_le hδ_nonneg hbound (Equiv.refl _) R hR hP2
  let Out : SmoothCcTensor g₀ 2 2 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 Live Pass
  have hOutNorm :
      ‖(⟨Out⟩ : SmoothCcTensorH1 g₀ 2 2)‖ ≤ Capp * Bt R * Ap := by
    simpa only [Out] using happ g₀ hEq hjet1 hjet2 Live Pass
      (Bt R) Ap (hBt R hR) hAp hLive hPass
  have hOut :
      (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i Out‖ ^ 2) ≤
        (Capp * Bt R * Ap) ^ 2 := by
    have hsquare := pow_le_pow_left₀
      (norm_nonneg (⟨Out⟩ : SmoothCcTensorH1 g₀ 2 2)) hOutNorm 2
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g₀ 2 2 Out] at hsquare
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hsquare
  calc
    (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁)‖ ^ 2) =
      ∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i Out‖ ^ 2 := by
          rw [lieCorrectionZeroRiemann_eq_ccOperatorFieldComp (I := I) (M := M) g₀ g₁]
          apply Finset.sum_congr rfl
          intro i _
          rw [iteratedCovGrad_neg, norm_neg]
    _ ≤ (Capp * Bt R * Ap) ^ 2 := hOut
    _ = (B0 R + B1 R * A) ^ 2 := by
      simp only [B0, B1, zero_mul, add_zero]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
