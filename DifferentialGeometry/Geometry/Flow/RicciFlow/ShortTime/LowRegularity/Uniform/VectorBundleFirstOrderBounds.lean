import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.ZeroStateForcing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.CoefficientJetBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.MixedTensorApplicationFirstSecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.MixedTensorApplicationSecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.CoefficientSecondOrderBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InteriorProductJetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroCoefficientDecomposition
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroVectorBundleExpansion

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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


theorem lieCorrectionZeroVectorBundle_h1_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
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
              (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  classical
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨Bt1, hBt1, htr1⟩ :=
    trace_h2_uniform (I := I) (M := M) 1 hDim gBase hΛ0 hδ₀
  obtain ⟨Bt2, hBt2, htr2⟩ :=
    trace_h2_uniform (I := I) (M := M) 2 hDim gBase hΛ0 hδ₀
  obtain ⟨Bc0, Bc1, hBc0, hBc1, hconn⟩ :=
    connLow_tame_uniform (I := I) (M := M) hDim gBase hΛ0 hδ₀
  obtain ⟨Cω, hCω, hωprod⟩ :=
    operatorFieldComposition_h2_h2_to_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 0 3 1
  obtain ⟨Cip, hCip, hiprod⟩ :=
    operatorFieldComposition_h2_h2_to_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 2 3 1
  obtain ⟨Cn, hCn, hnprod⟩ :=
    operatorFieldComposition_h1_uniform_bound (I := I) (M := M) hDim gBase hΛ 2 1 4
  obtain ⟨Co, hCo, hoprod⟩ :=
    operatorFieldComposition_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 2 4 2
  let sf : ℝ := Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2)
  let Cb : ℝ → ℝ → ℝ := fun R A => Bc0 R + Bc1 R * (R + A)
  let Ωb : ℝ → ℝ → ℝ := fun R A => Cω * Bt1 R * Cb R A
  let Sb : ℝ → ℝ → ℝ := fun R A => sf * Ωb R A
  let Ib : ℝ → ℝ → ℝ := fun R A => Cip * Bt1 0 * Sb R A
  let Hb : ℝ → ℝ := fun R => Real.sqrt 3 * (4 * R)
  let Nb : ℝ → ℝ → ℝ := fun R A => Cn * Hb R * Ib R A
  let Ob : ℝ → ℝ → ℝ := fun R A => Co * Bt2 R * Nb R A
  let F : ℝ → ℝ := fun R =>
    2 * Co * Bt2 R *
      (Cn * Hb R * (Cip * Bt1 0 * (sf * (Cω * Bt1 R))))
  let B0 : ℝ → ℝ := fun R => F R * (Bc0 R + Bc1 R * R)
  let B1 : ℝ → ℝ := fun R => F R * Bc1 R
  have hsf : 0 ≤ sf := Real.sqrt_nonneg _
  have hCb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Cb R A := by
    intro R hR A hA
    exact add_nonneg (hBc0 R hR)
      (mul_nonneg (hBc1 R hR) (add_nonneg hR hA))
  have hΩb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Ωb R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCω (hBt1 R hR)) (hCb R hR A hA)
  have hSb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Sb R A := by
    intro R hR A hA
    exact mul_nonneg hsf (hΩb R hR A hA)
  have hIb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Ib R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCip (hBt1 0 le_rfl)) (hSb R hR A hA)
  have hHb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Hb R := by
    intro R hR
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) hR)
  have hNb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Nb R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCn (hHb R hR)) (hIb R hR A hA)
  have hOb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Ob R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCo (hBt2 R hR)) (hNb R hR A hA)
  have hF : ∀ R : ℝ, 0 ≤ R → 0 ≤ F R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCo) (hBt2 R hR))
      (mul_nonneg (mul_nonneg hCn (hHb R hR))
        (mul_nonneg (mul_nonneg hCip (hBt1 0 le_rfl))
          (mul_nonneg hsf (mul_nonneg hCω (hBt1 R hR)))))
  refine ⟨B0, B1,
    fun R hR => mul_nonneg (hF R hR)
      (add_nonneg (hBc0 R hR) (mul_nonneg (hBc1 R hR) hR)),
    fun R hR => mul_nonneg (hF R hR) (hBc1 R hR), ?_⟩
  intro g₀ hEq hjet1 hjet2 g₁ P htie δ hδ_le hδ_nonneg hbound
    R A hR hA hP2 htop
  have hRA : 0 ≤ R + A := add_nonneg hR hA
  have htop2 : ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htop 2
  have hP3 : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ (R + A) ^ 2 := by
    calc
      _ = (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
          ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ^ 2 := by
            rw [show (4 : ℕ) = 3 + 1 by norm_num, Finset.sum_range_succ]
      _ ≤ R ^ 2 + A ^ 2 := add_le_add hP2 htop2
      _ ≤ (R + A) ^ 2 := by nlinarith [mul_nonneg hR hA]
  let T1 : SmoothCcTensor g₀ 3 1 :=
    reindexedPureTrace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)
  let C : SmoothCcTensor g₀ 0 3 :=
    metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁
  let Ω : SmoothCcTensor g₀ 0 1 :=
    deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀
  let Hf : SmoothCcTensor g₀ 1 4 :=
    lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁
  let Carm : SmoothCcTensor g₀ 3 1 :=
    reindexedPureTrace (I := I) (M := M) g₀ g₀ 1 ipTracePerm
  let Ωs : SmoothCcTensor g₀ 2 3 :=
    slotExtendIter (I := I) (M := M) g₀ 0 1 2 Ω
  let Ip : SmoothCcTensor g₀ 2 1 :=
    ipLowCc (I := I) (M := M) g₀ Ω
  let T2 : SmoothCcTensor g₀ 4 2 :=
    reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁
  let Inn : SmoothCcTensor g₀ 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4 Hf Ip
  let Out : SmoothCcTensor g₀ 2 2 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2 Inn
  have hT1 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i T1‖ ^ 2) ≤ (Bt1 R) ^ 2 := by
    simpa only [T1] using htr1 g₀ hEq hjet1 hjet2 g₁ P htie
      hδ_le hδ_nonneg hbound (Equiv.refl _) R hR hP2
  have hC : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i C‖ ^ 2) ≤ (Cb R A) ^ 2 := by
    simpa only [C, Cb] using hconn g₀ hEq hjet1 hjet2 g₁ P htie
      hδ_le hδ_nonneg hbound R (R + A) hR hRA hP2 hP3
  have hΩ : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 1 i Ω‖ ^ 2) ≤ (Ωb R A) ^ 2 := by
    rw [show Ω = ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 T1 C by
      simpa only [Ω, T1, C] using
        deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp (I := I) (M := M) g₀ g₁]
    simpa only [Ωb] using hωprod g₀ hEq hjet1 hjet2 T1 C
      (Bt1 R) (Cb R A) (hBt1 R hR) (hCb R hR A hA) hT1 hC
  have hK1 : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i
        (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤ (4 * R) ^ 2 := by
    simpa only using kappaSelf_h1
      (I := I) (M := M) g₀ g₁ P htie R hP2
  have hHterm : ∀ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 1 4 i Hf‖ ^ 2 ≤
        3 * ‖iteratedCovGrad (I := I) g₀ 0 3 i
          (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 := by
    intro i hi
    have h := norm_iteratedCovGrad_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_sq_le (I := I) (M := M) g₀ g₁ i
    have hκ : lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀ =
        metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀ := by
      apply SmoothCcTensor.ext
      rfl
    rw [hκ]
    simpa only [Hf, hDim, Nat.cast_ofNat] using h
  have hH : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 1 4 i Hf‖ ^ 2) ≤ (Hb R) ^ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range 2,
          3 * ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 :=
        Finset.sum_le_sum hHterm
      _ = 3 * (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) := by
        rw [Finset.mul_sum]
      _ ≤ 3 * (4 * R) ^ 2 := mul_le_mul_of_nonneg_left hK1 (by norm_num)
      _ = (Hb R) ^ 2 := by
        dsimp only [Hb]
        conv_rhs => rw [mul_pow]
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hzeroTie : ∀ (y : M) (v w : TangentSpace I y),
      g₀.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) y v w := by
    intro y v w
    rw [ccTensorBilinSymm_zero_apply, add_zero]
  have hzeroBound : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ := by
    intro y v w
    rw [ccTensorBilinSymm_zero_apply]
    simpa only [abs_zero] using
      (mul_nonneg (mul_nonneg hδ_nonneg (Real.sqrt_nonneg (g₀.inner y v v)))
        (Real.sqrt_nonneg (g₀.inner y w w)))
  have hzeroJet : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (0 : SmoothCcTensor g₀ 0 2)‖ ^ 2) ≤ (0 : ℝ) ^ 2 := by
    calc
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hz := DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real
          (I := I) (M := M) g₀ 0 2 j
          (0 : ℝ) (0 : SmoothCcTensor g₀ 0 2)
        have hzero : iteratedCovGrad (I := I) g₀ 0 2 j
            (0 : SmoothCcTensor g₀ 0 2) = 0 := by
          simpa only [zero_smul] using hz
        rw [hzero, norm_zero, zero_pow (by norm_num)]
      _ ≤ (0 : ℝ) ^ 2 := by norm_num
  have hCarm : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i Carm‖ ^ 2) ≤ (Bt1 0) ^ 2 := by
    simpa only [Carm] using htr1 g₀ hEq hjet1 hjet2 g₀
      (0 : SmoothCcTensor g₀ 0 2) hzeroTie hδ_le hδ_nonneg hzeroBound
      ipTracePerm 0 le_rfl hzeroJet
  have hΩs : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 3 i Ωs‖ ^ 2) ≤ (Sb R A) ^ 2 := by
    simpa only [Ωs, Sb, sf] using slotIter_h2b
      (I := I) (M := M) g₀ 0 1 2 Ω (Ωb R A) hΩ
  have hIpForm :
      Ip = ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 1 Carm Ωs := by
    apply SmoothCcTensor.ext
    rfl
  have hIp : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 1 i Ip‖ ^ 2) ≤ (Ib R A) ^ 2 := by
    rw [hIpForm]
    simpa only [Ib] using hiprod g₀ hEq hjet1 hjet2 Carm Ωs
      (Bt1 0) (Sb R A) (hBt1 0 le_rfl) (hSb R hR A hA) hCarm hΩs
  have hInn : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 4 i Inn‖ ^ 2) ≤ (Nb R A) ^ 2 := by
    have hnorm := hnprod g₀ hEq hjet1 hjet2 Hf Ip
      (Hb R) (Ib R A) (hHb R hR) (hIb R hR A hA) hH hIp
    have hsquare := pow_le_pow_left₀
      (norm_nonneg
        (⟨ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4 Hf Ip⟩ :
          SmoothCcTensorH1 g₀ 2 4)) hnorm 2
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g₀ 2 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4 Hf Ip)] at hsquare
    simpa only [Inn, Nb, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hsquare
  have hT2RF :
      T2 = reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 (Equiv.refl _) := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    dsimp only [T2]
    change (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁).toSection x) =
      (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 (Equiv.refl _)).toSection x)
    rw [reindexedCometricDoubleTrace_toSection, reindexedPureTrace_toSection]
    rfl
  have hT2 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i T2‖ ^ 2) ≤ (Bt2 R) ^ 2 := by
    rw [hT2RF]
    exact htr2 g₀ hEq hjet1 hjet2 g₁ P htie hδ_le hδ_nonneg hbound
      (Equiv.refl _) R hR hP2
  have hOut : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Out‖ ^ 2) ≤ (Ob R A) ^ 2 := by
    have hnorm := hoprod g₀ hEq hjet1 hjet2 T2 Inn
      (Bt2 R) (Nb R A) (hBt2 R hR) (hNb R hR A hA) hT2 hInn
    have hsquare := pow_le_pow_left₀
      (norm_nonneg
        (⟨ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2 Inn⟩ :
          SmoothCcTensorH1 g₀ 2 2)) hnorm 2
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g₀ 2 2
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2 Inn)] at hsquare
    simpa only [Out, Ob, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hsquare
  rw [lieCorrectionZeroVectorBundle_eq_expansion (I := I) (M := M) g₀ g₁]
  have htwo : (∑ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 j ((2 : ℝ) • Out)‖ ^ 2) =
      4 * ∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 2 2 j Out‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real,
      norm_smul, Real.norm_eq_abs]
    rw [mul_pow]
    norm_num
  have hExpansion :
      lieCorrectionZeroVectorBundleExpansion (I := I) (M := M) g₀ g₁ =
        (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2 Inn := by
    rw [lieCorrectionZeroVectorBundleExpansion]
  have hOut_def :
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2 Inn = Out := by
    rfl
  rw [hExpansion, hOut_def, htwo]
  change 4 * (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Out‖ ^ 2) ≤
    (B0 R + B1 R * A) ^ 2
  calc
    _ ≤ 4 * (Ob R A) ^ 2 := mul_le_mul_of_nonneg_left hOut (by norm_num)
    _ = (B0 R + B1 R * A) ^ 2 := by
      dsimp only [B0, B1, F, Ob, Nb, Ib, Sb, Ωb, Cb]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
