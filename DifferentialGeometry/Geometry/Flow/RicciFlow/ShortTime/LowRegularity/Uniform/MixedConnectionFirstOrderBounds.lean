import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.DeTurckLieFirstOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.MixedTensorApplicationFirstSecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.CoefficientSecondOrderBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem amix_jet_two
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (W : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j ((2 : ℝ) • W)‖ ^ 2) =
      4 * ∑ j ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real,
    norm_smul, Real.norm_eq_abs]
  norm_num
  ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem amix_jet_sum2
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (W Z : SmoothCcTensor g r s) (A B : ℝ)
    (hW : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2) ≤ A ^ 2)
    (hZ : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) ≤ B ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (W + Z)‖ ^ 2) ≤
      2 * (A ^ 2 + B ^ 2) := by
  have hterm : ∀ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (W + Z)‖ ^ 2 ≤
        2 * (‖iteratedCovGrad (I := I) g r s j W‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) := by
    intro j _
    rw [iteratedCovGrad_add]
    have htri := norm_add_le
      (iteratedCovGrad (I := I) g r s j W)
      (iteratedCovGrad (I := I) g r s j Z)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg
      (‖iteratedCovGrad (I := I) g r s j W‖ -
        ‖iteratedCovGrad (I := I) g r s j Z‖)]
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        2 * (‖iteratedCovGrad (I := I) g r s j W‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) :=
      Finset.sum_le_sum hterm
    _ = 2 * ((∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 2 * (A ^ 2 + B ^ 2) := by gcongr

theorem lieCorrectionZeroMixedConnection_h1_uniform_bound
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
        MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ →
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
              (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ gBase)‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  classical
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨Bt2, hBt2, htr2⟩ :=
    trace_h2_uniform (I := I) (M := M) 2 hDim gBase hΛ0 hδ₀
  obtain ⟨Bt3, hBt3, htr3⟩ :=
    trace_h2_uniform (I := I) (M := M) 3 hDim gBase hΛ0 hδ₀
  obtain ⟨Bt4, hBt4, htr4⟩ :=
    trace_h2_uniform (I := I) (M := M) 4 hDim gBase hΛ0 hδ₀
  obtain ⟨BK, hBK, hkbg⟩ :=
    kappaBackground_h1_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Cq, hCq, hqprod⟩ :=
    operatorFieldComposition_h2_h2_to_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 2 5 3
  obtain ⟨Cn, hCn, hnprod⟩ :=
    operatorFieldComposition_h1_uniform_bound (I := I) (M := M) hDim gBase hΛ 2 3 6
  obtain ⟨Cm, hCm, hmprod⟩ :=
    operatorFieldComposition_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 2 6 4
  obtain ⟨Co, hCo, hoprod⟩ :=
    operatorFieldComposition_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 2 4 2
  let sf : ℕ → ℝ := fun w =>
    Real.sqrt ((Module.finrank ℝ E : ℝ) ^ w)
  let Qb : ℝ → ℝ → ℝ := fun R A =>
    Cq * Bt3 R * (sf 2 * (4 * (R + A)))
  let Nb : ℝ → ℝ → ℝ := fun R A =>
    Cn * (sf 3 * BK R) * Qb R A
  let Mb : ℝ → ℝ → ℝ := fun R A =>
    Cm * Bt4 R * Nb R A
  let Ob : ℝ → ℝ → ℝ := fun R A =>
    Co * Bt2 R * Mb R A
  let F : ℝ → ℝ := fun R =>
    4 * Co * Bt2 R *
      (Cm * Bt4 R *
        (Cn * (sf 3 * BK R) *
          (Cq * Bt3 R * (sf 2 * 4))))
  let B0 : ℝ → ℝ := fun R => F R * R
  let B1 : ℝ → ℝ := F
  have hsf : ∀ w : ℕ, 0 ≤ sf w :=
    fun _ => Real.sqrt_nonneg _
  have hQb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Qb R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCq (hBt3 R hR))
      (mul_nonneg (hsf 2)
        (mul_nonneg (by norm_num) (add_nonneg hR hA)))
  have hNb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Nb R A := by
    intro R hR A hA
    exact mul_nonneg
      (mul_nonneg hCn (mul_nonneg (hsf 3) (hBK R hR)))
      (hQb R hR A hA)
  have hMb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Mb R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCm (hBt4 R hR))
      (hNb R hR A hA)
  have hOb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Ob R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCo (hBt2 R hR))
      (hMb R hR A hA)
  have hF : ∀ R : ℝ, 0 ≤ R → 0 ≤ F R := by
    intro R hR
    dsimp only [F]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCo) (hBt2 R hR))
      (mul_nonneg
        (mul_nonneg hCm (hBt4 R hR))
        (mul_nonneg
          (mul_nonneg hCn (mul_nonneg (hsf 3) (hBK R hR)))
          (mul_nonneg
            (mul_nonneg hCq (hBt3 R hR))
            (mul_nonneg (hsf 2) (by norm_num)))))
  refine ⟨B0, B1,
    fun R hR => by
      dsimp only [B0]
      exact mul_nonneg (hF R hR) hR,
    fun R hR => by
      simpa only [B1] using hF R hR, ?_⟩
  intro g₀ hEq hjet1 hjet2 hjet3 g₁ P htie
    δ hδ_le hδ_nonneg hbound R A hR hA hP2 htop
  have hRA : 0 ≤ R + A := add_nonneg hR hA
  have htop2 :
      ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htop 2
  have hP3 :
      (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤
        (R + A) ^ 2 := by
    calc
      _ = (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
          ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ^ 2 := by
        rw [show (4 : ℕ) = 3 + 1 by norm_num, Finset.sum_range_succ]
      _ ≤ R ^ 2 + A ^ 2 := add_le_add hP2 htop2
      _ ≤ (R + A) ^ 2 := by nlinarith [mul_nonneg hR hA]
  let T2a : SmoothCcTensor g₀ 4 2 :=
    reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  let T2b : SmoothCcTensor g₀ 4 2 :=
    reindexedPureTrace (I := I) (M := M) g₀ g₁ 2
      (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
  let T3 : SmoothCcTensor g₀ 5 3 :=
    reindexedPureTrace (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour
  let T4 : SmoothCcTensor g₀ 6 4 :=
    reindexedPureTrace (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne
  let K0 : SmoothCcTensor g₀ 0 3 :=
    lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀
  let KB : SmoothCcTensor g₀ 0 3 :=
    lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ gBase
  let K0s : SmoothCcTensor g₀ 2 5 :=
    slotExtendIter (I := I) (M := M) g₀ 0 3 2 K0
  let Q : SmoothCcTensor g₀ 2 3 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3 T3 K0s
  let KBs : SmoothCcTensor g₀ 3 6 :=
    slotExtendIter (I := I) (M := M) g₀ 0 3 3 KB
  let N : SmoothCcTensor g₀ 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6 KBs Q
  let Mid : SmoothCcTensor g₀ 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4 T4 N
  let Oa : SmoothCcTensor g₀ 2 2 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2a Mid
  let Ob' : SmoothCcTensor g₀ 2 2 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2b Mid
  have hT2a :
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i T2a‖ ^ 2) ≤
        (Bt2 R) ^ 2 := by
    simpa only [T2a] using
      htr2 g₀ hEq hjet1 hjet2 g₁ P htie hδ_le hδ_nonneg hbound
        lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne R hR hP2
  have hT2b :
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i T2b‖ ^ 2) ≤
        (Bt2 R) ^ 2 := by
    simpa only [T2b] using
      htr2 g₀ hEq hjet1 hjet2 g₁ P htie hδ_le hδ_nonneg hbound
        (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) R hR hP2
  have hT3 :
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 5 3 i T3‖ ^ 2) ≤
        (Bt3 R) ^ 2 := by
    simpa only [T3] using
      htr3 g₀ hEq hjet1 hjet2 g₁ P htie hδ_le hδ_nonneg hbound
        lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour R hR hP2
  have hT4 :
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 6 4 i T4‖ ^ 2) ≤
        (Bt4 R) ^ 2 := by
    simpa only [T4] using
      htr4 g₀ hEq hjet1 hjet2 g₁ P htie hδ_le hδ_nonneg hbound
        lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne R hR hP2
  have hK0 :
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 0 3 i K0‖ ^ 2) ≤
        (4 * (R + A)) ^ 2 := by
    simpa only [K0] using
      kappaSelf_h2 (I := I) (M := M) g₀ g₁ P htie
        (R + A) hRA hP3
  have hKB :
      (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 0 3 i KB‖ ^ 2) ≤
        (BK R) ^ 2 := by
    simpa only [KB] using
      hkbg g₀ hEq hjet1 hjet2 hjet3 g₁ P htie R hR hP2
  have hK0s :
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 2 5 i K0s‖ ^ 2) ≤
        (sf 2 * (4 * (R + A))) ^ 2 := by
    simpa only [K0s, sf] using
      slotIter_h2b (I := I) (M := M) g₀ 0 3 2 K0
        (4 * (R + A)) hK0
  have hQ :
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 2 3 i Q‖ ^ 2) ≤
        (Qb R A) ^ 2 := by
    simpa only [Q, Qb] using
      hqprod g₀ hEq hjet1 hjet2 T3 K0s
        (Bt3 R) (sf 2 * (4 * (R + A)))
        (hBt3 R hR)
        (mul_nonneg (hsf 2)
          (mul_nonneg (by norm_num) hRA))
        hT3 hK0s
  have hKBs :
      (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 3 6 i KBs‖ ^ 2) ≤
        (sf 3 * BK R) ^ 2 := by
    simpa only [KBs, sf] using
      slotIter_h1b (I := I) (M := M) g₀ 0 3 3 KB (BK R) hKB
  have hN :
      (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 2 6 i N‖ ^ 2) ≤
        (Nb R A) ^ 2 := by
    have hnorm :=
      hnprod g₀ hEq hjet1 hjet2 KBs Q
        (sf 3 * BK R) (Qb R A)
        (mul_nonneg (hsf 3) (hBK R hR))
        (hQb R hR A hA) hKBs hQ
    have hsquare := pow_le_pow_left₀
      (norm_nonneg
        (⟨ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6 KBs Q⟩ :
          SmoothCcTensorH1 g₀ 2 6)) hnorm 2
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g₀ 2 6
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6 KBs Q)] at hsquare
    simpa only [N, Nb, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, iteratedCovGrad_zero, iteratedCovGrad_succ,
      Nat.zero_add] using hsquare
  have hMid :
      (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 2 4 i Mid‖ ^ 2) ≤
        (Mb R A) ^ 2 := by
    have hnorm :=
      hmprod g₀ hEq hjet1 hjet2 T4 N
        (Bt4 R) (Nb R A)
        (hBt4 R hR) (hNb R hR A hA) hT4 hN
    have hsquare := pow_le_pow_left₀
      (norm_nonneg
        (⟨ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4 T4 N⟩ :
          SmoothCcTensorH1 g₀ 2 4)) hnorm 2
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g₀ 2 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4 T4 N)] at hsquare
    simpa only [Mid, Mb, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, iteratedCovGrad_zero, iteratedCovGrad_succ,
      Nat.zero_add] using hsquare
  have hOa :
      (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i Oa‖ ^ 2) ≤
        (Ob R A) ^ 2 := by
    have hnorm :=
      hoprod g₀ hEq hjet1 hjet2 T2a Mid
        (Bt2 R) (Mb R A)
        (hBt2 R hR) (hMb R hR A hA) hT2a hMid
    have hsquare := pow_le_pow_left₀
      (norm_nonneg
        (⟨ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2a Mid⟩ :
          SmoothCcTensorH1 g₀ 2 2)) hnorm 2
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g₀ 2 2
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2a Mid)] at hsquare
    simpa only [Oa, Ob, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, iteratedCovGrad_zero, iteratedCovGrad_succ,
      Nat.zero_add] using hsquare
  have hOb' :
      (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i Ob'‖ ^ 2) ≤
        (Ob R A) ^ 2 := by
    have hnorm :=
      hoprod g₀ hEq hjet1 hjet2 T2b Mid
        (Bt2 R) (Mb R A)
        (hBt2 R hR) (hMb R hR A hA) hT2b hMid
    have hsquare := pow_le_pow_left₀
      (norm_nonneg
        (⟨ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2b Mid⟩ :
          SmoothCcTensorH1 g₀ 2 2)) hnorm 2
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g₀ 2 2
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2b Mid)] at hsquare
    simpa only [Ob', Ob, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, iteratedCovGrad_zero, iteratedCovGrad_succ,
      Nat.zero_add] using hsquare
  rw [lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g₀ g₁ gBase]
  have hsum :=
    amix_jet_sum2 (I := I) (M := M) g₀ 2 2 2 Oa Ob'
      (Ob R A) (Ob R A) hOa hOb'
  have htwo :=
    amix_jet_two (I := I) (M := M) g₀ 2 2 2 (Oa + Ob')
  rw [show lieCorrectionZeroMixedConnectionExpansion (I := I) (M := M) g₀ g₁ gBase =
      (2 : ℝ) • (Oa + Ob') by rfl, htwo]
  change 4 * (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i (Oa + Ob')‖ ^ 2) ≤
    (B0 R + B1 R * A) ^ 2
  calc
    _ ≤ 4 * (2 * ((Ob R A) ^ 2 + (Ob R A) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (B0 R + B1 R * A) ^ 2 := by
      dsimp only [B0, B1, F, Ob, Mb, Nb, Qb]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
