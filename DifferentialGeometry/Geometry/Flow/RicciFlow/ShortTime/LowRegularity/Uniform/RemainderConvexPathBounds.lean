import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.ConvexJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.LowOrderRemainderTameBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.FirstOrderRemainderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.RicciConnectionDifferenceOrderOneBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.LowOrderRicciBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.DeTurckLie.ConnectionDifferenceDerivativeCoefficient
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.TailFirstOrderBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem ricciDeTurckRemainderZeroOrderCoefficient_h1_bound_of_uniform_component_bounds
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (C : ConvexJetConstants)
    (hC : HasUniformConvexPerturbationJetBounds (I := I) (M := M) gBase Λ C)
    (g : SmoothRiemannianMetric I M)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
    (hjet : ∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T T' : SmoothCcTensor g 0 2)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T') δ₀)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖ ≤ A →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g 2 2 i
              (ricciDeTurckRemainderZeroOrderCoefficient (I := I) (M := M) g gBase
                T T' hδ hδ' s)‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨hpath2, hpath3⟩ := hC.bounds g hEq hjet
  exact ricciDeTurckRemainderZeroOrderCoefficient_h1_tame_bound_of_segment_bounds (I := I) (M := M) hDim g gBase
    hδ₀_nonneg hδ₀_lt C.h2C C.h3C hC.h2_nonneg hC.h3_nonneg
    hpath2 hpath3

theorem ricciDeTurckRemainderZeroOrderCoefficient_h1_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T T' : SmoothCcTensor g 0 2)
          (hδ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ₀)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T') δ₀)
          (R A : ℝ), 0 ≤ R → 0 ≤ A →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ A →
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖ ≤ A →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
            (∑ i ∈ Finset.range 2,
              ‖iteratedCovGrad (I := I) g 2 2 i
                (ricciDeTurckRemainderZeroOrderCoefficient (I := I) (M := M) g gBase
                  T T' hδ hδ' s)‖ ^ 2) ≤
              (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨C, hC⟩ := exists_convex_jets (I := I) (M := M) gBase hΛ
  obtain ⟨Br0, Br1, hBr0, hBr1, hric⟩ :=
    linearizedRicciConnectionDifferenceOrder0CoeffField_h1_uniform_bound (I := I) (M := M) hDim gBase hΛ hδ₀_lt
  obtain ⟨Bd0, Bd1, hBd0, hBd1, hdla⟩ :=
    exists_uniform_deTurckLieConnectionDifferenceDerivativeCoefficient_covariantJetNormSq_one_bound (I := I) (M := M) hDim gBase hΛ hδ₀_lt
  obtain ⟨Bt0, Bt1, hBt0, hBt1, htail⟩ :=
    tail_h1_uniform (I := I) (M := M) hDim gBase hΛ hδ₀_lt
  let R0 : ℝ → ℝ := fun R => Br0 (C.h2C * R)
  let R1 : ℝ → ℝ := fun R => Br1 (C.h2C * R) * C.h3C
  let D0 : ℝ → ℝ := fun R => Bd0 (C.h2C * R)
  let D1 : ℝ → ℝ := fun R => Bd1 (C.h2C * R) * C.h3C
  let T0 : ℝ → ℝ := fun R => Bt0 (C.h2C * R)
  let T1 : ℝ → ℝ := fun R => Bt1 (C.h2C * R) * C.h3C
  let B0 : ℝ → ℝ := fun R => 4 * (R0 R + D0 R + T0 R)
  let B1 : ℝ → ℝ := fun R => 4 * (R1 R + D1 R + T1 R)
  have hCR : ∀ R : ℝ, 0 ≤ R → 0 ≤ C.h2C * R := fun R hR =>
    mul_nonneg hC.h2_nonneg hR
  have hR0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ R0 R := fun R hR =>
    hBr0 (C.h2C * R) (hCR R hR)
  have hR1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ R1 R := fun R hR =>
    mul_nonneg (hBr1 (C.h2C * R) (hCR R hR)) hC.h3_nonneg
  have hD0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ D0 R := fun R hR =>
    hBd0 (C.h2C * R) (hCR R hR)
  have hD1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ D1 R := fun R hR =>
    mul_nonneg (hBd1 (C.h2C * R) (hCR R hR)) hC.h3_nonneg
  have hT0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ T0 R := fun R hR =>
    hBt0 (C.h2C * R) (hCR R hR)
  have hT1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ T1 R := fun R hR =>
    mul_nonneg (hBt1 (C.h2C * R) (hCR R hR)) hC.h3_nonneg
  refine ⟨B0, B1, fun R hR => mul_nonneg (by norm_num)
      (add_nonneg (add_nonneg (hR0 R hR) (hD0 R hR)) (hT0 R hR)),
    fun R hR => mul_nonneg (by norm_num)
      (add_nonneg (add_nonneg (hR1 R hR) (hD1 R hR)) (hT1 R hR)), ?_⟩
  intro g hEq hjet T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3' s hs
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  have hjet3 := hjet 3 (by norm_num)
  obtain ⟨hpath2, hpath3⟩ := hC.bounds g hEq hjet
  let P : SmoothCcTensor g 0 2 := convexPerturbation (I := I) g T T' s
  let g₁ : SmoothRiemannianMetric I M := metricPerturbationPath (I := I) g T T' hδ hδ' s
  have hlow : 0 ≤ C.h2C * R := mul_nonneg hC.h2_nonneg hR
  have hhigh : 0 ≤ C.h3C * A := mul_nonneg hC.h3_nonneg hA
  have hP2 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ (C.h2C * R) ^ 2 := by
    simpa only [P] using hpath2 T T' R hR hT2 hT2' s hs
  have hP3 : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ (C.h3C * A) ^ 2 := by
    simpa only [P] using hpath3 T T' A hA hT3 hT3' s hs
  have hsingle : ‖iteratedCovGrad (I := I) g 0 2 3 P‖ ^ 2 ≤
      ∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2 := by
    have hmem : 3 ∈ Finset.range 4 := by norm_num
    exact Finset.single_le_sum
      (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2)
      (fun j _ => sq_nonneg _) hmem
  have htopSq : ‖iteratedCovGrad (I := I) g 0 2 3 P‖ ^ 2 ≤
      (C.h3C * A) ^ 2 := hsingle.trans hP3
  have htop : ‖iteratedCovGrad (I := I) g 0 2 3 P‖ ≤ C.h3C * A := by
    nlinarith [htopSq, hhigh,
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 3 P)]
  have hPbound : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ₀ := by
    have h := convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T T' hδ hδ' hs.1 hs.2
    have hscalar : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    rw [hscalar] at h
    simpa only [P] using h
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    simpa only [g₁, P] using metricPerturbationPath_inner_of_mem
      (I := I) g T T' hδ hδ'
        (Icc_subset_metricPerturbationPathDomain hδ₀_lt hδ₀_lt hs) y v w
  let RB : ℝ := R0 R + R1 R * A
  let DB : ℝ := D0 R + D1 R * A
  let TB : ℝ := T0 R + T1 R * A
  have hRB : 0 ≤ RB := add_nonneg (hR0 R hR) (mul_nonneg (hR1 R hR) hA)
  have hDB : 0 ≤ DB := add_nonneg (hD0 R hR) (mul_nonneg (hD1 R hR) hA)
  have hTB : 0 ≤ TB := add_nonneg (hT0 R hR) (mul_nonneg (hT1 R hR) hA)
  have hRicRaw := hric g hEq hjet1 hjet2 g₁ P htie
    (δ := δ₀) le_rfl hδ₀_nonneg hPbound
    (C.h2C * R) (C.h3C * A) hlow hhigh hP2 htop
  have hRic : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g 2 2 i
        (linearizedRicciConnectionDifferenceOrder0CoeffField
          (I := I) (M := M) g g₁)‖ ^ 2) ≤ RB ^ 2 := by
    simpa only [RB, R0, R1, mul_assoc] using hRicRaw
  have hDlaRaw := hdla g hEq hjet1 hjet2 hjet3 g₁ P htie
    (δ := δ₀) le_rfl hδ₀_nonneg hPbound
    (C.h2C * R) (C.h3C * A) hlow hhigh hP2 htop
  have hDla : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g 2 2 i
        (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g g₁ gBase)‖ ^ 2) ≤
      DB ^ 2 := by
    simpa only [DB, D0, D1, mul_assoc] using hDlaRaw
  have hTailRaw := htail g hEq hjet g₁ P htie
    (δ := δ₀) le_rfl hδ₀_nonneg hPbound
    (C.h2C * R) (C.h3C * A) hlow hhigh hP2 htop
  have hTail : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g 2 2 i
        (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g g₁ gBase +
          lieCorrectionZeroField (I := I) (M := M) g g₁ gBase)‖ ^ 2) ≤ TB ^ 2 := by
    simpa only [TB, T0, T1, mul_assoc] using hTailRaw
  have hraw := ricciDeTurckRemainderZeroOrderCoefficient_h1_bound_of_component_bounds (I := I) (M := M) g gBase T T' hδ hδ'
    s RB DB TB (by simpa only [g₁] using hRic)
    (by simpa only [g₁] using hDla) (by simpa only [g₁] using hTail)
  have hinside : 0 ≤ 4 * (4 * RB ^ 2 + DB ^ 2 + TB ^ 2) := by
    positivity
  have hbound : (Real.sqrt (4 * (4 * RB ^ 2 + DB ^ 2 + TB ^ 2))) ^ 2 ≤
      (4 * (RB + DB + TB)) ^ 2 := by
    rw [Real.sq_sqrt hinside]
    nlinarith [sq_nonneg RB, sq_nonneg DB, sq_nonneg TB,
      mul_nonneg hRB hDB, mul_nonneg hRB hTB, mul_nonneg hDB hTB]
  have hfactor : 4 * (RB + DB + TB) = B0 R + B1 R * A := by
    dsimp only [RB, DB, TB, B0, B1]
    ring
  exact hraw.trans (hbound.trans_eq (by rw [hfactor]))

theorem ricciDeTurckRemainderZeroOrderPathIntegral_h1_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T T' : SmoothCcTensor g 0 2)
          (hδ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ₀)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T') δ₀)
          (R A : ℝ), 0 ≤ R → 0 ≤ A →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ A →
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖ ≤ A →
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g 2 2 i
              (ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g gBase T T'
                hδ₀_lt hδ hδ₀_lt hδ')‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hcoeff⟩ :=
    ricciDeTurckRemainderZeroOrderCoefficient_h1_uniform_bound (I := I) (M := M) hDim gBase hΛ hδ₀_nonneg hδ₀_lt
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro g hEq hjet T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3'
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ₀) (δ' := δ₀) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ₀_lt hδ₀_lt
  have hBA : 0 ≤ B0 R + B1 R * A :=
    add_nonneg (hB0 R hR) (mul_nonneg (hB1 R hR) hA)
  have hpath := path_jetL2_le (I := I) (M := M) g 2 2 1
    (fun s => ricciDeTurckRemainderZeroOrderCoefficient (I := I) (M := M) g gBase T T' hδ hδ' s)
    (metricPerturbationPathDomain (δ := δ₀) (δ' := δ₀)) metricPerturbationPathDomain_isOpen hSI
    (ricciDeTurckRemainderZeroOrderCoefficient_path_joint (I := I) (M := M) g gBase T T' hδ hδ')
    (hcoeff g hEq hjet T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3')
  simpa only [ricciDeTurckRemainderZeroOrderPathIntegral] using hpath

theorem ricciDeTurckRemainderFirstOrderCoefficient_h2_bound_of_uniform_component_bounds
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (C : ConvexJetConstants)
    (hC : HasUniformConvexPerturbationJetBounds (I := I) (M := M) gBase Λ C)
    (g : SmoothRiemannianMetric I M)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
    (hjet : ∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T T' : SmoothCcTensor g 0 2)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T') δ₀)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖ ≤ A →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 3 2 i
              (ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g gBase
                T T' hδ hδ' s)‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨hpath2, hpath3⟩ := hC.bounds g hEq hjet
  exact ricciDeTurckRemainderFirstOrderCoefficient_h2_tame_bound_of_segment_bounds (I := I) (M := M) hDim g gBase
    hδ₀_nonneg hδ₀_lt C.h2C C.h3C hC.h2_nonneg hC.h3_nonneg
    hpath2 hpath3

theorem ricciDeTurckRemainderFirstOrderCoefficient_h2_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T T' : SmoothCcTensor g 0 2)
          (hδ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ₀)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T') δ₀)
          (R A : ℝ), 0 ≤ R → 0 ≤ A →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ A →
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖ ≤ A →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
            (∑ i ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 3 2 i
                (ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g gBase
                  T T' hδ hδ' s)‖ ^ 2) ≤
              (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨C, hC⟩ := exists_convex_jets (I := I) (M := M) gBase hΛ
  obtain ⟨Br0, Br1, hBr0, hBr1, hric⟩ :=
    exists_uniform_linearizedRicciConnectionDifferenceOrderOneCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim gBase hΛ hδ₀_lt
  obtain ⟨Bl0, Bl1, hBl0, hBl1, hlie⟩ :=
    deTurckLieFirstOrder_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ hδ₀_lt
  let R0 : ℝ → ℝ := fun R => Br0 (C.h2C * R)
  let R1 : ℝ → ℝ := fun R => Br1 (C.h2C * R) * C.h3C
  let L0 : ℝ → ℝ := fun R => Bl0 (C.h2C * R)
  let L1 : ℝ → ℝ := fun R => Bl1 (C.h2C * R) * C.h3C
  let B0 : ℝ → ℝ := fun R => 4 * R0 R + 2 * L0 R
  let B1 : ℝ → ℝ := fun R => 4 * R1 R + 2 * L1 R
  have hCR : ∀ R : ℝ, 0 ≤ R → 0 ≤ C.h2C * R := fun R hR =>
    mul_nonneg hC.h2_nonneg hR
  have hR0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ R0 R := fun R hR =>
    hBr0 (C.h2C * R) (hCR R hR)
  have hR1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ R1 R := fun R hR =>
    mul_nonneg (hBr1 (C.h2C * R) (hCR R hR)) hC.h3_nonneg
  have hL0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ L0 R := fun R hR =>
    hBl0 (C.h2C * R) (hCR R hR)
  have hL1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ L1 R := fun R hR =>
    mul_nonneg (hBl1 (C.h2C * R) (hCR R hR)) hC.h3_nonneg
  refine ⟨B0, B1, fun R hR => add_nonneg
      (mul_nonneg (by norm_num) (hR0 R hR))
      (mul_nonneg (by norm_num) (hL0 R hR)),
    fun R hR => add_nonneg
      (mul_nonneg (by norm_num) (hR1 R hR))
      (mul_nonneg (by norm_num) (hL1 R hR)), ?_⟩
  intro g hEq hjet T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3' s hs
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  have hjet3 := hjet 3 (by norm_num)
  obtain ⟨hpath2, hpath3⟩ := hC.bounds g hEq hjet
  let P : SmoothCcTensor g 0 2 := convexPerturbation (I := I) g T T' s
  let g₁ : SmoothRiemannianMetric I M := metricPerturbationPath (I := I) g T T' hδ hδ' s
  have hlow : 0 ≤ C.h2C * R := mul_nonneg hC.h2_nonneg hR
  have hhigh : 0 ≤ C.h3C * A := mul_nonneg hC.h3_nonneg hA
  have hP2 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ (C.h2C * R) ^ 2 := by
    simpa only [P] using hpath2 T T' R hR hT2 hT2' s hs
  have hP3 : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ (C.h3C * A) ^ 2 := by
    simpa only [P] using hpath3 T T' A hA hT3 hT3' s hs
  have hPbound : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ₀ := by
    have h := convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T T' hδ hδ' hs.1 hs.2
    have hscalar : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    rw [hscalar] at h
    simpa only [P] using h
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    simpa only [g₁, P] using metricPerturbationPath_inner_of_mem
      (I := I) g T T' hδ hδ'
        (Icc_subset_metricPerturbationPathDomain hδ₀_lt hδ₀_lt hs) y v w
  let RB : ℝ := R0 R + R1 R * A
  let LB : ℝ := L0 R + L1 R * A
  have hRB : 0 ≤ RB := add_nonneg (hR0 R hR) (mul_nonneg (hR1 R hR) hA)
  have hLB : 0 ≤ LB := add_nonneg (hL0 R hR) (mul_nonneg (hL1 R hR) hA)
  have hRicRaw := hric g hEq hjet1 hjet2 g₁ P htie
    (δ := δ₀) le_rfl hδ₀_nonneg hPbound
    (C.h2C * R) (C.h3C * A) hlow hhigh hP2 hP3
  have hRic : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 3 2 i
        (linearizedRicciConnectionDifferenceOrder1CoeffField
          (I := I) (M := M) g g₁)‖ ^ 2) ≤ RB ^ 2 := by
    simpa only [RB, R0, R1, mul_assoc] using hRicRaw
  have hLieRaw := hlie g hEq hjet1 hjet2 hjet3 g₁ P htie
    (δ := δ₀) le_rfl hδ₀_nonneg hPbound
    (C.h2C * R) (C.h3C * A) hlow hhigh hP2 hP3
  have hLie : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 3 2 i
        (deTurckLieFirstOrderCoeff (I := I) (M := M) g g₁ gBase)‖ ^ 2) ≤
      LB ^ 2 := by
    simpa only [LB, L0, L1, mul_assoc] using hLieRaw
  have hraw := rhs_one_coefficient_sobolev_two_bound (I := I) (M := M) g gBase T T' hδ hδ'
    s RB LB (by simpa only [g₁] using hRic) (by simpa only [g₁] using hLie)
  have hinside : 0 ≤ 2 * (4 * RB ^ 2 + LB ^ 2) := by positivity
  have hbound : (Real.sqrt (2 * (4 * RB ^ 2 + LB ^ 2))) ^ 2 ≤
      (4 * RB + 2 * LB) ^ 2 := by
    rw [Real.sq_sqrt hinside]
    nlinarith [sq_nonneg RB, sq_nonneg LB, mul_nonneg hRB hLB]
  have hfactor : 4 * RB + 2 * LB = B0 R + B1 R * A := by
    dsimp only [RB, LB, B0, B1]
    ring
  exact hraw.trans (hbound.trans_eq (by rw [hfactor]))

theorem ricciDeTurckRemainderFirstOrderPathIntegral_h2_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T T' : SmoothCcTensor g 0 2)
          (hδ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ₀)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T') δ₀)
          (R A : ℝ), 0 ≤ R → 0 ≤ A →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ A →
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖ ≤ A →
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 3 2 i
              (ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g gBase T T'
                hδ₀_lt hδ hδ₀_lt hδ')‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hcoeff⟩ :=
    ricciDeTurckRemainderFirstOrderCoefficient_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ hδ₀_nonneg hδ₀_lt
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro g hEq hjet T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3'
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ₀) (δ' := δ₀) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ₀_lt hδ₀_lt
  have hBA : 0 ≤ B0 R + B1 R * A :=
    add_nonneg (hB0 R hR) (mul_nonneg (hB1 R hR) hA)
  have hpath := path_jetL2_le (I := I) (M := M) g 3 2 2
    (fun s => ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g gBase T T' hδ hδ' s)
    (metricPerturbationPathDomain (δ := δ₀) (δ' := δ₀)) metricPerturbationPathDomain_isOpen hSI
    (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M) g gBase T T' hδ hδ')
    (hcoeff g hEq hjet T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3')
  simpa only [ricciDeTurckRemainderFirstOrderPathIntegral] using hpath

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
