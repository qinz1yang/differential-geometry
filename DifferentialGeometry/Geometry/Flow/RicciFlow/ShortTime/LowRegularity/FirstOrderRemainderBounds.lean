import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.LowOrderRemainderTameBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciConnectionDifferenceOrderOneBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.DeTurckLieFirstOrderBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSPathIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Parametric.JetIntegral
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
    DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
    DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Geometry.Curvature

noncomputable section


open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem ricciDeTurckRemainderFirstOrderCoefficient_h2_tame_bound_of_segment_bounds
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1)
    (C2 C3 : ℝ) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (hpath2 :
      ∀ (T T' : SmoothCcTensor g₀ 0 2) (R : ℝ), 0 ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤
            (C2 * R) ^ 2)
    (hpath3 :
      ∀ (T T' : SmoothCcTensor g₀ 0 2) (R : ℝ), 0 ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖ ≤ R →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤
            (C3 * R) ^ 2) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ₀)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖ ≤ A →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g₀ g_bg
                T T' hδ hδ' s)‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨Br0, Br1, hBr0, hBr1, hric⟩ :=
    exists_linearizedRicciConnectionDifferenceOrderOneCoefficient_covariantJetNormSq_two_tame_bound (I := I) (M := M) hDim g₀ hδ₀_lt
  obtain ⟨Bl0, Bl1, hBl0, hBl1, hlie⟩ :=
    deTurckLieFirstOrder_h2_tame_bound (I := I) (M := M) hDim g₀ g_bg hδ₀_lt
  let R0 : ℝ → ℝ := fun R => Br0 (C2 * R)
  let R1 : ℝ → ℝ := fun R => Br1 (C2 * R) * C3
  let L0 : ℝ → ℝ := fun R => Bl0 (C2 * R)
  let L1 : ℝ → ℝ := fun R => Bl1 (C2 * R) * C3
  let B0 : ℝ → ℝ := fun R => 4 * R0 R + 2 * L0 R
  let B1 : ℝ → ℝ := fun R => 4 * R1 R + 2 * L1 R
  have hCR : ∀ R : ℝ, 0 ≤ R → 0 ≤ C2 * R := fun R hR =>
    mul_nonneg hC2 hR
  have hR0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ R0 R := fun R hR =>
    hBr0 (C2 * R) (hCR R hR)
  have hR1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ R1 R := fun R hR =>
    mul_nonneg (hBr1 (C2 * R) (hCR R hR)) hC3
  have hL0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ L0 R := fun R hR =>
    hBl0 (C2 * R) (hCR R hR)
  have hL1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ L1 R := fun R hR =>
    mul_nonneg (hBl1 (C2 * R) (hCR R hR)) hC3
  refine ⟨B0, B1, fun R hR => add_nonneg
      (mul_nonneg (by norm_num) (hR0 R hR))
      (mul_nonneg (by norm_num) (hL0 R hR)),
    fun R hR => add_nonneg
      (mul_nonneg (by norm_num) (hR1 R hR))
      (mul_nonneg (by norm_num) (hL1 R hR)), ?_⟩
  intro T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3' s hs
  let P : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s
  let g₁ : SmoothRiemannianMetric I M := metricPerturbationPath (I := I) g₀ T T' hδ hδ' s
  have hlow : 0 ≤ C2 * R := mul_nonneg hC2 hR
  have hhigh : 0 ≤ C3 * A := mul_nonneg hC3 hA
  have hP2 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ (C2 * R) ^ 2 := by
    simpa only [P] using hpath2 T T' R hR hT2 hT2' s hs
  have hP3 : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ (C3 * A) ^ 2 := by
    simpa only [P] using hpath3 T T' A hA hT3 hT3' s hs
  have hPbound : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ P) δ₀ := by
    have h := convexPerturbation_gFibreOpBound
      (I := I) (M := M) g₀ T T' hδ hδ' hs.1 hs.2
    have hscalar : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    rw [hscalar] at h
    simpa only [P] using h
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    simpa only [g₁, P] using metricPerturbationPath_inner_of_mem
      (I := I) g₀ T T' hδ hδ'
        (Icc_subset_metricPerturbationPathDomain hδ₀_lt hδ₀_lt hs) y v w
  let RB : ℝ := R0 R + R1 R * A
  let LB : ℝ := L0 R + L1 R * A
  have hRB : 0 ≤ RB := add_nonneg (hR0 R hR) (mul_nonneg (hR1 R hR) hA)
  have hLB : 0 ≤ LB := add_nonneg (hL0 R hR) (mul_nonneg (hL1 R hR) hA)
  have hRicRaw := hric g₁ P htie (_hδ_le := le_rfl) hδ₀_nonneg hPbound
    (C2 * R) (C3 * A) hlow hhigh hP2 hP3
  have hRic : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnectionDifferenceOrder1CoeffField
          (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤ RB ^ 2 := by
    simpa only [RB, R0, R1, mul_assoc] using hRicRaw
  have hLieRaw := hlie g₁ P htie (_hδ_le := le_rfl) hδ₀_nonneg hPbound
    (C2 * R) (C3 * A) hlow hhigh hP2 hP3
  have hLie : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
      LB ^ 2 := by
    simpa only [LB, L0, L1, mul_assoc] using hLieRaw
  have hraw := rhs_one_coefficient_sobolev_two_bound (I := I) (M := M) g₀ g_bg T T' hδ hδ'
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

theorem ricciDeTurckRemainderFirstOrderCoefficient_h2_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ₀)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖ ≤ A →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g₀ g_bg
                T T' hδ hδ' s)‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨C2, hC2, hpath2⟩ := convex_h2_jet (I := I) (M := M) g₀
  obtain ⟨C3, hC3, hpath3⟩ := convex_h3_jet (I := I) (M := M) g₀
  obtain ⟨Br0, Br1, hBr0, hBr1, hric⟩ :=
    exists_linearizedRicciConnectionDifferenceOrderOneCoefficient_covariantJetNormSq_two_tame_bound (I := I) (M := M) hDim g₀ hδ₀_lt
  obtain ⟨Bl0, Bl1, hBl0, hBl1, hlie⟩ :=
    deTurckLieFirstOrder_h2_tame_bound (I := I) (M := M) hDim g₀ g_bg hδ₀_lt
  let R0 : ℝ → ℝ := fun R => Br0 (C2 * R)
  let R1 : ℝ → ℝ := fun R => Br1 (C2 * R) * C3
  let L0 : ℝ → ℝ := fun R => Bl0 (C2 * R)
  let L1 : ℝ → ℝ := fun R => Bl1 (C2 * R) * C3
  let B0 : ℝ → ℝ := fun R => 4 * R0 R + 2 * L0 R
  let B1 : ℝ → ℝ := fun R => 4 * R1 R + 2 * L1 R
  have hCR : ∀ R : ℝ, 0 ≤ R → 0 ≤ C2 * R := fun R hR =>
    mul_nonneg hC2 hR
  have hR0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ R0 R := fun R hR =>
    hBr0 (C2 * R) (hCR R hR)
  have hR1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ R1 R := fun R hR =>
    mul_nonneg (hBr1 (C2 * R) (hCR R hR)) hC3
  have hL0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ L0 R := fun R hR =>
    hBl0 (C2 * R) (hCR R hR)
  have hL1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ L1 R := fun R hR =>
    mul_nonneg (hBl1 (C2 * R) (hCR R hR)) hC3
  refine ⟨B0, B1, fun R hR => add_nonneg
      (mul_nonneg (by norm_num) (hR0 R hR))
      (mul_nonneg (by norm_num) (hL0 R hR)),
    fun R hR => add_nonneg
      (mul_nonneg (by norm_num) (hR1 R hR))
      (mul_nonneg (by norm_num) (hL1 R hR)), ?_⟩
  intro T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3' s hs
  let P : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s
  let g₁ : SmoothRiemannianMetric I M := metricPerturbationPath (I := I) g₀ T T' hδ hδ' s
  have hlow : 0 ≤ C2 * R := mul_nonneg hC2 hR
  have hhigh : 0 ≤ C3 * A := mul_nonneg hC3 hA
  have hP2 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ (C2 * R) ^ 2 := by
    simpa only [P] using hpath2 T T' R hR hT2 hT2' s hs
  have hP3 : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ (C3 * A) ^ 2 := by
    simpa only [P] using hpath3 T T' A hA hT3 hT3' s hs
  have hPbound : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ P) δ₀ := by
    have h := convexPerturbation_gFibreOpBound
      (I := I) (M := M) g₀ T T' hδ hδ' hs.1 hs.2
    have hscalar : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    rw [hscalar] at h
    simpa only [P] using h
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    simpa only [g₁, P] using metricPerturbationPath_inner_of_mem
      (I := I) g₀ T T' hδ hδ'
        (Icc_subset_metricPerturbationPathDomain hδ₀_lt hδ₀_lt hs) y v w
  let RB : ℝ := R0 R + R1 R * A
  let LB : ℝ := L0 R + L1 R * A
  have hRB : 0 ≤ RB := add_nonneg (hR0 R hR) (mul_nonneg (hR1 R hR) hA)
  have hLB : 0 ≤ LB := add_nonneg (hL0 R hR) (mul_nonneg (hL1 R hR) hA)
  have hRicRaw := hric g₁ P htie (_hδ_le := le_rfl) hδ₀_nonneg hPbound
    (C2 * R) (C3 * A) hlow hhigh hP2 hP3
  have hRic : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnectionDifferenceOrder1CoeffField
          (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤ RB ^ 2 := by
    simpa only [RB, R0, R1, mul_assoc] using hRicRaw
  have hLieRaw := hlie g₁ P htie (_hδ_le := le_rfl) hδ₀_nonneg hPbound
    (C2 * R) (C3 * A) hlow hhigh hP2 hP3
  have hLie : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
      LB ^ 2 := by
    simpa only [LB, L0, L1, mul_assoc] using hLieRaw
  have hraw := rhs_one_coefficient_sobolev_two_bound (I := I) (M := M) g₀ g_bg T T' hδ hδ'
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

theorem ricciDeTurckRemainderFirstOrderPathIntegral_h2_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ₀)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖ ≤ A →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
            (ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g₀ g_bg T T'
              hδ₀_lt hδ hδ₀_lt hδ')‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hcoeff⟩ :=
    ricciDeTurckRemainderFirstOrderCoefficient_h2_tame_bound (I := I) (M := M) hDim g₀ g_bg hδ₀_nonneg hδ₀_lt
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3'
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ₀) (δ' := δ₀) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ₀_lt hδ₀_lt
  have hBA : 0 ≤ B0 R + B1 R * A :=
    add_nonneg (hB0 R hR) (mul_nonneg (hB1 R hR) hA)
  have hpath := path_jetL2_le (I := I) (M := M) g₀ 3 2 2
    (fun s => ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g₀ g_bg T T' hδ hδ' s)
    (metricPerturbationPathDomain (δ := δ₀) (δ' := δ₀)) metricPerturbationPathDomain_isOpen hSI
    (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M) g₀ g_bg T T' hδ hδ')
    (hcoeff T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3')
  simpa only [ricciDeTurckRemainderFirstOrderPathIntegral] using hpath

end DifferentialGeometry.PDE.RicciFlow

end
