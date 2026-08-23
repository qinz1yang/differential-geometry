import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciConnectionDifferenceOrder0KernelJetGrid
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.MixedTensorApplicationFirstSecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.CoefficientSecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.GridTameBounds

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
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iteratedCovGrad_smul_real
    (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (W : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • W) =
      c • iteratedCovGrad (I := I) g r s j W := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem pure_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g₁ =
      pureTrace (I := I) (M := M) g₀ g₁ 2 := by
  rfl


theorem linearizedRicciConnectionDifferenceOrder0CoeffField_h1_uniform_bound
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
              (linearizedRicciConnectionDifferenceOrder0CoeffField
                (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  classical
  have hΛ0 : 0 ≤ Λ := le_trans (by norm_num) hΛ
  obtain ⟨Capp, hCapp, happ⟩ :=
    operatorFieldComposition_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 2 4 2
  obtain ⟨Bt, hBt, htrace⟩ :=
    trace2_h2_uniform (I := I) (M := M) hDim gBase hΛ0 hδ₀
  obtain ⟨Ck, hCk, hkerPt⟩ :=
    ricci0_ker_grid_unif (I := I) (M := M) hδ₀
  obtain ⟨Bk0, Bk1, hBk0, hBk1, hker⟩ :=
    h1_grid_uniform (I := I) (M := M) hDim gBase hΛ0
      (r := 2) (s := 4) Ck hCk
  let B0 : ℝ → ℝ := fun R => Capp * (2 * Bt R) * Bk0 R
  let B1 : ℝ → ℝ := fun R => Capp * (2 * Bt R) * Bk1 R
  refine ⟨B0, B1, fun R hR => by
    exact mul_nonneg
      (mul_nonneg hCapp (mul_nonneg (by norm_num) (hBt R hR)))
      (hBk0 R hR), fun R hR => by
    exact mul_nonneg
      (mul_nonneg hCapp (mul_nonneg (by norm_num) (hBt R hR)))
      (hBk1 R hR), ?_⟩
  intro g₀ hEq hjet1 hjet2 g₁ P htie δ hδ_le hδ_nonneg hbound
    R A hR hA hP2 htop
  have hkernel : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 4 i
        (linearizedRicciConnectionDifferenceOrder0KernelField (I := I) g₀ g₁)‖ ^ 2) ≤
      (Bk0 R + Bk1 R * A) ^ 2 := by
    refine hker g₀ hEq hjet1 hjet2 P
      (linearizedRicciConnectionDifferenceOrder0KernelField (I := I) g₀ g₁)
      R A hR hA hP2 htop ?_
    intro i hi x
    simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGrid] using
      hkerPt g₀ g₁ P htie hδ_le hδ_nonneg hbound i x
  let pureF : SmoothCcTensor g₀ 4 2 :=
    cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g₁
  let R1 : SmoothCcTensor g₀ 4 2 :=
    reindexCoeffGen (I := I) (M := M) g₀ 4 2 pureF fourTraceArgPerm0231
  let R2 : SmoothCcTensor g₀ 4 2 :=
    reindexCoeffGen (I := I) (M := M) g₀ 4 2 pureF fourTraceArgPerm0321
  let R3 : SmoothCcTensor g₀ 4 2 :=
    reindexCoeffGen (I := I) (M := M) g₀ 4 2 pureF fourTraceArgPerm2301
  have hcomb : ricciCometricFourTraceCastG0 (I := I) g₀ g₁ =
      ((1 : ℝ) / 2) • (R1 + R2 - pureF - R3) := by
    simpa only [pureF, R1, R2, R3] using
      ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) (M := M) g₀ g₁
  have hreindex : ∀ (ρ : Equiv.Perm (Fin 4)) (i : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 pureF ρ)‖ =
      ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ := by
    intro ρ i
    rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M),
      norm_reindexCoeffGen_eq (I := I) (M := M)]
  have hpure : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ ^ 2) ≤
      (Bt R) ^ 2 := by
    have ht := htrace g₀ hEq hjet1 hjet2 g₁ P htie
      hδ_le hδ_nonneg hbound (Equiv.refl (Fin 4)) R hR hP2
    calc
      _ = ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexedPureTrace (I := I) (M := M) g₀ g₁ 2
              (Equiv.refl (Fin 4)))‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [reindexedPureTrace, iteratedCovGrad_reindexCoeffGen
          (I := I) (M := M),
          norm_reindexCoeffGen_eq (I := I) (M := M)]
        dsimp only [pureF]
        rw [pure_eq (I := I) (M := M) g₀ g₁]
      _ ≤ (Bt R) ^ 2 := ht
  have hcastNorm : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ≤
      2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ := by
    intro i
    rw [hcomb, iteratedCovGrad_smul_real,
      iteratedCovGrad_sub, iteratedCovGrad_sub, iteratedCovGrad_add,
      norm_smul, Real.norm_eq_abs,
      show |(1 : ℝ) / 2| = 1 / 2 by norm_num]
    have h1 := norm_add_le
      (iteratedCovGrad (I := I) g₀ 4 2 i R1)
      (iteratedCovGrad (I := I) g₀ 4 2 i R2)
    have h2 := norm_sub_le
      (iteratedCovGrad (I := I) g₀ 4 2 i R1 +
        iteratedCovGrad (I := I) g₀ 4 2 i R2)
      (iteratedCovGrad (I := I) g₀ 4 2 i pureF)
    have h3 := norm_sub_le
      (iteratedCovGrad (I := I) g₀ 4 2 i R1 +
        iteratedCovGrad (I := I) g₀ 4 2 i R2 -
        iteratedCovGrad (I := I) g₀ 4 2 i pureF)
      (iteratedCovGrad (I := I) g₀ 4 2 i R3)
    rw [show ‖iteratedCovGrad (I := I) g₀ 4 2 i R1‖ =
        ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ by
          exact hreindex fourTraceArgPerm0231 i,
      show ‖iteratedCovGrad (I := I) g₀ 4 2 i R2‖ =
        ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ by
          exact hreindex fourTraceArgPerm0321 i] at h1
    rw [show ‖iteratedCovGrad (I := I) g₀ 4 2 i R3‖ =
        ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ by
          exact hreindex fourTraceArgPerm2301 i] at h3
    linarith [norm_nonneg
      (iteratedCovGrad (I := I) g₀ 4 2 i pureF)]
  have hcast : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ^ 2) ≤
      (2 * Bt R) ^ 2 := by
    have hsq : ∀ i : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤
        4 * ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ ^ 2 := by
      intro i
      have h := pow_le_pow_left₀ (norm_nonneg _) (hcastNorm i) 2
      nlinarith
    calc
      _ ≤ ∑ i ∈ Finset.range 3,
          4 * ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hsq i
      _ = 4 * (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ ^ 2) := by
        rw [Finset.mul_sum]
      _ ≤ 4 * (Bt R) ^ 2 :=
        mul_le_mul_of_nonneg_left hpure (by norm_num)
      _ = (2 * Bt R) ^ 2 := by ring
  rw [linearizedRicciConnectionDifferenceOrder0CoeffField_eq_ricciCometricFourTrace_comp_kernelField
    (I := I) (M := M) g₀ g₁]
  have hout := happ g₀ hEq hjet1 hjet2
    (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
    (linearizedRicciConnectionDifferenceOrder0KernelField (I := I) g₀ g₁)
    (2 * Bt R) (Bk0 R + Bk1 R * A)
    (mul_nonneg (by norm_num) (hBt R hR))
    (add_nonneg (hBk0 R hR) (mul_nonneg (hBk1 R hR) hA))
    hcast hkernel
  have hsquare := pow_le_pow_left₀
    (norm_nonneg
      (⟨ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
        (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
        (linearizedRicciConnectionDifferenceOrder0KernelField (I := I) g₀ g₁)⟩ :
          SmoothCcTensorH1 g₀ 2 2)) hout 2
  rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g₀ 2 2
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
      (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
      (linearizedRicciConnectionDifferenceOrder0KernelField (I := I) g₀ g₁))] at hsquare
  have houtJet : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
          (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
          (linearizedRicciConnectionDifferenceOrder0KernelField (I := I) g₀ g₁))‖ ^ 2) ≤
      (Capp * (2 * Bt R) * (Bk0 R + Bk1 R * A)) ^ 2 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hsquare
  have hfactor :
      Capp * (2 * Bt R) * (Bk0 R + Bk1 R * A) =
        B0 R + B1 R * A := by
    simp only [B0, B1]
    ring
  rw [← hfactor]
  exact houtJet

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
