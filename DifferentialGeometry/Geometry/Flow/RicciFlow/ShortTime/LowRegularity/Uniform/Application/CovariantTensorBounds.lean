import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Order.First
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Sobolev.Morrey
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Application.CovariantDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Application.MixedTensorFirstSecondOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Grid.ConvexJets
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.ApplicationJetWindow

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem operatorFieldApplication_h1_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (Φ : SmoothCcTensor g 2 2) (U : SmoothCcTensor g 0 2) (A : ℝ),
          0 ≤ A →
          (∑ j ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g 2 2 j Φ‖ ^ 2) ≤ A ^ 2 →
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (operatorFieldApply (I := I) (M := M) g 2 2 Φ U)‖ ≤
            C * A *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  classical
  obtain ⟨K, hK⟩ := exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  obtain ⟨Crs, hCrs, happ⟩ :=
    operatorFieldComposition_h1_uniform_bound (I := I) (M := M) hDim gBase hΛ 0 2 2
  let Ch : ℝ := h2CovsumC K.rankTwo
  let C : ℝ := Crs * Ch
  have hCh : 0 ≤ Ch := by
    dsimp [Ch]
    exact h2CovsumC_nonneg K.rankTwo
  refine ⟨C, by
    dsimp [C]
    positivity, ?_⟩
  intro g hEq hjet Φ U A hA hΦjet
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  obtain ⟨hact₂, _hact₃⟩ := hK.bounds g hEq hjet
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 Φ U
  have hN : 0 ≤ N := norm_nonneg _
  have hJ :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ ≤ Ch * N := by
    simpa only [Ch, N] using
      (covsum_hs_two (I := I) (M := M) g 2 hact₂ U)
  have hUjet :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j U‖ ^ 2) ≤
          (Ch * N) ^ 2 := by
    exact (Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => norm_nonneg
        (iteratedCovGrad (I := I) g 0 2 j U))).trans
      (pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j U))) hJ 2)
  have hmix := happ g hEq hjet1 hjet2 Φ U A (Ch * N)
    hA (mul_nonneg hCh hN) hΦjet hUjet
  have hmix' :
      ‖(⟨Y⟩ : SmoothCcTensorH1 g 0 2)‖ ≤ Crs * A * (Ch * N) := by
    simpa only [Y, operatorFieldComposition_zero_eq_operatorFieldApply] using hmix
  have hspec :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y‖ =
        ‖(⟨Y⟩ : SmoothCcTensorH1 g 0 2)‖ := by
    have hspectral := cc_h1_jet_sq (I := I) (M := M) g Y
    have hintrinsic := smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g 0 2 Y
    nlinarith [
      norm_nonneg (ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y),
      norm_nonneg (⟨Y⟩ : SmoothCcTensorH1 g 0 2)]
  change ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y‖ ≤ _
  calc
    _ = ‖(⟨Y⟩ : SmoothCcTensorH1 g 0 2)‖ := hspec
    _ ≤ Crs * A * (Ch * N) := hmix'
    _ = C * A * N := by dsimp [C]; ring

theorem operatorFieldApplication_h2cov_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (Φ : SmoothCcTensor g 3 2) (U : SmoothCcTensor g 0 2) (A : ℝ),
          0 ≤ A →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 3 2 j Φ‖ ^ 2) ≤ A ^ 2 →
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (operatorFieldApply (I := I) (M := M) g 3 2 Φ
                (covGrad (I := I) (M := M) g 0 2 U))‖ ≤
            C * A *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  classical
  obtain ⟨K, hK⟩ := exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  obtain ⟨Cm, hCm, hmor⟩ :=
    DifferentialGeometry.PDE.RicciFlow.morreyRS_uniform
      (I := I) (M := M) hDim gBase hΛ 3 2
  obtain ⟨Cg, hCg, hgrad⟩ :=
    operatorFieldApplication_grad_uniform (I := I) (M := M) hDim gBase hΛ 1 2
  let Ch : ℝ := h2CovsumC K.rankTwo
  let sd : ℝ := Real.sqrt 3
  let C : ℝ := Cm * Ch + Cg * Ch + sd * Cm * Ch
  have hCh : 0 ≤ Ch := by
    dsimp [Ch]
    exact h2CovsumC_nonneg K.rankTwo
  refine ⟨C, by
    dsimp [C, sd]
    positivity, ?_⟩
  intro g hEq hjet Φ U A hA hΦjet
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  obtain ⟨hact₂, _hact₃⟩ := hK.bounds g hEq hjet
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖
  let W : SmoothCcTensor g 0 3 :=
    covGrad (I := I) (M := M) g 0 2 U
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 3 2 Φ W
  have hN : 0 ≤ N := norm_nonneg _
  have hJ :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ ≤ Ch * N := by
    simpa only [Ch, N] using
      (covsum_hs_two (I := I) (M := M) g 2 hact₂ U)
  have hUjet :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j U‖ ^ 2) ≤
          (Ch * N) ^ 2 := by
    exact (Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => norm_nonneg
        (iteratedCovGrad (I := I) g 0 2 j U))).trans
      (pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j U))) hJ 2)
  have hW0 : ‖W‖ ≤ Ch * N := by
    have hpick : ‖iteratedCovGrad (I := I) g 0 2 1 U‖ ≤ Ch * N :=
      (Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g 0 2 j U‖)
        (fun j _ => norm_nonneg _) (by norm_num)).trans hJ
    simpa only [W, iteratedCovGrad_succ, iteratedCovGrad_zero,
      Nat.zero_add] using hpick
  have hW1 :
      ‖covGrad (I := I) (M := M) g 0 3 W‖ ≤ Ch * N := by
    have hpick : ‖iteratedCovGrad (I := I) g 0 2 2 U‖ ≤ Ch * N :=
      (Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g 0 2 j U‖)
        (fun j _ => norm_nonneg _) (by norm_num)).trans hJ
    calc
      ‖covGrad (I := I) (M := M) g 0 3 W‖ =
          ‖iteratedCovGrad (I := I) g 0 (2 + 1) 1
            (iteratedCovGrad (I := I) g 0 2 1 U)‖ := by
              simp only [W, iteratedCovGrad_succ,
                iteratedCovGrad_zero, Nat.add_zero]
      _ = ‖iteratedCovGrad (I := I) g 0 2 (1 + 1) U‖ :=
        iteratedCovGrad_comp_norm (I := I) (M := M) g 2 1 1 U
      _ ≤ Ch * N := by norm_num at hpick ⊢; exact hpick
  have hΦsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 3 2 x
          (Φ.toSection x) ≤ (Cm * A) ^ 2 := by
    intro x
    calc
      riemannianFiberNormSq (I := I) (M := M) g 3 2 x
          (Φ.toSection x) ≤
          Cm ^ 2 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 3 2 j Φ‖ ^ 2 :=
        hmor g hEq hjet1 hjet2 Φ x
      _ ≤ Cm ^ 2 * A ^ 2 :=
        mul_le_mul_of_nonneg_left hΦjet (sq_nonneg Cm)
      _ = (Cm * A) ^ 2 := by ring
  have hY0 : ‖Y‖ ≤ Cm * Ch * A * N := by
    have h0 := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g 3 2 Φ W (Cm * A)
      (mul_nonneg hCm hA) hΦsup
    dsimp [Y]
    calc
      ‖operatorFieldApply (I := I) (M := M) g 3 2 Φ W‖ ≤
          (Cm * A) * ‖W‖ := h0
      _ ≤ (Cm * A) * (Ch * N) :=
        mul_le_mul_of_nonneg_left hW0 (mul_nonneg hCm hA)
      _ = Cm * Ch * A * N := by ring
  have hcross :
      ‖operatorFieldApply (I := I) (M := M) g 3 3
          (covGrad (I := I) (M := M) g 3 2 Φ) W‖ ≤
        Cg * Ch * A * N := by
    have hc := hgrad g hEq hjet1 hjet2 Φ U A (Ch * N)
      hA (mul_nonneg hCh hN) hΦjet hUjet
    simpa only [W] using (hc.trans_eq (by ring))
  have hslotSup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 3 x
          ((slotExtend (I := I) (M := M) g 3 2 Φ).toSection x) ≤
        (sd * (Cm * A)) ^ 2 := by
    intro x
    change riemannianFiberNormSq (I := I) (M := M) g (3 + 1) (2 + 1) x
        ((slotExtend (I := I) (M := M) g 3 2 Φ).toSection x) ≤ _
    rw [riemannianFiberNormSq_slotExtend_eq (I := I) (M := M) g 3 2 Φ x]
    rw [hDim]
    calc
      (3 : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g 3 2 x
            (Φ.toSection x) ≤
          (3 : ℝ) * (Cm * A) ^ 2 :=
        mul_le_mul_of_nonneg_left (hΦsup x) (by norm_num)
      _ = (sd * (Cm * A)) ^ 2 := by
        dsimp only [sd]
        simp only [mul_pow]
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hslot :
      ‖operatorFieldApply (I := I) (M := M) g 4 3
          (slotExtend (I := I) (M := M) g 3 2 Φ)
          (covGrad (I := I) (M := M) g 0 3 W)‖ ≤
        sd * Cm * Ch * A * N := by
    have hs := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g 4 3
      (slotExtend (I := I) (M := M) g 3 2 Φ)
      (covGrad (I := I) (M := M) g 0 3 W)
      (sd * (Cm * A))
      (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCm hA)) hslotSup
    calc
      _ ≤ (sd * (Cm * A)) *
          ‖covGrad (I := I) (M := M) g 0 3 W‖ := hs
      _ ≤ (sd * (Cm * A)) * (Ch * N) :=
        mul_le_mul_of_nonneg_left hW1
          (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCm hA))
      _ = sd * Cm * Ch * A * N := by ring
  have hY1 :
      ‖covGrad (I := I) (M := M) g 0 2 Y‖ ≤
        (Cg * Ch + sd * Cm * Ch) * A * N := by
    rw [show covGrad (I := I) (M := M) g 0 2 Y =
        operatorFieldApply (I := I) (M := M) g 3 3
            (covGrad (I := I) (M := M) g 3 2 Φ) W +
          operatorFieldApply (I := I) (M := M) g 4 3
            (slotExtend (I := I) (M := M) g 3 2 Φ)
            (covGrad (I := I) (M := M) g 0 3 W) by
      dsimp [Y]
      exact covGrad_operatorFieldApplication_eq (I := I) (M := M) g 3 2 Φ W]
    calc
      _ ≤ ‖operatorFieldApply (I := I) (M := M) g 3 3
              (covGrad (I := I) (M := M) g 3 2 Φ) W‖ +
            ‖operatorFieldApply (I := I) (M := M) g 4 3
              (slotExtend (I := I) (M := M) g 3 2 Φ)
              (covGrad (I := I) (M := M) g 0 3 W)‖ := norm_add_le _ _
      _ ≤ Cg * Ch * A * N + sd * Cm * Ch * A * N :=
        add_le_add hcross hslot
      _ = (Cg * Ch + sd * Cm * Ch) * A * N := by ring
  have hspec :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y‖ ≤
        ‖Y‖ + ‖covGrad (I := I) (M := M) g 0 2 Y‖ := by
    have hsq := cc_h1_jet_sq (I := I) (M := M) g Y
    have hprod : 0 ≤ ‖Y‖ *
        ‖covGrad (I := I) (M := M) g 0 2 Y‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [norm_nonneg Y,
      norm_nonneg (covGrad (I := I) (M := M) g 0 2 Y),
      norm_nonneg (ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y)]
  change ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y‖ ≤ _
  calc
    _ ≤ ‖Y‖ + ‖covGrad (I := I) (M := M) g 0 2 Y‖ := hspec
    _ ≤ Cm * Ch * A * N +
          (Cg * Ch + sd * Cm * Ch) * A * N := add_le_add hY0 hY1
    _ = C * A * N := by dsimp [C]; ring

theorem operatorFieldApplication_h23_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (Φ : SmoothCcTensor g 4 2) (U : SmoothCcTensor g 0 2) (A : ℝ),
          0 ≤ A →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 4 2 j Φ‖ ^ 2) ≤ A ^ 2 →
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (operatorFieldApply (I := I) (M := M) g 4 2 Φ
                (iteratedCovGrad (I := I) g 0 2 2 U))‖ ≤
            C * A *
              ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
  classical
  obtain ⟨K, hK⟩ := exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  obtain ⟨Cm, hCm, hmor⟩ :=
    DifferentialGeometry.PDE.RicciFlow.morreyRS_uniform
      (I := I) (M := M) hDim gBase hΛ 4 2
  obtain ⟨Cg, hCg, hgrad⟩ :=
    operatorFieldApplication_grad_uniform (I := I) (M := M) hDim gBase hΛ 2 2
  let Ch : ℝ := h3CovsumC K.rankTwo K.rankThree
  let sd : ℝ := Real.sqrt 3
  let C : ℝ := Cm * Ch + Cg * Ch + sd * Cm * Ch
  have hCh : 0 ≤ Ch := by
    dsimp [Ch]
    exact h3CovsumC_nonneg K.rankTwo K.rankThree
  refine ⟨C, by
    dsimp [C, sd]
    positivity, ?_⟩
  intro g hEq hjet Φ U A hA hΦjet
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  obtain ⟨hact₂, hact₃⟩ := hK.bounds g hEq hjet
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖
  let V : SmoothCcTensor g 0 3 :=
    covGrad (I := I) (M := M) g 0 2 U
  let W : SmoothCcTensor g 0 4 :=
    iteratedCovGrad (I := I) g 0 2 2 U
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 Φ W
  have hN : 0 ≤ N := norm_nonneg _
  have hJ :
      ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ ≤ Ch * N := by
    simpa only [Ch, N] using
      (covsum_hs_three (I := I) (M := M) g 2 hact₂ hact₃ U)
  have hUjet :
      (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 0 2 j U‖ ^ 2) ≤
          (Ch * N) ^ 2 := by
    exact (Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => norm_nonneg
        (iteratedCovGrad (I := I) g 0 2 j U))).trans
      (pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j U))) hJ 2)
  have hV0 :
      ‖iteratedCovGrad (I := I) g 0 3 0 V‖ =
        ‖iteratedCovGrad (I := I) g 0 2 1 U‖ := by
    with_unfolding_all
      exact iteratedCovGrad_comp_norm (I := I) (M := M) g 2 1 0 U
  have hV1 :
      ‖iteratedCovGrad (I := I) g 0 3 1 V‖ =
        ‖iteratedCovGrad (I := I) g 0 2 2 U‖ := by
    with_unfolding_all
      exact iteratedCovGrad_comp_norm (I := I) (M := M) g 2 1 1 U
  have hV2 :
      ‖iteratedCovGrad (I := I) g 0 3 2 V‖ =
        ‖iteratedCovGrad (I := I) g 0 2 3 U‖ := by
    with_unfolding_all
      exact iteratedCovGrad_comp_norm (I := I) (M := M) g 2 1 2 U
  have hVjet :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 3 j V‖ ^ 2) ≤
          (Ch * N) ^ 2 := by
    apply le_trans _ hUjet
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hV0, hV1, hV2]
    nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g 0 2 0 U‖]
  have hW0 : ‖W‖ ≤ Ch * N := by
    have hpick : ‖iteratedCovGrad (I := I) g 0 2 2 U‖ ≤ Ch * N :=
      (Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g 0 2 j U‖)
        (fun j _ => norm_nonneg _) (by norm_num)).trans hJ
    simpa only [W] using hpick
  have hW1 :
      ‖covGrad (I := I) (M := M) g 0 4 W‖ ≤ Ch * N := by
    have hpick : ‖iteratedCovGrad (I := I) g 0 2 3 U‖ ≤ Ch * N :=
      (Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g 0 2 j U‖)
        (fun j _ => norm_nonneg _) (by norm_num)).trans hJ
    calc
      ‖covGrad (I := I) (M := M) g 0 4 W‖ =
          ‖iteratedCovGrad (I := I) g 0 (2 + 2) 1
            (iteratedCovGrad (I := I) g 0 2 2 U)‖ := by
              simp only [W, iteratedCovGrad_succ,
                iteratedCovGrad_zero, Nat.add_zero]
      _ = ‖iteratedCovGrad (I := I) g 0 2 (2 + 1) U‖ :=
        iteratedCovGrad_comp_norm (I := I) (M := M) g 2 2 1 U
      _ ≤ Ch * N := by norm_num at hpick ⊢; exact hpick
  have hΦsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (Φ.toSection x) ≤ (Cm * A) ^ 2 := by
    intro x
    calc
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (Φ.toSection x) ≤
          Cm ^ 2 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 4 2 j Φ‖ ^ 2 :=
        hmor g hEq hjet1 hjet2 Φ x
      _ ≤ Cm ^ 2 * A ^ 2 :=
        mul_le_mul_of_nonneg_left hΦjet (sq_nonneg Cm)
      _ = (Cm * A) ^ 2 := by ring
  have hY0 : ‖Y‖ ≤ Cm * Ch * A * N := by
    have h0 := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g 4 2 Φ W (Cm * A)
      (mul_nonneg hCm hA) hΦsup
    dsimp [Y]
    calc
      ‖operatorFieldApply (I := I) (M := M) g 4 2 Φ W‖ ≤
          (Cm * A) * ‖W‖ := h0
      _ ≤ (Cm * A) * (Ch * N) :=
        mul_le_mul_of_nonneg_left hW0 (mul_nonneg hCm hA)
      _ = Cm * Ch * A * N := by ring
  have hcross :
      ‖operatorFieldApply (I := I) (M := M) g 4 3
          (covGrad (I := I) (M := M) g 4 2 Φ) W‖ ≤
        Cg * Ch * A * N := by
    have hc := hgrad g hEq hjet1 hjet2 Φ V A (Ch * N)
      hA (mul_nonneg hCh hN) hΦjet hVjet
    calc
      ‖operatorFieldApply (I := I) (M := M) g 4 3
          (covGrad (I := I) (M := M) g 4 2 Φ) W‖ =
          ‖operatorFieldApply (I := I) (M := M) g 4 3
            (covGrad (I := I) (M := M) g 4 2 Φ)
            (covGrad (I := I) (M := M) g 0 3 V)‖ := by
              simp only [V, W, iteratedCovGrad_succ,
                iteratedCovGrad_zero, Nat.add_zero]
      _ ≤ Cg * A * (Ch * N) := hc
      _ = Cg * Ch * A * N := by ring
  have hslotSup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 5 3 x
          ((slotExtend (I := I) (M := M) g 4 2 Φ).toSection x) ≤
        (sd * (Cm * A)) ^ 2 := by
    intro x
    change riemannianFiberNormSq (I := I) (M := M) g (4 + 1) (2 + 1) x
        ((slotExtend (I := I) (M := M) g 4 2 Φ).toSection x) ≤ _
    rw [riemannianFiberNormSq_slotExtend_eq (I := I) (M := M) g 4 2 Φ x]
    rw [hDim]
    calc
      (3 : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            (Φ.toSection x) ≤
          (3 : ℝ) * (Cm * A) ^ 2 :=
        mul_le_mul_of_nonneg_left (hΦsup x) (by norm_num)
      _ = (sd * (Cm * A)) ^ 2 := by
        dsimp only [sd]
        simp only [mul_pow]
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hslot :
      ‖operatorFieldApply (I := I) (M := M) g 5 3
          (slotExtend (I := I) (M := M) g 4 2 Φ)
          (covGrad (I := I) (M := M) g 0 4 W)‖ ≤
        sd * Cm * Ch * A * N := by
    have hs := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g 5 3
      (slotExtend (I := I) (M := M) g 4 2 Φ)
      (covGrad (I := I) (M := M) g 0 4 W)
      (sd * (Cm * A))
      (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCm hA)) hslotSup
    calc
      _ ≤ (sd * (Cm * A)) *
          ‖covGrad (I := I) (M := M) g 0 4 W‖ := hs
      _ ≤ (sd * (Cm * A)) * (Ch * N) :=
        mul_le_mul_of_nonneg_left hW1
          (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCm hA))
      _ = sd * Cm * Ch * A * N := by ring
  have hY1 :
      ‖covGrad (I := I) (M := M) g 0 2 Y‖ ≤
        (Cg * Ch + sd * Cm * Ch) * A * N := by
    rw [show covGrad (I := I) (M := M) g 0 2 Y =
        operatorFieldApply (I := I) (M := M) g 4 3
            (covGrad (I := I) (M := M) g 4 2 Φ) W +
          operatorFieldApply (I := I) (M := M) g 5 3
            (slotExtend (I := I) (M := M) g 4 2 Φ)
            (covGrad (I := I) (M := M) g 0 4 W) by
      dsimp [Y]
      exact covGrad_operatorFieldApplication_eq (I := I) (M := M) g 4 2 Φ W]
    calc
      _ ≤ ‖operatorFieldApply (I := I) (M := M) g 4 3
              (covGrad (I := I) (M := M) g 4 2 Φ) W‖ +
            ‖operatorFieldApply (I := I) (M := M) g 5 3
              (slotExtend (I := I) (M := M) g 4 2 Φ)
              (covGrad (I := I) (M := M) g 0 4 W)‖ := norm_add_le _ _
      _ ≤ Cg * Ch * A * N + sd * Cm * Ch * A * N :=
        add_le_add hcross hslot
      _ = (Cg * Ch + sd * Cm * Ch) * A * N := by ring
  have hspec :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y‖ ≤
        ‖Y‖ + ‖covGrad (I := I) (M := M) g 0 2 Y‖ := by
    have hsq := cc_h1_jet_sq (I := I) (M := M) g Y
    have hprod : 0 ≤ ‖Y‖ *
        ‖covGrad (I := I) (M := M) g 0 2 Y‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [norm_nonneg Y,
      norm_nonneg (covGrad (I := I) (M := M) g 0 2 Y),
      norm_nonneg (ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y)]
  change ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y‖ ≤ _
  calc
    _ ≤ ‖Y‖ + ‖covGrad (I := I) (M := M) g 0 2 Y‖ := hspec
    _ ≤ Cm * Ch * A * N +
          (Cg * Ch + sd * Cm * Ch) * A * N := add_le_add hY0 hY1
    _ = C * A * N := by dsimp [C]; ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
