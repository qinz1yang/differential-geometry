import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.ResidualBase
import DifferentialGeometry.Analysis.Estimates.ProductBounds


noncomputable section

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators


namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorBilinSymm_apply
    ccTensorBilinSymm_symm)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [T2Space M] in
private theorem ccTensorBilinSymm_symmS_app_rf
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀ (symmS (I := I) (M := M) g₀ T) x v w =
      ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [ccTensorBilinSymm_apply, ccTensorBilin_symmS, ccTensorBilin_symmS,
    ccTensorBilinSymm_symm (I := I) g₀ T x w v, ccTensorBilinSymm_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [T2Space M] in
private theorem gFibreOpBound_symmS_rf
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (symmS (I := I) (M := M) g₀ T)) δ := by
  intro x v w
  rw [ccTensorBilinSymm_symmS_app_rf (I := I) (M := M) g₀ T x v w]
  exact hδ x v w

private lemma sum_shift_le_rf (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) (m c : ℕ) :
    ∑ i ∈ Finset.range m, g (i + c) ≤ ∑ j ∈ Finset.range (m + c), g j := by
  classical
  have hsub :
      (Finset.range m).map (addRightEmbedding c) ⊆
        Finset.range (m + c) := by
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_range] at hi ⊢
    rw [addRightEmbedding_apply]
    omega
  calc ∑ i ∈ Finset.range m, g (i + c)
      = ∑ j ∈ (Finset.range m).map (addRightEmbedding c), g j := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ j ∈ Finset.range (m + c), g j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hg j)

theorem ricciArmOrder0BaseCoeff_perOrder_l2_radiusFree
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Atop : ℕ → ℝ, (∀ i, 0 ≤ Atop i) ∧ ∃ Alow : ℕ → ℝ, (∀ i, 0 ≤ Alow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((symmS (I := I) (M := M) g₀ T).toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
          Atop i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
              (symmS (I := I) (M := M) g₀ T)‖ ^ 2 +
          Alow i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) := by
  classical
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨KtCr, hKtCr_nn, KcCr, hKcCr_nn, hCr⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_topOrderSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtCu, hKtCu_nn, KcCu, hKcCu_nn, hCu⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0CurvCoeff_backgroundDifference_topOrderSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Klg, hKlg_nn, Ktg, hKtg_nn, hgate⟩ :=
    boundedFactorGridWindow_integral_radiusFree_topOrderSeparated (I := I) (M := M) g₀ hΛ₀0
  refine ⟨fun i => 5 * KcCr i * Ktg i + 5 * KtCr + 5 * KcCu i * Ktg i + 5 * KtCu,
    fun i => by have := hKcCr_nn i; have := hKcCu_nn i; have := hKtg_nn i; positivity, ?_⟩
  refine ⟨fun i => 5 * KcCr i * Klg i + 5 * KcCu i * Klg i +
      5 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2,
    fun i => by have := hKcCr_nn i; have := hKcCu_nn i; have := hKlg_nn i; positivity, ?_⟩
  intro g₁ T δ hδ_le hδ0 hδ htie hsup i
  have htie_s : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ (symmS (I := I) (M := M) g₀ T) y v w := by
    intro y v w
    rw [ccTensorBilinSymm_symmS_app_rf (I := I) (M := M) g₀ T y v w]
    exact htie y v w
  have hbound_s : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (symmS (I := I) (M := M) g₀ T)) δ :=
    gFibreOpBound_symmS_rf (I := I) (M := M) g₀ T hδ
  obtain ⟨HdCr, hCr_head, hCr_res⟩ :=
    hCr g₁ (symmS (I := I) (M := M) g₀ T) htie_s hδ_le hδ0 hbound_s i
  obtain ⟨HdCu, hCu_head, hCu_res⟩ :=
    hCu g₁ (symmS (I := I) (M := M) g₀ T) htie_s hδ_le hδ0 hbound_s i
  obtain ⟨hgate_int, hgate_bd⟩ := hgate (symmS (I := I) (M := M) g₀ T) hsup i
  set W : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
    (symmS (I := I) (M := M) g₀ T)‖ ^ 2 with hW
  set low : ℝ := ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2 with hlow
  set RieDiff : SmoothCcTensor g₀ 2 (2 + i) := iteratedCovGrad (I := I) g₀ 2 2 i
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) with hRieDiff
  set CuDiff : SmoothCcTensor g₀ 2 (2 + i) := iteratedCovGrad (I := I) g₀ 2 2 i
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) with hCuDiff
  have hlow_nn : 0 ≤ low := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hC5 : iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) =
      iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
        (RieDiff - HdCr) + HdCr - (CuDiff - HdCu) - HdCu := by
    rw [hRieDiff, hCuDiff]
    have hsum : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ =
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) := by abel
    rw [hsum, iteratedCovGrad_sub, iteratedCovGrad_add]
    abel
  have hnorm : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ +
        ‖RieDiff - HdCr‖ + ‖HdCr‖ + ‖CuDiff - HdCu‖ + ‖HdCu‖ := by
    rw [hC5]
    exact le_trans (norm_sub_le _ _) (add_le_add (le_trans (norm_sub_le _ _)
      (add_le_add (le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)) le_rfl))
      le_rfl)
  have key5 : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
      5 * (‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 +
          ‖RieDiff - HdCr‖ ^ 2 + ‖HdCr‖ ^ 2 + ‖CuDiff - HdCu‖ ^ 2 + ‖HdCu‖ ^ 2) := by
    refine le_trans ?_ (DifferentialGeometry.Analysis.sq_sum_five_le _ _ _ _ _)
    simp only [pow_two]
    exact mul_self_le_mul_self (norm_nonneg _) hnorm
  have hheadL2 : ∀ (Hd : SmoothCcTensor g₀ 2 (2 + i)) (Kt : ℝ),
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
        Kt * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
            (symmS (I := I) (M := M) g₀ T)).toSection x)) →
      ‖Hd‖ ^ 2 ≤ Kt * W := by
    intro Hd Kt hhead
    have hFint : MeasureTheory.Integrable
        (fun x => Kt * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
            (symmS (I := I) (M := M) g₀ T)).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 2))
        (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) (symmS (I := I) (M := M) g₀ T))).const_mul _
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
      g₀ 2 (2 + i) Hd _ hFint hhead
    rw [MeasureTheory.integral_const_mul] at key
    rw [show (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
            (symmS (I := I) (M := M) g₀ T)).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) = W from by
      rw [hW, SmoothCcTensor.norm_def (I := I) (M := M)
          (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) (symmS (I := I) (M := M) g₀ T)),
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
          g₀ 0 (2 + (i + 2))
          (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) (symmS (I := I) (M := M) g₀ T))]] at key
    exact key
  have hHcr : ‖HdCr‖ ^ 2 ≤ KtCr * W := hheadL2 HdCr KtCr hCr_head
  have hHcu : ‖HdCu‖ ^ 2 ≤ KtCu * W := hheadL2 HdCu KtCu hCu_head
  have hresL2 : ∀ (D : SmoothCcTensor g₀ 2 (2 + i)) (Kc : ℝ), 0 ≤ Kc →
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (D.toSection x) ≤
        Kc * Combinatorics.boundedFactorGridWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l
              (symmS (I := I) (M := M) g₀ T)).toSection x)) (i + 1) (i + 3)) →
      ‖D‖ ^ 2 ≤ Kc * Klg i * (1 + low) + Kc * Ktg i * W := by
    intro D Kc hKc_nn hres
    have hFint : MeasureTheory.Integrable
        (fun x => Kc * Combinatorics.boundedFactorGridWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l
              (symmS (I := I) (M := M) g₀ T)).toSection x)) (i + 1) (i + 3))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgate_int.const_mul _
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
      g₀ 2 (2 + i) D _ hFint hres
    rw [MeasureTheory.integral_const_mul] at key
    refine le_trans key ?_
    refine le_trans (mul_le_mul_of_nonneg_left hgate_bd hKc_nn) (le_of_eq ?_)
    ring
  have hRcr : ‖RieDiff - HdCr‖ ^ 2 ≤ KcCr i * Klg i * (1 + low) + KcCr i * Ktg i * W :=
    hresL2 (RieDiff - HdCr) (KcCr i) (hKcCr_nn i) hCr_res
  have hRcu : ‖CuDiff - HdCu‖ ^ 2 ≤ KcCu i * Klg i * (1 + low) + KcCu i * Ktg i * W :=
    hresL2 (CuDiff - HdCu) (KcCu i) (hKcCu_nn i) hCu_res
  set B : ℝ := ‖iteratedCovGrad (I := I) g₀ 2 2 i
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 with hB
  have hB_nn : 0 ≤ B := sq_nonneg _
  refine le_trans key5 ?_
  have hstep : 5 * (B + ‖RieDiff - HdCr‖ ^ 2 + ‖HdCr‖ ^ 2 + ‖CuDiff - HdCu‖ ^ 2 + ‖HdCu‖ ^ 2) ≤
      5 * (B + (KcCr i * Klg i * (1 + low) + KcCr i * Ktg i * W) + KtCr * W +
        (KcCu i * Klg i * (1 + low) + KcCu i * Ktg i * W) + KtCu * W) := by
    have h5 : (0 : ℝ) ≤ 5 := by norm_num
    apply mul_le_mul_of_nonneg_left _ h5
    linarith [hRcr, hHcr, hRcu, hHcu]
  refine le_trans hstep ?_
  have hslack : (0 : ℝ) ≤ 5 * B * low :=
    mul_nonneg (mul_nonneg (by norm_num) hB_nn) hlow_nn
  have hbal : (5 * KcCr i * Ktg i + 5 * KtCr + 5 * KcCu i * Ktg i + 5 * KtCu) * W +
        (5 * KcCr i * Klg i + 5 * KcCu i * Klg i + 5 * B) * (1 + low) -
      5 * (B + (KcCr i * Klg i * (1 + low) + KcCr i * Ktg i * W) + KtCr * W +
        (KcCu i * Klg i * (1 + low) + KcCu i * Ktg i * W) + KtCu * W) = 5 * B * low := by
    ring
  linarith [hbal, hslack]

theorem ricciArmOrder0BaseCoeff_summed_l2_radiusFree
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Klow : ℝ, 0 ≤ Klow ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w),
        ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
          Ktop * (∑ j ∈ Finset.range (a + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) +
          Klow * (1 + ∑ j ∈ Finset.range (a + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) := by
  classical
  obtain ⟨Atop, hAtop_nn, Alow, hAlow_nn, hper⟩ :=
    ricciArmOrder0BaseCoeff_perOrder_l2_radiusFree (I := I) (M := M) g₀ hδ₀
      (Λ₀ := max 0 ((Module.finrank ℝ E : ℝ) * δ₀)) (le_max_left _ _)
  refine ⟨∑ i ∈ Finset.range (a + 1), Atop i,
    Finset.sum_nonneg (fun i _ => hAtop_nn i), ?_⟩
  refine ⟨∑ i ∈ Finset.range (a + 1), Alow i,
    Finset.sum_nonneg (fun i _ => hAlow_nn i), ?_⟩
  intro g₁ T δ hδ_le hδ htie
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        have : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ T x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hδ₀0 : 0 ≤ δ₀ := le_trans hδ0 hδ_le
    have hmaxeq : max 0 ((Module.finrank ℝ E : ℝ) * δ₀) = (Module.finrank ℝ E : ℝ) * δ₀ :=
      max_eq_right (mul_nonneg (Nat.cast_nonneg _) hδ₀0)
    have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((symmS (I := I) (M := M) g₀ T).toSection x) ≤
        (max 0 ((Module.finrank ℝ E : ℝ) * δ₀)) ^ 2 := by
      intro x
      rw [hmaxeq]
      exact riemannianFiberNormSq_symmS_zero_le_fibreSmall (I := I) (M := M) g₀ hδ₀0 T hδ_le hδ0 hδ x
    have hper' : ∀ i, i ≤ a →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
          Atop i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
              (symmS (I := I) (M := M) g₀ T)‖ ^ 2 +
          Alow i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) :=
      fun i _ => hper g₁ T hδ_le hδ0 hδ htie hsup i
    set w : ℕ → ℝ := fun j =>
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2 with hw
    have hw_nn : ∀ j, 0 ≤ w j := fun j => sq_nonneg _
    have hAtop_sum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 1), Atop i :=
      Finset.sum_nonneg (fun i _ => hAtop_nn i)
    have hAlow_sum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 1), Alow i :=
      Finset.sum_nonneg (fun i _ => hAlow_nn i)
    calc ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2
        ≤ ∑ i ∈ Finset.range (a + 1),
            (Atop i * w (i + 2) + Alow i * (1 + ∑ j ∈ Finset.range (i + 2), w j)) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact hper' i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      _ = (∑ i ∈ Finset.range (a + 1), Atop i * w (i + 2)) +
            ∑ i ∈ Finset.range (a + 1), Alow i * (1 + ∑ j ∈ Finset.range (i + 2), w j) := by
          rw [Finset.sum_add_distrib]
      _ ≤ (∑ i ∈ Finset.range (a + 1), Atop i) * (∑ j ∈ Finset.range (a + 3), w j) +
            (∑ i ∈ Finset.range (a + 1), Alow i) * (1 + ∑ j ∈ Finset.range (a + 2), w j) := by
          refine add_le_add ?_ ?_
          · calc ∑ i ∈ Finset.range (a + 1), Atop i * w (i + 2)
                ≤ ∑ i ∈ Finset.range (a + 1), Atop i * (∑ j ∈ Finset.range (a + 3), w j) := by
                  refine Finset.sum_le_sum (fun i hi => ?_)
                  have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
                  refine mul_le_mul_of_nonneg_left ?_ (hAtop_nn i)
                  exact Finset.single_le_sum (f := fun j => w j) (fun j _ => hw_nn j)
                    (Finset.mem_range.mpr (by omega))
              _ = (∑ i ∈ Finset.range (a + 1), Atop i) * (∑ j ∈ Finset.range (a + 3), w j) := by
                  rw [Finset.sum_mul]
          · calc ∑ i ∈ Finset.range (a + 1), Alow i * (1 + ∑ j ∈ Finset.range (i + 2), w j)
                ≤ ∑ i ∈ Finset.range (a + 1),
                    Alow i * (1 + ∑ j ∈ Finset.range (a + 2), w j) := by
                  refine Finset.sum_le_sum (fun i hi => ?_)
                  have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
                  refine mul_le_mul_of_nonneg_left ?_ (hAlow_nn i)
                  have hsub : Finset.range (i + 2) ⊆ Finset.range (a + 2) := by
                    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
                  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw_nn j)
                  linarith
              _ = (∑ i ∈ Finset.range (a + 1), Alow i) *
                    (1 + ∑ j ∈ Finset.range (a + 2), w j) := by
                  rw [Finset.sum_mul]
  · have hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hL0 : ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]; ring
    rw [hL0]
    have h1 : 0 ≤ (∑ i ∈ Finset.range (a + 1), Atop i) *
        (∑ j ∈ Finset.range (a + 3),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) :=
      mul_nonneg (Finset.sum_nonneg (fun i _ => hAtop_nn i))
        (Finset.sum_nonneg (fun j _ => sq_nonneg _))
    have h2 : 0 ≤ (∑ i ∈ Finset.range (a + 1), Alow i) *
        (1 + ∑ j ∈ Finset.range (a + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2) := by
      refine mul_nonneg (Finset.sum_nonneg (fun i _ => hAlow_nn i)) ?_
      have : 0 ≤ ∑ j ∈ Finset.range (a + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ^ 2 :=
        Finset.sum_nonneg (fun j _ => sq_nonneg _)
      linarith
    linarith

end Connection
end Integral
end DifferentialGeometry
