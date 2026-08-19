import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.TopOrderSeparatedCurvatureBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.ResidualFree
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Residual

open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Geometry.Operator

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel
    ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

namespace CurvatureCoefficientDifferenceJetTower
end CurvatureCoefficientDifferenceJetTower

open CurvatureCoefficientDifferenceJetTower

section TopOrderSeparatedResidualIntegrator


set_option backward.isDefEq.respectTransparency false

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_symmS_zero_le_fibreSmall
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((symmS (I := I) (M := M) g₀ T).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * δ₀) ^ 2 := by
  have h := riemannianFiberNormSq_symmS_zero_le_of_ball (I := I) (M := M) g₀ T hδ0 hbound x
  rw [mul_pow]
  refine le_trans h ?_
  have hδsq : δ ^ 2 ≤ δ₀ ^ 2 := by nlinarith [hδ0, hδ_le, hδ₀0]
  exact mul_le_mul_of_nonneg_left hδsq (by positivity)

theorem ricciArmOrder0BaseCoeff_perOrder_l2_topOrderSeparated_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
                Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) ∧
            ‖Hd‖ ^ 2 ≤ Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 ∧
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - Hd‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨KtCr, hKtCr_nn, KcCr, hKcCr_nn, hCr⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_topOrderSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtCu, hKtCu_nn, KcCu, hKcCu_nn, hCu⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0CurvCoeff_backgroundDifference_topOrderSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_backgroundJet_riemannianFiberNormSq_bound (I := I) (M := M) g₀ 2 2
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
  obtain ⟨KI, hKI_nn, hKI⟩ := boundedFactorGridWindow_integral_ballUniform_tameWindow
    (I := I) (M := M) g₀ a ha_super hR
  refine ⟨2 * KtCr + 2 * KtCu, by linarith, ?_⟩
  refine ⟨fun i => (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i,
    fun i => mul_nonneg
      (by have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith)
      (hKI_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hia
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    obtain ⟨HdCr, hCr_head, hCr_res⟩ := hCr g₁ P htie hδ_le hδ0 hδ i
    obtain ⟨HdCu, hCu_head, hCu_res⟩ := hCu g₁ P htie hδ_le hδ0 hδ i
    refine ⟨HdCr - HdCu, ?_, ?_, ?_⟩
    · intro x
      rw [show ((HdCr - HdCu).toSection x) = HdCr.toSection x - HdCu.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
      have h1 := hCr_head x
      have h2 := hCu_head x
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCr.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCu.toSection x)
          ≤ 2 * (KtCr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
            2 * (KtCu * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
              (mul_le_mul_of_nonneg_left h2 (by norm_num))
        _ = (2 * KtCr + 2 * KtCu) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by ring
    · have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((HdCr - HdCu).toSection x) ≤
            (2 * KtCr + 2 * KtCu) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
        intro x
        rw [show ((HdCr - HdCu).toSection x) = HdCr.toSection x - HdCu.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
        have h1 := hCr_head x
        have h2 := hCu_head x
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (HdCr.toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCu.toSection x)
            ≤ 2 * (KtCr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
              2 * (KtCu * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
              add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
                (mul_le_mul_of_nonneg_left h2 (by norm_num))
          _ = (2 * KtCr + 2 * KtCu) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by ring
      have hF_int : MeasureTheory.Integrable
          (fun x => (2 * KtCr + 2 * KtCu) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
        (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 2))
          (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)).const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 2 (2 + i) (HdCr - HdCu) _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      rw [show (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 from by
        rw [SmoothCcTensor.norm_def (I := I) (M := M)
            (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P),
          tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
            g₀ 0 (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)]]
    · have harm0 : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ =
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
          ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) := by abel
      have hdiff : iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - (HdCr - HdCu) =
          iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)) := by
        rw [harm0]
        rw [show iteratedCovGrad (I := I) g₀ 2 2 i
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))) =
            iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
             iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) from by
          rw [iteratedCovGrad_add (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
            ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))]
          rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)]]
        abel
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
                (HdCr - HdCu)).toSection x) ≤
            (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
              Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
        intro x
        set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
        have hb : ∀ l, 0 ≤ b l :=
          fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
        have hW_one : 1 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
          Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
        have hW_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          linarith
        rw [hdiff]
        rw [show ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu))).toSection x) =
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x
            from by rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i)
          x _ _) ?_
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
            cbg i := hcbg i x
        have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            (((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x) ≤
            2 * (KcCr i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
              2 * (KcCu i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
          rw [show (((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x) =
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr).toSection x -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu).toSection x
              from by rw [SmoothCcTensor.toSection_sub]; rfl]
          refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
          exact add_le_add (mul_le_mul_of_nonneg_left (hCr_res x) (by norm_num))
            (mul_le_mul_of_nonneg_left (hCu_res x) (by norm_num))
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (((iteratedCovGrad (I := I) g₀ 2 2 i
                  (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                    ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
                (iteratedCovGrad (I := I) g₀ 2 2 i
                  (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                    ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x)
            ≤ 2 * cbg i +
              2 * (2 * (KcCr i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
                2 * (KcCu i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3))) := by
              refine add_le_add ?_ (mul_le_mul_of_nonneg_left h2 (by norm_num))
              have := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 2 by norm_num)
              linarith
          _ ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
              have hc1 : 2 * cbg i ≤ 2 * cbg i *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
                nlinarith [hcbg_nn i, hW_one]
              nlinarith [hKcCr_nn i, hKcCu_nn i, hW_nn]
      obtain ⟨hint, hbound_int⟩ := hKI P hPball i hia
      have hF_int : MeasureTheory.Integrable
          (fun x => (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hint.const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 2 (2 + i)
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - (HdCr - HdCu))
        _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      calc (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            ∫ x, Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
          ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            (KI i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left hbound_int ?_
            have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith
        _ = (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    refine ⟨0, fun x => (IsEmpty.false x).elim, ?_, ?_⟩
    · have hz : ‖(0 : SmoothCcTensor g₀ 2 (2 + i))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have := sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖
      nlinarith [hKtCr_nn, hKtCu_nn]
    · have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
          (0 : SmoothCcTensor g₀ 2 (2 + i))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have hKc_nn : (0 : ℝ) ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i :=
        mul_nonneg
          (by have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith)
          (hKI_nn i)
      nlinarith

end TopOrderSeparatedResidualIntegrator

end Spectral
end Analysis
end DifferentialGeometry

end
