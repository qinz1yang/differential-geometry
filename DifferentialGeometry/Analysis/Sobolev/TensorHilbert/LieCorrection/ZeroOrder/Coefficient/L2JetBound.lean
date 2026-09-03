import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Coefficient.L2JetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrectionZeroSplit
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieEndoTermField deTurckLieEndoTermField_toSection deTurckLieCovariantDerivativeInsertionFib)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (metricPerturbationPath)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem deTurckLieEndomorphismTerm_eq_covariantDerivativeInsertion (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieEndoTermField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieEndoTermField_toSection, deTurckLieCovariantDerivativeInsertionField_toSection]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem lieCorrectionZeroInsertion_base_eq_neg_covariantDerivativeInsertion (g₀ g₁ : SmoothRiemannianMetric I M) :
    lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀ =
      -deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g₀ := by
  have h := insert_base (I := I) (M := M) g₀ g₁ g₀
  rw [sub_self] at h
  rw [eq_neg_of_add_eq_zero_left h, deTurckLieEndomorphismTerm_eq_covariantDerivativeInsertion]

private theorem lieCorrectionZeroInsertionBase_metricPerturbationPath_perOrder_topOrderSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorrectionZeroInsertion (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hnn, Kc, hKcnn, h⟩ :=
    deTurckLieCovariantDerivativeInsertionField_metricPerturbationPath_jetL2_perOrder_topOrderSeparated (I := I) (M := M) g₀ g₀ a
      ha_super hR hδ₀
  refine ⟨Ktop, hnn, Kc, hKcnn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hb := h T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi
  rw [lieCorrectionZeroInsertion_base_eq_neg_covariantDerivativeInsertion, iteratedCovGrad_neg, norm_neg]
  exact hb

end DifferentialGeometry.Analysis.Sobolev

end
